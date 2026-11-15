-- Prove2me | Definitions.Def_RPLib_S4_KummerUnrCore
-- name    : RPLib_S4_KummerUnrCore
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:12:47.394266+00:00
-- url     : https://prove2.me/theorems/b1a72fd0-6ede-4806-92ec-999ef88ed15c
-- title:
--   An inertia element fixes an $N$-th root of an $N$-th-power ideal class
-- statement:
--   Let $M \le L$ be subfields of $\overline{K}$ and $\sigma$ an element of the inertia group of a prime $Q$ of the integral closure of $A$ in $L$ that fixes $M$. If $z^N = 1$, $z - 1 \in Q$ and $N$ is invertible then $z = 1$. Consequently, if $\gamma^N = a \in M$ and $$I^N \cdot (a) = (1)$$ for a fractional ideal $I$ of the integral closure of $A$ in $M$, then $\sigma(\gamma) = \gamma$: an $N$-th root of an element generating an $N$-th power ideal is not moved by inertia.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9 and Chapter IV, Section 3

import Mathlib
import Definitions.Def_RPLib_S4_KummerConst

/-!
# S4-Kummer, part K4a (core): an inertia element fixes an `N`-th root of an `N`-th-power ideal class

* `eq_one_of_sub_mem`: `z ^ N = 1`, `z - 1 ∈ Q` (prime), `N` invertible ⇒ `z = 1` (geometric sum).
* `fixed_of_inertia`: `M ≤ L` in `K̄`, `σ ∈ Q.inertia Gal(L/K)` fixing `M`, `γ ^ N = a ∈ M` with
  `I ^ N * (a) = 1` for a fractional ideal `I` of `integralClosure A M`: then `σ γ = γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

noncomputable section

/-- `z ^ N = 1` and `z ≡ 1` modulo a prime `Q` with `N` invertible force `z = 1`. -/
theorem eq_one_of_sub_mem {B : Type*} [CommRing B] [IsDomain B] {Q : Ideal B} [hQ : Q.IsPrime] {N : ℕ}
    (hN : IsUnit (N : B)) {z : B} (hz : z ^ N = 1) (hzQ : z - 1 ∈ Q) : z = 1 := by
  by_contra hne
  have hsum : ∑ i ∈ Finset.range N, z ^ i = 0 := by
    have h := geom_sum_mul z N
    rw [hz, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have hmod : (Ideal.Quotient.mk Q) z = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk Q), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hzQ
  have hN0 : (Ideal.Quotient.mk Q) (N : B) = 0 := by
    have h := congrArg (Ideal.Quotient.mk Q) hsum
    simp only [map_sum, map_pow, hmod, one_pow, map_zero, Finset.sum_const, Finset.card_range] at h
    simpa using h
  rw [Ideal.Quotient.eq_zero_iff_mem] at hN0
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hN0 hN)

section Core

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
variable {M L : IntermediateField K (AlgebraicClosure K)} (hML : M ≤ L)

/-- The `B_M`-submodule `{x ∈ M | x γⁿ ∈ Q}` of `M`. -/
def rootSub (Q : Ideal (integralClosure A L)) (γ : L) (n : ℕ) : Submodule (integralClosure A M) M where
  carrier := {x | ∃ q ∈ Q, ((q : integralClosure A L) : L) = IntermediateField.inclusion hML x * γ ^ n}
  add_mem' := by
    rintro x y ⟨q1, hq1, h1⟩ ⟨q2, hq2, h2⟩
    refine ⟨q1 + q2, Q.add_mem hq1 hq2, ?_⟩
    show (q1 : L) + (q2 : L) = _
    rw [h1, h2, map_add, add_mul]
  zero_mem' := ⟨0, Q.zero_mem, by simp⟩
  smul_mem' := by
    rintro b x ⟨q, hq, h⟩
    refine ⟨incl A K hML b * q, Q.mul_mem_left _ hq, ?_⟩
    show ((incl A K hML b : integralClosure A L) : L) * (q : L) = _
    rw [h, Algebra.smul_def, map_mul]
    have hb : ((incl A K hML b : integralClosure A L) : L) = IntermediateField.inclusion hML (b : M) := rfl
    rw [hb, mul_assoc]
    rfl

theorem mem_rootSub {Q : Ideal (integralClosure A L)} {γ : L} {n : ℕ} {x : M} :
    x ∈ rootSub hML Q γ n ↔
      ∃ q ∈ Q, ((q : integralClosure A L) : L) = IntermediateField.inclusion hML x * γ ^ n := Iff.rfl

/-- **Inertia fixes Kummer generators of `N`-th-power ideal classes.** -/
theorem fixed_of_inertia [IsFractionRing (integralClosure A M) M] {N : ℕ} [NeZero N] (hN : IsUnit (N : A)) (Q : Ideal (integralClosure A L))
    [hQ : Q.IsPrime] (σ : L ≃ₐ[K] L) (hσ : σ ∈ Q.inertia (L ≃ₐ[K] L))
    (hσM : ∀ x : M, σ (IntermediateField.inclusion hML x) = IntermediateField.inclusion hML x)
    {a : M} (I : FractionalIdeal (nonZeroDivisors (integralClosure A M)) M)
    (hI : I ^ N * FractionalIdeal.spanSingleton _ a = 1)
    (γ : L) (hγ : γ ^ N = IntermediateField.inclusion hML a) : σ γ = γ := by
  have hNpos : 0 < N := NeZero.pos N
  by_cases hγ0 : γ = 0
  · rw [hγ0, map_zero]
  by_contra hne
  have hI' : (I : Submodule (integralClosure A M) M) ^ N * Submodule.span (integralClosure A M) {a} = 1 := by
    rw [← FractionalIdeal.coe_pow, ← FractionalIdeal.coe_spanSingleton (nonZeroDivisors (integralClosure A M)) a, ← FractionalIdeal.coe_mul, hI,
      FractionalIdeal.coe_one]
  -- the root of unity `z = σ γ / γ`
  set z : L := σ γ / γ with hzdef
  have hσγ : σ γ = z * γ := by rw [hzdef, div_mul_cancel₀ _ hγ0]
  have hzN : z ^ N = 1 := by
    have h1 : (σ γ) ^ N = γ ^ N := by rw [← map_pow, hγ, hσM]
    rw [hσγ, mul_pow] at h1
    exact (mul_eq_right₀ (pow_ne_zero N hγ0)).1 h1
  have hzint : IsIntegral A z := IsIntegral.of_pow hNpos (by rw [hzN]; exact isIntegral_one)
  let zB : integralClosure A L := ⟨z, hzint⟩
  have hz1 : zB ≠ 1 := by
    intro h
    apply hne
    have hz : z = 1 := congrArg Subtype.val h
    rw [hσγ, hz, one_mul]
  have hNB : IsUnit (N : integralClosure A L) := by
    simpa using hN.map (algebraMap A (integralClosure A L))
  have hzB : zB ^ N = 1 := Subtype.ext (by simp [zB, hzN])
  have hzQ : zB - 1 ∉ Q := fun h => hz1 (eq_one_of_sub_mem hNB hzB h)
  -- every `e γ` with `e ∈ I` lies in `Q`
  have hW1 : (I : Submodule (integralClosure A M) M) ≤ rootSub hML Q γ 1 := by
    intro e he
    have hmem : e ^ N * a ∈ (1 : Submodule (integralClosure A M) M) := by
      rw [← hI']
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ he N) (Submodule.mem_span_singleton_self a)
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 hmem
    have hpow : (IntermediateField.inclusion hML e * γ) ^ N = IntermediateField.inclusion hML (b : M) := by
      rw [mul_pow, ← map_pow, hγ, ← map_mul]
      congr 1
      exact hb.symm
    have hbint : IsIntegral A (IntermediateField.inclusion hML (b : M)) :=
      (incl A K hML b).2
    have hint : IsIntegral A (IntermediateField.inclusion hML e * γ) :=
      IsIntegral.of_pow hNpos (by rw [hpow]; exact hbint)
    let y : integralClosure A L := ⟨_, hint⟩
    have hy : σ • y - y = (zB - 1) * y := by
      apply Subtype.ext
      show σ (IntermediateField.inclusion hML e * γ) - IntermediateField.inclusion hML e * γ =
        (z - 1) * (IntermediateField.inclusion hML e * γ)
      rw [map_mul, hσM, hσγ]
      ring
    have hyQ : σ • y - y ∈ Q := hσ y
    rw [hy] at hyQ
    refine ⟨y, (hQ.mem_or_mem hyQ).resolve_left hzQ, ?_⟩
    rw [pow_one]
  have hWn : ∀ n : ℕ, (I : Submodule (integralClosure A M) M) ^ (n + 1) ≤ rootSub hML Q γ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using hW1
    | succ n ih =>
      rw [pow_succ]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨q1, hq1, h1⟩ := ih hx
      obtain ⟨q2, hq2, h2⟩ := hW1 hy
      refine ⟨q1 * q2, Q.mul_mem_right _ hq1, ?_⟩
      show (q1 : L) * (q2 : L) = _
      rw [h1, h2, map_mul]
      ring
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hNpos).symm⟩
  have hfin : (I : Submodule (integralClosure A M) M) ^ N * Submodule.span (integralClosure A M) {a} ≤
      rootSub hML Q γ 0 := by
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [hn] at hx
    obtain ⟨q, hq, h⟩ := hWn n hx
    refine ⟨incl A K hML b * q, Q.mul_mem_left _ hq, ?_⟩
    show ((incl A K hML b : integralClosure A L) : L) * (q : L) = _
    have hb : ((incl A K hML b : integralClosure A L) : L) = IntermediateField.inclusion hML (b : M) := rfl
    have hab : algebraMap (integralClosure A M) M b = (b : M) := rfl
    rw [hb, h, ← hn, hγ, pow_zero, mul_one, Algebra.smul_def, hab, map_mul, map_mul]
    ring
  have h1 : (1 : M) ∈ rootSub hML Q γ 0 := by
    apply hfin
    rw [hI']
    exact Submodule.one_le.1 le_rfl
  obtain ⟨q, hq, hq1⟩ := h1
  rw [map_one, pow_zero, one_mul] at hq1
  have : q = 1 := Subtype.ext hq1
  exact hQ.ne_top ((Ideal.eq_top_iff_one Q).2 (this ▸ hq))

end Core

end

end Kummer
end RamanujanPetersson


