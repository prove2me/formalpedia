-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogB
-- name    : RPLib_S3_DWSIsogB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:26:15.309988+00:00
-- url     : https://prove2.me/theorems/41531b34-703a-4701-ae30-5f61de529503
-- title:
--   Weight-two Ramanujan-Petersson library: `End_{F_q}(E)` is an imaginary quadratic order
-- statement:
--   `End_{F_q}(E)` is an imaginary quadratic order.
--
--   `W` is an elliptic curve over `F = F_q`, `a = q + 1 - #W(F)` its trace, `π` the `q`-Frobenius.
--
--   * `dws_comm_lift` : pairwise commuting elements of a ring live in a commutative ring mapping injectively
--     into it (so identities between commuting endomorphisms are checked by `linear_combination`).
--   * `endo_int_of_mul` : a rational endomorphism (`c θ = a`, `c ≠ 0`) is an integer;
--     `endo_int_of_mul_self` : `χ² = m ≥ 0` forces `χ ∈ ℤ`.
--   * **`two_D_mul`** : `2 (4q - a²) φ ∈ ℤ + ℤ π` for every `φ ∈ End_{F_q}(E)`.
--   * `endo_rs_indep` : `1, π` are `ℤ`-independent when `a² < 4q`; **`endFq_comm`** : `End_{F_q}(E)` is commutative.
--   * **`endFq_order_basis`** (`a² < 4q`): `End_{F_q}(E) = ℤ ⊕ ℤ ω` with `f ω = π - b`, `f > 0`,
--     `a = 2b + f tr ω`, `q = b² + f b tr ω + f² deg ω`, `a² - 4q = f² (tr ω² - 4 deg ω)` and `tr ω² < 4 deg ω`:
--     an order of the imaginary quadratic field `ℚ(π)` containing `ℤ[π]` with index `f`.
--   * `trace_sq_lt_of_not_dvd` : ordinary curves (`p ∤ a`) have `a² < 4q`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogA

/-!
# S3-DWS-Isog, part B: `End_{F_q}(E)` is an imaginary quadratic order

`W` is an elliptic curve over `F = F_q`, `a = q + 1 - #W(F)` its trace, `π` the `q`-Frobenius.

* `dws_comm_lift` : pairwise commuting elements of a ring live in a commutative ring mapping injectively
  into it (so identities between commuting endomorphisms are checked by `linear_combination`).
* `endo_int_of_mul` : a rational endomorphism (`c θ = a`, `c ≠ 0`) is an integer;
  `endo_int_of_mul_self` : `χ² = m ≥ 0` forces `χ ∈ ℤ`.
* **`two_D_mul`** : `2 (4q - a²) φ ∈ ℤ + ℤ π` for every `φ ∈ End_{F_q}(E)`.
* `endo_rs_indep` : `1, π` are `ℤ`-independent when `a² < 4q`; **`endFq_comm`** : `End_{F_q}(E)` is commutative.
* **`endFq_order_basis`** (`a² < 4q`): `End_{F_q}(E) = ℤ ⊕ ℤ ω` with `f ω = π - b`, `f > 0`,
  `a = 2b + f tr ω`, `q = b² + f b tr ω + f² deg ω`, `a² - 4q = f² (tr ω² - 4 deg ω)` and `tr ω² < 4 deg ω`:
  an order of the imaginary quadratic field `ℚ(π)` containing `ℤ[π]` with index `f`.
* `trace_sq_lt_of_not_dvd` : ordinary curves (`p ∤ a`) have `a² < 4q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

universe u

/-- Pairwise commuting elements of a ring live in a commutative ring that maps injectively into it. -/
lemma dws_comm_lift {R : Type u} [Ring R] (s : Set R) (hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    ∃ (T : Type u) (_ : CommRing T) (e : T →+* R), Function.Injective e ∧
      ∀ x ∈ s, ∃ x' : T, e x' = x := by
  let S : Subring R := Subring.centralizer (Set.centralizer s)
  have hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    Set.centralizer_centralizer_comm_of_comm hs x hx y hy
  let _ : CommRing S :=
    { (inferInstance : Ring S) with mul_comm := fun a b => Subtype.ext (hS a.1 a.2 b.1 b.2) }
  exact ⟨S, inferInstance, S.subtype, Subtype.val_injective,
    fun x hx => ⟨⟨x, Set.subset_centralizer_centralizer hx⟩, rfl⟩⟩

section Ordinary

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]

/-- **Ordinary curves have `a² < 4q`**: `a² = 4q` would force `p ∣ a`. -/
theorem trace_sq_lt_of_not_dvd (h : ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace W)) :
    RPLib.EllFq.trace W ^ 2 < 4 * (Fintype.card F : ℤ) := by
  classical
  have hle := trace_sq_le W (AlgebraicClosure F)
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨n, hp, hq⟩ := FiniteField.card F (ringChar F)
    apply h
    have hpq : (ringChar F : ℤ) ∣ (Fintype.card F : ℤ) := by
      rw [hq]
      push_cast
      exact dvd_pow_self _ n.ne_zero
    have hp' : Prime (ringChar F : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h2 : (ringChar F : ℤ) ∣ RPLib.EllFq.trace W ^ 2 := by
      rw [heq]
      exact dvd_mul_of_dvd_right hpq 4
    exact hp'.dvd_of_dvd_pow h2

end Ordinary

section Order

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF torsModule

lemma endo_deg_intCast (r : ℤ) : (deg (r : AddMonoid.End (Pt W L)) : ℤ) = r ^ 2 := by
  have h : (deg (r : AddMonoid.End (Pt W L)) : ℤ) =
      r ^ 2 + RPLib.EllFq.trace W * r * 0 + (Fintype.card F : ℤ) * 0 ^ 2 := by
    rw [intCast_eq_rsHom]; exact deg_rsHom r 0
  rw [h]; ring

lemma rsE_eq (x y : ℤ) :
    rsE W L x y = (x : AddMonoid.End (Pt W L)) + (y : AddMonoid.End (Pt W L)) * piE W L :=
  AddMonoidHom.ext fun P => by
    show rsHom W L x y P = x • P + y • RPLib.EllFq.frob W L P
    rw [rsHom_apply]

/-- **`1, π` are `ℤ`-independent** when `a² < 4q` (`deg (x + y π)` is positive definite). -/
theorem endo_rs_indep (ht : RPLib.EllFq.trace W ^ 2 < 4 * (Fintype.card F : ℤ)) {x y : ℤ}
    (h : (x : AddMonoid.End (Pt W L)) + (y : AddMonoid.End (Pt W L)) * piE W L = 0) :
    x = 0 ∧ y = 0 := by
  have hd : (deg (rsE W L x y) : ℤ) =
      x ^ 2 + RPLib.EllFq.trace W * x * y + (Fintype.card F : ℤ) * y ^ 2 := deg_rsHom x y
  have h0 : deg (0 : AddMonoid.End (Pt W L)) = 0 := deg_zero
  rw [rsE_eq, h, h0, Nat.cast_zero] at hd
  have hy : y = 0 := by
    by_contra hy
    have h1 : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
    nlinarith [sq_nonneg (2 * x + RPLib.EllFq.trace W * y), mul_pos (sub_pos.mpr ht) h1]
  subst hy
  have h2 : x ^ 2 = 0 := by linarith
  exact ⟨(pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2, rfl⟩

/-- A rational endomorphism is an integer: `c θ = a` with `c ≠ 0` forces `θ ∈ ℤ`. -/
lemma endo_int_of_mul {θ : AddMonoid.End (Pt W L)} (hθ : θ ∈ endRing W L) {c a : ℤ}
    (hc : c ≠ 0) (h : (c : AddMonoid.End (Pt W L)) * θ = a) :
    ∃ k : ℤ, θ = k := by
  have h1 := deg_mul (intCast_mem (endRing W L) c) hθ
  rw [h] at h1
  have h2 := endo_deg_intCast (W := W) (L := L) a
  have h3 := endo_deg_intCast (W := W) (L := L) c
  have h4 : a ^ 2 = c ^ 2 * (deg θ : ℤ) := by
    rw [← h2, ← h3, h1, Nat.cast_mul]
  obtain ⟨k, rfl⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨_, h4⟩
  refine ⟨k, ?_⟩
  have h5 : (c : AddMonoid.End (Pt W L)) * (θ - k) = 0 := by
    rw [mul_sub, h, Int.cast_mul, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_intCast_mul hc h5)

/-- An endomorphism whose square is a nonnegative integer is an integer. -/
lemma endo_int_of_mul_self {χ : AddMonoid.End (Pt W L)} (hχ : χ ∈ endRing W L) {m : ℤ}
    (hm : 0 ≤ m) (h : χ * χ = m) : ∃ k : ℤ, χ = k := by
  have hc := ch hχ
  rw [h] at hc
  have h2 : (tr χ : AddMonoid.End (Pt W L)) * χ =
      ((m + deg χ : ℤ) : AddMonoid.End (Pt W L)) := by
    refine sub_eq_zero.mp ?_
    rw [← neg_eq_zero, ← hc, Int.cast_add]
    abel
  by_cases hc0 : tr χ = 0
  · rw [hc0, Int.cast_zero, zero_mul] at h2
    have h3 : m + deg χ = 0 := intCast_eq_zero h2.symm
    have h4 : m = 0 := by have := Int.natCast_nonneg (deg χ); omega
    rw [h4, Int.cast_zero] at h
    have h5 : χ = 0 := by
      rcases (mul_eq_zero_iff hχ).mp h with h6 | h6 <;> exact h6
    exact ⟨0, by rw [h5, Int.cast_zero]⟩
  · exact endo_int_of_mul hχ hc0 h2

/-- **`2 D φ ∈ ℤ + ℤ π`** for every `φ ∈ End_{F_q}(E)`, `D = 4q - a²`
(`χ = (2φ - tr φ)(2π - a)` has `χ² = (4 deg φ - tr φ²) D ≥ 0`, so `χ ∈ ℤ`). -/
theorem two_D_mul {φ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endFq W L) :
    ∃ x y : ℤ, ((2 * (4 * (Fintype.card F : ℤ) - RPLib.EllFq.trace W ^ 2) : ℤ) :
      AddMonoid.End (Pt W L)) * φ =
        (x : AddMonoid.End (Pt W L)) + (y : AddMonoid.End (Pt W L)) * piE W L := by
  obtain ⟨hφR, hφπ⟩ := mem_endFq.mp hφ
  have hcomm : ∀ x ∈ ({φ, piE W L} : Set (AddMonoid.End (Pt W L))),
      ∀ y ∈ ({φ, piE W L} : Set (AddMonoid.End (Pt W L))), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | rfl | exact hφπ | exact hφπ.symm
  obtain ⟨T, _, e, he, hlift⟩ := dws_comm_lift _ hcomm
  obtain ⟨a, ha⟩ := hlift φ (by simp)
  obtain ⟨b, hb⟩ := hlift (piE W L) (by simp)
  have hA : a * a - (tr φ : T) * a + ((deg φ : ℤ) : T) = 0 :=
    he (by simpa only [map_add, map_sub, map_mul, map_intCast, map_zero, ha] using ch hφR)
  have hB : b * b - (RPLib.EllFq.trace W : T) * b + ((Fintype.card F : ℤ) : T) = 0 :=
    he (by simpa only [map_add, map_sub, map_mul, map_intCast, map_zero, hb] using
      frob_ch (W := W) (L := L))
  have key : (((2 : ℤ) : T) * a - (tr φ : T)) * (((2 : ℤ) : T) * b - (RPLib.EllFq.trace W : T)) *
      ((((2 : ℤ) : T) * a - (tr φ : T)) * (((2 : ℤ) : T) * b - (RPLib.EllFq.trace W : T))) =
      (((4 * (deg φ : ℤ) - tr φ ^ 2) *
        (4 * (Fintype.card F : ℤ) - RPLib.EllFq.trace W ^ 2) : ℤ) : T) := by
    push_cast at hA hB ⊢
    linear_combination (4 * (2 * b - (RPLib.EllFq.trace W : T)) ^ 2) * hA +
      (4 * ((tr φ : T) ^ 2 - 4 * (deg φ : T))) * hB
  have hm : 0 ≤ (4 * (deg φ : ℤ) - tr φ ^ 2) *
      (4 * (Fintype.card F : ℤ) - RPLib.EllFq.trace W ^ 2) :=
    mul_nonneg (by linarith [tr_sq_le hφR]) (by linarith [trace_sq_le W L])
  have hχR : e ((((2 : ℤ) : T) * a - (tr φ : T)) *
      (((2 : ℤ) : T) * b - (RPLib.EllFq.trace W : T))) ∈ endRing W L := by
    simp only [map_mul, map_sub, map_intCast, ha, hb]
    exact mul_mem (sub_mem (mul_mem (intCast_mem _ 2) hφR) (intCast_mem _ _))
      (sub_mem (mul_mem (intCast_mem _ 2) (endFq_le frob_mem_endFq)) (intCast_mem _ _))
  obtain ⟨k, hk⟩ := endo_int_of_mul_self hχR hm (by rw [← map_mul e, key, map_intCast])
  have hk' : (((2 : ℤ) : T) * a - (tr φ : T)) * (((2 : ℤ) : T) * b - (RPLib.EllFq.trace W : T)) =
      (k : T) := he (by rw [hk, map_intCast])
  refine ⟨tr φ * (4 * (Fintype.card F : ℤ) - RPLib.EllFq.trace W ^ 2) + k * RPLib.EllFq.trace W,
    -2 * k, ?_⟩
  have key2 : ((2 * (4 * (Fintype.card F : ℤ) - RPLib.EllFq.trace W ^ 2) : ℤ) : T) * a =
      ((tr φ * (4 * (Fintype.card F : ℤ) - RPLib.EllFq.trace W ^ 2) +
        k * RPLib.EllFq.trace W : ℤ) : T) + ((-2 * k : ℤ) : T) * b := by
    push_cast at hk' hB ⊢
    linear_combination (-(2 * b - (RPLib.EllFq.trace W : T))) * hk' +
      (4 * (2 * a - (tr φ : T))) * hB
  simpa only [map_mul, map_add, map_intCast, ha, hb] using congrArg e key2

/-- **`End_{F_q}(E)` is commutative** when `a² < 4q`. -/
theorem endFq_comm (ht : RPLib.EllFq.trace W ^ 2 < 4 * (Fintype.card F : ℤ))
    {φ ψ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endFq W L) (hψ : ψ ∈ endFq W L) :
    φ * ψ = ψ * φ := by
  obtain ⟨x₁, y₁, h₁⟩ := two_D_mul hφ
  obtain ⟨x₂, y₂, h₂⟩ := two_D_mul hψ
  set c : ℤ := 2 * (4 * (Fintype.card F : ℤ) - RPLib.EllFq.trace W ^ 2) with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hc0 : c * c ≠ 0 := mul_ne_zero hcpos.ne' hcpos.ne'
  have hπc : ∀ (x y : ℤ) (z : AddMonoid.End (Pt W L)), Commute z (piE W L) →
      Commute z ((x : AddMonoid.End (Pt W L)) + (y : AddMonoid.End (Pt W L)) * piE W L) :=
    fun x y z hz => (Int.cast_commute x z).symm.add_right ((Int.cast_commute y z).symm.mul_right hz)
  have hcomm := hπc x₂ y₂ _ ((Int.cast_commute x₁ (piE W L)).add_left
    ((Int.cast_commute y₁ (piE W L)).mul_left (Commute.refl _)))
  rw [← h₁, ← h₂] at hcomm
  have e1 := (Int.cast_commute c φ).symm.mul_mul_mul_comm (c : AddMonoid.End (Pt W L)) ψ
  have e2 := (Int.cast_commute c ψ).symm.mul_mul_mul_comm (c : AddMonoid.End (Pt W L)) φ
  apply sub_eq_zero.mp
  apply eq_zero_of_intCast_mul hc0
  rw [mul_sub, Int.cast_mul, ← e1, ← e2, hcomm.eq, sub_self]

variable (W L) in
/-- The `π`-coefficients `y` of `c φ = x + y π`, `φ ∈ End_{F_q}(E)`: a subgroup of `ℤ`. -/
noncomputable def piCoeffs (c : ℤ) : AddSubgroup ℤ where
  carrier := {y | ∃ φ ∈ endFq W L, ∃ x : ℤ,
    (c : AddMonoid.End (Pt W L)) * φ = x + (y : AddMonoid.End (Pt W L)) * piE W L}
  add_mem' := by
    rintro y₁ y₂ ⟨φ₁, h₁m, x₁, h₁⟩ ⟨φ₂, h₂m, x₂, h₂⟩
    refine ⟨φ₁ + φ₂, add_mem h₁m h₂m, x₁ + x₂, ?_⟩
    rw [mul_add, h₁, h₂, Int.cast_add, Int.cast_add, add_mul]
    abel
  zero_mem' := ⟨0, zero_mem _, 0, by simp⟩
  neg_mem' := by
    rintro y ⟨φ, hm, x, h⟩
    refine ⟨-φ, neg_mem hm, -x, ?_⟩
    have e1 : (c : AddMonoid.End (Pt W L)) * -φ = -((c : AddMonoid.End (Pt W L)) * φ) := by
      first
        | exact mul_neg (c : AddMonoid.End (Pt W L)) φ
        | exact AddMonoidHom.ext fun P => map_neg _ _
    have e2 : ((-y : ℤ) : AddMonoid.End (Pt W L)) * piE W L =
        -((y : AddMonoid.End (Pt W L)) * piE W L) := by
      rw [Int.cast_neg]; exact neg_mul (y : AddMonoid.End (Pt W L)) (piE W L)
    rw [e1, e2, h, Int.cast_neg]
    exact neg_add (x : AddMonoid.End (Pt W L)) ((y : AddMonoid.End (Pt W L)) * piE W L)

lemma mem_piCoeffs {c y : ℤ} : y ∈ piCoeffs W L c ↔ ∃ φ ∈ endFq W L, ∃ x : ℤ,
    (c : AddMonoid.End (Pt W L)) * φ = x + (y : AddMonoid.End (Pt W L)) * piE W L := Iff.rfl

/-- **`End_{F_q}(E)` is an order of the imaginary quadratic field `ℚ(π)`** (`a² < 4q`):
`End_{F_q}(E) = ℤ ⊕ ℤ ω` with `f ω = π - b`, `f > 0` (so `ℤ[π] ⊆ End_{F_q}(E)` with index `f`),
`a = 2b + f tr ω`, `q = b² + f b tr ω + f² deg ω`, `a² - 4q = f² (tr ω² - 4 deg ω)`, `tr ω² < 4 deg ω`. -/
theorem endFq_order_basis (ht : RPLib.EllFq.trace W ^ 2 < 4 * (Fintype.card F : ℤ)) :
    ∃ (f b : ℤ) (ω : AddMonoid.End (Pt W L)), 0 < f ∧ ω ∈ endFq W L ∧
      (f : AddMonoid.End (Pt W L)) * ω = piE W L - (b : AddMonoid.End (Pt W L)) ∧
      (∀ φ ∈ endFq W L, ∃ i j : ℤ,
        φ = (i : AddMonoid.End (Pt W L)) + (j : AddMonoid.End (Pt W L)) * ω) ∧
      (∀ i j : ℤ, (i : AddMonoid.End (Pt W L)) + (j : AddMonoid.End (Pt W L)) * ω = 0 →
        i = 0 ∧ j = 0) ∧
      RPLib.EllFq.trace W = 2 * b + f * tr ω ∧
      (Fintype.card F : ℤ) = b ^ 2 + f * tr ω * b + f ^ 2 * (deg ω : ℤ) ∧
      RPLib.EllFq.trace W ^ 2 - 4 * (Fintype.card F : ℤ) = f ^ 2 * (tr ω ^ 2 - 4 * (deg ω : ℤ)) ∧
      tr ω ^ 2 < 4 * (deg ω : ℤ) := by
  set c : ℤ := 2 * (4 * (Fintype.card F : ℤ) - RPLib.EllFq.trace W ^ 2) with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  -- a commutative model of `End_{F_q}(E)`
  obtain ⟨T, _, e, he, hlift⟩ := dws_comm_lift (endFq W L : Set (AddMonoid.End (Pt W L)))
    (fun x hx y hy => endFq_comm ht hx hy)
  obtain ⟨p, hp⟩ := hlift (piE W L) frob_mem_endFq
  have hpT : p * p - (RPLib.EllFq.trace W : T) * p + ((Fintype.card F : ℤ) : T) = 0 :=
    he (by simpa only [map_add, map_sub, map_mul, map_intCast, map_zero, hp] using
      frob_ch (W := W) (L := L))
  -- the `π`-coefficients form `|g| ℤ`
  obtain ⟨g, hg⟩ := Int.subgroup_cyclic (piCoeffs W L c)
  have hdvd : ∀ y ∈ piCoeffs W L c, |g| ∣ y := by
    intro y hy
    rw [hg, AddSubgroup.mem_closure_singleton] at hy
    obtain ⟨n, rfl⟩ := hy
    exact (abs_dvd g _).mpr (Dvd.intro_left n (smul_eq_mul n g).symm)
  have hgY : |g| ∈ piCoeffs W L c := by
    have h1 : g ∈ piCoeffs W L c := by
      rw [hg]; exact AddSubgroup.subset_closure (Set.mem_singleton g)
    rcases abs_choice g with h | h
    · rw [h]; exact h1
    · rw [h]; exact (piCoeffs W L c).neg_mem h1
  have hcY : c ∈ piCoeffs W L c :=
    mem_piCoeffs.mpr ⟨piE W L, frob_mem_endFq, 0, by rw [Int.cast_zero, zero_add]⟩
  obtain ⟨f, hf⟩ := hdvd c hcY
  have hg0 : 0 < |g| := by
    rcases (abs_nonneg g).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, zero_mul] at hf; linarith
  have hfpos : 0 < f := by nlinarith
  obtain ⟨ω₀, hω₀, x₀, hx₀⟩ := mem_piCoeffs.mp hgY
  obtain ⟨w, hw⟩ := hlift ω₀ hω₀
  have hx₀T : (c : T) * w = (x₀ : T) + ((|g| : ℤ) : T) * p :=
    he (by simpa only [map_add, map_mul, map_intCast, hw, hp] using hx₀)
  have hcT : (c : T) = ((|g| : ℤ) : T) * (f : T) := by rw [hf, Int.cast_mul]
  -- `f ω₀ - π` is an integer `k`
  have hθ : (c : AddMonoid.End (Pt W L)) * ((f : AddMonoid.End (Pt W L)) * ω₀ - piE W L) =
      ((f * x₀ : ℤ) : AddMonoid.End (Pt W L)) := by
    have key : (c : T) * ((f : T) * w - p) = ((f * x₀ : ℤ) : T) := by
      push_cast
      linear_combination (f : T) * hx₀T - p * hcT
    simpa only [map_mul, map_sub, map_intCast, hw, hp] using congrArg e key
  obtain ⟨k, hk⟩ := endo_int_of_mul (endFq_le (sub_mem (mul_mem (intCast_mem (endFq W L) f) hω₀)
    frob_mem_endFq)) hcpos.ne' hθ
  have hfω' : (f : AddMonoid.End (Pt W L)) * ω₀ = piE W L + (k : AddMonoid.End (Pt W L)) := by
    rw [← hk]; abel
  have hfω : (f : AddMonoid.End (Pt W L)) * ω₀ = piE W L - ((-k : ℤ) : AddMonoid.End (Pt W L)) := by
    rw [Int.cast_neg, sub_neg_eq_add]; exact hfω'
  have hfωT : (f : T) * w = p + (k : T) :=
    he (by simpa only [map_add, map_mul, map_intCast, hw, hp] using hfω')
  -- `1, ω₀` are independent
  have hind : ∀ i j : ℤ, (i : AddMonoid.End (Pt W L)) + (j : AddMonoid.End (Pt W L)) * ω₀ = 0 →
      i = 0 ∧ j = 0 := by
    intro i j hij
    have hijT : (i : T) + (j : T) * w = 0 :=
      he (by simpa only [map_add, map_mul, map_intCast, map_zero, hw] using hij)
    have key : ((f * i - j * -k : ℤ) : T) + (j : T) * p = 0 := by
      push_cast
      linear_combination (f : T) * hijT - (j : T) * hfωT
    have key' := congrArg e key
    rw [map_zero] at key'
    obtain ⟨h3, h4⟩ := endo_rs_indep (x := f * i - j * -k) (y := j) ht
      (by simpa only [map_add, map_mul, map_intCast, hp] using key')
    subst h4
    refine ⟨?_, rfl⟩
    have h5 : f * i = 0 := by linarith
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact absurd h6 hfpos.ne'
    · exact h6
  have hindT : ∀ i j : ℤ, (i : T) + (j : T) * w = 0 → i = 0 ∧ j = 0 := fun i j h =>
    hind i j (by simpa only [map_add, map_mul, map_intCast, map_zero, hw] using congrArg e h)
  -- every `φ` is `i + j ω₀`
  have hbasis : ∀ φ ∈ endFq W L, ∃ i j : ℤ,
      φ = (i : AddMonoid.End (Pt W L)) + (j : AddMonoid.End (Pt W L)) * ω₀ := by
    intro φ hφ
    obtain ⟨x, y, h⟩ := two_D_mul hφ
    rw [← hc] at h
    obtain ⟨j, hj⟩ := hdvd y (mem_piCoeffs.mpr ⟨φ, hφ, x, h⟩)
    obtain ⟨a, ha⟩ := hlift φ hφ
    have hT : (c : T) * a = (x : T) + (y : T) * p :=
      he (by simpa only [map_add, map_mul, map_intCast, ha, hp] using h)
    have hyT : (y : T) = ((|g| : ℤ) : T) * (j : T) := by rw [hj, Int.cast_mul]
    have key : (c : T) * (a - (j : T) * w) = ((x - j * x₀ : ℤ) : T) := by
      push_cast
      linear_combination hT - (j : T) * hx₀T + p * hyT
    have hR : (c : AddMonoid.End (Pt W L)) * (φ - (j : AddMonoid.End (Pt W L)) * ω₀) =
        ((x - j * x₀ : ℤ) : AddMonoid.End (Pt W L)) := by
      simpa only [map_mul, map_sub, map_intCast, ha, hw] using congrArg e key
    obtain ⟨i, hi⟩ := endo_int_of_mul
      (endFq_le (sub_mem hφ (mul_mem (intCast_mem (endFq W L) j) hω₀))) hcpos.ne' hR
    exact ⟨i, j, sub_eq_iff_eq_add.mp hi⟩
  -- trace and norm relations
  have chω := ch (endFq_le hω₀)
  have hwT : w * w - (tr ω₀ : T) * w + ((deg ω₀ : ℤ) : T) = 0 :=
    he (by simpa only [map_add, map_sub, map_mul, map_intCast, map_zero, hw] using chω)
  have keyR : (((-k) ^ 2 - RPLib.EllFq.trace W * (-k) + (Fintype.card F : ℤ) -
      f ^ 2 * (deg ω₀ : ℤ) : ℤ) : T) +
      ((f ^ 2 * tr ω₀ + 2 * f * (-k) - RPLib.EllFq.trace W * f : ℤ) : T) * w = 0 := by
    push_cast at hpT hwT ⊢
    linear_combination hpT + (p + (f : T) * w - (k : T) - (RPLib.EllFq.trace W : T)) * hfωT -
      (f : T) ^ 2 * hwT
  obtain ⟨h1, h2⟩ := hindT _ _ keyR
  have htr : RPLib.EllFq.trace W = 2 * -k + f * tr ω₀ := by
    have h3 : f * (f * tr ω₀ + 2 * (-k) - RPLib.EllFq.trace W) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hfpos.ne'
    · linarith
  have hq : (Fintype.card F : ℤ) = (-k) ^ 2 + f * tr ω₀ * -k + f ^ 2 * (deg ω₀ : ℤ) := by
    linear_combination h1 + (-k) * htr
  have hdisc : RPLib.EllFq.trace W ^ 2 - 4 * (Fintype.card F : ℤ) =
      f ^ 2 * (tr ω₀ ^ 2 - 4 * (deg ω₀ : ℤ)) := by
    linear_combination (RPLib.EllFq.trace W + 2 * (-k) + f * tr ω₀) * htr - 4 * hq
  have hneg : tr ω₀ ^ 2 < 4 * (deg ω₀ : ℤ) := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg (sq_nonneg f) (sub_nonneg.mpr hcon)]
  exact ⟨f, -k, ω₀, hfpos, hω₀, hfω, hbasis, hind, htr, hq, hdisc, hneg⟩

end Order

end RPLib.DWS


