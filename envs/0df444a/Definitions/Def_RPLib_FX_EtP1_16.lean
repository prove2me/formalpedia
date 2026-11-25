-- Prove2me | Definitions.Def_RPLib_FX_EtP1_16
-- name    : RPLib_FX_EtP1_16
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T07:06:29.958608+00:00
-- url     : https://prove2.me/theorems/1e7f384b-5a0c-5a1d-b173-245f7d3832bd
-- title:
--   Étale cohomology of the projective line, library file 16 of 34
-- statement:
--   File 16 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Gm`: S4-EtCompact: the overlap of the two charts of `P^1` is `G_m` (O8c, file M3)
--   * `S4.Def_RP_Kummer_UnrCore`: S4-Kummer, part K4a (core): an inertia element fixes an `N`-th root of an `N`-th-power ideal class
--   * `S4.Def_RP_Kummer_Unr`: S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified
--   * `S4.Def_RP_Kummer_Bridge`: S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes
--   * `S4.Def_RP_EtCompact_GmRoot`: S4-EtCompact: Kummer theory of `G_m` (O8c, file M4a)
--   * `S4.Def_RP_EtCompact_KumForm`: S4-EtCompact, part 56: Kummer arithmetic for the local step (F7e1 of plan v5)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_37

/-!
# Étale cohomology of the projective line, library file 16 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Gm`: S4-EtCompact: the overlap of the two charts of `P^1` is `G_m` (O8c, file M3)
* `S4.Def_RP_Kummer_UnrCore`: S4-Kummer, part K4a (core): an inertia element fixes an `N`-th root of an `N`-th-power ideal class
* `S4.Def_RP_Kummer_Unr`: S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified
* `S4.Def_RP_Kummer_Bridge`: S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes
* `S4.Def_RP_EtCompact_GmRoot`: S4-EtCompact: Kummer theory of `G_m` (O8c, file M4a)
* `S4.Def_RP_EtCompact_KumForm`: S4-EtCompact, part 56: Kummer arithmetic for the local step (F7e1 of plan v5)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Gm =====
section

/-!
# S4-EtCompact: the overlap of the two charts of `P^1` is `G_m` (O8c, file M3)

* `LX k = k[X]_X`: a domain, a principal ideal ring; `Algebra (LX k) k(X)` with `IsScalarTower` and
  `IsFractionRing`; **`LX.unit_eq`**: every unit of `k[X]_X` is `c X^m` in `k(X)`.
* `chartGm k : Spec k[X]_X ⟶ P^1_k` (open immersion), **`P1.opensRange_chartGm`**: its range is the overlap
  `range chartA1 ⊓ range chartA1'`.
* **`P1.h2EquivGm`**: `H^2(P^1, Λ) ≃ H^1(G_m, Λ)` when `H^1(A^1, Λ) = H^2(A^1, Λ) = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section LX

variable (k : Type u) [Field k]

instance LX.isScalarTower : IsScalarTower k[X] (LX k) (RatFunc k) :=
  IsScalarTower.of_algebraMap_eq (fun p => (LX.algebraMap_algebraMap k p).symm)

instance LX.isFractionRing : IsFractionRing (LX k) (RatFunc k) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (X : k[X])) (LX k) (RatFunc k)

/-- **Units of `k[X]_X`**: `u = c X^m` in `k(X)`, `c ≠ 0`. -/
theorem LX.unit_eq (u : (LX k)ˣ) :
    ∃ (c : k) (m : ℤ), c ≠ 0 ∧ algebraMap (LX k) (RatFunc k) u = RatFunc.C c * RatFunc.X ^ m := by
  obtain ⟨⟨p, ⟨_, s, rfl⟩⟩, hp⟩ := IsLocalization.surj (Submonoid.powers (X : k[X])) (u : LX k)
  obtain ⟨⟨q, ⟨_, t, rfl⟩⟩, hq⟩ := IsLocalization.surj (Submonoid.powers (X : k[X])) ((u⁻¹ : (LX k)ˣ) : LX k)
  simp only at hp hq
  have hpq : p * q = X ^ (s + t) := by
    apply LX.injective k
    rw [map_mul, ← hp, ← hq, pow_add, map_mul]
    calc (u : LX k) * algebraMap k[X] (LX k) (X ^ s) * ((↑u⁻¹ : LX k) * algebraMap k[X] (LX k) (X ^ t))
        = ((u : LX k) * ↑u⁻¹) * (algebraMap k[X] (LX k) (X ^ s) * algebraMap k[X] (LX k) (X ^ t)) := by ring
      _ = _ := by rw [Units.mul_inv, one_mul]
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X (R := k)) (s + t)).1 (Dvd.intro q hpq)
  obtain ⟨w, hw⟩ := hi.symm
  obtain ⟨c, hc, hcw⟩ := Polynomial.isUnit_iff.1 w.isUnit
  have hpe : p = X ^ i * C c := by
    rw [hcw, hw]
  refine ⟨c, (i : ℤ) - s, hc.ne_zero, ?_⟩
  have h1 := congrArg (algebraMap (LX k) (RatFunc k)) hp
  rw [map_mul, LX.algebraMap_algebraMap, LX.algebraMap_algebraMap, hpe, map_mul, map_pow, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C] at h1
  have hX0 : (RatFunc.X : RatFunc k) ^ s ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  rw [zpow_sub₀ RatFunc.X_ne_zero, zpow_natCast, zpow_natCast, ← mul_div_assoc, eq_div_iff hX0, h1]
  ring

end LX

section Chart

variable (k : Type u) [Field k]

/-- **The overlap of the two charts of `P^1` is `G_m`.** -/
theorem P1.opensRange_chartGm :
    (chartGm k).opensRange = (chartA1 k).opensRange ⊓ (chartA1' k).opensRange := by
  have e : (chartGm k).opensRange =
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] (LX k))) ≫ chartA1 k).opensRange := rfl
  rw [e, Scheme.Hom.opensRange_comp, ← Scheme.Hom.image_preimage_eq_opensRange_inf,
    chartA1_preimage_range']
  congr 1
  exact Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of k[X]) X

variable {Λ : Type u} [CommRing Λ]

end Chart

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_Kummer_UnrCore =====
section

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


end

-- ===== S4.Def_RP_Kummer_Unr =====
section

/-!
# S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified

* `mem_fixingSubgroup_adjoin`: an automorphism of `K̄` fixing `S` fixes `K(S)`.
* `lift_mem_fixingSubgroup`: a lift to `K̄` of an inertia element of `Gal(L/K)` fixes every unramified
  Galois subextension of `L` (the `key` step of `GalCover.sup_mem_unramSet`).
* `root_mem_maxUnram`: `M ∈ unramSet A K`, `0 ≠ a ∈ M`, `N` invertible in `A`, and for every `τ ∈ Gal(M/K)` a
  fractional ideal `I` of `integralClosure A M` with `I ^ N * (τ a) = 1`: every `γ ∈ K̄` with `γ ^ N = a` lies in
  `K_U = maxUnram A K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Kummer

noncomputable section

variable {K : Type} [Field K]

/-- An automorphism of `K̄` fixing a generating set fixes the intermediate field it generates. -/
theorem mem_fixingSubgroup_adjoin {S : Set (AlgebraicClosure K)}
    {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K} (h : ∀ x ∈ S, σ x = x) :
    σ ∈ (IntermediateField.adjoin K S).fixingSubgroup := by
  have hle : IntermediateField.adjoin K S ≤
      IntermediateField.fixedField (_root_.fixingSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) S) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (_root_.mem_fixingSubgroup_iff _).1 hf x hx
  exact (IntermediateField.le_iff_le _ _).1 hle ((_root_.mem_fixingSubgroup_iff _).2 h)

section Lift

variable (A : Type) [CommRing A] [Algebra A K]

/-- A lift `σ` to `K̄` of an inertia element `τ ∈ Gal(L/K)` fixes every unramified Galois subextension `L' ≤ L`. -/
theorem lift_mem_fixingSubgroup {L L' : IntermediateField K (AlgebraicClosure K)} (hle : L' ≤ L) [IsGalois K L']
    (uL : IsUnramifiedSub A K L') (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime] (τ : L ≃ₐ[K] L)
    (hτ : τ ∈ Q.inertia (L ≃ₐ[K] L)) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ : ∀ y : L, σ (y : AlgebraicClosure K) = ((τ y : L) : AlgebraicClosure K)) : σ ∈ L'.fixingSubgroup := by
  have hP : (Q.comap (incl A K hle)).IsPrime := Ideal.IsPrime.comap _
  have hin : AlgEquiv.restrictNormalHom L' σ ∈ (Q.comap (incl A K hle)).inertia (L' ≃ₐ[K] L') := by
    intro y
    show (incl A K hle) (AlgEquiv.restrictNormalHom L' σ • y - y) ∈ Q
    have h : τ • incl A K hle y - incl A K hle y ∈ Q := hτ (incl A K hle y)
    convert h using 2
    apply Subtype.ext; apply Subtype.ext
    show ((AlgEquiv.restrictNormalHom L' σ (y : L') : L') : AlgebraicClosure K) - ((y : L') : AlgebraicClosure K)
      = ((τ (incl A K hle y : L) : L) : AlgebraicClosure K) - ((y : L') : AlgebraicClosure K)
    rw [AlgEquiv.restrictNormalHom_apply, ← hσ]
    rfl
  have h1 := uL _ hP
  rw [h1, Subgroup.mem_bot] at hin
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have := congrArg (fun e : L' ≃ₐ[K] L' => ((e ⟨x, hx⟩ : L') : AlgebraicClosure K)) hin
  simpa [AlgEquiv.restrictNormalHom_apply] using this

end Lift

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Bridge =====
section

/-!
# S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes

* `count_spanSingleton`: `val_v((a)) = -log v(a)` for a nonzero `a` in the fraction field of a Dedekind domain.
* `exists_pow_mul_spanSingleton_eq_one`: if `N ∣ log v(a)` for every height-one prime `v`, then
  `I ^ N * (a) = 1` for a fractional ideal `I`.
* `root_mem_maxUnram_of_dvd`: `M ∈ unramSet A K`, `0 ≠ a ∈ M` with `N ∣ log v(a)` at every prime of the integral
  closure of `A` in `M`, `N` invertible in `A`: every `γ ∈ K̄` with `γ ^ N = a` lies in `maxUnram A K`
  (Galois conjugates handled by `PicDescent.valuation_pullH`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson
namespace Kummer

noncomputable section

section Bridge

variable {B M : Type*} [CommRing B] [IsDedekindDomain B] [Field M] [Algebra B M] [IsFractionRing B M]

/-- `val_v((a)) = -log v(a)`. -/
theorem count_spanSingleton (v : HeightOneSpectrum B) {a : M} (ha : a ≠ 0) :
    FractionalIdeal.count M v (FractionalIdeal.spanSingleton (nonZeroDivisors B) a) =
      -WithZero.log (v.valuation M a) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) a
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact ha (by simp)
  have hspan : ∀ t : B, t ≠ 0 → Ideal.span {t} ≠ 0 := fun t ht => by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hM : ∀ t : B, t ≠ 0 → algebraMap B M t ≠ 0 := fun t ht =>
    (map_ne_zero_iff _ (IsFractionRing.injective B M)).2 ht
  rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul M v ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (hM r hr0))
      (inv_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (hM s hs0))),
    FractionalIdeal.count_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe M v (hspan r hr0),
    FractionalIdeal.count_coe M v (hspan s hs0), map_mul, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def,
    HeightOneSpectrum.intValuation_def, if_neg hr0, if_neg hs0, ← WithZero.exp_neg, ← WithZero.exp_add,
    WithZero.log_exp]
  ring

end Bridge

section Assembly

variable {K : Type} [Field K] (A : Type) [CommRing A] [Algebra A K]

end Assembly

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtCompact_GmRoot =====
section

/-!
# S4-EtCompact: Kummer theory of `G_m` (O8c, file M4a)

`R = k[X]_X`, `K = k(X)`, `E = K_U = maxUnram R K`, `Γ = π₁(G_m) = Gal(E/K)`.

* `LX.exists_root_X`: **`X^{1/N}` lies in `E`** (`N` invertible in `k`; `root_mem_maxUnram_of_dvd` with `M = K`,
  `X` a unit of `R`).
* `kchar_pow_left'`: `kchar (γ ^ j) = j • kchar γ`.
* **`LX.exists_kchar_eq_nsmul`**: for `k` algebraically closed, every Kummer character on `π₁(G_m)` is a multiple of
  the character of `X^{1/N}` (`α ^ N = c X^m b^N` by `dvd_ord_of_unram0` + units of `R`).
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr Kummer EtPi1

section Root

variable (k : Type) [Field k]

theorem LX.isUnit_algebraMap_X : IsUnit (algebraMap k[X] (LX k) X) :=
  IsLocalization.Away.algebraMap_isUnit X

theorem LX.algebraMap_X : algebraMap (LX k) (RatFunc k) (algebraMap k[X] (LX k) X) = RatFunc.X := by
  rw [LX.algebraMap_algebraMap, RatFunc.algebraMap_X]

theorem LX.isUnit_natCast {N : ℕ} (hN : (N : k) ≠ 0) : IsUnit (N : LX k) := by
  have h : IsUnit (C (N : k) : k[X]) := Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hN)
  rw [map_natCast] at h
  have h2 := h.map (algebraMap k[X] (LX k))
  rwa [map_natCast] at h2

end Root

section KPow

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)} {N : ℕ} [NeZero N]
  {ζ : E} (hζ : IsPrimitiveRoot ζ N)

end KPow

section Kum

variable {k : Type} [Field k] [IsAlgClosed k]

end Kum

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_KumForm =====
section

/-!
# S4-EtCompact, part 56: Kummer arithmetic for the local step (F7e1 of plan v5)

`ζ` a primitive `d`-th root of unity in a field `Ω`, `σ ∈ Aut_K(Ω)`.

* `dlog_mul_of`, `dlog_pow_of` (on `d`-th roots of unity), `ratio_pow_eq_one`;
* **`root_twist_pow`**: from `t c = v π^n`, `γ^d = c`, `ϖ^d = π`: `(γ t / ϖ^n)^d = v t^(d-1)`;
* **`dlog_twist`**: `dlog(σβ/β) = dlog(σγ/γ) - n dlog(σϖ/ϖ)` for `β = γ t / ϖ^n` with `σ t = t`;
* **`sum_twist`**: on a `d`-torsion group, `∑ (a i - n i b).val • e i = ∑ (a i).val • e i - b.val • ∑ n i • e i`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtCompact.KumForm

open RamanujanPetersson.Kummer

section Dlog

variable {Ω : Type} [Field Ω] {d : ℕ} [NeZero d] {ζ : Ω} (hζ : IsPrimitiveRoot ζ d)

theorem dlog_mul_of {x y : Ω} (hx : x ^ d = 1) (hy : y ^ d = 1) :
    dlog hζ (x * y) = dlog hζ x + dlog hζ y := by
  conv_lhs => rw [← epow_dlog hζ hx, ← epow_dlog hζ hy, ← epow_add hζ]
  exact dlog_epow hζ _

end Dlog

section Twist

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {d : ℕ} [NeZero d] {ζ : Ω} (hζ : IsPrimitiveRoot ζ d)

end Twist

section Sum

variable {M : Type*} [AddCommGroup M] {d : ℕ} [NeZero d]

end Sum

end RamanujanPetersson.EtCompact.KumForm

end

end


