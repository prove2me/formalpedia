-- Prove2me | Definitions.Def_RPLib_S4_CDPack39
-- name    : RPLib_S4_CDPack39
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:46:40.687606+00:00
-- url     : https://prove2.me/theorems/d0bf928b-75f5-419b-a0d5-7bc350d281b9
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 39 of 71
-- statement:
--   Part 39 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_Center`: The Jacobian (unit S4-JacComplete), part `Center` (the place of a `K`-point of a chart of `X1`)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack38
import Definitions.Def_RPLib_S4_CDPack23
import Definitions.Def_RPLib_S4_CDPack28c

/-!
# Curve-duality library package, part 39 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_Center`: The Jacobian (unit S4-JacComplete), part `Center` (the place of a `K`-point of a chart of `X1`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_Center =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Center` (the place of a `K`-point of a chart of `X1`)

For `x = algebraMap K[X] F X` and a nonempty finset `A ⊆ K`, the chart ring `B_A = chartRing x A`.
* `IsCenter R ψ`: the place `R` is `≤ 1` on `B_A` and `< 1` exactly on `ker ψ` (`ψ : B_A →ₐ[K] K`).
* `isCenter_restrict` / `isCenter_extend`: centers pass between `B_A ⊆ B_A'` (`B_A' ⊆ B_A[1/w]`, `wt` lemmas).
* `rfinG c : B_{c} ≃ₐ[K] Rfin K (SynF K F c)`, `ptSyn c ψ`, **`plc c ψ`** `:= (synPlace c).symm (inl (ptP (ptSyn c ψ)))`.
* **`isCenter_plc`**, **`eq_plc_of_isCenter`** (uniqueness), `isCenter_unique`, **`plc_eq_plc`** (chart independence).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw
open RamanujanPetersson.JacSym (chartRing wt chartRing_mono)

section Center

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- The place `R` is the center of the `K`-point `ψ` of the chart ring `B_A`. -/
def IsCenter (R : Place K F) {A : Finset K} (ψ : chartRing (algebraMap K[X] F X) A →ₐ[K] K) : Prop :=
  (∀ y : chartRing (algebraMap K[X] F X) A, placeVal R (y : F) ≤ 1) ∧
    ∀ y : chartRing (algebraMap K[X] F X) A, placeVal R (y : F) < 1 ↔ ψ y = 0

theorem isCenter_restrict {R : Place K F} {A A' : Finset K} (h : A ⊆ A')
    (ψ : chartRing (algebraMap K[X] F X) A' →ₐ[K] K) (hR : IsCenter R ψ) :
    IsCenter R (ψ.comp (Subalgebra.inclusion (chartRing_mono _ h))) := by
  refine ⟨fun y => ?_, fun y => ?_⟩
  · have h1 := hR.1 (Subalgebra.inclusion (chartRing_mono _ h) y)
    rwa [Subalgebra.coe_inclusion] at h1
  · have h1 := hR.2 (Subalgebra.inclusion (chartRing_mono _ h) y)
    rwa [Subalgebra.coe_inclusion, ← AlgHom.comp_apply] at h1

theorem isCenter_extend [DecidableEq K] {R : Place K F} {A A' : Finset K} (h : A ⊆ A') {c0 : K} (hc0 : c0 ∈ A)
    (ψ : chartRing (algebraMap K[X] F X) A' →ₐ[K] K)
    (hR : IsCenter R (ψ.comp (Subalgebra.inclusion (chartRing_mono _ h)))) : IsCenter R ψ := by
  have hx := transcendental_xF K F
  have hR2 : ∀ y : chartRing (algebraMap K[X] F X) A, placeVal R (y : F) < 1 ↔
      ψ (Subalgebra.inclusion (chartRing_mono _ h) y) = 0 := fun y => by
    rw [hR.2 y, AlgHom.comp_apply]
  have hwA : wt (algebraMap K[X] F X) c0 (A' \ A) ∈ chartRing (algebraMap K[X] F X) A := JacSym.wt_mem_chartRing hx hc0 _
  have hwinv : (wt (algebraMap K[X] F X) c0 (A' \ A))⁻¹ ∈ chartRing (algebraMap K[X] F X) A' :=
    JacSym.wt_inv_mem_chartRing hx Finset.sdiff_subset c0
  have hψw : ψ (Subalgebra.inclusion (chartRing_mono _ h) ⟨_, hwA⟩) ≠ 0 := by
    intro h0
    have e1 : Subalgebra.inclusion (chartRing_mono _ h) ⟨_, hwA⟩ * ⟨_, hwinv⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ (JacSym.wt_ne_zero hx c0 _))
    have e2 := congrArg ψ e1
    rw [map_mul, h0, zero_mul, map_one] at e2
    exact zero_ne_one e2
  have hvw : placeVal R (wt (algebraMap K[X] F X) c0 (A' \ A)) = 1 :=
    le_antisymm (hR.1 ⟨_, hwA⟩) (not_lt.1 fun hlt => hψw ((hR2 ⟨_, hwA⟩).1 hlt))
  have e1 : ∀ (n : ℕ) (y : F), placeVal R (wt (algebraMap K[X] F X) c0 (A' \ A) ^ n * y) = placeVal R y := fun n y => by
    rw [map_mul, map_pow, hvw, one_pow, one_mul]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · obtain ⟨n, hn⟩ := JacSym.exists_pow_mul_mem_chartRing hx hc0 y.2
    have h1 : placeVal R (wt (algebraMap K[X] F X) c0 (A' \ A) ^ n * y) ≤ 1 := hR.1 ⟨_, hn⟩
    rwa [e1] at h1
  · obtain ⟨n, hn⟩ := JacSym.exists_pow_mul_mem_chartRing hx hc0 y.2
    have h1 : placeVal R (wt (algebraMap K[X] F X) c0 (A' \ A) ^ n * y) < 1 ↔
        ψ (Subalgebra.inclusion (chartRing_mono _ h) ⟨_, hn⟩) = 0 := hR2 ⟨_, hn⟩
    have e2 : Subalgebra.inclusion (chartRing_mono _ h) (⟨_, hn⟩ : chartRing (algebraMap K[X] F X) A) =
        (Subalgebra.inclusion (chartRing_mono _ h) ⟨_, hwA⟩) ^ n * y := Subtype.ext (by simp)
    rw [e1, e2, map_mul, map_pow] at h1
    rw [h1, mul_eq_zero, or_iff_right (pow_ne_zero n hψw)]

variable (c : K)

/-- `B_{c}` as the ring of `x'`-integers `Rfin K (SynF K F c)`. -/
noncomputable def rfinG : chartRing (algebraMap K[X] F X) {c} ≃ₐ[K] Rfin K (SynF K F c) :=
  (rfinSynEquiv c).trans
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

theorem rfinG_coe (y : chartRing (algebraMap K[X] F X) {c}) :
    ((rfinG c y : Rfin K (SynF K F c)) : SynF K F c) = synEquiv K F c y := rfl

theorem placeVal_synPlace (R : Place K F) (f : F) :
    placeVal (synPlace c R) (synEquiv K F c f) = placeVal R f := by
  rw [synPlace, placeEquiv_apply, placeVal_placeMap, Valuation.comap_apply]
  have e : ((synEquiv K F c).symm : SynF K F c →+* F) (synEquiv K F c f) = f :=
    (synEquiv K F c).symm_apply_apply f
  rw [e]

variable [IsAlgClosed K]

/-- The `K`-point of `Rfin K (SynF K F c)` attached to a `K`-point of `B_{c}`. -/
noncomputable def ptSyn (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) : Rfin K (SynF K F c) →ₐ[K] K :=
  ψ.comp (rfinG c).symm.toAlgHom

theorem ptSyn_rfinG (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) (y : chartRing (algebraMap K[X] F X) {c}) :
    ptSyn c ψ (rfinG c y) = ψ y := by
  simp [ptSyn]

/-- **The place of a `K`-point of the chart `{c}`.** -/
noncomputable def plc (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) : Place K F :=
  (synPlace c).symm (Sum.inl (ptP (ptSyn c ψ)))

theorem synPlace_plc (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) :
    synPlace c (plc c ψ) = Sum.inl (ptP (ptSyn c ψ)) :=
  Equiv.apply_symm_apply _ _

theorem placeVal_plc (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) (y : chartRing (algebraMap K[X] F X) {c}) :
    placeVal (plc c ψ) (y : F) = (ptP (ptSyn c ψ)).valuation (SynF K F c)
      (algebraMap (Rfin K (SynF K F c)) (SynF K F c) (rfinG c y)) := by
  rw [← placeVal_synPlace c, synPlace_plc, placeVal_inl]
  rfl

theorem isCenter_plc (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) : IsCenter (plc c ψ) ψ := by
  refine ⟨fun y => ?_, fun y => ?_⟩
  · rw [placeVal_plc]
    exact HeightOneSpectrum.valuation_le_one (K := SynF K F c) _ _
  · rw [placeVal_plc, HeightOneSpectrum.valuation_lt_one_iff_mem (K := SynF K F c), mem_ptP, ptSyn_rfinG]

/-- **Uniqueness of the center on the chart `{c}`.** -/
theorem eq_plc_of_isCenter {R : Place K F} {ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K}
    (hR : IsCenter R ψ) : R = plc c ψ := by
  apply (synPlace c).injective
  rw [synPlace_plc]
  have hbv : ∀ b : Rfin K (SynF K F c), placeVal (synPlace c R) (b : SynF K F c) =
      placeVal R (((rfinG c).symm b : chartRing (algebraMap K[X] F X) {c}) : F) := fun b => by
    have e : (b : SynF K F c) = synEquiv K F c (((rfinG c).symm b : chartRing (algebraMap K[X] F X) {c}) : F) := by
      rw [← rfinG_coe, AlgEquiv.apply_symm_apply]
    rw [e, placeVal_synPlace]
  rcases hRc : synPlace c R with P | Q
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    have h1 : ∀ b, ptSyn c ψ b = 0 → φ b = 0 := fun b hb0 => by
      have h2 : placeVal R (((rfinG c).symm b : chartRing (algebraMap K[X] F X) {c}) : F) < 1 :=
        (hR.2 _).2 hb0
      rw [← hbv b, hRc, placeVal_inl] at h2
      exact mem_ptP.1 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := SynF K F c) _ b).1 h2)
    suffices hφ : φ = ptSyn c ψ by rw [hφ]
    refine AlgHom.ext fun b => ?_
    have ht := h1 (b - algebraMap K (Rfin K (SynF K F c)) (ptSyn c ψ b))
      (by rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at ht
    exact ht
  · exfalso
    have h1 := one_lt_placeVal_inr_x (K := K) (F := SynF K F c) Q
    have h2 := hR.1 ((rfinG c).symm (algebraMap K[X] (Rfin K (SynF K F c)) X))
    rw [← hbv, hRc] at h2
    have e : ((algebraMap K[X] (Rfin K (SynF K F c)) X : Rfin K (SynF K F c)) : SynF K F c) =
        algebraMap K[X] (SynF K F c) X := rfl
    rw [e] at h2
    exact absurd h2 (not_le.2 h1)

theorem isCenter_iff_eq_plc {R : Place K F} (ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K) :
    IsCenter R ψ ↔ R = plc c ψ :=
  ⟨eq_plc_of_isCenter c, fun h => h ▸ isCenter_plc c ψ⟩

variable {c}

/-- The center of a `K`-point of `B_A` is the chart-`{c}` center for any `c ∈ A`. -/
theorem isCenter_plc_of_mem [DecidableEq K] {A : Finset K} (hc : c ∈ A)
    (ψ : chartRing (algebraMap K[X] F X) A →ₐ[K] K) :
    IsCenter (plc c (ψ.comp (Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 hc))))) ψ :=
  isCenter_extend (Finset.singleton_subset_iff.2 hc) (Finset.mem_singleton_self c) ψ (isCenter_plc c _)

theorem eq_plc_of_isCenter_of_mem [DecidableEq K] {A : Finset K} (hc : c ∈ A)
    {ψ : chartRing (algebraMap K[X] F X) A →ₐ[K] K} {R : Place K F} (hR : IsCenter R ψ) :
    R = plc c (ψ.comp (Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 hc)))) :=
  eq_plc_of_isCenter c (isCenter_restrict (Finset.singleton_subset_iff.2 hc) ψ hR)

theorem isCenter_unique [DecidableEq K] {A : Finset K} (hc : c ∈ A)
    {ψ : chartRing (algebraMap K[X] F X) A →ₐ[K] K} {R R' : Place K F} (hR : IsCenter R ψ)
    (hR' : IsCenter R' ψ) : R = R' :=
  (eq_plc_of_isCenter_of_mem hc hR).trans (eq_plc_of_isCenter_of_mem hc hR').symm

/-- **Chart independence of the center.** -/
theorem plc_eq_plc [DecidableEq K] {A : Finset K} {c' : K} (hc : c ∈ A) (hc' : c' ∈ A)
    (ψ : chartRing (algebraMap K[X] F X) A →ₐ[K] K) :
    plc c (ψ.comp (Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 hc)))) =
      plc c' (ψ.comp (Subalgebra.inclusion (chartRing_mono _ (Finset.singleton_subset_iff.2 hc')))) :=
  eq_plc_of_isCenter_of_mem hc' (isCenter_plc_of_mem hc ψ)

end Center

end RamanujanPetersson.JacComplete

end


