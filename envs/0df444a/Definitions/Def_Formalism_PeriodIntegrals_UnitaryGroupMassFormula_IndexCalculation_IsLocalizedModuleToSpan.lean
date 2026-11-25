-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:20:30.308266+00:00
-- url     : https://prove2.me/theorems/f16a6c96-c968-50a4-b6a2-94ee536e535e
-- title:
--   Is Localized Module To Span
-- statement:
--   Definitions and structural lemmas for Is Localized Module To Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/IsLocalizedModuleToSpan.lean

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_ElementDenominator_eltDen__8ca64acdbeb6
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.Dv.IdxW
open Module
section Gen
variable {R : Type*} [CommRing R] (S : Submonoid R)
variable {V : Type*} [AddCommGroup V] [Module R V]
def lenS (M N : Submodule R V) : ℕ∞ :=
  Module.length (Localization S) (LocalizedModule S (↥M ⧸ N.comap M.subtype))
end Gen
section Frac
variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable (K) in
include K in
theorem smul_eq_zero_iff' {c : R} (hc : c ≠ 0) {x : V} : c • x = 0 ↔ x = 0 := by
  rw [← algebraMap_smul K c x, smul_eq_zero]
  have : algebraMap R K c ≠ 0 := by
    intro h
    exact hc ((IsFractionRing.injective R K) (by rw [h, map_zero]))
  simp [this]
theorem eltDen (Y : Submodule R V) {y : V} (hy : y ∈ Submodule.span K (Y : Set V)) :
    ∃ s : R, s ≠ 0 ∧ s • y ∈ Y :=
  _root_.P2M_UpperTheory_Reformulated_B_ElementDenominator_eltDen__8ca64acdbeb6 Y hy
def toSpan (M : Submodule R V) : ↥M →ₗ[R] ↥(Submodule.span K (M : Set V)) where
  toFun x := ⟨x, Submodule.subset_span x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
instance isLocalizedModule_toSpan (M : Submodule R V) :
    IsLocalizedModule (nonZeroDivisors R) (toSpan (K := K) M) where
  map_units x := by
    rw [Module.End.isUnit_iff]
    have hx0 : (x : R) ≠ 0 := nonZeroDivisors.ne_zero x.2
    have hx' : algebraMap R K x ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      apply Subtype.ext
      have : (x : R) • ((y : V) - z) = 0 := by
        rw [smul_sub, sub_eq_zero]
        exact congrArg Subtype.val hyz
      exact sub_eq_zero.mp ((smul_eq_zero_iff' K hx0).mp this)
    · intro y
      refine ⟨(algebraMap R K x)⁻¹ • y, ?_⟩
      apply Subtype.ext
      show (x : R) • ((algebraMap R K x)⁻¹ • (y : V)) = y
      rw [← algebraMap_smul K (x : R), smul_smul, mul_inv_cancel₀ hx', one_smul]
  surj y := by
    obtain ⟨s, hs, hsy⟩ := eltDen (K := K) M y.2
    refine ⟨(⟨s • (y : V), hsy⟩, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), ?_⟩
    apply Subtype.ext
    rfl
  exists_of_eq {x₁ x₂} h := by
    refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val h
    have : x₁ = x₂ := Subtype.ext h'
    rw [this]
end Frac
end PI.Dv.IdxW


