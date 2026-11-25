-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyStructureSheafCohomologyModelOfQuasiIso
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyStructureSheafCohomologyModelOfQuasiIso
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:40:11.268642+00:00
-- url     : https://prove2.me/theorems/3da0209d-8a2e-4128-a35e-aa8251bd1d6d
-- title:
--   Nonempty Structure Sheaf Cohomology Model Of Quasi Iso
-- statement:
--   Definitions and structural lemmas for Nonempty Structure Sheaf Cohomology Model Of Quasi Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyStructureSheafCohomologyModelOfQuasiIso.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AbCoh
section Transfer
variable {R : Type} [CommRing R] {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
  (R' : Type) [CommRing R'] [Algebra R R']
theorem dB_comm (i j : ℕ) (x : R' ⊗[R] K.X i) :
    dB C R' i j ((φ.f i).hom.baseChange R' x) = (φ.f j).hom.baseChange R' (dB K R' i j x) := by
  simp only [dB, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, φ.comm]
def cycMap (i j : ℕ) : LinearMap.ker (dB K R' i j) →ₗ[R'] LinearMap.ker (dB C R' i j) :=
  ((φ.f i).hom.baseChange R').restrict (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [dB_comm, hx, map_zero])
end Transfer
end GlobalTheory.AbCoh


