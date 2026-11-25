-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2ExteriorSquareIso
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2ExteriorSquareIso
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T16:44:51.156389+00:00
-- url     : https://prove2.me/theorems/7b6f3232-d8aa-580f-ad77-efb50a331bce
-- title:
--   Hyper H2 Exterior Square Iso
-- statement:
--   Definitions and structural lemmas for Hyper H2 Exterior Square Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2ExteriorSquareIso.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalOneFormFrameCoordinatesConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumCupOneFormsZeroImpCoordinatesZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CupSumClosedGlobalOneFormsEqZeroIffSumWedgeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2GeneratedByCupsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumWedgeGlobalOneFormsEqZeroIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjectiveStatement
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
section Wedge
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
theorem update_pair_vector_zero (a b x : M) : Function.update ![a, b] 0 x = ![x, b] := by
  funext i; fin_cases i <;> simp
theorem update_pair_vector_one (a b x : M) : Function.update ![a, b] 1 x = ![a, x] := by
  funext i; fin_cases i <;> simp
def ιTwo : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun a a' b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 0 a a'
      simpa only [update_pair_vector_zero] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 0 r a
      simpa only [update_pair_vector_zero] using h)
    (fun a b b' ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 1 b b'
      simpa only [update_pair_vector_one] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 1 r b
      simpa only [update_pair_vector_one] using h)
end Wedge
section Forget
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
def fnZZ2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def hypercohomologyTwoToAlgebraCohomology : Hyp2 F →ₗ[R] CatCoh.H2 F :=
  Submodule.mapQ _ _ (fnZZ2 F) (by rintro _ ⟨e, rfl⟩; exact ⟨e.1, rfl⟩)
def cupProductWedge (halt : ∀ a, cupHyp F a a = 0) : Hyp1 F [⋀^Fin 2]→ₗ[R] Hyp2 F where
  toFun v := cupHyp F (v 0) (v 1)
  map_update_add' v i a b := by fin_cases i <;> simp
  map_update_smul' v i r a := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all
def cupWedge (halt : ∀ a, cupHyp F a a = 0) : ⋀[R]^2 (Hyp1 F) →ₗ[R] Hyp2 F :=
  exteriorPower.alternatingMapLinearEquiv (cupProductWedge F halt)
end Forget
end GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
end GlobalTheory.AbCoh


