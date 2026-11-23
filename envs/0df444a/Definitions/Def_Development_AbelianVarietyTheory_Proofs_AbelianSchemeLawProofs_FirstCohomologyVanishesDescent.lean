-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:41.965997+00:00
-- url     : https://prove2.me/theorems/bdb2655e-fe0f-4c3d-8036-37d8c390908a
-- title:
--   First Cohomology Vanishes Descent
-- statement:
--   Definitions and structural lemmas for First Cohomology Vanishes Descent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesDescent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw.PowVanish
section Descent
variable {X Y Z : Scheme.{0}}
def pb (h : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (e : W ≤ h ⁻¹ᵁ U) : Γ(X, U) →+* Γ(Y, W) :=
  (h.appLE U W e).hom
theorem pre_mono (h : Y ⟶ X) {U U' : X.Opens} (i : U ≤ U') : h ⁻¹ᵁ U ≤ h ⁻¹ᵁ U' := fun _ hy => i hy
theorem pre_comp (g : Z ⟶ Y) (h : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (e' : W ≤ g ⁻¹ᵁ V) : W ≤ (g ≫ h) ⁻¹ᵁ U := fun _ hy => e (e' hy)
theorem pre_pull (M : LB X) (f : Y ⟶ X) (i j : M.ι) {W : Y.Opens}
    (e : W ≤ (M.pull f).U (fun _ => i) ⊓ (M.pull f).U (fun _ => j)) : W ≤ f ⁻¹ᵁ (M.U i ⊓ M.U j) :=
  fun _ hy => ⟨mem_pull.1 (e hy).1, mem_pull.1 (e hy).2⟩
end Descent
end GlobalTheory.AbLaw.PowVanish


