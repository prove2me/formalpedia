-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:25.05008+00:00
-- url     : https://prove2.me/theorems/9ac8fbe4-1692-4825-b899-14711c0793f5
-- title:
--   First Cohomology Vanishes Of Iso Of Is Gen
-- statement:
--   Definitions and structural lemmas for First Cohomology Vanishes Of Iso Of Is Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw
namespace H1Iso
variable {X Y Z : Scheme.{0}}
def pb (f : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) : Γ(X, U) →+* Γ(Y, W) :=
  (f.appLE U W h).hom
theorem le_pre (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (h' : U ≤ U') :
    W ≤ f ⁻¹ᵁ U' := fun _ hy => h' (h hy)
theorem le_pre_inf (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (h' : W ≤ f ⁻¹ᵁ U') :
    W ≤ f ⁻¹ᵁ (U ⊓ U') := fun _ hy => ⟨h hy, h' hy⟩
theorem le_of_comp_id {f : X ⟶ Y} {e : Y ⟶ X} (hfe : f ≫ e = 𝟙 X) {U W : X.Opens} {V : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ V) (h' : V ≤ e ⁻¹ᵁ U) : W ≤ U := by
  have : W ≤ (f ≫ e) ⁻¹ᵁ U := fun _ hy => h' (h hy)
  rw [hfe] at this
  exact this
theorem pull_U_le (M : LB X) (e : Y ⟶ X) (j : (M.pull e).ι) :
    (M.pull e).U j ≤ e ⁻¹ᵁ M.U (j PUnit.unit) := LB.wchart_le M (fun _ : PUnit => e) j PUnit.unit
def wu {N M : LB X} (w : LB.Iso M N) (i : N.ι) (k : M.ι) : Γ(X, N.U i ⊓ M.U k)ˣ := w.s (i, k)
end H1Iso
end GlobalTheory.AbLaw


