-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianVarietyLineBundleSectionsFinite
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianVarietyLineBundleSectionsFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:14.151802+00:00
-- url     : https://prove2.me/theorems/05bbaf7f-03bd-4835-8c19-5509436cd421
-- title:
--   Abelian Variety Line Bundle Sections Finite
-- statement:
--   Definitions and structural lemmas for Abelian Variety Line Bundle Sections Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AbelianVarietyLineBundleSectionsFinite.lean

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
def finSecPullId {X : Scheme.{0}} {M : LB X} (s : LB.Sec M) : LB.Sec (M.pull (𝟙 X)) where
  f := fun j => rs X (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) (s.f (j PUnit.unit))
  compat := fun i j => by
    have h := congrArg (rs X (inf_le_inf (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) i PUnit.unit)
      (LB.wchart_le M (K := PUnit) (fun _ => 𝟙 X) j PUnit.unit) :
        (M.pull (𝟙 X)).U i ⊓ (M.pull (𝟙 X)).U j ≤ M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)))
      (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at h
    erw [rs_rs, rs_rs] at h
    erw [rs_rs, rs_rs, h]
    congr 1
    unfold LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    rfl
end GlobalTheory.AbLaw


