-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:16.814849+00:00
-- url     : https://prove2.me/theorems/263cd390-9dc6-4223-b0cc-14098783807d
-- title:
--   Exists Finite Cube Induction
-- statement:
--   Definitions and structural lemmas for Exists Finite Cube Induction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFiniteCubeInduction.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
namespace PsiSpread
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
def Extends {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (χ : D.X) : Prop :=
  ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (cP D T χ).left) (fun _ => -1)), t.IsGen ∧
    ∀ z J, Good D.P.L z J → val t κ.left z J = val (D.psi χ) (𝟙 _) z J
end PsiSpread
end GlobalTheory


