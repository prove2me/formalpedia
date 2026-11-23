-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:44.141406+00:00
-- url     : https://prove2.me/theorems/2b833305-d840-4d16-a484-90dedc0c8a94
-- title:
--   Grp Obj Of Dense Open
-- statement:
--   Definitions and structural lemmas for Grp Obj Of Dense Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GrpObjOfDenseOpen.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}
variable [GrpObj A] (w : φ ≫ G.hom = A.hom ≫ j)
end GlobalTheory.GrpDense
namespace GlobalTheory
open GrpDense
end GlobalTheory


