-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:56.659821+00:00
-- url     : https://prove2.me/theorems/5803602a-3f08-47f1-a593-a44b529ec0f1
-- title:
--   Exists Gen Of Rigid
-- statement:
--   Definitions and structural lemmas for Exists Gen Of Rigid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfRigid.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
namespace GlobalTheory.RigidTriv
variable {X Y Z : Scheme.{0}}
def LocGen (N : LB Y) (W : Y.Opens) (s : ∀ i, Γ(Y, W ⊓ N.U i)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : N.ι), f z ∈ W → f z ∈ N.U i → f z ∈ N.U j →
    gm f z (W ⊓ N.U i) (s i) = gm f z (N.U i ⊓ N.U j) (N.g i j) * gm f z (W ⊓ N.U j) (s j)
end GlobalTheory.RigidTriv


