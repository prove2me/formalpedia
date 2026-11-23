-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:03.518963+00:00
-- url     : https://prove2.me/theorems/4c44bcc9-761a-4148-9e31-3e0916d634b1
-- title:
--   Weil Is Grp Pullback Iff
-- statement:
--   Definitions and structural lemmas for Weil Is Grp Pullback Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
namespace WeilCube
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)
def IsRatio (k : ℕ) {T : Over S} (x y : T ⟶ A) (e : Γ(T.left, ⊤)ˣ) : Prop :=
  ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good Lr.L z J →
    gm ρ.left z ⊤ e * cubN (cubV c z J) k 1 (ρ ≫ x) (ρ ≫ y) = cubN (cubV c z J) k 1 (ρ ≫ y) (ρ ≫ x)
end WeilCube
open WeilCube
end GlobalTheory


