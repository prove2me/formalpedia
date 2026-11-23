-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:42.668802+00:00
-- url     : https://prove2.me/theorems/4c6ff1f1-6b4b-41f6-b902-b5527087407d
-- title:
--   Exists Mul Pull Sec
-- statement:
--   Definitions and structural lemmas for Exists Mul Pull Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulPullSec.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.MulPullSec
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
def powGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (N : ℕ) :
    LB.Gen (LB.LinComb L φ (fun k => ε k * N)) where
  s := fun j => t.s j ^ N
end GlobalTheory.MulPullSec
namespace GlobalTheory
end GlobalTheory


