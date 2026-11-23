-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:47.345533+00:00
-- url     : https://prove2.me/theorems/77f31610-4757-49bf-b2cb-eb519a97c82e
-- title:
--   Mem Period Lattice Of Exp Theta Lin Form
-- statement:
--   Definitions and structural lemmas for Mem Period Lattice Of Exp Theta Lin Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemPeriodLatticeOfExpThetaLinForm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
def thetaLinForm {g : ℕ} (n : Fin g → ℤ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun z := -(2 * Real.pi * Complex.I) * (ofIntVec n ⬝ᵥ z)
  map_add' z w := by rw [dotProduct_add, mul_add]
  map_smul' c z := by simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply]; ring
end GlobalTheory


