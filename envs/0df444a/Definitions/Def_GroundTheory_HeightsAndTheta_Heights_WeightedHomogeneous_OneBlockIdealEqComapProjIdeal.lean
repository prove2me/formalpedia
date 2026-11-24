-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:47:15.512477+00:00
-- url     : https://prove2.me/theorems/64332fff-e745-4ca1-b552-6ef2f5e07aeb
-- title:
--   One Block Ideal Eq Comap Proj Ideal
-- statement:
--   Definitions and structural lemmas for One Block Ideal Eq Comap Proj Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
def blockCoordEquiv (k₀ : ι) : Fin (n k₀ + 1) ≃ Coord (fun _ : Unit ↦ n k₀) where
  toFun i := ⟨(), i⟩
  invFun v := v.2
  left_inv _ := rfl
  right_inv := fun ⟨(), _⟩ ↦ rfl
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close


