-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:02.82844+00:00
-- url     : https://prove2.me/theorems/9cca80af-1ed6-442f-8bcd-97406fef5e4d
-- title:
--   Log Weyl Dimension Estimate
-- statement:
--   Definitions and structural lemmas for Log Weyl Dimension Estimate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogWeylDimensionEstimate.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
namespace TDim
def hh (z : ℝ) (d : ℕ) : ℝ := Real.log ((z + d) / d)
def G (la : ℕ → ℤ) (i j : ℕ) : ℝ :=
  Real.log ((((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)))
def pa (la : ℕ → ℤ) (i j : ℕ) : ℝ := if la i ≠ 0 ∧ la j ≠ 0 then G la i j else 0
def pb (la : ℕ → ℤ) (i j : ℕ) : ℝ := if la j = 0 then hh ((max (la i) 0 : ℤ) : ℝ) (j - i) else 0
def pc (la : ℕ → ℤ) (i j : ℕ) : ℝ := if la i = 0 then hh ((max (-(la j)) 0 : ℤ) : ℝ) (j - i) else 0
end TDim
end Formalism.InvariantFactorPaths.BranchingDimensions


