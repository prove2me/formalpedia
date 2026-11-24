-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:54.182136+00:00
-- url     : https://prove2.me/theorems/01e76a48-2b9b-4543-a09b-ed698c369b5b
-- title:
--   Herm Value Is Least
-- statement:
--   Definitions and structural lemmas for Herm Value Is Least, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/HermValueIsLeast.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.MCSchur
open Matrix
noncomputable section
def qf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ := u ⬝ᵥ (A *ᵥ u)
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
end
end GroundTheory.Heights₂.Heights.MCSchur


