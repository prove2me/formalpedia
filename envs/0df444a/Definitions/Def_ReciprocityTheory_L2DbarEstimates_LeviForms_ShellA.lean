-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:38.862535+00:00
-- url     : https://prove2.me/theorems/ab37a648-1cc2-4d05-a020-8251c398da3e
-- title:
--   Shell A
-- statement:
--   Definitions and structural lemmas for Shell A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
def shG {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) : V n :=
  WithLp.toLp 2 (fun i => g i (s y))
end
end ReciprocityTheory.L2DbarEstimates.I


