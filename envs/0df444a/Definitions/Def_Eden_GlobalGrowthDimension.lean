-- Prove2me | Definitions.Def_Eden_GlobalGrowthDimension
-- name    : Eden_GlobalGrowthDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:40:15.403686+00:00
-- url     : https://prove2.me/theorems/1a8b7055-f679-5d55-accd-df3d668a736a
-- title:
--   Global Growth Dimension
-- statement:
--   Definitions and structural lemmas for Global Growth Dimension, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthDimension.lean

import Definitions.Def_Eden_ExactGlobalGrowth
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def globalGrowthIncrements (c : ℝ) (i : Fin 5) : ℝ :=
  globalGrowthRate c (i.val + 1) - globalGrowthRate c i.val
def globalGrowthInterpolation (c d : ℝ) : ℝ :=
  spectrumInterpolation (globalGrowthIncrements c) d
def globalGrowthDimension (c : ℝ) : ℝ :=
  sSup {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ globalGrowthInterpolation c d}
end Eden


