-- Prove2me | Definitions.Def_Eden_PeriodicGlobalDimension
-- name    : Eden_PeriodicGlobalDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:37:09.144478+00:00
-- url     : https://prove2.me/theorems/fc7bb3d9-2e67-566a-8459-cc8a17f7132b
-- title:
--   Periodic Global Dimension
-- statement:
--   Definitions and structural lemmas for Periodic Global Dimension, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean

import Definitions.Def_Eden_PeriodicGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def periodicGlobalGrowthIncrements (c : ℝ) (i : Fin 5) : ℝ :=
  periodicGlobalGrowthRate c (i.val + 1) - periodicGlobalGrowthRate c i.val
def periodicGlobalGrowthInterpolation (c d : ℝ) : ℝ :=
  spectrumInterpolation (periodicGlobalGrowthIncrements c) d
def periodicGlobalGrowthDimension (c : ℝ) : ℝ :=
  sSup {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ periodicGlobalGrowthInterpolation c d}
end Eden


