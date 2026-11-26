-- Prove2me | Definitions.Def_Eden_LogarithmicInterpolation
-- name    : Eden_LogarithmicInterpolation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:48:22.530633+00:00
-- url     : https://prove2.me/theorems/225d6074-1d54-58cc-bd4c-837a0be062c6
-- title:
--   Logarithmic Interpolation
-- statement:
--   Definitions and structural lemmas for Logarithmic Interpolation, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
namespace Eden
def spectrumInterpolation (a : Fin 5 → ℝ) (d : ℝ) : ℝ :=
  ∑ i : Fin 5, singularWeight i d * a i
end Eden


