-- Prove2me | Definitions.Def_Eden_LyapunovExponents
-- name    : Eden_LyapunovExponents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:43:40.204882+00:00
-- url     : https://prove2.me/theorems/7529cc6f-2489-5f1f-9139-4b8ec8e96f84
-- title:
--   Lyapunov Exponents
-- statement:
--   Definitions and structural lemmas for Lyapunov Exponents, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
namespace Eden
def normalizedLogSingularValues (c t : ℝ) (p : PhaseSpace) : Fin 5 → ℝ :=
  fun i => Real.log ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t
def lyapunovExponent (c : ℝ) (p : PhaseSpace) (i : Fin 5) : ℝ :=
  limUnder atTop (fun t => normalizedLogSingularValues c t p i)
end Eden


