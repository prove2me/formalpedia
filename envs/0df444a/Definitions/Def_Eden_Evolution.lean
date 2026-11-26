-- Prove2me | Definitions.Def_Eden_Evolution
-- name    : Eden_Evolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:02:48.537741+00:00
-- url     : https://prove2.me/theorems/b352a762-31a5-4422-89c1-f0f50f3fbc17
-- title:
--   Evolution
-- statement:
--   Definitions and structural lemmas for Evolution, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Evolution.lean

import Definitions.Def_Eden_PlanarFlow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
set_option autoImplicit true
noncomputable section
namespace Eden
def evolution (c t : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[planarX 1 t (p 0) (p 1), planarY 1 t (p 0) (p 1),
     planarX (Real.sqrt 2) t (p 2) (p 3), planarY (Real.sqrt 2) t (p 2) (p 3),
     Real.exp (-c * t) * p 4]
end Eden


