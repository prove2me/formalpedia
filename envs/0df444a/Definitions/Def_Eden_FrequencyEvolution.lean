-- Prove2me | Definitions.Def_Eden_FrequencyEvolution
-- name    : Eden_FrequencyEvolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:23:01.361347+00:00
-- url     : https://prove2.me/theorems/ffcf7a9a-5624-528e-aa53-e53c45ff88cb
-- title:
--   Frequency Evolution
-- statement:
--   Definitions and structural lemmas for Frequency Evolution, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyEvolution.lean

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
namespace Eden
def frequencyVectorField (c ν : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[q (radiusSq₁ p) * p 0 - p 1, q (radiusSq₁ p) * p 1 + p 0,
     q (radiusSq₂ p) * p 2 - ν * p 3, q (radiusSq₂ p) * p 3 + ν * p 2, -c * p 4]
def frequencyEvolution (c ν t : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[planarX 1 t (p 0) (p 1), planarY 1 t (p 0) (p 1),
     planarX ν t (p 2) (p 3), planarY ν t (p 2) (p 3), Real.exp (-c * t) * p 4]
end Eden


