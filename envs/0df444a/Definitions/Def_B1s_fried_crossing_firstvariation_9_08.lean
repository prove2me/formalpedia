-- Prove2me | Definitions.Def_B1s_fried_crossing_firstvariation_9_08
-- name    : B1s_fried_crossing_firstvariation_9_08
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:38:43.471433+00:00
-- url     : https://prove2.me/theorems/8d62803f-b88c-5d17-bc96-cd1a7dfe1ed6
-- title:
--   fried crossing firstvariation 9 08
-- statement:
--   Definitions and structural lemmas for fried crossing firstvariation 9 08, from Ben Lawton (blawton/fried-conj-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Resonance-cluster conditional reduction for a proposed counterexample to Fried's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean

import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
namespace FriedCrossing
open Filter Topology Matrix
namespace FirstVariation
variable {K : Type*} [Field K]
def Nmat0 (Bcc Bcψ p : K) : Matrix (Fin 2) (Fin 2) K := !![0, -(Bcψ * p); 0, Bcc * p]
def Nmat (Bcc Bcψ Bψc Bψψ p : K) : Matrix (Fin 2) (Fin 2) K :=
  (1 / (Bcc * Bψψ - Bcψ * Bψc)) • Nmat0 Bcc Bcψ p
end FirstVariation
namespace Hadamard
end Hadamard
namespace Capstone
open TwinRate FirstVariation Hadamard OrderCount TorsionCore
end Capstone
end FriedCrossing


