-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:56.281655+00:00
-- url     : https://prove2.me/theorems/85377805-cc89-4f06-9c09-855f4583eabc
-- title:
--   Finite Dimensional Span Algebra Orbit Of Annihilated
-- statement:
--   Definitions and structural lemmas for Finite Dimensional Span Algebra Orbit Of Annihilated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.KilledFin
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def powSpan (t : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ i < d, ∃ n ∈ N, v = (t ^ i) n}
end GlobalTheory.KilledFin


