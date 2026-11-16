-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_IsUnambiguousNFA
-- name    : DDNNFNeg_Supplement_IsUnambiguousNFA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:44:39.498582+00:00
-- url     : https://prove2.me/theorems/e7748bfe-144d-487f-9a60-16392a549cd9
-- title:
--   Unambiguous NFA
-- statement:
--   A nondeterministic finite automaton is **unambiguous** if on every input there is at most one accepting run, i.e. any two accepting runs on the same input coincide.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 8.4, p.20

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_IsAcceptingRun

namespace DDNNFNeg.Supplement

/-- The NFA `M` is unambiguous (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 8.4, p.20): "on any input, there is at most one
sequence of moves leading to an accept state", i.e. any two accepting runs on the same input are
equal. -/
def IsUnambiguousNFA {α σ : Type*} (M : NFA α σ) : Prop :=
  ∀ (x : List α) (p p' : Fin (x.length + 1) → σ),
    IsAcceptingRun M x p → IsAcceptingRun M x p' → p = p'

end DDNNFNeg.Supplement


