-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_IsUFAOfSize
-- name    : DDNNFNeg_Supplement_IsUFAOfSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:45:25.435288+00:00
-- url     : https://prove2.me/theorems/e7c25364-4ede-4911-b2ed-0661904f526f
-- title:
--   Language decided by a UFA of size $s$
-- statement:
--   A language $L \subseteq \{0,1\}^*$ is **decided by a UFA of size $s$** if there is an unambiguous nondeterministic finite automaton $(\Sigma, Q, q_0, F, \delta)$ over the alphabet $\Sigma = \{0,1\}$ with exactly $|Q| = s$ states and a single initial state $q_0$ whose accepted language is $L$. A computation with no available transition rejects.
--
--   **Formalization Note** The states are $\{0, \dots, s-1\}$, so the size is exactly $s$; the automaton is Mathlib's `NFA` with start set $\{q_0\}$, and acceptance is Mathlib's `NFA.accepts`.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 8.4, p.20

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_IsUnambiguousNFA

namespace DDNNFNeg.Supplement

/-- The language `L ⊆ {0,1}*` is decided by a UFA of size `s` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 8.4, p.20):
there is an unambiguous NFA over the alphabet `{0,1}` with exactly `s` states and a single
initial state whose accepted language is `L`.

**Formalization Note** The states are `Fin s`, so the size (number of states) is exactly `s`.
The alphabet `{0,1}` is `Bool`. The transition relation is Mathlib's `NFA.step`; a missing
transition is an empty set of successors, so that computation rejects. Mathlib's `NFA.accepts`
is acceptance by some run from the start state ending in an accept state. -/
def IsUFAOfSize (L : Language Bool) (s : ℕ) : Prop :=
  ∃ M : NFA Bool (Fin s), (∃ q₀ : Fin s, M.start = {q₀}) ∧ IsUnambiguousNFA M ∧ M.accepts = L

end DDNNFNeg.Supplement


