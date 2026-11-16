-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_cfgSize
-- name    : DDNNFNeg_Supplement_cfgSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:45:37.593363+00:00
-- url     : https://prove2.me/theorems/a7e04cbb-fbb1-405f-9de9-f5093f175fff
-- title:
--   Size of a context-free grammar
-- statement:
--   The **size** of a context-free grammar $G = (N, N_0, \Sigma, P)$ is
--
--   $$|G| = \sum_{(S \to T) \in P} |T|,$$
--
--   the total length of the right-hand sides of its production rules.
--
--   **Formalization Note** Mathlib's `ContextFreeGrammar` has a finite set of rules; its type of nonterminals need not be finite, but nonterminals in no rule affect neither the language nor the size.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 8.6, p.21

import Mathlib

namespace DDNNFNeg.Supplement

/-- The size of a context-free grammar `G = (N, N₀, Σ, P)` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 8.6, p.21):
`∑_{(S→T)∈P} |T|`, the total length of the right-hand sides of its production rules.

**Formalization Note** Mathlib's `ContextFreeGrammar` has a finite set of rules and a type of
nonterminals that need not be finite; nonterminals occurring in no rule do not affect the
language or the size, so this is the paper's notion. -/
def cfgSize {T : Type*} (g : ContextFreeGrammar T) : ℕ :=
  ∑ r ∈ g.rules, r.output.length

end DDNNFNeg.Supplement


