-- Prove2me | Definitions.Def_HypercliqueFalse_Hypergraph
-- name    : HypercliqueFalse_Hypergraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:56.1826+00:00
-- url     : https://prove2.me/theorems/a548856b-3e8e-4213-9faa-c00a961c3871
-- title:
--   $h$-uniform hypergraph on $[n]$
-- statement:
--   An **$h$-uniform hypergraph** $G = ([n], E)$ on the vertex set $[n]$ consists of a set $E$ of $h$-element subsets of $[n]$, the **hyperedges**:
--   $$
--   E \subseteq \binom{[n]}{h}.
--   $$
--
--   Hypergraphs are the inputs of the detection problem of Theorem 1.1.
--
--   **Formalization Note** The vertex set $[n]$ is `Fin n` $=\{0,\dots,n-1\}$; $E$ is a finite set of subsets of `Fin n`, each of cardinality $h$.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, Hyperclique Polynomials, p.4

import Mathlib

set_option autoImplicit false

namespace HypercliqueFalse

/-- **An `h`-uniform hypergraph on `[n]`.** Fischer, *The Hyperclique Hypothesis is False*,
arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, "Hyperclique Polynomials", p.4:
"An h-uniform hypergraph G = ([n], E) consists of a set E ⊆ ([n] choose h) of hyperedges on the
vertex set [n]."

**Formalization Note.** The vertex set `[n]` is `Fin n` (0-based); `E` is a finite set of
`h`-element subsets of `Fin n`. -/
structure Hypergraph (n h : ℕ) where
  /-- the hyperedges -/
  E : Finset (Finset (Fin n))
  /-- every hyperedge has exactly `h` vertices -/
  card_eq : ∀ e ∈ E, e.card = h

end HypercliqueFalse


