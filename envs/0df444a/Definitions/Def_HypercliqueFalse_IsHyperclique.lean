-- Prove2me | Definitions.Def_HypercliqueFalse_IsHyperclique
-- name    : HypercliqueFalse_IsHyperclique
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:48.703417+00:00
-- url     : https://prove2.me/theorems/075d93b5-0656-46d3-b78a-e03d6c81f296
-- title:
--   $k$-hyperclique in a hypergraph
-- statement:
--   Let $G = ([n], E)$ be an $h$-uniform hypergraph. A set $s \subseteq [n]$ is a **$k$-hyperclique** of $G$ if it has exactly $k$ vertices and any $h$ of them form a hyperedge:
--   $$
--   |s| = k \quad\text{and}\quad t \in E \ \text{ for every } t \subseteq s \text{ with } |t| = h.
--   $$
--
--   Detecting a $k$-hyperclique is the problem of Theorem 1.1; for $h = 2$ it is $k$-clique detection in graphs.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, Hyperclique Polynomials, p.4

import Mathlib
import Definitions.Def_HypercliqueFalse_Hypergraph

set_option autoImplicit false

namespace HypercliqueFalse

/-- **A `k`-hyperclique.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held
version, sha256 6bd5cf5d…7730), Section 2, p.4: "A k-hyperclique in G is a set of k vertices any h
of which form a hyperedge." `s` has exactly `k` vertices and every `h`-element subset of `s` is a
hyperedge of `G`. -/
def IsHyperclique {n h : ℕ} (G : Hypergraph n h) (k : ℕ) (s : Finset (Fin n)) : Prop :=
  s.card = k ∧ ∀ t ⊆ s, t.card = h → t ∈ G.E

end HypercliqueFalse


