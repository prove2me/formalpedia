-- Prove2me | Definitions.Def_IntADSat_topSet
-- name    : IntADSat_topSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:36.463581+00:00
-- url     : https://prove2.me/theorems/958e80dc-1e59-41cc-ad7e-b578aef06f54
-- title:
--   $S_C$: the $r$ highest-degree vertices of $G[[n]\setminus C]$
-- statement:
--   For a simple graph $G$ on $[n]$, $C\subseteq[n]$ and $r\in\mathbb N$, rank the vertices $u\notin C$ by their degree $\deg_{G[[n]\setminus C]}(u)$, larger degree first, ties broken by vertex label (smaller label first). $S_C$ is the set of the first $r$ vertices in this order: $v\notin C$ belongs to $S_C$ iff fewer than $r$ vertices $u\notin C$ rank above $v$. When $n-|C|\ge r$ it has exactly $r$ elements.
--
--   **Formalization Note** The paper uses "vertex labels to break ties" without saying which label wins; the smaller label is chosen.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.8, p.18 (PDF 19)

import Mathlib
import Definitions.Def_IntADSat_degOut

set_option autoImplicit false

namespace IntADSat

/-- `S_C`, the `r` highest-degree vertices of `G[[n] ∖ C]`, ties broken by vertex labels
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.8, p.18 (PDF 19)): a vertex `v ∉ C` belongs to it iff fewer than `r` vertices
`u ∉ C` rank above it, where `u` ranks above `v` if `deg_{G[[n]∖C]}(u) > deg_{G[[n]∖C]}(v)`, or the
two degrees are equal and `u` has the smaller label.

**Formalization Note** The paper does not say which label wins a tie; the smaller label is chosen.
When `n − |C| ≥ r` the set has exactly `r` elements. -/
noncomputable def topSet {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (r : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun v => v ∉ C ∧
    (Finset.univ.filter fun u => u ∉ C ∧
      (degOut G C v < degOut G C u ∨ (degOut G C u = degOut G C v ∧ u < v))).card < r

end IntADSat


