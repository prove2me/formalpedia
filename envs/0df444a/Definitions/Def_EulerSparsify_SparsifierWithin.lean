-- Prove2me | Definitions.Def_EulerSparsify_SparsifierWithin
-- name    : EulerSparsify_SparsifierWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:56.328006+00:00
-- url     : https://prove2.me/theorems/5beb4bc9-b7ef-4416-a85b-de02687b32f0
-- title:
--   An $\varepsilon$-approximate Eulerian sparsifier with at most $C\varepsilon^{-2}n$ edges
-- statement:
--   Given an Eulerian graph $\vec G=(V,E,w)$, $\varepsilon>0$, a constant $C$ and new weights $w'$, the predicate says:
--
--   1. $w'$ describes a reweighted subgraph $\vec H=(V,\mathrm{supp}(w'),w')$ of $\vec G$;
--   2. $\vec H$ is an $\varepsilon$-Eulerian spectral approximation of $\vec G$ (Definition 1.1);
--   3. $\vec H$ has few edges:
--   $$\mathrm{nnz}(w')\le C\,\varepsilon^{-2}\,n,\qquad n=|V|.$$
--
--   Both clauses of Theorem 1.2 (existence and the polynomial-time algorithm) use this predicate with the same constant $C$.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Theorem 1.2, p.2 (PDF p.4); Definition 1.1, p.1

import Mathlib
import Definitions.Def_EulerSparsify_IsEulerianApprox
import Definitions.Def_EulerSparsify_DiGraph_IsReweightedSubgraph
import Definitions.Def_EulerSparsify_nnz

namespace EulerSparsify

/-- **An ε-approximate Eulerian sparsifier with at most `C ε⁻² n` edges** (Theorem 1.2, p.2,
PDF p.4; Definition 1.1, p.1, PDF p.3).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Theorem 1.2: "an ε-approximate Eulerian sparsifier ⃗H with |E(⃗H)| = O(ε⁻²n)".

`SparsifierWithin G ε C w'` says that the reweighted subgraph `⃗H = G.withWeights w'` is an
ε-Eulerian spectral approximation of `⃗G` (Definition 1.1) and has at most `C · ε⁻² · n` edges,
`n = |V|`, where the edges of `⃗H` are those of nonzero new weight.

**Formalization Note.** Used with the same constant `C` by both clauses of Theorem 1.2 (existence
and the polynomial-time algorithm). -/
def SparsifierWithin {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (ε C : ℝ) (w' : E → ℝ) : Prop :=
  G.IsReweightedSubgraph w' ∧ IsEulerianApprox G (G.withWeights w') ε ∧
    (nnz w' : ℝ) ≤ C * ε⁻¹ ^ 2 * Fintype.card V

end EulerSparsify


