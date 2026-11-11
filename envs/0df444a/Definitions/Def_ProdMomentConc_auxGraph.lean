-- Prove2me | Definitions.Def_ProdMomentConc_auxGraph
-- name    : ProdMomentConc_auxGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:15.460384+00:00
-- url     : https://prove2.me/theorems/321bdb81-b1c6-4982-b19e-164a197d0e66
-- title:
--   The auxiliary graph on the underlying variables
-- statement:
--   Given the read sets $P_1,\dots,P_n \subseteq [m]$, the **auxiliary graph** is the simple graph on the underlying variables $[m]$ in which two distinct vertices $j \ne j'$ are adjacent exactly when they have a common output neighbour, that is, when $j, j' \in P_i$ for some output $i$.
--
--   A stable set of this graph is a set of underlying variables whose output neighbourhoods are pairwise disjoint. Its fractional chromatic number $\chi$ appears in condition (9) of the main theorem and in Janson's tail estimate (13).
--
--   **Formalization Note** A simple graph has no loops, so $j \ne j'$ is part of adjacency.
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Theorem 3.5, p.16 (PDF p.16), and §A.2, p.36 ("j and j′ are adjacent whenever N(j) ∩ N(j′) ≠ ∅")

import Mathlib

namespace ProdMomentConc

/-- **The auxiliary graph on the underlying variables.**
Saks, Srinivasan, Valieva, arXiv:2608.04125 (held version, sha256 5218e9d0…), Theorem 3.5, p.16:
"the graph on the underlying variables, where two vertices are adjacent if they have a common output
neighbor"; also §A.2, p.36: "j and j′ are adjacent whenever N(j) ∩ N(j′) ≠ ∅".

Vertices are `j ∈ [m]`; distinct `j, j'` are adjacent iff some output `i` reads both
(`j ∈ P i` and `j' ∈ P i`).

**Formalization Note.** A simple graph has no loops, so `j ≠ j'` is part of adjacency. -/
def auxGraph {m n : ℕ} (P : Fin n → Finset (Fin m)) : SimpleGraph (Fin m) where
  Adj j j' := j ≠ j' ∧ ∃ i, j ∈ P i ∧ j' ∈ P i
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim fun i hi => ⟨i, hi.2, hi.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end ProdMomentConc


