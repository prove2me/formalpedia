-- Prove2me | Definitions.Def_AlonMilman_PropertyT_Supplement_oddGraph
-- name    : AlonMilman_PropertyT_Supplement_oddGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:26:43.461517+00:00
-- url     : https://prove2.me/theorems/181c0167-e734-40c1-92eb-71b79c25de1b
-- title:
--   The odd graph $O_k$
-- statement:
--   Let $k \ge 1$ and let $S_k$ be a set of cardinality $2k - 1$. The **odd graph** $O_k$ has as vertices the subsets of $S_k$ of cardinality $k - 1$, and two distinct vertices are adjacent iff the corresponding subsets are disjoint.
--
--   For $k > 1$ this is the definition of Alon and Milman, Theorem 3.4 (i), following Biggs: the vertices are nonempty sets, so two disjoint vertices are automatically distinct. $O_2$ is the triangle and $O_3$ is the Petersen graph. For $k = 1$, where the paper's family $\{O_k\}_{k=1}^\infty$ starts but its definition does not, $O_1$ is the graph with one vertex (the empty set) and no edge.
--
--   **Formalization Note** The definition takes an arbitrary type $S$ and the parameter $k$; the cardinality condition $|S| = 2k - 1$ is a hypothesis of the theorems that use it, so every model set of the right size is covered.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 81, Theorem 3.4 (i)

import Mathlib

namespace AlonMilman.PropertyT.Supplement

/-- The odd graph `O_k` (Alon–Milman 1985, Theorem 3.4 (i), p. 81) on a ground set `S`, which in
every use has `|S| = 2k − 1`: its vertices are the subsets of `S` of cardinality `k − 1`, and two
distinct vertices are adjacent iff the corresponding subsets are disjoint. For `k > 1` the
vertices are nonempty sets, so disjoint vertices are automatically distinct; for `k = 1` there is
one vertex (`∅`) and no edge. -/
def oddGraph (S : Type) (k : ℕ) : SimpleGraph {A : Finset S // A.card = k - 1} where
  Adj A B := A ≠ B ∧ Disjoint A.1 B.1
  symm := ⟨fun _ _ ⟨h, h'⟩ => ⟨Ne.symm h, h'.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance oddGraph.decidableAdj (S : Type) [DecidableEq S] (k : ℕ) :
    DecidableRel (oddGraph S k).Adj :=
  fun A B => inferInstanceAs (Decidable (A ≠ B ∧ Disjoint A.1 B.1))

end AlonMilman.PropertyT.Supplement


