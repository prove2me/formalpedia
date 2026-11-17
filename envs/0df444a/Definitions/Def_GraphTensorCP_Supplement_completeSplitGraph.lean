-- Prove2me | Definitions.Def_GraphTensorCP_Supplement_completeSplitGraph
-- name    : GraphTensorCP_Supplement_completeSplitGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:23:03.568785+00:00
-- url     : https://prove2.me/theorems/46889dcb-4413-4f81-a90c-3012b45ccc17
-- title:
--   Complete split graph $J_{a,b}$ and split graphs with a specified partition
-- statement:
--   A **split graph** has a specified partition into a clique and an independent set. For positive integers $a,b$, the **complete split graph**
--
--   $$
--   J_{a,b}=K_a\vee\overline{K_b}
--   $$
--
--   has a clique of size $a$, an independent set of size $b$, and every edge between the two parts. A general split graph with the same specified partition may omit arbitrary cross edges.
--
--   **Formalization Note** The vertex type is `Fin (a+b)`: the first $a$ vertices form the clique and the final $b$ vertices form the independent set. The predicate for a general specified split partition leaves cross edges unrestricted.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 6.11, p.64

import Mathlib

namespace GraphTensorCP

namespace Supplement

/-- The complete split graph `J_{a,b} = K_a ∨ overline(K_b)`
(Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*,
arXiv:2610.34273 (version of 2026-11-03), Definition 6.11, p.64).

**Formalization Note.** Vertices `0,...,a-1` form the clique and vertices `a,...,a+b-1`
form the independent set. `SimpleGraph.fromRel` supplies symmetry and removes loops; two distinct
vertices are adjacent exactly when at least one belongs to the clique. -/
def completeSplitGraph (a b : ℕ) : SimpleGraph (Fin (a + b)) :=
  SimpleGraph.fromRel fun i j => i.val < a ∨ j.val < a

noncomputable instance completeSplitGraph_decidableAdj (a b : ℕ) :
    DecidableRel (completeSplitGraph a b).Adj := Classical.decRel _

/-- A graph on the specified `a+b` vertices is split with the displayed partition when the first
`a` vertices form a clique and the last `b` vertices form an independent set (Zhou,
arXiv:2610.34273 (version of 2026-11-03), Definition 6.11, p.64). Cross edges are unrestricted. -/
def IsSplitWithParts {a b : ℕ} (G : SimpleGraph (Fin (a + b))) : Prop :=
  (∀ i j, i ≠ j → i.val < a → j.val < a → G.Adj i j) ∧
    ∀ i j, a ≤ i.val → a ≤ j.val → ¬ G.Adj i j

end Supplement

end GraphTensorCP


