-- Prove2me | Definitions.Def_CentralityGame_IsCutSet
-- name    : CentralityGame_IsCutSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:40.908459+00:00
-- url     : https://prove2.me/theorems/87274ea2-04d4-4e23-8f91-c5cfd4a811ac
-- title:
--   Cut-set between two distinct nodes
-- statement:
--   For two distinct nodes $i$ and $j$, a subset $\mathcal C\subseteq\mathcal V\setminus\{i,j\}$ **cuts** (or is a **cut-set**) between $i$ and $j$ if every path from $i$ to $j$ has at least a node in $\mathcal C$.
--
--   Cut-sets appear in Proposition 3(iv), which compares a hitting time with the minimum over a cut-set.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, p.5

import Mathlib
import Definitions.Def_CentralityGame_IsPath

namespace CentralityGame

/-- **Cut-set** (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, p.5): for two distinct nodes `i` and `j`, a subset
`C ⊆ V ∖ {i, j}` cuts (is a cut-set) between `i` and `j` if every path from `i` to `j` has at
least a node in `C`.

**Formalization Note** The page defines cut-sets only between distinct nodes, so `i ≠ j` is part
of the definition. -/
def IsCutSet {V : Type*} (N : V → Finset V) (i j : V) (C : Finset V) : Prop :=
  i ≠ j ∧ i ∉ C ∧ j ∉ C ∧
    ∀ (l : ℕ) (r : Fin (l + 1) → V), IsPath N r → r 0 = i → r (Fin.last l) = j →
      ∃ h, r h ∈ C

end CentralityGame


