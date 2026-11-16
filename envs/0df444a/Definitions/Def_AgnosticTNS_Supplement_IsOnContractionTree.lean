-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_IsOnContractionTree
-- name    : AgnosticTNS_Supplement_IsOnContractionTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:28:49.052088+00:00
-- url     : https://prove2.me/theorems/69c25161-cfbf-4637-88a1-5ba916f58ba3
-- title:
--   TTN on the binary contraction tree
-- statement:
--   A contraction sequence $\pi$ of a connected graph induces, by Lemma 5.5, a learning sequence $\mathcal L_\pi$ with one step per merge: step $i$, merging $A$ and $B$, has $S_i=A\cup B$, as children the earlier steps that created $A$ or $B$, and as fresh vertices the original singletons among $A$, $B$. The **binary contraction tree** ("the tree formed by the dependencies between reconstruction steps") is the dependency tree of $\mathcal L_\pi$. A tree tensor network is *on the binary contraction tree* if its nodes are the merges, the parent of node $j$ is the later merge that uses the set $S_j$ created at step $j$, and each qudit $v$ sits at the merge where $\{v\}$ is first merged.
--
--   **Formalization Note** Node indices are positions in the list of merges; a created set is never created again, so the parent is unique and the last merge is the root.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 1.2, p.3; Lemma 5.5, p.41; Corollary 5.10, p.44

import Mathlib
import Definitions.Def_AgnosticTNS_TTN

namespace AgnosticTNS.Supplement

/-- **A TTN on the binary contraction tree**, Theorem 1.2, p.3 ("the tree formed by the dependencies
between reconstruction steps") and Corollary 5.10, p.44, with Lemma 5.5, p.41 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
The induced learning sequence `L_π` of Lemma 5.5 has one step per merge; step `i` merging `A` and
`B` has as children the earlier steps that created `A` or `B`, and introduces the original singletons
among `A`, `B` as fresh qudits. The TTN has one node per merge, the parent of node `j` is the step
that later merges the set `S_j = A_j ∪ B_j` created at step `j`, and qudit `v` sits at the step where
`v` is first merged.

**Formalization Note** Nodes are the indices of `steps`; `S_j` is never re-created, so the parent is
unique, and the last step is the root. -/
def IsOnContractionTree {n d : ℕ} (steps : List (Finset (Fin n) × Finset (Fin n)))
    (D : TTN steps.length n d) : Prop :=
  (∀ j i : Fin steps.length, D.parent j = some i ↔
      (j < i ∧ (steps[i].1 = steps[j].1 ∪ steps[j].2 ∨ steps[i].2 = steps[j].1 ∪ steps[j].2))) ∧
    ∀ (v : Fin n) (i : Fin steps.length), D.site v = i ↔ (steps[i].1 = {v} ∨ steps[i].2 = {v})

end AgnosticTNS.Supplement


