-- Prove2me | Definitions.Def_CutSetEnum_IsSourceMinMinTerminalCut
-- name    : CutSetEnum_IsSourceMinMinTerminalCut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:22.806419+00:00
-- url     : https://prove2.me/theorems/153d900b-53e9-4d13-95c6-30c235920ef9
-- title:
--   Source minimal minimum $(S,T)$-terminal cut
-- statement:
--   Let $S,T\subseteq V$ be disjoint non-empty vertex sets. A 2-partition $(A,\bar A)$ is an **$(S,T)$-terminal cut** if $S\subseteq A\subseteq V\setminus T$; it is a **minimum** $(S,T)$-terminal cut if $d(A)$ is least among all $(S,T)$-terminal cuts. The **source minimal** minimum $(S,T)$-terminal cut is the minimum $(S,T)$-terminal cut $(A,\bar A)$ whose source set $A$ is contained in the source set of every minimum $(S,T)$-terminal cut. It exists and is unique for every pair of disjoint non-empty $S,T$.
--
--   These cuts are the computational primitive of the paper: they are computable by max-flow, and the paper's enumeration algorithms run over them.
--
--   **Formalization Note** Terminal cuts are the published `IsTerminalCut S T A := S ⊆ A ∧ Disjoint A T` and `IsMinTerminalCut`; for non-empty $S,T$ they are the paper's 2-partitions. The paper's "source minimal" (inclusion-minimal among minimum cuts) is stated as "contained in every minimum cut"; the two agree because the minimum cuts have a least source set (published `HyperKCut.Structure.source_max_cut`).
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, §1.2, pp.4–5 (PDF 5–6)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Source minimal minimum `(S, T)`-terminal cut.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, §1.2, pp.4–5 (PDF 5–6): "A minimum-valued
(S, T)-terminal cut is known as a minimum (S, T)-terminal cut. Since there could be multiple
minimum (S, T)-terminal cuts, we will be interested in source minimal minimum (S, T)-terminal
cuts. For every pair of disjoint non-empty subsets S and T of vertices, there exists a unique
source minimal minimum (S, T)-terminal cut".

`IsSourceMinMinTerminalCut H S T A` says that `(A, Aᶜ)` is a minimum `(S, T)`-terminal cut and
that its source set `A` is contained in the source set of every minimum `(S, T)`-terminal cut.

**Formalization Note.** Terminal cuts are the published `IsTerminalCut S T A := S ⊆ A ∧
Disjoint A T` and `IsMinTerminalCut`; for non-empty `S` and `T` these are exactly the paper's
2-partitions with `S ⊆ A ⊆ V \ T`. The paper's "source minimal" means inclusion-minimal among the
minimum cuts. By the published `HyperKCut.Structure.source_max_cut` (second conjunct) the minimum
cuts have a least source set, so inclusion-minimal and "contained in every minimum cut" define the
same cut; the latter form is used here. -/
def IsSourceMinMinTerminalCut (H : HyperKCut.Structure.Hypergraph V) (S T A : Finset V) : Prop :=
  IsMinTerminalCut H S T A ∧ ∀ A' : Finset V, IsMinTerminalCut H S T A' → A ⊆ A'

end CutSetEnum


