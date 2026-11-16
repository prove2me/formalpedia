-- Prove2me | Definitions.Def_ParallelHAC_Supplement_CCHard
-- name    : ParallelHAC_Supplement_CCHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:32:12.630304+00:00
-- url     : https://prove2.me/theorems/f3739946-6b22-4ac9-a95f-4455eb4829c7
-- title:
--   The class CC and CC-hardness (Definition 7)
-- statement:
--   A language $L\subseteq\{0,1\}^*$ is **in CC** if it is many-one reducible to Comparator Circuit Value by a deterministic logspace transducer. A promise problem $Q$ is **CC-hard** (Definition 7) if every language in CC is logspace-reducible to $Q$: for each $L\in$ CC there is a logspace-computable map $f$ such that, for every string $x$, $f(x)$ lies in the promise (domain) of $Q$, and $Q$ answers YES on $f(x)$ exactly when $x\in L$.
--
--   CC-hardness is widely believed to rule out NC algorithms; the paper uses it in Theorem 8.
--
--   **Formalization Note** Logspace transducers and reductions are the published `ArrighiStarFree.HalfLevel.LogspaceComputable` and `Reduces`: deterministic multitape machines whose work tapes visit $O(\log|x|)$ cells, with a write-only output stream. Cook–Filmus–Lê define CC as the closure of CCV under AC⁰ reductions; closing under logspace reductions gives a class at least as large, and CC-hardness is the same notion for both, because the composition of a logspace reduction and an AC⁰ reduction is a logspace reduction.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §2.5, Definition 7, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_ArrighiStarFree_HalfLevel_SpaceMachine
import Definitions.Def_ArrighiStarFree_HalfLevel_Reductions
import Definitions.Def_ParallelHAC_Supplement_CCV

namespace ParallelHAC.Supplement

open ArrighiStarFree.HalfLevel

/-- A language `L ⊆ {0,1}*` is **in CC** if it is deterministic-logspace many-one reducible to
Comparator Circuit Value (`CCV`).
Source: arXiv:2507.20047 (sha256 a21061c8…), §2.5, p.12 (PDF p.15); the class is [CFL14]'s.

**Formalization Note.** [CFL14] closes CCV under AC⁰ many-one reductions. Using logspace
reductions gives a class at least as large. Hardness for it is the same notion, because a
logspace reduction composed with an AC⁰ one is a logspace reduction. Reductions are the published
`ArrighiStarFree.HalfLevel.Reduces LogspaceComputable`: deterministic logspace transducers with a
write-only output. -/
def InCC (L : Set (List Bool)) : Prop :=
  Reduces LogspaceComputable L (totalProblem CCV)

/-- **CC-hardness** (Definition 7, p.12): a promise problem `Q` is CC-hard if every language of
CC is logspace-reducible to it. A reduction must send every string, YES or NO, into the domain of
`Q` (the promise), with the right answer.
Source: arXiv:2507.20047 (sha256 a21061c8…), §2.5, Definition 7, printed p.12 (PDF p.15). -/
def CCHard (Q : PromiseProblem) : Prop :=
  ∀ L : Set (List Bool), InCC L → Reduces LogspaceComputable L Q

end ParallelHAC.Supplement


