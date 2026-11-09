-- Prove2me | Definitions.Def_DirTeleMC_ScheduleRun
-- name    : DirTeleMC_ScheduleRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:32:31.637368+00:00
-- url     : https://prove2.me/theorems/3a3bc769-9cec-407c-8cf0-976e2ec7ff97
-- title:
--   The procedure SCHEDULE as a run relation
-- statement:
--   For a jump tree $J$ and a set $Y$ of kept terminals, SCHEDULE$(J)$ lets $F$ be the set of arcs used by the jumps of $J$, takes a breadth-first out-arborescence of $(V, F)$ from $s$, deletes its branches that contain no vertex of $Y$, and lets every vertex call its children in non-increasing order of the numbers of leaves in their subtrees, starting in the round after it is informed. For DTM $Y = K$; for $k$-multicast $Y$ consists of $k$ of the terminals that $J$ covers.
--
--   The relation contains every run: any breadth-first tree and any order among children with equal leaf counts.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §B.2, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_DirTeleMC_IsPrunedSPT
import Definitions.Def_DirTeleMC_arbSchedule
import Definitions.Def_DirTeleMC_JTree

namespace DirTeleMC

variable {n : ℕ}

/-- The digraph `(V, F)` of the arcs `F` used by the jumps of `J` (§B.2, p.20). -/
def JTree.arcAdj (J : JTree n) : Fin n → Fin n → Bool := fun a b => decide ((a, b) ∈ J.arcs)

/-- **A run of SCHEDULE(J)** that keeps the terminal set `Y`.
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §B.2, p.20: "the procedure SCHEDULE(J) lets F be the set of arcs used by the
jumps of J, takes a breadth-first out-arborescence of (V, F) from s, deletes its branches that contain no
terminal, and lets every vertex call its children in non-increasing order of the number of leaves in their
subtrees, starting in the round after it is informed. For k-multicast it keeps k of the terminals that J covers
and deletes the branches that contain none of them."

`ScheduleRun s J Y S`: `S` is the schedule along some breadth-first out-arborescence of `(V, F)` from `s`
pruned to `Y`, with some child order that is non-increasing in leaf counts.

**Formalization Note.** `Y` is the set of kept terminals (all of `K` for DTM, `k` covered terminals for
k-multicast); the caller chooses it. The breadth-first tree and the order among children with equal leaf counts
are left open: the relation contains every run. -/
def ScheduleRun (s : Fin n) (J : JTree n) (Y : Finset (Fin n)) (S : Schedule n) : Prop :=
  ∃ (A : Arb n) (ord : Fin n → List (Fin n)), IsPrunedSPT J.arcAdj s Y A ∧ A.IsChildOrder ord ∧
    (∀ u ∈ A.verts, (ord u).Pairwise fun a b => A.leafCount b ≤ A.leafCount a) ∧
    S = A.arbSchedule ord

end DirTeleMC


