-- Prove2me | Definitions.Def_DirTeleMC_IsPrunedSPT
-- name    : DirTeleMC_IsPrunedSPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:30:48.440877+00:00
-- url     : https://prove2.me/theorems/f80f4184-911e-430a-bd88-efa85700ee5b
-- title:
--   Shortest-path out-arborescences pruned to a terminal set
-- statement:
--   A **breadth-first (shortest-path) out-arborescence** of a digraph from $s$, **pruned** to a vertex set $Y$, is an out-arborescence rooted at $s$ that contains $Y$, all of whose leaves lie in $Y$, and in which every vertex lies at depth equal to its distance from $s$.
--
--   Pruning a breadth-first out-arborescence (deleting its branches that contain no vertex of $Y$) gives such a tree, and every such tree arises this way, so this describes every possible result of that step, with ties left open.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §3, p.9 (PDF p.10); §B.2, p.20 (PDF p.21); Algorithm 2, line 2, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_DirTeleMC_Arb

namespace DirTeleMC

/-- **A shortest-path (breadth-first) out-arborescence from `s`, pruned to the vertex set `Y`.**
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §3, p.9 ("Construct a shortest-path out-arborescence rooted at s and prune all
branches containing no terminal"); §B.2, p.20 ("takes a breadth-first out-arborescence of (V, F) from s,
deletes its branches that contain no terminal"); Algorithm 2, line 2.

`IsPrunedSPT adj s Y A`: `A` is an out-arborescence of `adj` rooted at `s` that contains `Y`, all of whose
leaves are in `Y`, and in which every vertex lies at depth equal to its distance from `s` in `adj`.

**Formalization Note.** Pruning a breadth-first (shortest-path) out-arborescence to `Y` gives exactly such a
tree, and every such tree is the pruning of a breadth-first out-arborescence (extend it by shortest-path
parents of the remaining reachable vertices); so this predicate describes every possible output of the step,
with all ties left open. -/
def IsPrunedSPT {n : ℕ} (adj : Fin n → Fin n → Bool) (s : Fin n) (Y : Finset (Fin n)) (A : Arb n) :
    Prop :=
  A.IsIn adj ∧ A.root = s ∧ Y ⊆ A.verts ∧ A.leaves ⊆ Y ∧ ∀ v ∈ A.verts, A.depth v = dist adj s v

end DirTeleMC


