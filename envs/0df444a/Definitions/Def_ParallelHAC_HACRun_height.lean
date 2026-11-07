-- Prove2me | Definitions.Def_ParallelHAC_HACRun_height
-- name    : ParallelHAC_HACRun_height
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:17.60917+00:00
-- url     : https://prove2.me/theorems/945b47e6-bbed-444c-bf16-f854743443c2
-- title:
--   Height of the dendrogram of a HAC run
-- statement:
--   The merges of a HAC run on $P$ form a rooted binary tree, the **dendrogram**, with leaves $\{x\}$, $x\in P$, and an internal node $A_i\cup B_i$ with children $A_i,B_i$ for each merge $i$. The depth of the leaf $\{x\}$ is the number of merges $i\in[1,n-1]$ with $x\in A_i\cup B_i$, i.e. the number of merges in which the cluster containing $x$ participates. The **height** of the dendrogram is
--   $$\max_{x\in P}\ \bigl|\{\,i\in[1,n-1] : x\in A_i\cup B_i\,\}\bigr|.$$
--
--   It is the quantity bounded by Theorem 3; its proof bounds the depth of every leaf.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §1 p.1 (PDF p.4); §2.2 p.7 (PDF p.10); proof of Theorem 3, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_ParallelHAC_HACRun

namespace ParallelHAC

/-- The **height of the dendrogram** of a HAC run (§1, p.1; §2.2, p.7): the maximum over leaves
`{x}`, `x ∈ P`, of the depth of the leaf, i.e. of the number of merges `i ∈ [1, n − 1]` whose
merged cluster `A_i ∪ B_i` contains `x` (each such merge is one ancestor of `{x}`).
Source: arXiv:2507.20047 (sha256 a21061c8…), pp.1, 7; proof of Theorem 3, p.25.

**Formalization Note.** A natural number; the leaf `{x}` has depth equal to the number of merges in
which the cluster containing `x` participates, which is the quantity bounded in §4. -/
def HACRun.height {V : Type*} [DecidableEq V] {P : Finset V} {d : Finset V → Finset V → ℝ}
    {c : ℝ} (R : HACRun P d c) : ℕ :=
  P.sup (fun x => ((Finset.Icc 1 (P.card - 1)).filter (fun i => x ∈ R.A i ∪ R.B i)).card)

end ParallelHAC


