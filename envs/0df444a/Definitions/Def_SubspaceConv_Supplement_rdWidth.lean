-- Prove2me | Definitions.Def_SubspaceConv_Supplement_rdWidth
-- name    : SubspaceConv_Supplement_rdWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:47:28.066501+00:00
-- url     : https://prove2.me/theorems/9160676d-290b-401a-8aea-455c2eeb4b4e
-- title:
--   Width of a rank-decomposition
-- statement:
--   A **rank-decomposition** of a graph $G$ is a subcubic tree whose leaves are in bijection with $V(G)$. Deleting a tree edge splits the leaves, hence $V(G)$, into two sides $X$ and $V(G) \setminus X$; the **width** of the decomposition is the maximum binary cut-rank $\rho_G(X) = \operatorname{rank}_{\mathbb F_2} A_G[X, V(G)\setminus X]$ over these cuts.
--
--   Rank-decompositions are the supplied structure in Theorem 6 and in the second clauses of Theorems 8 and 9.
--
--   **Formalization Note** A rank-decomposition is the published `ApproxCliqueWidth.Certificate.BranchDecomp`, whose tree has at least two nodes, so graphs with at most one vertex have none. Both orientations of every tree edge are included in the maximum.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), §1.1.1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank
import Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp

set_option autoImplicit false

open Classical

namespace SubspaceConv.Supplement

/-- The **width of a rank-decomposition** (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1.1, p.4 (PDF p.5)): a rank-decomposition
of `G` is a subcubic tree whose leaves are in bijection with `V(G)` (the published
`ApproxCliqueWidth.Certificate.BranchDecomp`), and its width is the maximum binary cut-rank
`ρ_G` (published `cutrk`) over the cuts induced by deleting a tree edge.

**Formalization Note** For a tree edge `uw`, the cut is `D.side u w`, the vertices whose leaf
lies on `u`'s side; both orientations of every edge are included, and `ρ_G` is symmetric anyway.
The published `BranchDecomp` requires a tree with at least two nodes, so graphs with `N ≤ 1`
have no rank-decomposition. The width is `0` if no cut has positive rank. That
`D.WidthLE (cutrk G) r` holds exactly when `rdWidth G D ≤ r` (for `r ≥ 0`) follows from the
definitions. -/
noncomputable def rdWidth {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (D : ApproxCliqueWidth.Certificate.BranchDecomp (Fin N)) : ℕ :=
  (Finset.univ.filter (fun e : Fin D.n × Fin D.n => D.T.Adj e.1 e.2)).sup
    (fun e => (ApproxCliqueWidth.Certificate.cutrk G (D.side e.1 e.2)).toNat)

end SubspaceConv.Supplement


