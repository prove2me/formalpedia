-- Prove2me | Definitions.Def_SubspaceConv_Supplement_layoutWidth
-- name    : SubspaceConv_Supplement_layoutWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:47:08.544204+00:00
-- url     : https://prove2.me/theorems/dbc5bf61-4f5f-474c-9564-01d91d43e1fd
-- title:
--   Width of a linear layout
-- statement:
--   For a graph $G$ with adjacency matrix $A_G$ and $X \subseteq V(G)$, the **binary cut-rank** is $\rho_G(X) = \operatorname{rank}_{\mathbb F_2} A_G[X, V(G) \setminus X]$. A **linear layout** of an $N$-vertex graph is an ordering $\pi = (v_1, \dots, v_N)$ of its vertices, and its **width** is
--
--   $$r(\pi) = \max_{1 \le i < N} \rho_G(\{v_1, \dots, v_i\}),$$
--
--   with $r(\pi) = 0$ when $N \le 1$. Linear layouts are the supplied structure in Theorems 8, 9 and 10.
--
--   **Formalization Note** Vertices are `Fin N`; the ordering is a bijection $\pi$ with $\pi(i) = v_{i+1}$; the cut-rank is the published `ApproxCliqueWidth.Certificate.cutrk`.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), §1.1.1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank

set_option autoImplicit false

open Classical

namespace SubspaceConv.Supplement

/-- The **width of a linear layout** (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1.1, p.4 (PDF p.5)): a linear layout of an
`N`-vertex graph `G` is a vertex ordering `π = (v_1, …, v_N)`, and its width is
`r(π) = max_{1 ≤ i < N} ρ_G({v_1, …, v_i})`, where `ρ_G(X) = rank_{F_2} A_G[X, V(G) \ X]` is the
binary cut-rank (the published `ApproxCliqueWidth.Certificate.cutrk`).

**Formalization Note** The vertices are `Fin N`, and the ordering is a bijection
`π : Fin N ≃ Fin N` with `π i = v_{i+1}` (0-based). The prefix `{v_1, …, v_{i+1}}` is the image of
`{0, …, i}`, and `i` ranges over `i + 1 < N`. The maximum over an empty range (`N ≤ 1`) is `0`.
`cutrk` is integer valued and nonnegative; `Int.toNat` loses nothing. -/
noncomputable def layoutWidth {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (π : Fin N ≃ Fin N) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => i.val + 1 < N)).sup
    (fun i => (ApproxCliqueWidth.Certificate.cutrk G
      ((Finset.univ.filter (fun j : Fin N => j ≤ i)).image π)).toNat)

end SubspaceConv.Supplement


