-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_qmcHam
-- name    : HeilmanMax3Cut_Supplement_qmcHam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:02:33.900616+00:00
-- url     : https://prove2.me/theorems/a4d09dbb-f1d9-4997-b344-a91bfdca2d7b
-- title:
--   The Quantum MAX-CUT operator $\sum_{i,j}w_{ij}(I-X_iX_j-Y_iY_j-Z_iZ_j)$
-- statement:
--   For weights $w:\{1,\dots,n\}^2\to[0,\infty)$ with $w_{ij}=w_{ji}$ and $w_{ii}=0$, the operator
--
--   $$H_w=\sum_{i,j=1}^n w_{ij}\big(I_2^{\otimes n}-X_iX_j-Y_iY_j-Z_iZ_j\big)$$
--
--   on $(\mathbb C^2)^{\otimes n}$. Its largest value $u^*H_wu$ over unit vectors is the Quantum MAX-CUT value of $w$.
--
--   **Formalization Note** The weights come from a graph with natural-number edge multiplicities: $w_{ij}$ is the number of listed edges joining $i$ and $j$ (symmetric, zero on the diagonal). The double sum runs over ordered pairs, as printed.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 2.1, p.10

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_HeilmanMax3Cut_Supplement_qubitOp
open OptInapprox.MaxCut

namespace HeilmanMax3Cut.Supplement

/-- **The Quantum MAX-CUT operator of a weighted graph.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 2.1, p.10:
`∑_{i,j=1}^n w_{ij} (I₂^{⊗n} − X_iX_j − Y_iY_j − Z_iZ_j)`, for weights `w : {1, …, n}² → [0, ∞)` with
`w_{ij} = w_{ji}` and `w_{ii} = 0`, where `X = [[0, 1], [1, 0]]`, `Y = [[0, −√−1], [√−1, 0]]`,
`Z = [[1, 0], [0, −1]]` act on the indicated qubit (`qubitOp`).

**Formalization Note.** The instance is the published `OptInapprox.MaxCut.WMaxCut` (vertices
`Fin G.n`, a loopless edge list in which an edge listed `m` times has weight `m`). The weight
`w_{ij}` is the number of list entries equal to `(i, j)` or `(j, i)`; it is symmetric, and
`w_{ii} = 0` by looplessness. The double sum runs over ordered pairs `(i, j)`, as printed. -/
noncomputable def qmcHam (G : WMaxCut) : Matrix (Fin G.n → Fin 2) (Fin G.n → Fin 2) ℂ :=
  ∑ i : Fin G.n, ∑ j : Fin G.n,
    (((G.edges.count (i, j) + G.edges.count (j, i) : ℕ) : ℂ)) •
      (1 - qubitOp !![0, 1; 1, 0] i * qubitOp !![0, 1; 1, 0] j
        - qubitOp !![0, -Complex.I; Complex.I, 0] i * qubitOp !![0, -Complex.I; Complex.I, 0] j
        - qubitOp !![1, 0; 0, -1] i * qubitOp !![1, 0; 0, -1] j)

end HeilmanMax3Cut.Supplement


