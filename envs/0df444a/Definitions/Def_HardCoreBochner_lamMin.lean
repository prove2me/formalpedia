-- Prove2me | Definitions.Def_HardCoreBochner_lamMin
-- name    : HardCoreBochner_lamMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:27.264973+00:00
-- url     : https://prove2.me/theorems/94ecfa52-8298-4601-b04a-f819ac13fdcd
-- title:
--   Minimum eigenvalue $\lambda_{\min}(A_G)$ of the adjacency matrix of a graph
-- statement:
--   For a finite simple graph $G$ with adjacency matrix $A_G$ (entry $1$ for each edge, $0$ otherwise, zero diagonal), $\lambda_{\min}(A_G)$ is the **minimum eigenvalue** of the real symmetric matrix $A_G$:
--   $$\lambda_{\min}(A_G)=\min_i \lambda_i(A_G).$$
--   The quantity $-\lambda_{\min}(A_G)-1$ enters the activity threshold of Theorem 1.1; on a random $\Delta$-regular graph $\lambda_{\min}(A_G)=-2\sqrt{\Delta-1}+o(1)$ with high probability.
--
--   **Formalization Note** The minimum eigenvalue is the published `BlockBochner.lamMin`, the infimum of the real spectrum, applied to Mathlib's `SimpleGraph.adjMatrix ℝ`. For a symmetric matrix on a non-empty index type the spectrum is the finite set of eigenvalues, so this is their minimum. On an empty vertex type the value is $0$.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), Theorem 1.1, p.3 (PDF p.3)

import Definitions.Def_BlockBochner_lamMin

namespace HardCoreBochner

/-- `λ_min(A_G)`, the minimum eigenvalue of the adjacency matrix `A_G` of a finite simple graph `G`.
Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…),
Theorem 1.1, p.3: "λmin(AG) is the minimum eigenvalue of the adjacency matrix AG of G".

**Formalization Note** `A_G` is Mathlib's `SimpleGraph.adjMatrix ℝ` (entry `1` on edges, `0`
elsewhere, zero diagonal), a real symmetric matrix. The minimum eigenvalue is the published
`BlockBochner.lamMin`, the infimum of the real spectrum; for a symmetric matrix on a non-empty index
type the spectrum is the finite non-empty set of eigenvalues, so this is their minimum. For a graph
on an empty vertex type the value is `0`. -/
noncomputable def lamMin {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  BlockBochner.lamMin (G.adjMatrix ℝ)

end HardCoreBochner


