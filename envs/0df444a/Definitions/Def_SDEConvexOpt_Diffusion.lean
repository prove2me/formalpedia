-- Prove2me | Definitions.Def_SDEConvexOpt_Diffusion
-- name    : SDEConvexOpt_Diffusion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:24:54.637022+00:00
-- url     : https://prove2.me/theorems/b8ec4c7d-1a4f-40ca-98cb-0397e2cfe1e2
-- title:
--   The space $\mathbb R^{d\times m}$ of diffusion matrices, with the Frobenius norm
-- statement:
--   The diffusion term of (SDE) takes values in the space $\mathbb R^{d\times m}$ of real $d\times m$ matrices, normed by the Frobenius norm
--   $$
--   \|M\|_F=\Big(\sum_{i=1}^d\sum_{k=1}^m M_{ik}^2\Big)^{1/2}.
--   $$
--   This is the matrix space of every statement of the mission.
--
--   **Formalization Note** A matrix is a vector indexed by `Fin d × Fin m` in `EuclideanSpace`, so the Lean norm is exactly the Frobenius norm; the entry $M_{ik}$ is `M (i, k)`. The published `EthierKurtz.SDEDiffusion d` is the square case $m=d$.
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, (SDE), p.2; §2 notation (Frobenius norm), p.6

import Mathlib

open scoped NNReal

namespace SDEConvexOpt

/-- The space `ℝ^{d×m}` of real `d × m` matrices, the values of the diffusion term
`σ : ℝ₊ × ℝ^d → ℝ^{d×m}` of (SDE) (Maulen S., Fadili, Attouch, An SDE perspective on stochastic
convex optimization, arXiv:2207.02750v1, (SDE), p.2; Frobenius norm, §2, p.6).

**Formalization Note** A matrix is flattened to `EuclideanSpace ℝ (Fin d × Fin m)`, so its norm is
the Frobenius norm `‖M‖_F = (∑ᵢₖ Mᵢₖ²)^{1/2}` used by the paper. The entry `σᵢₖ` of a matrix `M` is
`M (i, k)`. This mirrors the published `EthierKurtz.SDEDiffusion d` (the case `m = d`). -/
abbrev Diffusion (d m : ℕ) := EuclideanSpace ℝ (Fin d × Fin m)

end SDEConvexOpt


