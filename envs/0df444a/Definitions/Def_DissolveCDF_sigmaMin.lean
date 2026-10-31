-- Prove2me | Definitions.Def_DissolveCDF_sigmaMin
-- name    : DissolveCDF_sigmaMin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:52.174528+00:00
-- url     : https://prove2.me/theorems/73431012-f73f-4da9-ad31-365c03c05a27
-- title:
--   $\sigma_{\min}(B)$ — smallest singular value
-- statement:
--   For a matrix $B\in\mathbb R^{n\times p}$, viewed as a linear map $\mathbb R^p\to\mathbb R^n$,
--
--   $$
--   \sigma_{\min}(B)=\inf\{\|B\nu\| : \nu\in\mathbb R^p,\ \|\nu\|=1\}.
--   $$
--
--   When $p\le n$ this is the smallest singular value of $B$. It is used for $B=J_c(y)$, where it measures how far the constraint gradients are from linear dependence.
--
--   **Formalization Note** The infimum is over the unit sphere of $\mathbb R^p$; for $p=0$ the sphere is empty and Lean's convention gives the value $0$ (the paper's $\sigma_{\min}$ is undefined there; the theorems that use it assume $p\ge 1$).
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.1, p.5

import Mathlib

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.1 (p.5): `σ_min(B)`, the smallest singular value of a matrix `B ∈ ℝ^{n×p}`,
here a linear map `B : ℝᵖ → ℝⁿ`.

**Formalization Note** `σ_min(B)` is encoded as `inf {‖Bν‖ : ‖ν‖ = 1}`, the infimum over the unit
sphere of `ℝᵖ`. When `p ≤ n` this is the smallest singular value; every `σ_min` used in the paper
is of some `J_c(y) ∈ ℝ^{n×p}`, and LICQ forces `p ≤ n` at feasible points. For `p = 0` the sphere
is empty and Lean's `sInf ∅ = 0` gives `0`. -/
noncomputable def sigmaMin {n p : ℕ}
    (B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  sInf ((fun ν => ‖B ν‖) '' Metric.sphere (0 : EuclideanSpace ℝ (Fin p)) 1)

end DissolveCDF


