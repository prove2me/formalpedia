-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_Region
-- name    : IntroDelayAMDP_Supplement_Region
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:46:20.76252+00:00
-- url     : https://prove2.me/theorems/94e04de5-9baa-4f37-bdf7-65e108bebcb0
-- title:
--   A region of Algorithm 2
-- statement:
--   A region returned by **Algorithm 2** is recorded by three objects: the matrix $\Lambda_j=\lambda I+\frac1{m_j}\sum_{i\in R_j}\phi_i\phi_i^\top$ that defines its ellipsoid $\{\phi:\|\phi\|^2_{\Lambda_j^{-1}}\le 2d\log(1+1/\lambda)\}$, its empirical probability $\hat p_j=|R_j|/\sqrt K$, and the truncated empirical covariance $\hat\Sigma_j$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 2, lines 3–8, p.17

import Mathlib

namespace IntroDelayAMDP.Supplement

/-- **A region returned by Algorithm 2** (Algorithm 2, lines 3–8, printed p.17, PDF p.19, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). The `j`-th region is stored by
* `lam`: the final matrix `Λ_j = λI + (1/m_j) ∑_{i∈R_j} ϕ_iϕ_iᵀ` (line 5), which defines the ellipsoid
  `{ϕ : ‖ϕ‖²_{Λ_j^{-1}} ≤ 2d log(1 + 1/λ)}` of line 6 (the region is this ellipsoid minus the earlier ones,
  see `regionOf`);
* `phat`: its empirical probability `p̂_j = |R_j|/√K` (line 7);
* `sig`: the matrix `Σ̂_j` of line 8 (empirical covariance with the eigenvalues below `λm_j/|R_j|`
  truncated to zero). -/
structure Region (d : ℕ) where
  /-- `Λ_j` -/
  lam : Matrix (Fin d) (Fin d) ℝ
  /-- `p̂_j` -/
  phat : ℝ
  /-- `Σ̂_j` -/
  sig : Matrix (Fin d) (Fin d) ℝ

end IntroDelayAMDP.Supplement


