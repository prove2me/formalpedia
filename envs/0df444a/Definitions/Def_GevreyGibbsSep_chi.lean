-- Prove2me | Definitions.Def_GevreyGibbsSep_chi
-- name    : GevreyGibbsSep_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:47.165357+00:00
-- url     : https://prove2.me/theorems/9d53b5f6-d894-4728-81ba-b82e6c10c100
-- title:
--   Two-level profile $\chi_{\nu,\ell}$
-- statement:
--   For $0<\nu\le\ell/4$ the **mollified two-level profile** concentrated inside $[0,\ell]^d$ is
--   $$\chi_{\nu,\ell}(x)=\prod_{k=1}^{d}H_\nu(x_k)\,H_\nu(\ell-x_k):\ \mathbb R^d\to[0,1].$$
--   It equals $1$ on the plateau $[2\nu,\ell-2\nu]^d$ and vanishes outside $[0,\ell]^d$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.5, Eq. (B17), p.38

import Mathlib
import Definitions.Def_GevreyGibbsSep_Hnu

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The mollified two-level profile `χ_{ν,ℓ}(x) = ∏_k H_ν(x_k) H_ν(ℓ − x_k)` (arXiv:2608.24527
(sha256 d4fd40eb…), Definition B.5, Eq. (B17), p.38). -/
noncomputable def chi {d : ℕ} (s ν ℓ : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ k, Hnu s ν (x k) * Hnu s ν (ℓ - x k)

end GevreyGibbsSep


