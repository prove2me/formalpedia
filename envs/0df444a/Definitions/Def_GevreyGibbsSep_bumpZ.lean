-- Prove2me | Definitions.Def_GevreyGibbsSep_bumpZ
-- name    : GevreyGibbsSep_bumpZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:50.040367+00:00
-- url     : https://prove2.me/theorems/23d3da0d-bf6b-49e2-bcdd-aa27b52cc0fb
-- title:
--   Normalization $Z_{\nu,\ell,\alpha}$ of the bump
-- statement:
--   The normalization of the bump density,
--   $$Z_{\nu,\ell,\alpha}=(2\pi)^d+(\alpha-1)\,\ell^d(1-2\varrho)^d,\qquad\varrho=\nu/\ell .$$
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition 4, Eq. (30), p.13

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The normalization `Z_{ν,ℓ,α} = (2π)^d + (α − 1) ℓ^d (1 − 2ϱ)^d`, `ϱ = ν/ℓ` (arXiv:2608.24527
(sha256 d4fd40eb…), Definition 4, Eq. (30), p.13). -/
noncomputable def bumpZ (d : ℕ) (ν ℓ α : ℝ) : ℝ :=
  (2 * Real.pi) ^ d + (α - 1) * ℓ ^ d * (1 - 2 * (ν / ℓ)) ^ d

end GevreyGibbsSep


