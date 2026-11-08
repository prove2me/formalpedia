-- Prove2me | Definitions.Def_AsymSpecConn_geomAvg
-- name    : AsymSpecConn_geomAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:41.341468+00:00
-- url     : https://prove2.me/theorems/72aabcb4-ffcd-4c68-9b71-07ac8e1b89b8
-- title:
--   Weighted geometric average $w_\theta$ of spectral points
-- statement:
--   Let $g_1,\dots,g_r\in\Delta$ and let $\theta$ be a probability vector on $[r]$. The **$\theta$-weighted geometric average** of the $g_i$ is
--   $$w_\theta(s)=\prod_{i=1}^r g_i(s)^{\theta_i},\qquad s\in\mathcal S.$$
--   It is the function to which the interpolation construction is applied.
--
--   **Formalization Note** Real powers of $\mathbb R_{\ge0}$ satisfy $0^0=1$, the source's convention (p.12). The weight vector is an arbitrary real family in the definition; the theorems restrict it to the standard simplex.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §2.3, p.16

import Mathlib
import Definitions.Def_AsymSpecConn_Spectrum

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **Weighted geometric average** `w_θ(s) := ∏_{i=1}^r g_i(s)^{θ_i}` of spectral points
`g₁, …, g_r ∈ Δ` (§2.3, p.16 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)); `θ` is meant to range over
`P([r]) = {θ ∈ ℝ^r_{≥0} : Σ θ_i = 1}` (Mathlib's `stdSimplex ℝ (Fin r)`).

**Formalization Note** Real powers of `ℝ≥0` (`NNReal.rpow`) satisfy `0^0 = 1`, the paper's
convention (p.12). -/
noncomputable def geomAvg {S : Type*} [CommSemiring S] {P : Preorder S} {r : ℕ}
    (g : Fin r → ↥(Spectrum S P)) (θ : Fin r → ℝ) (s : S) : ℝ≥0 :=
  ∏ i, ((g i).1 s) ^ (θ i)

end AsymSpecConn


