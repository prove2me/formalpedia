-- Prove2me | Definitions.Def_FTPLLinBandit_ellipsoid
-- name    : FTPLLinBandit_ellipsoid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:14.338303+00:00
-- url     : https://prove2.me/theorems/7d12ea32-7185-4abb-ae58-e6f81da76215
-- title:
--   Ellipsoid $\mathcal E_\Sigma(L)=\{z:\|z\|_{\Sigma^{-1}}\le L\}$
-- statement:
--   For a positive definite matrix $\Sigma$ and a clipping radius $L$, the **ellipsoid** is
--   $$\mathcal E_\Sigma(L)=\big\{z\in\mathbb R^d:\ \|z\|_{\Sigma^{-1}}\le L\big\},\qquad\|z\|_{\Sigma^{-1}}=\sqrt{z^\top\Sigma^{-1}z}.$$
--   It is the integration domain of the clipped elliptical information $\mathcal J^{v,L}$ of Definition 2.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Definition 2, p.12

import Mathlib
import Definitions.Def_FTPLLinBandit_quadForm

namespace FTPLLinBandit

/-- **The ellipsoid `E_Σ(L) = {z : ‖z‖_{Σ⁻¹} ≤ L}`.** Wei, arXiv:2610.17818, Definition 2, p.12:
"For a clipping radius L > 0, define the ellipsoid E_Σ(L) := {z ∈ ℝ^d : ‖z‖_{Σ⁻¹} ≤ L}".

**Formalization Note.** `‖z‖_{Σ⁻¹} = √(zᵀΣ⁻¹z)`; used with `Σ` positive definite. -/
def ellipsoid {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (L : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {z | Real.sqrt (quadForm S⁻¹ z) ≤ L}

end FTPLLinBandit


