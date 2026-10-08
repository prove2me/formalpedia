-- Prove2me | Definitions.Def_RWPI_Limit_rwp
-- name    : RWPI_Limit_rwp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:50:05.242169+00:00
-- url     : https://prove2.me/theorems/bafe3dc1-540c-4bfb-9c2e-544263a3e3d6
-- title:
--   The cost $\|w-u\|_q^\rho$ (Eq. (17)) and the Robust Wasserstein Profile function $R_n(\theta)$ (Eq. (16))
-- statement:
--   This file defines two objects of §3.1.
--
--   1. **The cost (17).** For $q \in [1, \infty]$ and $\rho \ge 1$, the cost on $\mathbb R^m$ is
--   $$
--   c(u, w) = \|w - u\|_q^\rho ,
--   $$
--   where $\|\cdot\|_q$ is the $\ell_q$ norm.
--
--   2. **The Robust Wasserstein Profile (RWP) function (16).** Let $h : \mathbb R^m \times \mathbb R^l \to \mathbb R^r$ be an estimating function, $\theta \in \mathbb R^l$ a parameter, $c$ a $[0,\infty]$-valued cost on $\mathbb R^m$ and $Q$ a reference probability law on $\mathbb R^m$. The RWP function is
--   $$
--   R(\theta) = \inf\big\{ D_c(P, Q) \;:\; \mathbb E_P[h(W, \theta)] = \mathbf 0 \big\},
--   $$
--   the smallest transport cost needed to move $Q$ to a law $P$ under which the estimating equation holds. The infimum ranges over probability measures $P$ on $\mathbb R^m$ under which $u \mapsto h(u, \theta)$ is integrable. In the paper $Q$ is the empirical distribution $\mathbb P_n$ of the samples $W_1, \dots, W_n$, and the value is written $R_n(\theta)$.
--
--   The RWP function is the optimal-transport analogue of Owen's empirical-likelihood profile function: small values of $R_n(\theta)$ indicate that $\theta$ is compatible with the data, and its asymptotic law calibrates confidence regions for the root $\theta_*$ of $\mathbb E[h(W, \theta)] = \mathbf 0$.
--
--   **Formalization Note.** $R(\theta)$ takes values in $[0, \infty]$; the infimum over an empty set is $+\infty$. The requirement that $h(\cdot,\theta)$ be $P$-integrable is the paper's class $\mathcal P_\Omega$ (App. B, p. 46). The $\ell_q$ norm is Mathlib's `PiLp q` norm, so $q = \infty$ (the max norm) is allowed. The cost is finite; it is stored in $[0, \infty]$ only to fit the transport cost $D_c$.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 12, §3.1, Eqs. (16)–(17); App. B, p. 46 (class P_Ω)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost

open MeasureTheory

namespace RWPI.Limit

/-- The transport cost (17) of Blanchet, Kang & Murthy, p. 12 (and Assumption A1), p. 15):
`c(u, w) = ‖w − u‖_q^ρ` on `ℝ^m`, where `‖·‖_q` is the `ℓ_q` norm (`q = ∞` allowed), taken
through `PiLp q`. The value is finite; it is stored in `[0, ∞]` only to match `transportCost`. -/
noncomputable def costQ {m : ℕ} (q : ENNReal) (ρ : ℝ) (u w : Fin m → ℝ) : ENNReal :=
  ENNReal.ofReal (‖WithLp.toLp q (w - u)‖ ^ ρ)

/-- The (Robust) Wasserstein Profile function (16) of Blanchet, Kang & Murthy, p. 12:
`R(θ) = inf { D_c(P, Q) : E_P[h(W, θ)] = 0 }` for a reference law `Q` on `ℝ^m` (in the paper `Q`
is the empirical distribution `P_n`). The infimum ranges over probability measures `P` on `ℝ^m`
under which `u ↦ h(u, θ)` is integrable (the class `P_Ω` of App. B, p. 46) and has mean `0`.
It is `[0, ∞]`-valued; the infimum over an empty set is `⊤`. -/
noncomputable def rwp {m l r : ℕ} (c : (Fin m → ℝ) → (Fin m → ℝ) → ENNReal)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θ : Fin l → ℝ)
    (Q : Measure (Fin m → ℝ)) : ENNReal :=
  ⨅ (P : Measure (Fin m → ℝ))
    (_ : IsProbabilityMeasure P ∧ Integrable (fun u => h u θ) P ∧ ∫ u, h u θ ∂P = 0),
    RWPI.SqrtLasso.transportCost c P Q

end RWPI.Limit


