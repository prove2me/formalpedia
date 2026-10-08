-- Prove2me | Definitions.Def_RWPI_Limit_dualRep
-- name    : RWPI_Limit_dualRep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:50:23.491054+00:00
-- url     : https://prove2.me/theorems/c4d4c35b-523c-47a2-b51d-f00ca85ae0d9
-- title:
--   The quantities $H_n$ and $M_n(\zeta)$ of the rescaled dual representation (31)–(32)
-- statement:
--   Fix an estimating function $h : \mathbb R^m \times \mathbb R^l \to \mathbb R^r$, a parameter $\theta \in \mathbb R^l$ such that $w \mapsto h(w, \theta)$ is differentiable, with derivative $Dh(w) = D_w h(w, \theta)$ (an $r \times m$ matrix), and sample points $W_1, \dots, W_n \in \mathbb R^m$. Fix $q \in [1, \infty]$ and $\rho \ge 1$. Define
--
--   $$
--   H_n = n^{-1/2} \sum_{i=1}^n h(W_i, \theta) \in \mathbb R^r
--   $$
--
--   and, for $\zeta \in \mathbb R^r$,
--
--   $$
--   M_n(\zeta) = \frac1n \sum_{i=1}^n \sup_{\Delta \in \mathbb R^m} \Big\{ \zeta^T \int_0^1 Dh\big(W_i + n^{-1/2} \Delta u\big)\, \Delta \, du - \|\Delta\|_q^\rho \Big\} .
--   $$
--
--   These are the ingredients of the representation $n^{\rho/2} R_n(\theta_*) = \sup_\zeta \{ -\zeta^T H_n - M_n(\zeta) \}$ (Eq. (31)), the starting point of the asymptotic analysis of the RWP function: $H_n$ is the normalized sum that obeys the central limit theorem, and $M_n$ is a random convex penalty that converges to a deterministic one.
--
--   **Formalization Note.** $Dh(w)$ is the Fréchet derivative of $w \mapsto h(w, \theta)$, and the integral is the interval integral over $[0,1]$ of an $\mathbb R^r$-valued function, as printed. Each inner supremum is at least $0$ (take $\Delta = 0$) and may be $+\infty$, so $M_n(\zeta)$ is computed in the extended reals.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 32, App. A.3, Eq. (32) and the definition of H_n

import Mathlib

open MeasureTheory

namespace RWPI.Limit

/-- `H_n = n^{-1/2} Σ_{i=1}^n h(W_i, θ)` (App. A.3, p. 32), for sample points `w : Fin n → ℝ^m`. -/
noncomputable def Hn {m l r n : ℕ} (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ))
    (θ : Fin l → ℝ) (w : Fin n → (Fin m → ℝ)) : Fin r → ℝ :=
  (Real.sqrt n)⁻¹ • ∑ i, h (w i) θ

/-- `M_n(ζ)` of (32) (App. A.3, p. 32):
`M_n(ζ) = (1/n) Σ_{i=1}^n sup_Δ { ζ^T ∫_0^1 Dh(W_i + n^{-1/2} Δ u) Δ du − ‖Δ‖_q^ρ }`,
where `Dh(w) = D_w h(w, θ)` is the Fréchet derivative of `w ↦ h(w, θ)` and `Δ` ranges over `ℝ^m`.
Each inner supremum is `≥ 0` (take `Δ = 0`) and may be `+∞`, so it is taken in `EReal`. -/
noncomputable def Mn {m l r n : ℕ} (q : ENNReal) (ρ : ℝ)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θ : Fin l → ℝ)
    (w : Fin n → (Fin m → ℝ)) (ζ : Fin r → ℝ) : EReal :=
  ((1 / (n : ℝ) : ℝ) : EReal) * ∑ i, ⨆ Δ : Fin m → ℝ,
    (((ζ ⬝ᵥ ∫ u in (0 : ℝ)..1,
        fderiv ℝ (fun x => h x θ) (w i + (Real.sqrt n)⁻¹ • (u • Δ)) Δ)
      - ‖WithLp.toLp q Δ‖ ^ ρ : ℝ) : EReal)

end RWPI.Limit


