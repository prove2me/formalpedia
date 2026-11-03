-- Prove2me | Definitions.Def_PLIAG_alpha0
-- name    : PLIAG_alpha0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:44.532502+00:00
-- url     : https://prove2.me/theorems/76b5b151-beb9-4d4b-89c0-a1e17b1815f7
-- title:
--   Step-size bound $\alpha_0$ of (4.5)
-- statement:
--   For $\mu>0$ (assumption B3), $L>0$ and $\ell$ (assumption B4), let
--
--   $$
--   \alpha_0:=\frac{\Big(1+\frac{\mu}{L}\cdot\frac1{\ell(\tau+1)}\Big)^{\frac1{\tau+1}}-1}{\mu}. \tag{4.5}
--   $$
--
--   Theorem 4.2 proves linear convergence for every constant step $0<\alpha\le\alpha_0$. When $\tau=0$ it equals $1/L$.
--
--   **Formalization Note** The power is the real power `Real.rpow`; in the theorems its base exceeds $1$. $L$ is passed as a real number (`Lmax Lc J` in the theorems).
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, (4.5), Theorem 4.2, p.12

import Mathlib

namespace PLIAG

/-- **The step-size bound `α_0`** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, (4.5), p.12):
`α_0 := ((1 + (μ/L) · 1/ℓ(τ+1))^{1/(τ+1)} − 1) / μ`, with `μ` the constant of B3, `L` the constant
`max_k Σ_{j ∈ J_k} L_j` and `ℓ` the function of B4.

**Formalization Note.** The power is `Real.rpow`; its base is `> 1` whenever `μ, L > 0` and
`ℓ(τ+1) ≥ 1`, which the theorems assume. `L` is passed as a real number (`Lmax Lc J` in the
theorems). -/
noncomputable def alpha0 (μ L : ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) : ℝ :=
  ((1 + μ / L * (1 / ℓ (τ + 1))) ^ ((1 : ℝ) / ((τ : ℝ) + 1)) - 1) / μ

end PLIAG


