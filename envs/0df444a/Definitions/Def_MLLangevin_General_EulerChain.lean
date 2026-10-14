-- Prove2me | Definitions.Def_MLLangevin_General_EulerChain
-- name    : MLLangevin_General_EulerChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:55.796011+00:00
-- url     : https://prove2.me/theorems/480da479-840e-4f76-85da-6d2c0cfab2f4
-- title:
--   (2), §1 and §2.3, pp. 1, 6 — the constant-step Euler scheme X̄^{γ,x}_{nγ}, the Lipschitz constant [f]₁ and the steps γ_r = γ₀2^{−r}
-- statement:
--   Let $d\ge 1$ (any $d\in\mathbb N$ is allowed) and write $\mathbb R^d$ for Euclidean space with its Euclidean norm $|\cdot|$. Let $b:\mathbb R^d\to\mathbb R^d$ be a drift and $\sigma:\mathbb R^d\to\mathbb M_{d,d}$ a diffusion coefficient, where $\sigma(x)$ is a $d\times d$ matrix acting linearly on $\mathbb R^d$. Let $(W_t)_{t\ge0}$ be an $\mathbb R^d$-valued path on a probability space $(\Omega,\mathcal F,\mathbb P)$.
--
--   For a step $\gamma>0$ and a starting point $x\in\mathbb R^d$, the **Euler (Euler–Maruyama) scheme** $(\bar X^{\gamma,x}_{n\gamma})_{n\in\mathbb N}$ driven by $W$ is defined recursively by $\bar X^{\gamma,x}_0=x$ and
--   $$\bar X^{\gamma,x}_{(n+1)\gamma}=\bar X^{\gamma,x}_{n\gamma}+\gamma\, b\big(\bar X^{\gamma,x}_{n\gamma}\big)+\sigma\big(\bar X^{\gamma,x}_{n\gamma}\big)\big(W_{(n+1)\gamma}-W_{n\gamma}\big),\qquad n\ge0 .$$
--
--   For $f:\mathbb R^d\to\mathbb R$, the **Lipschitz constant** is
--   $$[f]_1=\sup_{x\neq y}\frac{|f(x)-f(y)|}{|x-y|},$$
--   that is, the least $K\ge0$ with $|f(x)-f(y)|\le K|x-y|$ for all $x,y$. Finally, the steps of the multilevel procedure are $\gamma_r=\gamma_0 2^{-r}$, $r\in\mathbb N$.
--
--   These three objects are used by every statement of the mission: the scheme is the basic simulated chain, $[f]_1$ scales every error bound, and $\gamma_r$ is the step of level $r$.
--
--   **Formalization Note.** The state space is the published `EthierKurtz.SDEState d` (Euclidean space). The diffusion coefficient takes values in continuous linear maps $\mathbb R^d\to\mathbb R^d$ (equivalently $d\times d$ matrices); Lipschitz continuity of $\sigma$ is then measured in the operator norm, which is equivalent to any matrix norm. Times of the path are nonnegative reals, so $n\gamma$ is passed as `Real.toNNReal (n * γ)`, which is exact for $\gamma>0$. `lipConst f` is the infimum of the set of admissible constants; it equals $[f]_1$ whenever $f$ is Lipschitz (the set is then nonempty and closed), and every theorem that uses it assumes $f$ Lipschitz.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, (2), p. 1; [f]₁ in §2.3, p. 6 and §2.1, p. 5; γ_r = γ₀2^{−r} in §2.2, p. 6

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian

namespace MLLangevin.General

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The state space `ℝ^d` with its Euclidean norm. -/
abbrev Rd (d : ℕ) := EthierKurtz.SDEState d

/-- The constant-step Euler(–Maruyama) scheme (2) at its grid times: `eulerChain b σ γ x W n ω`
is `X̄^{γ,x}_{nγ}(ω)` driven by the path `W`, with `X̄_0 = x` and
`X̄_{(n+1)γ} = X̄_{nγ} + γ b(X̄_{nγ}) + σ(X̄_{nγ}) (W_{(n+1)γ} − W_{nγ})`. -/
noncomputable def eulerChain {d : ℕ} {Ω : Type*} (b : Rd d → Rd d)
    (σ : Rd d → (Rd d →L[ℝ] Rd d)) (γ : ℝ) (x : Rd d) (W : ℝ≥0 → Ω → Rd d) :
    ℕ → Ω → Rd d
  | 0 => fun _ => x
  | n + 1 => fun ω =>
      eulerChain b σ γ x W n ω + γ • b (eulerChain b σ γ x W n ω)
        + σ (eulerChain b σ γ x W n ω)
            (W (Real.toNNReal (((n : ℝ) + 1) * γ)) ω - W (Real.toNNReal ((n : ℝ) * γ)) ω)

/-- `[f]₁ = sup_{x ≠ y} |f(x) − f(y)| / |x − y|`, written as the least constant `K ≥ 0` with
`|f(x) − f(y)| ≤ K |x − y|` for all `x, y` (the set is nonempty when `f` is Lipschitz). -/
noncomputable def lipConst {d : ℕ} (f : Rd d → ℝ) : ℝ :=
  sInf {K : ℝ | 0 ≤ K ∧ ∀ x y, |f x - f y| ≤ K * ‖x - y‖}

/-- The step of level `r`: `γ_r = γ₀ 2^{−r}`. -/
noncomputable def levelStep (γ₀ : ℝ) (r : ℕ) : ℝ := γ₀ / 2 ^ r

end MLLangevin.General


