-- Prove2me | Definitions.Def_RobustMDP_EntropyInner_dualFunction
-- name    : RobustMDP_EntropyInner_dualFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:28:52.540754+00:00
-- url     : https://prove2.me/theorems/d3611aa6-6354-45c8-83dc-e28b7f26ef20
-- title:
--   The dual function $\sigma(\lambda)=\lambda\log\sum_j q(j)e^{v(j)/\lambda}+\beta\lambda$, the tilted distribution, $v_{\max}$ and $Q(v)$
-- statement:
--   Fix $q,v\in\mathbb R^n$ and $\beta\in\mathbb R$. For $\lambda>0$ and $\mu\in\mathbb R$ define
--
--   1. the **one-dimensional dual function** (47)
--   $$
--   \sigma(\lambda) = \lambda\log\Big(\sum_j q(j)\exp\frac{v(j)}{\lambda}\Big)+\beta\lambda ;
--   $$
--   2. the **two-variable dual objective**
--   $$
--   d(\lambda,\mu) = \mu+\beta\lambda+\lambda\sum_j q(j)\exp\Big(\frac{v(j)-\mu}{\lambda}-1\Big);
--   $$
--   3. the **tilted distribution**
--   $$
--   p^*(j) = \frac{q(j)\exp(v(j)/\lambda)}{\sum_i q(i)\exp(v(i)/\lambda)} ;
--   $$
--   4. the maximal value $v_{\max} := \max_j v(j)$ and the mass of the maximisers
--   $$
--   Q(v) := \sum_{j:\ v(j)=v_{\max}} q(j),
--   $$
--   which is the probability that a random variable taking value $v(j)$ with probability $q(j)$ equals $v_{\max}$.
--
--   These are the objects in which Nilim and El Ghaoui reduce the worst-case expectation over a Kullback–Leibler ball to a one-dimensional convex minimisation.
--
--   **Formalization Note** `dualFn q v β λ`, `dualObj q v β λ μ` and `tiltedDist q v λ` are total functions of $\lambda$; at $\lambda=0$ Lean's $x/0=0$ makes `dualFn` equal $0$, not the paper's $\sigma(0)=v_{\max}$, so every theorem uses them only for $\lambda>0$ and the value at $0$ appears as a one-sided limit. $v_{\max}$ is the indexed supremum `⨆ j, v j`, which over the finite nonempty index set is the attained maximum; for $n=0$ it would be $0$, a case excluded throughout since $q\in\Delta_n$ forces $n\ge 1$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 791, §6.2 (the dual, the optimal distribution p*, Eq. (47)) and §6.3 (Q(v)); p. 791, §6.1 (v_max)

import Mathlib

namespace RobustMDP.EntropyInner

/-- The one-dimensional dual function (47) of the entropy model (Nilim–El Ghaoui 2005, §6.2,
p. 791): `σ(λ) = λ log (∑ⱼ q(j) exp (v(j)/λ)) + β λ`. Only its values at `λ > 0` are meaningful
(at `λ = 0` Lean's division by zero gives `0`, not the paper's `σ(0) = v_max`); every theorem of this
mission uses it for `λ > 0` only, and the value at `0` appears as a limit. -/
noncomputable def dualFn {n : ℕ} (q v : Fin n → ℝ) (β lam : ℝ) : ℝ :=
  lam * Real.log (∑ j, q j * Real.exp (v j / lam)) + β * lam

/-- The two-variable dual objective of §6.2 (p. 791):
`d(λ, μ) = μ + β λ + λ ∑ⱼ q(j) exp ((v(j) − μ)/λ − 1)`, used for `λ > 0`, `μ ∈ ℝ`. -/
noncomputable def dualObj {n : ℕ} (q v : Fin n → ℝ) (β lam mu : ℝ) : ℝ :=
  mu + β * lam + lam * ∑ j, q j * Real.exp ((v j - mu) / lam - 1)

/-- The tilted ("optimal") distribution of §6.2 (p. 791):
`p*(j) = q(j) exp (v(j)/λ) / ∑ᵢ q(i) exp (v(i)/λ)`. -/
noncomputable def tiltedDist {n : ℕ} (q v : Fin n → ℝ) (lam : ℝ) : Fin n → ℝ :=
  fun j => q j * Real.exp (v j / lam) / ∑ i, q i * Real.exp (v i / lam)

/-- `v_max := maxⱼ v(j)` (§6.1, p. 791), written as the indexed supremum `⨆ j, v j`. Over the finite
index `Fin n` with `n ≥ 1` this is the maximum (attained); for `n = 0` it is `0`, a case that never
arises in this mission because `q ∈ Δₙ` forces `n ≥ 1`. -/
noncomputable def vmax {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ⨆ j, v j

/-- `Q(v) := ∑_{j : v(j) = v_max} q(j)` (§6.3, p. 791), the `q`-probability that the random variable
taking value `v(j)` with probability `q(j)` equals its maximum `v_max`. -/
noncomputable def maxMass {n : ℕ} (q v : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => v j = vmax v), q j

end RobustMDP.EntropyInner


