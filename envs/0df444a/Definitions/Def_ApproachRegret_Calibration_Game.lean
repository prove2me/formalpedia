-- Prove2me | Definitions.Def_ApproachRegret_Calibration_Game
-- name    : ApproachRegret_Calibration_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:11:16.655986+00:00
-- url     : https://prove2.me/theorems/9cb65b34-f66d-44b0-aaab-5adc9dd6dda6
-- title:
--   The calibration game (11), the ℓ₁ ball, the cube $B_\infty(1)$, the $(\ell_1,\varepsilon)$-calibration rate and linear regret
-- statement:
--   This file fixes the objects of Section 5 of Abernethy, Bartlett and Hazan (COLT 2011). Throughout, $\mathbb R^n$ carries the Euclidean norm $\|\cdot\|_2$; the other norms are written out explicitly.
--
--   1. **ℓ₁ norm and ℓ₁ ball.** For $x\in\mathbb R^n$, $\|x\|_1=\sum_i |x_i|$, and $B_1(r)=\{y\in\mathbb R^n:\|y\|_1\le r\}$.
--   2. **The unit cube.** $B_\infty(1)=\{\theta\in\mathbb R^n:|\theta_i|\le 1\text{ for every }i\}$, the unit ball of the sup norm.
--   3. **The grid.** For a positive integer $m$ the grid width is $\varepsilon=1/m$, and the forecaster's possible predictions are $0,1/m,\dots,1$, indexed by $i=0,\dots,m$.
--   4. **The vector-valued game (11).** For weights $w=(w(0),\dots,w(m))$ and an outcome $y$,
--   $$u(w,y)=\Bigl(w(0)\bigl(y-\tfrac0m\bigr),\,w(1)\bigl(y-\tfrac1m\bigr),\,\dots,\,w(m)(y-1)\Bigr)\in\mathbb R^{m+1}.$$
--   5. **Average payoff.** For weights $w_1,\dots,w_T$ and outcomes $y_1,\dots,y_T$, $\bar u_T=\frac1T\sum_{t=1}^T u(w_t,y_t)$.
--   6. **The calibration rate of the forecast distributions.** Definition 19 sets
--   $C^\varepsilon_T=\max\bigl\{0,\sum_{i}\frac{n_T(i\varepsilon,\varepsilon)}{T}|i\varepsilon-\rho_T(i\varepsilon,\varepsilon)|-\frac\varepsilon2\bigr\}$, and the $i$-th summand equals $\bigl|\frac1T\sum_{t=1}^T\mathbb I[p_t=i/m](i/m-y_t)\bigr|$. Replacing the indicator by its expectation $w_t(i)$ under the forecaster's randomization gives
--   $$\bar C^\varepsilon_T=\max\Bigl\{0,\ \sum_{i=0}^m\Bigl|\frac1T\sum_{t=1}^T w_t(i)\Bigl(\frac im-y_t\Bigr)\Bigr|-\frac\varepsilon2\Bigr\}.$$
--   7. **Linear regret.** For a set $\mathcal K\subseteq\mathbb R^n$, loss vectors $g_1,\dots,g_T$ and points $\theta_1,\dots,\theta_T$,
--   $$\mathrm{Regret}_T=\sum_{t=1}^T\langle g_t,\theta_t\rangle-\min_{\theta\in\mathcal K}\sum_{t=1}^T\langle g_t,\theta\rangle .$$
--   8. **Euclidean projection.** $z$ is a projection of $y$ onto $\mathcal K$ when $z\in\mathcal K$ and $\|z-y\|_2\le\|x-y\|_2$ for every $x\in\mathcal K$.
--
--   These are the objects in which the paper's efficient calibration algorithm and its rate (Theorem 22) are stated.
--
--   **Formalization Note** Vectors are `EuclideanSpace ℝ (Fin n)`; coordinate $i\in\{0,\dots,m\}$ is `i : Fin (m+1)` and $i/m$ is `(i : ℝ) / m`. The paper writes the calibration vector in $\mathbb R^{\lfloor\varepsilon^{-1}\rfloor}$; it has $m+1$ coordinates. Rounds are $t=1,\dots,T$ (`Finset.Icc 1 T`). The rate $\bar C$ is defined from Definition 19's formula, not as a distance, so Claim 1 and (13) keep their content. The minimum in the regret is `sInf` of the image of $\mathcal K$; every theorem that uses it has $\mathcal K$ nonempty and bounded, where this is the true (attained, for closed $\mathcal K$) minimum. `eps m = 1/m` is a junk $0$ at $m=0$; every theorem assumes $m\ge1$. The projection predicate is the same notion as `LogRegretOCO.OGD.IsProj`, whose module is not available here.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Definition 19 and the calibration vector, p. 40; game (11), p. 41; B∞(1), p. 42; regret, condition 2, p. 42

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones

namespace ApproachRegret.Calibration

/-- The ℓ₁ norm `‖x‖₁ = ∑ᵢ |xᵢ|`, written out explicitly (the norm of `E n` is ℓ₂). -/
noncomputable def l1norm {n : ℕ} (x : ApproachRegret.ToOLO.E n) : ℝ :=
  ∑ i, |x i|

/-- The closed ℓ₁ ball `B₁(r) = {y : ‖y‖₁ ≤ r}`. -/
def l1Ball (n : ℕ) (r : ℝ) : Set (ApproachRegret.ToOLO.E n) :=
  {y | l1norm y ≤ r}

/-- The unit cube `B∞(1) = {θ : ‖θ‖∞ ≤ 1} = {θ : |θᵢ| ≤ 1 for every i}` (p. 42). -/
def cube (n : ℕ) : Set (ApproachRegret.ToOLO.E n) :=
  {θ | ∀ i, |θ i| ≤ 1}

/-- The grid width `ε = 1/m` (p. 41). -/
noncomputable def eps (m : ℕ) : ℝ :=
  1 / (m : ℝ)

/-- The vector-valued calibration game (11), p. 41: for a distribution `w` on the grid
`{0, 1/m, …, 1}` (indexed by `i = 0, …, m`) and an outcome `y`,
`u(w, y) = (w(0)(y − 0/m), w(1)(y − 1/m), …, w(m)(y − m/m)) ∈ ℝ^{m+1}`. -/
noncomputable def payoff (m : ℕ) (w : Fin (m + 1) → ℝ) (y : ℝ) : ApproachRegret.ToOLO.E (m + 1) :=
  WithLp.toLp 2 (fun i => w i * (y - ((i : ℕ) : ℝ) / (m : ℝ)))

/-- The average payoff `(1/T) ∑_{t=1}^T u(w_t, y_t)` over rounds `t = 1, …, T`. -/
noncomputable def avgPayoff (m T : ℕ) (w : ℕ → Fin (m + 1) → ℝ) (y : ℕ → ℝ) : ApproachRegret.ToOLO.E (m + 1) :=
  (1 / (T : ℝ)) • ∑ t ∈ Finset.Icc 1 T, payoff m (w t) (y t)

/-- The `(ℓ₁, ε)`-calibration rate of Definition 19 (p. 40), with `ε = 1/m`, evaluated for the
forecast distributions `w_t`: the indicator `𝕀[p_t = i/m]` is replaced by its expectation
`w_t(i)`, so that
`C̄ = max {0, ∑_{i=0}^m |(1/T) ∑_{t=1}^T w_t(i)(i/m − y_t)| − ε/2}`. -/
noncomputable def calibRate (m T : ℕ) (w : ℕ → Fin (m + 1) → ℝ) (y : ℕ → ℝ) : ℝ :=
  max 0 ((∑ i : Fin (m + 1),
      |(1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, w t i * (((i : ℕ) : ℝ) / (m : ℝ) - y t)|)
    - eps m / 2)

/-- The regret of the points `θ₁, …, θ_T` against the linear losses `θ ↦ ⟨g_t, θ⟩`,
`t = 1, …, T`, relative to the best fixed point of `K`:
`∑_{t=1}^T ⟨g_t, θ_t⟩ − min_{θ ∈ K} ∑_{t=1}^T ⟨g_t, θ⟩`. The minimum is the infimum of the
image of `K`; it is attained whenever `K` is nonempty and compact. -/
noncomputable def linRegret {n : ℕ} (K : Set (ApproachRegret.ToOLO.E n)) (T : ℕ) (g θ : ℕ → ApproachRegret.ToOLO.E n) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, inner ℝ (g t) (θ t)
    - sInf ((fun x => ∑ t ∈ Finset.Icc 1 T, inner ℝ (g t) x) '' K)

/-- `IsProj K y z`: `z` is a Euclidean (ℓ₂) projection of `y` onto `K`, i.e.
`z ∈ K` and `‖z − y‖₂ ≤ ‖x − y‖₂` for every `x ∈ K`. -/
def IsProj {n : ℕ} (K : Set (ApproachRegret.ToOLO.E n)) (y z : ApproachRegret.ToOLO.E n) : Prop :=
  z ∈ K ∧ ∀ x ∈ K, ‖z - y‖ ≤ ‖x - y‖

end ApproachRegret.Calibration


