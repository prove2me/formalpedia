-- Prove2me | Definitions.Def_Roberts1997_RWM_Langevin
-- name    : Roberts1997_RWM_Langevin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:45:08.065402+00:00
-- url     : https://prove2.me/theorems/c5bf64e6-4998-447b-aae1-40d066e606e1
-- title:
--   The Langevin generator GV = h(l)[V″/2 + (log f)′V′/2] and solutions of the Langevin SDE (1.2) as a martingale problem
-- statement:
--   The limiting diffusion of Theorem 1.1 is the **Langevin SDE** (1.2)
--
--   $$ dU_t = h(l)^{1/2}\,dB_t + h(l)\,\frac{f'(U_t)}{2f(U_t)}\,dt, $$
--
--   whose generator (p. 113) is
--
--   $$ GV(x) = h(l)\Big[\tfrac12 V''(x) + \tfrac12 \tfrac{d}{dx}(\log f)(x)\,V'(x)\Big]. $$
--
--   A process $(Y_t)_{t\ge0}$ on a probability space $(\Omega,Q)$ is called a **Langevin law** (for $f$ and $l$) when
--
--   1. every $Y_t$ is measurable and every path $t\mapsto Y_t(\omega)$ is continuous;
--   2. $Y_0$ has law $f(x)\,dx$;
--   3. for every $V\in C_c^\infty(\mathbb R)$, the process $V(Y_t)-V(Y_0)-\int_0^t GV(Y_u)\,du$ is a martingale for the natural filtration of $Y$: for all $0\le s\le t$, all times $r_1,\dots,r_k\le s$ and all bounded measurable $h_1,\dots,h_k$,
--   $$ \mathbb E_Q\Big[\Big(V(Y_t)-V(Y_s)-\int_s^t GV(Y_u)\,du\Big)\prod_{i=1}^k h_i(Y_{r_i})\Big]=0 . $$
--
--   This is the statement "$U_0$ is distributed according to $f$ and $U$ satisfies the Langevin SDE (1.2)" of Theorem 1.1.
--
--   **Formalization Note** Mathlib has no stochastic integral, so "satisfies the SDE" is read as "solves the martingale problem for $G$ on $C_c^\infty$ with continuous paths": weak solutions of (1.2) and solutions of this martingale problem have the same laws (Ethier–Kurtz 1986, Ch. 5, Prop. 3.1 and Thm 3.3), and the paper identifies the limit exactly by $G$ on the core $C_c^\infty$ (pp. 113–114). The shape follows the platform definition `EthierKurtz_IsContinuousDiffusionLaw`. $V''$ is `iteratedDeriv 2 V`, $(\log f)'$ is `deriv (fun y => Real.log (f y))`, and $C_c^\infty$ is `ContDiff ℝ ∞` (smooth, not analytic) with `HasCompactSupport`. Condition 2 fixes a probability law, so the zero measure is never a Langevin law.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 112, Eq. (1.2); p. 113, definition of GV; p. 114, core C_c^∞

import Definitions.Def_Roberts1997_RWM_Speed

open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff

namespace Roberts1997.RWM

/-- The generator of the Langevin diffusion (1.2), p. 113:
`GV(x) = h(l) [ (1/2) V''(x) + (1/2) (d/dx)(log f)(x) V'(x) ]`. -/
noncomputable def langevinGen (f : ℝ → ℝ) (l : ℝ) (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  speed f l * ((1 / 2) * iteratedDeriv 2 V x
    + (1 / 2) * deriv (fun y => Real.log (f y)) x * deriv V x)

/-- `Y` under `Q` is a (weak) solution of the Langevin SDE (1.2) with `Y_0 ~ f`:
measurable coordinates, continuous paths, initial law `f(x) dx`, and for every
`V ∈ C_c^∞` the process `V(Y_t) - V(Y_0) - ∫_0^t GV(Y_u) du` is a martingale for the natural
filtration of `Y`, expressed through bounded measurable history tests
`∏ h_i(Y_{r_i})`, `r_i ≤ s` (the encoding of `EthierKurtz_IsContinuousDiffusionLaw`). -/
def IsLangevinLaw {Ω : Type*} [MeasurableSpace Ω] (f : ℝ → ℝ) (l : ℝ) (Q : Measure Ω)
    (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Measurable (Y t)) ∧ (∀ w, Continuous (fun t => Y t w)) ∧
  Measure.map (Y 0) Q = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
  ∀ V : ℝ → ℝ, ContDiff ℝ ∞ V → HasCompactSupport V →
    ∀ s t : ℝ≥0, s ≤ t → ∀ (k : ℕ) (r : Fin k → ℝ≥0), (∀ i, r i ≤ s) →
    ∀ h : Fin k → ℝ → ℝ, (∀ i, Measurable (h i) ∧ ∃ C : ℝ, ∀ x, |h i x| ≤ C) →
    (∫ w, (V (Y t w) - V (Y s w) -
      ∫ u in (s : ℝ)..(t : ℝ), langevinGen f l V (Y u.toNNReal w)) *
      ∏ i, h i (Y (r i) w) ∂Q) = 0

end Roberts1997.RWM


