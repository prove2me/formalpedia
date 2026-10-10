-- Prove2me | Definitions.Def_PowerOfDUniversality_Diffusion_Limit
-- name    : PowerOfDUniversality_Diffusion_Limit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:01.06699+00:00
-- url     : https://prove2.me/theorems/4b09a9bd-c13e-44e4-b8a1-ed5c08286284
-- title:
--   Theorem 2.4, (2.4), p. 8 — the stochastic integral equations (2.4) with regulator $U_1$ and the diffusion limit they define
-- statement:
--   This file defines the limit object of Theorem 2.4: the system of integral equations (2.4) with a one-sided regulator, and the random process that solves it when driven by a Brownian motion.
--
--   **The equations (2.4), p. 8.** Fix $\beta>0$, a level $k\ge2$, a real path $w$ and an initial value $x=(x_1,\dots,x_k)\in\mathbb R^k$. A pair $(\bar Q,U_1)$, with $\bar Q=(\bar Q_1,\bar Q_2,\dots)$, solves (2.4) if
--   1. $\bar Q_i\equiv0$ for $i\ge k+1$ and $\bar Q_i(0)=x_i$ for $i=1,\dots,k$;
--   2. $\bar Q_1,\dots,\bar Q_k$ and $U_1$ are càdlàg on $[0,\infty)$;
--   3. $U_1$ is nonnegative and nondecreasing, and $\int_0^\infty \mathbb 1_{[\bar Q_1(t)<0]}\,dU_1(t)=0$;
--   4. $\bar Q_1(t)\le 0$ for all $t\ge0$;
--   5. for all $t\ge0$,
--   $$\begin{aligned}\bar Q_1(t)&=\bar Q_1(0)+\sqrt2\,w(t)-\beta t+\int_0^t\big(-\bar Q_1(s)+\bar Q_2(s)\big)\,ds-U_1(t),\\ \bar Q_2(t)&=\bar Q_2(0)+U_1(t)-\int_0^t\big(\bar Q_2(s)-\bar Q_3(s)\big)\,ds,\\ \bar Q_i(t)&=\bar Q_i(0)-\int_0^t\big(\bar Q_i(s)-\bar Q_{i+1}(s)\big)\,ds,\qquad i=3,\dots,k.\end{aligned}$$
--
--   **The diffusion limit.** On a probability space $(\Omega',P')$, processes $(\bar Q,U_1)$ form the diffusion limit with initial law $\nu$ on $\mathbb R^k$ if there are a standard Brownian motion $W$ and an initial value $\xi$ with law $\nu$, independent of $W$, such that almost surely $(\bar Q,U_1)$ solves (2.4) driven by $w=W$ from $x=\xi$.
--
--   The equations describe the scaled number of vacant servers $-\bar Q_1$ and the scaled numbers $\bar Q_i$ of servers with at least $i$ tasks, $i\ge2$, in the Halfin–Whitt limit; $U_1$ is the cumulative push that keeps $\bar Q_1$ at or below $0$.
--
--   **Formalization Note** Coordinates use the paper's index base, so `Q t i` is $\bar Q_i(t)$ for $i\ge1$ and the unused coordinate $0$ is $0$; `x j` for `j : Fin k` is $\bar Q_{j+1}(0)$. The condition $\int_0^\infty\mathbb 1_{[\bar Q_1(t)<0]}\,dU_1(t)=0$ states that the Lebesgue–Stieltjes measure of $t\mapsto U_1(\max(t,0))$ gives zero mass to $\{t\ge0:\bar Q_1(t)<0\}$. The constraint $\bar Q_1\le0$ is implicit in the paper: the prelimit $\bar Q_1^{d(N)}$ is always $\le 0$, and without the constraint $U_1\equiv0$ satisfies the complementarity condition and uniqueness fails. Càdlàg is the published `BellWilliams2001.ThresholdPolicy.IsCadlag`. The Brownian motion is Mathlib's `IsBrownianReal`, indexed by $t\in\mathbb R_{\ge0}$, and the driving path is $t\mapsto W(\max(t,0))$.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 7–8, Theorem 2.4, equations (2.4) and the regulator U_1

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Diffusion

/-!
Mukherjee, Borst, van Leeuwaarden & Whiting, arXiv:1612.00723v2, Theorem 2.4 (pp. 7–8): the
stochastic integral equations (2.4) with the regulator `U₁`, and the diffusion limit they
characterize.

Coordinates use the paper's index base: `Q t i` is `Q̄_i(t)` for `i ≥ 1`; the unused coordinate
`0` is `0`. The initial value `x : Fin k → ℝ` lists `(Q̄_1(0), …, Q̄_k(0))`, so `x j` is
`Q̄_{j+1}(0)`.
-/

/-- **`(Q̄, U₁)` solves (2.4)** (p. 8) for the parameter `β`, the level `k`, the driving path `w`
(a Brownian path in Theorem 2.4) and the initial value `x = (Q̄_1(0), …, Q̄_k(0))`:
1. `Q̄_0 ≡ 0` (unused coordinate) and `Q̄_i ≡ 0` for `i ≥ k + 1`;
2. `Q̄_i(0) = x_i` for `i = 1, …, k`;
3. `Q̄_1, …, Q̄_k` are càdlàg (solutions in `D_{ℝ^k}[0, ∞)`), and `U₁` is càdlàg;
4. `U₁` is nonnegative and nondecreasing on `[0, ∞)`, and `∫_0^∞ 𝟙[Q̄_1(t) < 0] dU₁(t) = 0`: the
   Lebesgue–Stieltjes measure `dU₁` of the extension `t ↦ U₁(max t 0)` gives zero mass to
   `{t ≥ 0 : Q̄_1(t) < 0}`;
5. `Q̄_1(t) ≤ 0` for all `t ≥ 0` — implicit in the paper (the prelimit `Q̄_1^{d(N)} ≤ 0` always);
   without it the regulator could be `U₁ ≡ 0` and uniqueness would fail;
6. for all `t ≥ 0`,
   `Q̄_1(t) = Q̄_1(0) + √2 w(t) − βt + ∫_0^t (−Q̄_1(s) + Q̄_2(s)) ds − U₁(t)`,
   `Q̄_2(t) = Q̄_2(0) + U₁(t) − ∫_0^t (Q̄_2(s) − Q̄_3(s)) ds`,
   `Q̄_i(t) = Q̄_i(0) − ∫_0^t (Q̄_i(s) − Q̄_{i+1}(s)) ds` for `i = 3, …, k`.

The integrands are càdlàg on `[0, t]`, hence bounded and integrable there. -/
def Solves24 (β : ℝ) (k : ℕ) (w : ℝ → ℝ) (x : Fin k → ℝ) (Q : ℝ → ℕ → ℝ) (U : ℝ → ℝ) :
    Prop :=
  (∀ t : ℝ, 0 ≤ t → Q t 0 = 0 ∧ ∀ i : ℕ, k + 1 ≤ i → Q t i = 0) ∧
  (∀ j : Fin k, Q 0 ((j : ℕ) + 1) = x j) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ k → BellWilliams2001.ThresholdPolicy.IsCadlag (fun t => Q t i)) ∧
  BellWilliams2001.ThresholdPolicy.IsCadlag U ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ U t) ∧
  (∃ hU : Monotone (fun t : ℝ => U (max t 0)),
    hU.stieltjesFunction.measure {t : ℝ | 0 ≤ t ∧ Q t 1 < 0} = 0) ∧
  (∀ t : ℝ, 0 ≤ t → Q t 1 ≤ 0) ∧
  (∀ t : ℝ, 0 ≤ t → Q t 1 = Q 0 1 + Real.sqrt 2 * w t - β * t +
      (∫ s in (0 : ℝ)..t, (-Q s 1 + Q s 2)) - U t) ∧
  (∀ t : ℝ, 0 ≤ t → Q t 2 = Q 0 2 + U t - ∫ s in (0 : ℝ)..t, (Q s 2 - Q s 3)) ∧
  (∀ i : ℕ, 3 ≤ i → i ≤ k → ∀ t : ℝ, 0 ≤ t →
      Q t i = Q 0 i - ∫ s in (0 : ℝ)..t, (Q s i - Q s (i + 1)))

/-- **The diffusion limit of Theorem 2.4** on a probability space `(Ω', P')`, with parameter `β`,
level `k` and initial law `ν` on `ℝ^k`: `W` is a standard Brownian motion, the initial value `ξ`
has law `ν` and is independent of `W`, and almost surely the path `Q̄ = Qlim ω` together with the
regulator `U₁ = U ω` solves (2.4) driven by `w(t) = W(t)(ω)` from `x = ξ(ω)`. -/
def IsDiffusionLimit24 {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (β : ℝ) (k : ℕ)
    (ν : Measure (Fin k → ℝ)) (W : ℝ≥0 → Ω' → ℝ) (ξ : Ω' → Fin k → ℝ)
    (Qlim : Ω' → ℝ → ℕ → ℝ) (U : Ω' → ℝ → ℝ) : Prop :=
  IsProbabilityMeasure P' ∧
  ProbabilityTheory.IsBrownianReal W P' ∧
  Measurable ξ ∧ P'.map ξ = ν ∧
  ProbabilityTheory.IndepFun (fun ω (t : ℝ≥0) => W t ω) ξ P' ∧
  ∀ᵐ ω ∂P', Solves24 β k (fun t => W t.toNNReal ω) (ξ ω) (Qlim ω) (U ω)

end PowerOfDUniversality.Diffusion


