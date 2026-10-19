-- Prove2me | Definitions.Def_SpeedFactory_BreakEven_Model
-- name    : SpeedFactory_BreakEven_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:26.96161+00:00
-- url     : https://prove2.me/theorems/5a7cea3b-6e0b-4729-a35a-68ea2250bdb2
-- title:
--   §2–§3, pp. 4–11, 18 — the dual-sourcing model (µ, σ, h, b, u, m, p, L), iid normal demand, φ, Φ⁻¹, z_i, z_q, σ_i, σ_q, σ_{i,s}, p⁻ (20), condition (21)
-- statement:
--   This file fixes the data of the dual-sourcing production–inventory model of Boute, Disney, Gijsbrechts and Van Mieghem and the closed-form quantities the paper prints.
--
--   A **model** consists of real numbers $\mu, \sigma, h, b, u, m, p$ and a natural number $L$:
--
--   1. $\mu$ and $\sigma$ are the mean and the standard deviation of the per-period demand $N(\mu,\sigma)$;
--   2. $h$ and $b$ are the per-period, per-unit holding and backlog costs;
--   3. $u$ is the local (SpeedFactory) unit labour cost at nominal capacity and $m$ the overtime multiplier, so overtime costs $um$ per unit;
--   4. $p$ is the landed unit purchasing price of the global supplier;
--   5. $L$ is the global lead time (the local lead time is one period).
--
--   The **standing assumptions** are $\mu>0$, $\sigma>0$, $h>0$, $b>0$, $u>0$, $m>1$, $p\ge 0$ and $L\ge 2$.
--
--   A demand process $(d_t)_{t\in\mathbb N}$ on a probability space $(\Omega,P)$ is **iid normal** if the $d_t$ are mutually independent and each $d_t$ has law $N(\mu,\sigma^2)$ (variance $\sigma^2$).
--
--   Let $\varphi$ be the standard normal density and $\Phi$ its distribution function. The standard normal quantile is $\Phi^{-1}(r)=\sup\{z:\Phi(z)\le r\}$, and the two critical fractiles are
--   $$z_i=\Phi^{-1}\Big[\frac{b}{b+h}\Big],\qquad z_q=\Phi^{-1}\Big[\frac{m-1}{m}\Big].$$
--   For a smoothing parameter $\alpha\in(-1,1)$ the paper's standard deviations (14) and the single-sourcing standard deviation are
--   $$\sigma_i=\sigma\sqrt{\frac{1}{1-\alpha^2}},\qquad \sigma_q=\sigma\sqrt{\frac{1-\alpha}{1+\alpha}},\qquad \sigma_{i,s}=\sigma\sqrt L.$$
--   For an allocation $\gamma\in(0,1]$ the **break-even price** (20) is
--   $$p^-(\gamma)=\frac{h+b}{\mu\gamma}(\sigma_i-\sigma_{i,s})\varphi[z_i]+\frac{um}{\mu\gamma}\sigma_q\varphi[z_q]+u,$$
--   and **condition (21)** is
--   $$\frac{h+b}{um}\cdot\frac{\sigma_{i,s}-\sigma_i}{\sigma_q}\cdot\frac{\varphi[z_i]}{\varphi[z_q]}>1.$$
--
--   These are the shared objects of every statement of the mission. The long-run costs themselves are not closed forms: they are defined from the dynamics in the companion definition file.
--
--   **Formalization Note** The paper allows $m\ge 1$, but at $m=1$ the fractile $z_q$ is $-\infty$, so $m>1$ is assumed. The quantile is defined by its characterizing set because Mathlib has no normal quantile; it is the unique solution of $\Phi(z)=r$ for $r\in(0,1)$. The formulas for $\sigma_i,\sigma_q$ are meaningful only for $\alpha\in(-1,1)$ and $p^-$ only for $\gamma>0$; every statement carries these restrictions. Independence of the demands is assumed throughout (the paper's "identically, normally distributed" together with §5's "iid").
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), pp. 4–6 (§2), p. 9 ((10), (11), (14)), p. 11 (σ_{i,s} after (18)), p. 18 ((20), (21))

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SpeedFactory.BreakEven

/-- The data of the dual-sourcing production–inventory model.
Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand
Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020),
pp. 4–6, §2, (1)–(5), and p. 8, §3.

* `μ`, `σ`: mean and standard deviation of the per-period demand `N(μ, σ)`;
* `h`, `b`: per-period, per-unit holding and backlog cost, (2);
* `u`: local unit labour cost at nominal capacity, `m`: overtime multiplier, (4);
* `p`: total landed unit purchasing price of the global supplier, (3);
* `L`: the global lead time (the local lead time is 1).

The policy parameters (allocation `γ`, smoothing `α`, safety stock `i⋆`, capacity `k`) are
not fields: every statement quantifies over them. -/
structure Model where
  μ : ℝ
  σ : ℝ
  h : ℝ
  b : ℝ
  u : ℝ
  m : ℝ
  p : ℝ
  L : ℕ

/-- Standing assumptions on the parameters (pp. 4–6): positive mean demand and demand standard
deviation, positive holding, backlog and labour costs, nonnegative purchasing price, global lead
time `L > 1`.

**Formalization Note.** The paper allows `m ≥ 1` (p. 6) but at `m = 1` the critical fractile
`z_q = Φ⁻¹[(m − 1)/m]` of (11) is `−∞` and the capacity problem has no minimiser, so the strict
`1 < m` is posed. `σ > 0` excludes deterministic demand. -/
def Model.Standing (M : Model) : Prop :=
  0 < M.μ ∧ 0 < M.σ ∧ 0 < M.h ∧ 0 < M.b ∧ 0 < M.u ∧ 1 < M.m ∧ 0 ≤ M.p ∧ 2 ≤ M.L

/-- The demand `d t`, `t ∈ ℕ`, is independent and identically distributed `N(μ, σ)` (with `σ`
the standard deviation, i.e. variance `σ²`) under the probability measure `P`.
Propositions 1, 3, 4 ("Let `d_t = N(µ,σ)` be identically, normally distributed for each `t`"),
p. 9, p. 11, p. 18, and §5, p. 17 ("under normal iid demand").

**Formalization Note.** Independence across periods is posed: (14), `σ_{i,s} = σ√L` and §5 all
use it. Periods are numbered from `1`; `d 0` is never used by the dynamics. -/
def IIDNormalDemand (M : Model) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (d : ℕ → Ω → ℝ) : Prop :=
  iIndepFun d P ∧ ∀ t, HasLaw (d t) (gaussianReal M.μ (M.σ ^ 2).toNNReal) P

/-- The standard normal density `φ` (p. 9). -/
noncomputable def stdNormalPDF (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The standard normal quantile `Φ⁻¹(r)` (p. 9), defined through its characterizing set as
`sup {z | Φ(z) ≤ r}`; this is the unique `z` with `Φ(z) = r` for `r ∈ (0, 1)` (Mathlib has no
normal quantile). Junk outside `(0, 1)`. -/
noncomputable def stdNormalQuantile (r : ℝ) : ℝ :=
  sSup {z : ℝ | cdf (gaussianReal 0 1) z ≤ r}

/-- The inventory critical fractile `z_i = Φ⁻¹[b/(b + h)]`, (10), p. 9. -/
noncomputable def zi (M : Model) : ℝ := stdNormalQuantile (M.b / (M.b + M.h))

/-- The capacity critical fractile `z_q = Φ⁻¹[(m − 1)/m]`, (11), p. 9. -/
noncomputable def zq (M : Model) : ℝ := stdNormalQuantile ((M.m - 1) / M.m)

/-- The long-run inventory standard deviation under TBS-POUT with iid demand,
`σ_i = σ √(1/(1 − α²))`, (14), p. 9 (meaningful for `α ∈ (−1, 1)`). -/
noncomputable def sigmaI (M : Model) (α : ℝ) : ℝ := M.σ / Real.sqrt (1 - α ^ 2)

/-- The long-run local-order standard deviation under TBS-POUT with iid demand,
`σ_q = σ √((1 − α)/(1 + α))`, (14), p. 9 (meaningful for `α ∈ (−1, 1)`). -/
noncomputable def sigmaQ (M : Model) (α : ℝ) : ℝ := M.σ * Real.sqrt ((1 - α) / (1 + α))

/-- The inventory standard deviation under single (off-shore) sourcing with iid demand,
`σ_{i,s} = σ √L`, p. 11 (after (18)). -/
noncomputable def sigmaIS (M : Model) : ℝ := M.σ * Real.sqrt M.L

/-- The break-even price, (20), p. 18:
`p⁻ = (h + b)/(µγ) (σ_i − σ_{i,s}) φ[z_i] + um/(µγ) σ_q φ[z_q] + u`.
Meaningful for `γ > 0` only; the value at `γ = 0` is a junk value never used. -/
noncomputable def pMinus (M : Model) (α γ : ℝ) : ℝ :=
  (M.h + M.b) / (M.μ * γ) * (sigmaI M α - sigmaIS M) * stdNormalPDF (zi M)
    + M.u * M.m / (M.μ * γ) * sigmaQ M α * stdNormalPDF (zq M) + M.u

/-- Condition (21), p. 18:
`(h + b)/(um) · (σ_{i,s} − σ_i)/σ_q · φ[z_i]/φ[z_q] > 1`. -/
def Cond21 (M : Model) (α : ℝ) : Prop :=
  1 < (M.h + M.b) / (M.u * M.m) * ((sigmaIS M - sigmaI M α) / sigmaQ M α)
        * (stdNormalPDF (zi M) / stdNormalPDF (zq M))

end SpeedFactory.BreakEven


