-- Prove2me | Definitions.Def_DataDrivenRO_FwdBwd_Setting
-- name    : DataDrivenRO_FwdBwd_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:43:27.823132+00:00
-- url     : https://prove2.me/theorems/ae6f2663-46dc-4c49-aa1d-dda727c7665a
-- title:
--   §5.2, (20)–(24), pp. 18–19 — forward/backward deviations, the region 𝒫^{FB}, the set 𝒰^{FB}_ε and the closed form (24)
-- statement:
--   This file fixes the objects of §5.2 of Bertsimas, Gupta and Kallus.
--
--   The uncertain parameter is $\tilde u \in \mathbb R^d$ and $\mathbb P$ is a probability measure on $\mathbb R^d$. For $\varepsilon\in(0,1)$ and $v\in\mathbb R^d$ the **Value at Risk** (6) is
--   $$\mathrm{VaR}^{\mathbb P}_\varepsilon(v) = \inf\{t : \mathbb P(\tilde u^\top v \le t) \ge 1-\varepsilon\},$$
--   taken from the published `MultistageStochastic.valueAtRisk` at level $1-\varepsilon$.
--
--   For a probability measure $\mathbb P_i$ on $\mathbb R$ with mean $\mu_i$, the **forward and backward deviations** (20) are
--   $$\sigma_{f}(\mathbb P_i) = \sup_{x>0}\sqrt{-\frac{2\mu_i}{x} + \frac{2}{x^2}\log \mathbb E^{\mathbb P_i}[e^{x\tilde u_i}]},\qquad \sigma_{b}(\mathbb P_i) = \sup_{x>0}\sqrt{\frac{2\mu_i}{x} + \frac{2}{x^2}\log \mathbb E^{\mathbb P_i}[e^{-x\tilde u_i}]}.$$
--   The file records the statements $\sigma_f(\mathbb P_i)\le\sigma$ and $\sigma_b(\mathbb P_i)\le\sigma$ as predicates: the expression under the root is at most $\sigma^2$ for every $x>0$.
--
--   Given data $m_{b}, m_{f}, \bar\sigma_{f}, \bar\sigma_{b}\in\mathbb R^d$ (from the bootstrap of Algorithm 1), a family of marginals $(\mathbb P_1,\dots,\mathbb P_d)$ is **admissible** for the confidence region $\mathcal P^{FB}$ (p. 18) when each $\mathbb P_i$ has bounded support, $m_{bi}\le \mathbb E^{\mathbb P_i}[\tilde u_i]\le m_{fi}$, $\sigma_f(\mathbb P_i)\le\bar\sigma_{fi}$ and $\sigma_b(\mathbb P_i)\le\bar\sigma_{bi}$. The joint law is the product $\mathbb P_1\otimes\cdots\otimes\mathbb P_d$.
--
--   The uncertainty set (23) is
--   $$\mathcal U^{FB}_\varepsilon = \Big\{y_1+y_2-y_3 : y_2,y_3\in\mathbb R^d_+,\ \sum_{i=1}^d\Big(\frac{y_{2i}^2}{2\bar\sigma_{fi}^2}+\frac{y_{3i}^2}{2\bar\sigma_{bi}^2}\Big)\le\log(1/\varepsilon),\ m_{bi}\le y_{1i}\le m_{fi}\Big\}.$$
--
--   Two closed-form expressions are named: the right-hand side of the Chen–Sim–Sun bound (22) for means $\mu$ and deviations $\sigma_f,\sigma_b$,
--   $$\sum_i \mu_i v_i + \sqrt{2\log(1/\varepsilon)\Big(\sum_{i:v_i<0}\sigma_{bi}^2v_i^2+\sum_{i:v_i\ge0}\sigma_{fi}^2v_i^2\Big)},$$
--   and the right-hand side of (24),
--   $$\sum_{i:v_i\ge0}m_{fi}v_i+\sum_{i:v_i<0}m_{bi}v_i+\sqrt{2\log(1/\varepsilon)\Big(\sum_{i:v_i\ge0}\bar\sigma_{fi}^2v_i^2+\sum_{i:v_i<0}\bar\sigma_{bi}^2v_i^2\Big)}.$$
--   Finally, the set of values of the inner Lagrangian objective of the proof of Theorem 6 at a multiplier $\lambda$, $\sum_i v_i(y_{1i}+y_{2i}-y_{3i}) - \lambda\sum_i\big(y_{2i}^2/(2\bar\sigma_{fi}^2)+y_{3i}^2/(2\bar\sigma_{bi}^2)\big)$ over $m_b\le y_1\le m_f$, $y_2,y_3\ge0$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Coordinates are indexed by `Fin d` (0-based; the paper's $i=1,\dots,d$). $\tilde u^\top v$ is `u ⬝ᵥ v`. For $\sigma\ge0$, "$\sigma_f(\mathbb P_i)\le\sigma$" is equivalent to the predicate `FwdDevLe`, because $\sqrt{a}\le\sigma \iff a\le\sigma^2$ for $\sigma\ge0$; the predicate form avoids a real supremum that could be unbounded. Bounded support (the section's standing assumption, p. 18) makes every exponential moment finite, so the Bochner integrals in the predicates are the true expectations. The product measure (`Measure.pi`) builds in the independence of components that Theorem 6 and the bound (22) assume; the page's set-builder for $\mathcal P^{FB}$ omits it. The probability-measure condition on each marginal is carried as an instance hypothesis in the theorems rather than in `Admissible`, because `Measure.pi` needs it as an instance.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §5.2, (20), 𝒫^{FB}, (22), p. 18; (23), (24), p. 19; proof of Theorem 6 (EC.1.4), p. ec5; (6), p. 10

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RobustMDP_Shared_supportFunction

namespace DataDrivenRO.FwdBwd

open MeasureTheory

/-- Value at Risk (6), p. 10: `VaR^ℙ_ε(v) = inf {t : ℙ(ũᵀv ≤ t) ≥ 1 − ε}`, the published
`MultistageStochastic.valueAtRisk` of the loss `u ↦ uᵀv` at level `1 − ε`. -/
noncomputable def VaR {d : ℕ} (P : Measure (Fin d → ℝ)) (ε : ℝ) (v : Fin d → ℝ) : ℝ :=
  MultistageStochastic.valueAtRisk P (fun u => u ⬝ᵥ v) (1 - ε)

/-- A measure on `ℝ` has bounded support: it puts no mass outside some interval `[-R, R]`
(the standing assumption of §5.2, p. 18). -/
def HasBoundedSupport (Q : Measure ℝ) : Prop :=
  ∃ R : ℝ, Q (Set.Icc (-R) R)ᶜ = 0

/-- The forward deviation (20) of `Q` is at most `σ`:
`−2μ/x + (2/x²) log E[e^{xũ}] ≤ σ²` for every `x > 0`, where `μ = E[ũ]`. -/
def FwdDevLe (Q : Measure ℝ) (σ : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x →
    -2 * (∫ t, t ∂Q) / x + 2 / x ^ 2 * Real.log (∫ t, Real.exp (x * t) ∂Q) ≤ σ ^ 2

/-- The backward deviation (20) of `Q` is at most `σ`:
`2μ/x + (2/x²) log E[e^{−xũ}] ≤ σ²` for every `x > 0`, where `μ = E[ũ]`. -/
def BwdDevLe (Q : Measure ℝ) (σ : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x →
    2 * (∫ t, t ∂Q) / x + 2 / x ^ 2 * Real.log (∫ t, Real.exp (-x * t) ∂Q) ≤ σ ^ 2

/-- The marginal conditions of the confidence region `𝒫^{FB}` (p. 18) on a family of marginals
`Q i`, i = 1..d: bounded support, mean in `[m_{bi}, m_{fi}]`, forward deviation at most
`σ̄_{fi}`, backward deviation at most `σ̄_{bi}`. The joint law is `Measure.pi Q` (independent
components). -/
structure Admissible {d : ℕ} (mb mf sf sb : Fin d → ℝ) (Q : Fin d → Measure ℝ) : Prop where
  bdd : ∀ i, HasBoundedSupport (Q i)
  mean_ge : ∀ i, mb i ≤ ∫ t, t ∂(Q i)
  mean_le : ∀ i, ∫ t, t ∂(Q i) ≤ mf i
  fwd : ∀ i, FwdDevLe (Q i) (sf i)
  bwd : ∀ i, BwdDevLe (Q i) (sb i)

/-- The uncertainty set `𝒰^{FB}_ε` of (23), p. 19. -/
def UFB {d : ℕ} (mb mf sf sb : Fin d → ℝ) (ε : ℝ) : Set (Fin d → ℝ) :=
  {u | ∃ y₁ y₂ y₃ : Fin d → ℝ, 0 ≤ y₂ ∧ 0 ≤ y₃ ∧ (∀ i, mb i ≤ y₁ i ∧ y₁ i ≤ mf i) ∧
    ∑ i, (y₂ i ^ 2 / (2 * sf i ^ 2) + y₃ i ^ 2 / (2 * sb i ^ 2)) ≤ Real.log (1 / ε) ∧
    u = y₁ + y₂ - y₃}

/-- The right-hand side of the Chen–Sim–Sun bound (22), p. 18, for means `μ` and deviations
`σf`, `σb`: `Σ μᵢvᵢ + √(2 log(1/ε) (Σ_{vᵢ<0} σ²_{bi}vᵢ² + Σ_{vᵢ≥0} σ²_{fi}vᵢ²))`. -/
noncomputable def cssBound {d : ℕ} (μ σf σb : Fin d → ℝ) (ε : ℝ) (v : Fin d → ℝ) : ℝ :=
  ∑ i, μ i * v i + Real.sqrt (2 * Real.log (1 / ε) *
    ∑ i, (if v i < 0 then σb i ^ 2 * v i ^ 2 else σf i ^ 2 * v i ^ 2))

/-- The right-hand side of (24), p. 19:
`Σ_{vᵢ≥0} m_{fi}vᵢ + Σ_{vᵢ<0} m_{bi}vᵢ + √(2 log(1/ε) (Σ_{vᵢ≥0} σ̄²_{fi}vᵢ² + Σ_{vᵢ<0} σ̄²_{bi}vᵢ²))`. -/
noncomputable def fbValue {d : ℕ} (mb mf sf sb : Fin d → ℝ) (ε : ℝ) (v : Fin d → ℝ) : ℝ :=
  ∑ i, (if 0 ≤ v i then mf i * v i else mb i * v i) + Real.sqrt (2 * Real.log (1 / ε) *
    ∑ i, (if 0 ≤ v i then sf i ^ 2 * v i ^ 2 else sb i ^ 2 * v i ^ 2))

/-- The values of the inner Lagrangian objective of the proof of Theorem 6 (p. ec5) at multiplier
`λ`: `Σ vᵢ(y_{1i} + y_{2i} − y_{3i}) − λ Σ (y²_{2i}/(2σ̄²_{fi}) + y²_{3i}/(2σ̄²_{bi}))` over
`m_b ≤ y₁ ≤ m_f`, `y₂, y₃ ≥ 0`. -/
def lagrangianValues {d : ℕ} (mb mf sf sb : Fin d → ℝ) (lam : ℝ) (v : Fin d → ℝ) : Set ℝ :=
  (fun y : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) =>
      ∑ i, v i * (y.1 i + y.2.1 i - y.2.2 i) -
        lam * ∑ i, (y.2.1 i ^ 2 / (2 * sf i ^ 2) + y.2.2 i ^ 2 / (2 * sb i ^ 2))) ''
    {y | (∀ i, mb i ≤ y.1 i ∧ y.1 i ≤ mf i) ∧ 0 ≤ y.2.1 ∧ 0 ≤ y.2.2}

end DataDrivenRO.FwdBwd


