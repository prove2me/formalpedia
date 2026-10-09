-- Prove2me | Definitions.Def_MultiItemRev_BundlingOpt_Model
-- name    : MultiItemRev_BundlingOpt_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:06.351599+00:00
-- url     : https://prove2.me/theorems/07ca3e6f-ace8-4c7f-8ed2-9bc69113d555
-- title:
--   §2.1, pp. 11–15 and p. 21 — mechanisms on ℝ^k_+, IC, IR, NPT, R(µ;X), Rev, SRev, BRev, the ER law
-- statement:
--   The single-buyer, multi-good selling model of Hart and Nisan (§2.1).
--
--   A seller offers a finite set $\iota$ of goods ($k = |\iota|$) to one buyer whose valuation is a vector $x \in \mathbb{R}^k_+$; the buyer's value for a set of goods is additive. A random valuation $X$ is described by its law $\mu$, a probability measure on $\mathbb{R}^k_+$.
--
--   1. A **mechanism** $\mu = (q, s)$ consists of an allocation $q : \mathbb{R}^k_+ \to \mathbb{R}^k$, where $q_i(x)$ is the probability that good $i$ is allocated when the buyer reports $x$, and a payment $s : \mathbb{R}^k_+ \to \mathbb{R}$. The buyer's payoff is
--   $$b(x) = q(x)\cdot x - s(x) = \sum_i q_i(x)\,x_i - s(x).$$
--   2. The mechanism is **feasible** if $q(x) \in [0,1]^k$ for every $x$; **incentive compatible (IC)** if $b(x) \ge q(\tilde x)\cdot x - s(\tilde x)$ for all $x, \tilde x \in \mathbb{R}^k_+$; **individually rational (IR)** if $b(x) \ge 0$ for all $x$; and has **no positive transfer (NPT)** if $s(x) \ge 0$ for all $x$. The class $\mathcal M$ of admissible mechanisms consists of the feasible, IC and IR mechanisms whose payment function is measurable.
--   3. The **expected revenue** of $\mu$ from $X$ is $R(\mu; X) = \mathbb{E}[s(X)] \in (-\infty, +\infty]$, the integral of the positive part of $s$ minus the integral of its negative part.
--   4. The **optimal revenue** is $\mathrm{Rev}(X) = \sup_{\mu \in \mathcal M} R(\mu; X) \in [0, \infty]$. For one good with law $\nu$ on $\mathbb{R}_+$ this is written $\mathrm{Rev}(\nu)$.
--   5. The **separate revenue** is $\mathrm{SRev}(X) = \sum_i \mathrm{Rev}(X_i)$ and the **bundled revenue** is $\mathrm{BRev}(X) = \mathrm{Rev}(X_1 + \dots + X_k)$.
--   6. The **equal-revenue (ER) law** is the law on $[1,\infty)$ with density $1/x^2$, i.e. $\mathbb{P}[V \ge p] = 1/p$ for $p \ge 1$ (p. 21).
--
--   These objects are the vocabulary of every statement in the mission.
--
--   **Formalization Note** Valuations are functions $\iota \to \mathbb{R}_{\ge 0}$ and random valuations are given by their laws. $R(\mu;X)$ is an extended real (positive part minus negative part of $s$), so a non-integrable payment never defaults to $0$; for an IC mechanism the negative part is finite, since $s \ge s(0)$. In $\mathrm{Rev}$ each revenue is clipped at $0$ before the supremum; the zero mechanism is admissible with revenue $0$, so this does not change the supremum. Measurability of $s$ is part of admissibility, as footnote 12 of the paper allows without loss of generality. One good is the index type `Unit`.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, pp. 11–15, §2.1 (mechanism, b, IC, IR, footnote 12, R(µ;X), Rev, SRev, BRev, NPT); p. 21 (ER distribution)

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt

/-- A (direct) mechanism for the goods `ι` (§2.1, p. 11): an allocation `q x i` (the probability
that good `i` is allocated at the reported valuation `x`) and a payment `s x`. -/
structure Mechanism (ι : Type*) where
  q : (ι → ℝ≥0) → ι → ℝ
  s : (ι → ℝ≥0) → ℝ

variable {ι : Type*} [Fintype ι]

/-- The buyer's payoff `b(x) = q(x) · x − s(x)` (p. 11). -/
def buyerPayoff (M : Mechanism ι) (x : ι → ℝ≥0) : ℝ :=
  ∑ i, M.q x i * (x i : ℝ) - M.s x

/-- `q : ℝ^k_+ → [0,1]^k` (p. 11). -/
def IsFeasible (M : Mechanism ι) : Prop :=
  ∀ x i, 0 ≤ M.q x i ∧ M.q x i ≤ 1

/-- Incentive compatibility (IC, p. 12): `b(x) ≥ q(x') · x − s(x')` for all `x, x'`. -/
def IsIC (M : Mechanism ι) : Prop :=
  ∀ x x', ∑ i, M.q x' i * (x i : ℝ) - M.s x' ≤ buyerPayoff M x

/-- Individual rationality (IR, p. 12): `b(x) ≥ 0` for all `x`. -/
def IsIR (M : Mechanism ι) : Prop :=
  ∀ x, 0 ≤ buyerPayoff M x

/-- No positive transfer (NPT, p. 14): `s(x) ≥ 0` for all `x`. -/
def IsNPT (M : Mechanism ι) : Prop :=
  ∀ x, 0 ≤ M.s x

/-- The class `𝓜` of IC and IR mechanisms (p. 12), with a measurable payment function
(footnote 12). -/
def IsAdmissible (M : Mechanism ι) : Prop :=
  IsFeasible M ∧ IsIC M ∧ IsIR M ∧ Measurable M.s

/-- The expected revenue `R(µ; X) = E[s(X)]` (p. 12) when `X` has law `μ`, as an extended real:
positive part minus negative part. -/
noncomputable def expRevenue (μ : Measure (ι → ℝ≥0)) (M : Mechanism ι) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (M.s x) ∂μ : ℝ≥0∞) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-M.s x) ∂μ : ℝ≥0∞) : EReal)

/-- The optimal revenue `Rev(X) = sup_{µ ∈ 𝓜} R(µ; X)` (p. 12). -/
noncomputable def Rev (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  ⨆ (M : Mechanism ι) (_ : IsAdmissible M), (expRevenue μ M).toENNReal

/-- A one-good law, viewed as a law on `Unit → ℝ≥0`. -/
noncomputable def oneGood (ν : Measure ℝ≥0) : Measure (Unit → ℝ≥0) :=
  ν.map (fun t _ => t)

/-- The optimal revenue from one good with law `ν`. -/
noncomputable def Rev1 (ν : Measure ℝ≥0) : ℝ≥0∞ :=
  Rev (oneGood ν)

/-- `SRev(X) = Rev(X₁) + … + Rev(X_k)` (p. 12). -/
noncomputable def SRev (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  ∑ i, Rev1 (μ.map (fun x => x i))

/-- `BRev(X) = Rev(X₁ + … + X_k)` (p. 13). -/
noncomputable def BRev (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  Rev1 (μ.map (fun x => ∑ i, x i))

/-- The equal-revenue (ER) law (p. 21): `P[V ≥ p] = 1/p` for `p ≥ 1`, density `1/x²` on `[1, ∞)`. -/
noncomputable def erLaw : Measure ℝ≥0 :=
  ((volume.restrict (Set.Ici (1 : ℝ))).withDensity
    (fun x => ENNReal.ofReal (1 / x ^ 2))).map Real.toNNReal

end MultiItemRev.BundlingOpt


