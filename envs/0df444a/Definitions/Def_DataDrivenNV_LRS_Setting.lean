-- Prove2me | Definitions.Def_DataDrivenNV_LRS_Setting
-- name    : DataDrivenNV_LRS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:03:31.037089+00:00
-- url     : https://prove2.me/theorems/61305213-96e1-4a78-bc23-da597db9cd2e
-- title:
--   §2, pp. 7–8 — newsvendor cost C, critical quantile q*, ε-optimality, ∂±C formulas, S^LRS_ε (3), empirical cdf and SAA quantile (2)
-- statement:
--   The data-driven newsvendor model of Levi, Perakis and Uichanco (§2–§2.1).
--
--   A retailer orders $q$ units before a real-valued demand $D$ with law $\mu$ (a probability measure on $\mathbb R$) is observed. Each unit of unmet demand costs $b>0$ (underage cost) and each unsold unit costs $h>0$ (overage cost). This file defines:
--
--   1. the realized cost $b(d-q)^+ + h(q-d)^+$ and the **expected cost**
--   $$C(q) = \mathbb E\big[b(D-q)^+ + h(q-D)^+\big];$$
--   2. the **critical quantile** $q^* = \inf\{q : F(q) \ge b/(b+h)\}$, where $F(q)=\Pr(D\le q)$ is the right-continuous cdf of $D$;
--   3. **$\epsilon$-optimality**: $q$ is $\epsilon$-optimal when its relative regret is at most $\epsilon$, i.e. $C(q) \le (1+\epsilon)\,C(q^*)$;
--   4. the formulas for the one-sided derivatives of $C$,
--   $$\partial_+C(q) = -b + (b+h)F(q), \qquad \partial_-C(q) = -b + (b+h)\Pr(D<q);$$
--   5. the **LRS interval** of display (3),
--   $$S^{LRS}_\epsilon = \Big\{q : \partial_-C(q) \le \tfrac{\epsilon}{3}\min(b,h) \text{ and } \partial_+C(q) \ge -\tfrac{\epsilon}{3}\min(b,h)\Big\};$$
--   6. for a sample $x = (x_1,\dots,x_N)$, the **empirical cdf** $\hat F_N(q) = \frac1N\sum_{k=1}^N \mathbf 1[x_k\le q]$ and the **SAA solution** of display (2), the $b/(b+h)$ sample quantile
--   $$\hat Q_N = \inf\{q : \hat F_N(q) \ge b/(b+h)\}.$$
--
--   These are the objects of the distribution-free analysis of SAA accuracy: Theorem 2 bounds the probability that $\hat Q_N$ is not $\epsilon$-optimal.
--
--   **Formalization Note** The realized cost is the published `InventoryControl.newsboyLoss h b q d` (overage cost first). $C$ is a Bochner integral, which is $0$ when the cost is not integrable, so every theorem that evaluates $C$ assumes $\mathbb E|D|<\infty$. The two derivative formulas are defined as functions named after $\partial_\pm C$; that they are the one-sided derivatives is a separate theorem. Both quantiles are `sInf` of a set that, for $0<b/(b+h)<1$, a probability measure and $N\ge1$, is nonempty and bounded below, so they are true infima. The sample is indexed by `Fin N` (0-based). No sign restriction is placed on $D$.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), pp. 7–8, §2 (C, ∂±C, q*, (2)) and §2.1 (ε-optimality, (3)); relative regret defined on p. 2

import Mathlib
import Definitions.Def_InventoryControl_newsboy

open MeasureTheory ProbabilityTheory

namespace DataDrivenNV.LRS

/-- The realized newsvendor cost of ordering `q` when the demand is `d`, with unit underage cost
`b` and unit overage cost `h`: `b (d - q)⁺ + h (q - d)⁺` (Levi–Perakis–Uichanco, §2, p. 7).
It is the published `InventoryControl.newsboyLoss` with the overage cost `h` first. -/
noncomputable def nvLoss (b h q d : ℝ) : ℝ := InventoryControl.newsboyLoss h b q d

/-- The expected newsvendor cost `C(q) = E[b (D - q)⁺ + h (q - D)⁺]` under the demand law `μ`
(§2, p. 7). -/
noncomputable def expCost (μ : Measure ℝ) (b h q : ℝ) : ℝ := ∫ d, nvLoss b h q d ∂μ

/-- The critical (newsvendor) quantile `q* = inf {q : F(q) ≥ b/(b+h)}`, where `F = cdf μ` is the
right-continuous cdf `F(q) = μ(-∞, q]` (§2, p. 7). -/
noncomputable def critQuantile (μ : Measure ℝ) (b h : ℝ) : ℝ :=
  sInf {q : ℝ | b / (b + h) ≤ cdf μ q}

/-- `q` is `ε`-optimal: its relative regret `(C(q) - C(q*)) / C(q*)` is at most `ε`, written in the
multiplicative form `C(q) ≤ (1 + ε) C(q*)` (§2.1, p. 8; p. 2; p. 13). -/
def IsEpsOptimal (μ : Measure ℝ) (b h ε q : ℝ) : Prop :=
  expCost μ b h q ≤ (1 + ε) * expCost μ b h (critQuantile μ b h)

/-- The formula `∂₊C(q) = -b + (b + h) F(q)` for the right-sided derivative of `C` (§2, p. 7). -/
noncomputable def dPlus (μ : Measure ℝ) (b h q : ℝ) : ℝ := -b + (b + h) * cdf μ q

/-- The formula `∂₋C(q) = -b + (b + h) Pr(D < q)` for the left-sided derivative of `C`
(§2, p. 7). -/
noncomputable def dMinus (μ : Measure ℝ) (b h q : ℝ) : ℝ :=
  -b + (b + h) * (μ (Set.Iio q)).toReal

/-- The LRS interval `S^LRS_ε = {q : ∂₋C(q) ≤ (ε/3) min(b,h) and ∂₊C(q) ≥ -(ε/3) min(b,h)}`,
display (3), §2.1, p. 8. -/
noncomputable def lrsSet (μ : Measure ℝ) (b h ε : ℝ) : Set ℝ :=
  {q | dMinus μ b h q ≤ ε / 3 * min b h ∧ -(ε / 3 * min b h) ≤ dPlus μ b h q}

/-- The empirical cdf `F̂_N(q) = (1/N) Σ_k 1[x_k ≤ q]` of a sample `x : Fin N → ℝ` (§2, p. 7). -/
noncomputable def empCdf {N : ℕ} (x : Fin N → ℝ) (q : ℝ) : ℝ :=
  ((Finset.univ.filter fun k => x k ≤ q).card : ℝ) / N

/-- The SAA order quantity `Q̂_N = inf {q : F̂_N(q) ≥ b/(b+h)}`, the `b/(b+h)` sample quantile,
display (2), §2, p. 7. -/
noncomputable def saaQuantile {N : ℕ} (b h : ℝ) (x : Fin N → ℝ) : ℝ :=
  sInf {q : ℝ | b / (b + h) ≤ empCdf x q}

end DataDrivenNV.LRS


