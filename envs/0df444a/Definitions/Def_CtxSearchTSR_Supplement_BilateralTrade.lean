-- Prove2me | Definitions.Def_CtxSearchTSR_Supplement_BilateralTrade
-- name    : CtxSearchTSR_Supplement_BilateralTrade
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:21:02.400308+00:00
-- url     : https://prove2.me/theorems/8fbf1bd6-334a-446a-b167-59c2ff73e0e1
-- title:
--   Bilateral trade: trade bit, lost gain, $L(p)$, $D(p)$ and $\Psi_{\mathrm{tr}}$
-- statement:
--   In **contextual bilateral trade** a seller and a buyer are represented by vectors $s,b\in\mathbb R^d$. Given a context $x$ the broker posts a common price $p$; with $S=x^\top s$ and $B=x^\top b$ the **trade bit** and the **lost gain from trade** are
--
--   $$Y(p)=\mathbf 1\{S\le p\le B\},\qquad \ell=(B-S)_+\,(1-Y(p)),$$
--
--   where $(B-S)_+=(x^\top(b-s))_+$.
--
--   For a joint law $\mu$ of a pair $(S,B)$ of square-integrable reals, the paper's (15) and (16) are
--
--   $$L(p)=\mathbb E\big[(B-S)_+(1-Y(p))\big],\qquad D(p)=\big(\operatorname{sd}(S)-\mathbb E[\operatorname{sd}(S\mid Y(p))]\big)+\big(\operatorname{sd}(B)-\mathbb E[\operatorname{sd}(B\mid Y(p))]\big),$$
--
--   with $\mathbb E[\operatorname{sd}(Z\mid Y(p))]=\sum_{y\in\{0,1\}}\mathbb P(Y(p)=y)\operatorname{sd}(Z\mid Y(p)=y)$, outcomes of probability zero omitted.
--
--   For a joint law $\pi$ of $(s,b)$ with finite second moments, (14) defines
--
--   $$\Psi_{\mathrm{tr}}(\pi)=\operatorname{Tr}\sqrt{\operatorname{Cov}(s)}+\operatorname{Tr}\sqrt{\operatorname{Cov}(b)},$$
--
--   the sum over the two marginals, not the trace square root of the joint covariance.
--
--   **Formalization Note** The trade bit is a Boolean (`true` = trade). Conditioning on $\{Y(p)=y\}$ is `ProbabilityTheory.cond`; a zero-probability outcome contributes $0\cdot\operatorname{sd}$ under the zero measure, which is the omission of p.23.
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §3 p.11, (14) p.11, (15)–(16) p.12, App. D.1 p.23

import Mathlib
import Definitions.Def_CtxSearchTSR_Supplement_Moments

open MeasureTheory ProbabilityTheory

namespace CtxSearchTSR.Supplement

/-!
# The bilateral-trade protocol, the loss L(p), the information D(p), and Ψtr

Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, *Contextual Search and Bilateral Trade with a
Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
§3 (p.11): Yₜ = 1{xₜᵀs ≤ pₜ ≤ xₜᵀb}, ℓₜ = (xₜᵀ(b − s))₊(1 − Yₜ); (14) p.11; (15)–(17) p.12;
App. D.1, p.23 (D(p) written out; zero-probability outcomes omitted from E[sd(Z | Y(p))]).

**Formalization Note.** The trade bit is `Bool` (`true` = trade = Y = 1), both inequalities
non-strict. All one-dimensional quantities are written for the scalar pair (S, B); in context `x`
they are applied to S = xᵀs, B = xᵀb, and (xᵀ(b − s))₊ = (B − S)₊. A joint law of (S, B) is a
measure on ℝ × ℝ. E[sd(Z | Y(p))] = Σ_y P(Y(p) = y) · sd(Z | Y(p) = y); an outcome of probability
zero contributes `0 · sd(·)` under the zero measure, i.e. it is omitted, as on p.23.
-/

/-- The trade bit Y(p) = 1{S ≤ p ≤ B}. -/
noncomputable def tradeBit (S B p : ℝ) : Bool := decide (S ≤ p ∧ p ≤ B)

/-- The lost gain from trade (B − S)₊ (1 − Y(p)). -/
noncomputable def tradeLoss (S B p : ℝ) : ℝ :=
  max (B - S) 0 * (1 - if tradeBit S B p then 1 else 0)

/-- The expected lost gain (15): L(p) = E[(B − S)₊(1 − Y(p))] under the joint law `μ` of (S, B). -/
noncomputable def lossL (μ : Measure (ℝ × ℝ)) (p : ℝ) : ℝ :=
  ∫ q, tradeLoss q.1 q.2 p ∂μ

/-- The event {Y(p) = y}. -/
def tradeEvent (p : ℝ) (y : Bool) : Set (ℝ × ℝ) := {q | tradeBit q.1 q.2 p = y}

/-- E[sd(Z | Y(p))] = Σ_y P(Y(p) = y) · sd(Z | Y(p) = y) for the coordinate `f` (= S or B). -/
noncomputable def expCondSd (f : ℝ × ℝ → ℝ) (μ : Measure (ℝ × ℝ)) (p : ℝ) : ℝ :=
  ∑ y : Bool, (μ (tradeEvent p y)).toReal * sd f (μ[|tradeEvent p y])

/-- The standard-deviation drop (16): D(p) = (sd(S) − E[sd(S | Y(p))]) + (sd(B) − E[sd(B | Y(p))]). -/
noncomputable def infoD (μ : Measure (ℝ × ℝ)) (p : ℝ) : ℝ :=
  (sd Prod.fst μ - expCondSd Prod.fst μ p) + (sd Prod.snd μ - expCondSd Prod.snd μ p)

/-- The bilateral potential (14): Ψtr(π) = Tr √Cov(s) + Tr √Cov(b), the sum over the two marginals. -/
noncomputable def psiTr {d : ℕ} (π : Measure ((Fin d → ℝ) × (Fin d → ℝ))) : ℝ :=
  trSqrt (covMat (π.map Prod.fst)) + trSqrt (covMat (π.map Prod.snd))

end CtxSearchTSR.Supplement


