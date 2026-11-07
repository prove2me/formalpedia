-- Prove2me | Definitions.Def_LDPSelect_Fa
-- name    : LDPSelect_Fa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:05.067892+00:00
-- url     : https://prove2.me/theorems/6cab2cff-d3b2-4a8c-8c76-a5fed5fbc298
-- title:
--   The one-stage value $F_a(X,s)$, private kernels, post-processings and binary randomized response
-- statement:
--   For an integrable $X\ge0$ with mean $\mu$ and a continuation value $s\ge0$,
--
--   $$F_a(X,s)=\max\Big\{s,\ \mu,\ \frac{as+\mu+(a-1)\,\mathbb E(X-s)_+}{a+1}\Big\}.\qquad(1)$$
--
--   The file also defines the objects of the one-stage problem.
--
--   1. A Markov kernel $Q$ is **$a$-locally private** if $Q(B\mid x)\le a\,Q(B\mid x')$ for all measurable $B$ and all $x,x'$.
--   2. A **post-processing** is a measurable $\varphi$ with values in $[0,1]$, the probability of taking $X$ after the report; $q(x)=\int\varphi\,dQ(\cdot\mid x)$ is the resulting acceptance probability.
--   3. The **expected payoff** of taking $X$ with probability $q(X)$ and $s$ otherwise is $\mathbb E[q(X)X+(1-q(X))s]$.
--   4. **Binary randomized response** to $\{X>s\}$ reports $1$ with probability $a/(a+1)$ when $X>s$ and $1/(a+1)$ otherwise.
--
--   **Formalization Note** $\mu$ and $\mathbb E(X-s)_+$ are Lebesgue integrals converted to reals; every statement using them assumes $\mathbb E X<\infty$, under which the conversion is exact.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §2.1, p.5 (pdf p.6), display (1) and Lemma 9

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-!
# The one-stage value `F_a(X, s)` and one-stage rules

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), §2.1, p.5, display (1), Lemma 9.

**Formalization Note.** `µ` and `E(X − s)_+` are lintegrals converted with `.toReal`. Every use is under
an integrability hypothesis, which makes the lintegrals finite, so this is not a junk value. The
post-processing `φ` of a report is a measurable function into `[0, 1]`, the acceptance probability.
The expected payoff is a Bochner integral whose integrand is measurable and at most `x + s`, so it is
integrable for an integrable prior.
-/

/-- `µ = E X`. -/
noncomputable def meanOf (P : Measure ℝ≥0) : ℝ := (∫⁻ x, (x : ℝ≥0∞) ∂P).toReal

/-- `E (X − s)_+`. -/
noncomputable def excess (P : Measure ℝ≥0) (s : ℝ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal ((x : ℝ) - s) ∂P).toReal

/-- The third term of (1): `(a s + µ + (a − 1) E(X − s)_+) / (a + 1)`. -/
noncomputable def faThird (a : ℝ) (P : Measure ℝ≥0) (s : ℝ) : ℝ :=
  (a * s + meanOf P + (a - 1) * excess P s) / (a + 1)

/-- `F_a(X, s) = max {s, µ, (a s + µ + (a − 1) E(X − s)_+) / (a + 1)}`, display (1), p.5. -/
noncomputable def Fa (a : ℝ) (P : Measure ℝ≥0) (s : ℝ) : ℝ :=
  max s (max (meanOf P) (faThird a P s))

/-- A kernel is `a`-locally private: `Q(A | x) ≤ a Q(A | x')` for all measurable `A`, all `x, x'`. -/
def IsPrivateKernel {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] (a : ℝ)
    (Q : Kernel X Z) : Prop :=
  ∀ (x x' : X) (A : Set Z), MeasurableSet A → Q x A ≤ ENNReal.ofReal a * Q x' A

/-- A post-processing of a report: a measurable acceptance probability. -/
def IsPostProcessing {Z : Type*} [MeasurableSpace Z] (φ : Z → ℝ) : Prop :=
  Measurable φ ∧ ∀ z, 0 ≤ φ z ∧ φ z ≤ 1

/-- The acceptance probability `q(x) = ∫ φ dQ(· | x)`. -/
noncomputable def acceptProb {Z : Type*} [MeasurableSpace Z] (Q : Kernel ℝ≥0 Z) (φ : Z → ℝ)
    (x : ℝ≥0) : ℝ :=
  ∫ z, φ z ∂Q x

/-- The expected payoff of taking `X` with probability `q(X)` and `s` otherwise. -/
noncomputable def stagePayoff {Z : Type*} [MeasurableSpace Z] (P : Measure ℝ≥0) (s : ℝ)
    (Q : Kernel ℝ≥0 Z) (φ : Z → ℝ) : ℝ :=
  ∫ x, (acceptProb Q φ x * (x : ℝ) + (1 - acceptProb Q φ x) * s) ∂P

/-- The Bernoulli law on `Bool` with mass `p` at `true`. -/
noncomputable def bern (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

lemma measurableSet_gt_coe (s : ℝ) : MeasurableSet {x : ℝ≥0 | s < (x : ℝ)} :=
  measurableSet_lt measurable_const measurable_coe_nnreal_real

/-- Binary randomized response to the event `{X > s}`: report `true` with probability `a/(a+1)` on the
event and `1/(a+1)` off it (Lemma 9, p.5). -/
noncomputable def rrKernel (a s : ℝ) : Kernel ℝ≥0 Bool :=
  open Classical in
  Kernel.piecewise (measurableSet_gt_coe s)
    (Kernel.const _ (bern (a / (a + 1)))) (Kernel.const _ (bern (1 / (a + 1))))

/-- Accept exactly on the report `true`. -/
def acceptTrue : Bool → ℝ := fun b => if b then 1 else 0

end LDPSelect


