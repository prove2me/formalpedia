-- Prove2me | Definitions.Def_ComputationalLearning_Boosting
-- name    : ComputationalLearning_Boosting
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T03:20:01.278358+00:00
-- url     : https://prove2.me/theorems/63f5d7d4-0995-4acb-9039-fdf1e44a6426
-- title:
--   Chapter 4 and Appendix: g(β) = 3β² − 2β³, the filtered distributions D₂ and D₃, majority of three, majority trees, weak learnability, k-run sample law, mistakes; Bernoulli trials
-- statement:
--   The objects of Chapter 4 and of the Appendix, on the framework of Mission I.
--
--   **The modest boosting procedure (§4.3.1).** `boostFun β` is $g(\beta) = 3\beta^2 - 2\beta^3$. Given the target $c$, the distribution $D$ and a first hypothesis $h_1$, the **filtered distribution** `filtered2 D c h₁` is $D_2 = \tfrac12 D[\cdot \mid h_1 = c] + \tfrac12 D[\cdot \mid h_1 \ne c]$ (Mathlib's conditional measure; a part whose conditioning event is $D$-null contributes the zero measure), which gives weight exactly $1/2$ to the instances on which $h_1$ errs and preserves relative weights within each part; `filtered3 D h₁ h₂` is $D_3 = D[\cdot \mid h_1 \ne h_2]$. `majority3 h₁ h₂ h₃` is the majority vote. `majorityTrees H` is the class of ternary majority trees with leaves from $H$: the smallest class containing $H$ and closed under `majority3` (Theorem 4.9's hypothesis class).
--
--   **Weak learning (§4.1).** `WeaklyLearnable C H`: for some advantage $\gamma > 0$, confidence $\delta_0 > 0$ and sample size $m$, a learning algorithm outputs hypotheses in $H$ and, for every measurable $c \in C$ and every distribution $D$, its hypothesis has error greater than $1/2 - \gamma$ with probability at most $1 - \delta_0$ (that is, error at most $1/2 - \gamma$ with probability at least $\delta_0$). This is the book's definition for a fixed class, where $1/p(n, \mathrm{size}(c))$ and $1/q(n, \mathrm{size}(c))$ are constants. The algorithm is also required to be **jointly measurable**: $(S, x) \mapsto L(S)(x)$ is measurable. Every algorithm is, and the boosting argument needs it. The filtered distributions on which $L$ is run again are built from its earlier outputs, so the probability that the combined run fails is an integral over the earlier samples. For an arbitrary function $L$ the combined failure event need not be measurable, and outer-measure bounds on the separate runs do not combine.
--
--   **Confidence boosting (§4.2).** `blockSampleLaw D c k m` is the law of $k$ independent samples of $m$ examples; `mistakes h S` is the number of examples of $S$ misclassified by $h$.
--
--   **Bernoulli trials (§9.3).** `bernoulliMeasure p` is the Bernoulli distribution on `Bool`, `trialsLaw p m` the law of $m$ independent trials, `successes ω` the number $S = X_1 + \dots + X_m$ of successes.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, Chapter 4: §4.1 weak PAC learning (p. 74), §4.2 confidence boosting (pp. 76-77), §4.3.1 the filtered distributions and majority (pp. 79-81), §4.3.2 g(β) (p. 82), Theorem 4.9's majority trees (p. 100); Chapter 9, §9.3 Bernoulli trials (p. 190)

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_ComputationalLearning_VC

/-!
# Kearns and Vazirani, Chapter 4: weak and strong learning

Kearns and Vazirani, *An Introduction to Computational Learning Theory*, MIT Press 1994,
doi:10.7551/mitpress/3897.001.0001, Chapter 4 (pp. 73–102) and the Appendix (Chapter 9,
pp. 189–191).

**Weak learning (§4.1, p. 74).** `L` is a *weak* PAC learning algorithm for `C` using `H` if it
outputs `h ∈ H` that with probability at least `1/q(n, size(c))` satisfies
`error(h) ≤ 1/2 − 1/p(n, size(c))`: inverse-polynomial confidence and an inverse-polynomial
advantage over random guessing. Theorem 4.9 (p. 100): if `C` is efficiently weakly PAC
learnable using `H`, it is efficiently strongly PAC learnable using ternary majority trees with
leaves from `H`. In the sample-complexity sense, for a fixed class, the confidence and the
advantage are constants `δ₀, γ > 0`, and the algorithm is jointly measurable in the sample and
the instance (`WeaklyLearnable`).

**Boosting the confidence (§4.2, pp. 76–77).** Run the learner `k` times on independent samples,
then choose, on a fresh sample, the hypothesis that makes the fewest mistakes.

**The modest accuracy boosting procedure (§4.3.1–4.3.2, pp. 79–85).** From `h₁` with
`error_D(h₁) ≤ β`, the *filtered* distribution `D₂` gives weight exactly `1/2` to the instances
on which `h₁` errs and `1/2` to those on which it is correct, keeping relative weights within
each part; `D₃` is `D` conditioned on `h₁ ≠ h₂`; the output is `majority(h₁, h₂, h₃)`, and Lemma
4.1 bounds its error by `g(β) = 3β² − 2β³`.

**Chernoff bounds (Theorem 9.2, p. 190).** For `m` independent Bernoulli trials of success
probability `p` and `0 < γ ≤ 1`: `Pr[S ≥ (p+γ)m] ≤ e^{−2mγ²}`, `Pr[S ≤ (p−γ)m] ≤ e^{−2mγ²}`,
`Pr[S ≥ (1+γ)pm] ≤ e^{−mpγ²/3}`, `Pr[S ≤ (1−γ)pm] ≤ e^{−mpγ²/2}`.
-/

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

section Boosting

variable {X : Type*} [MeasurableSpace X]

/-- `g(β) = 3β² − 2β³`, the error bound of the modest boosting procedure (p. 82). -/
def boostFun (β : ℝ) : ℝ :=
  3 * β ^ 2 - 2 * β ^ 3

/-- The **filtered distribution** `D₂` (p. 80): with probability `1/2` a draw from `D` conditioned
on `h₁(x) = c(x)`, with probability `1/2` a draw from `D` conditioned on `h₁(x) ≠ c(x)` (Mathlib's
`cond`, the zero measure if the conditioning event is `D`-null). -/
noncomputable def filtered2 (D : Measure X) (c h₁ : X → Bool) : Measure X :=
  (1 / 2 : ENNReal) • D[|{x | h₁ x = c x}] + (1 / 2 : ENNReal) • D[|{x | h₁ x ≠ c x}]

/-- The **filtered distribution** `D₃` (p. 81): `D` conditioned on `h₁(x) ≠ h₂(x)`. -/
noncomputable def filtered3 (D : Measure X) (h₁ h₂ : X → Bool) : Measure X :=
  D[|{x | h₁ x ≠ h₂ x}]

/-- `majority(h₁, h₂, h₃)`: `1` iff at least two of the three hypotheses output `1` (p. 81). -/
def majority3 (h₁ h₂ h₃ : X → Bool) : X → Bool :=
  fun x ↦ (h₁ x && h₂ x) || (h₁ x && h₃ x) || (h₂ x && h₃ x)

/-- The hypothesis class of **ternary majority trees with leaves from `H`** (Theorem 4.9): the
smallest class containing `H` and closed under `majority3`. -/
inductive MajorityTree (H : Set (X → Bool)) : (X → Bool) → Prop
  | leaf {h : X → Bool} : h ∈ H → MajorityTree H h
  | node {h₁ h₂ h₃ : X → Bool} :
      MajorityTree H h₁ → MajorityTree H h₂ → MajorityTree H h₃ →
      MajorityTree H (majority3 h₁ h₂ h₃)

/-- The class of ternary majority trees with leaves from `H`, as a set. -/
def majorityTrees (H : Set (X → Bool)) : Set (X → Bool) :=
  {h | MajorityTree H h}

/-- `C` is **weakly PAC learnable using `H`** (§4.1, sample-complexity sense, fixed class): for
some advantage `γ > 0`, confidence `δ₀ > 0` and sample size `m`, an algorithm outputs hypotheses
in `H` that, for every measurable target in `C` and every distribution, have error at most
`1/2 − γ` with probability at least `δ₀`. The algorithm is jointly measurable: its prediction
`L S x` is a measurable function of the sample and the instance together, as for every algorithm.
Boosting needs this, because the filtered distributions are built from earlier outputs of `L` and
the failure probability of the combined run is an integral over the earlier samples. -/
def WeaklyLearnable (C H : Set (X → Bool)) : Prop :=
  ∃ (γ δ₀ : ℝ) (m : ℕ) (L : (Fin m → X × Bool) → X → Bool), 0 < γ ∧ 0 < δ₀ ∧
    (∀ S, L S ∈ H) ∧ Measurable (fun p : (Fin m → X × Bool) × X ↦ L p.1 p.2) ∧
    ∀ c ∈ C, Measurable c → ∀ D : Measure X, IsProbabilityMeasure D →
      sampleLaw D c m {S | 1 / 2 - γ < errorOf D c (L S)} ≤ ENNReal.ofReal (1 - δ₀)

/-- The law of `k` independent samples of `m` examples each (the `k` runs of §4.2). -/
noncomputable def blockSampleLaw (D : Measure X) (c : X → Bool) (k m : ℕ) :
    Measure (Fin k → Fin m → X × Bool) :=
  Measure.pi (fun _ ↦ sampleLaw D c m)

/-- The number of mistakes of `h` on the labeled sample `S` (its empirical error times `m`). -/
def mistakes {m : ℕ} (h : X → Bool) (S : Fin m → X × Bool) : ℕ :=
  (Finset.univ.filter (fun i ↦ h (S i).1 ≠ (S i).2)).card

end Boosting

/-! ### Bernoulli trials (Appendix, §9.3) -/

section Chernoff

/-- The Bernoulli distribution on `Bool` with success probability `p ∈ [0, 1]`. -/
noncomputable def bernoulliMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

/-- The law of `m` independent Bernoulli trials with success probability `p`. -/
noncomputable def trialsLaw (p : ℝ) (m : ℕ) : Measure (Fin m → Bool) :=
  Measure.pi (fun _ ↦ bernoulliMeasure p)

/-- `S = X₁ + ⋯ + Xₘ`, the number of successes. -/
def successes {m : ℕ} (ω : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun i ↦ ω i = true)).card

end Chernoff

end ComputationalLearning


