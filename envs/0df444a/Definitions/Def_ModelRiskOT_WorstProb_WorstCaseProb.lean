-- Prove2me | Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb
-- name    : ModelRiskOT_WorstProb_WorstCaseProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:48:21.543976+00:00
-- url     : https://prove2.me/theorems/dbf1ca69-cc24-406d-b533-d1461200f93c
-- title:
--   $c(x,A)$, the worst-case probability (12) in measure and coupling form, the objective of (13), and $\underline c$, $\overline c$ (14)
-- statement:
--   Let $S$, $c$, $\mu$, $\delta$, $d_c$ and $\Phi_{\mu,\delta}$ be as in the previous definition, and let $A \subseteq S$.
--
--   1. **Cost to a set** (p. 9): $c(x,A) := \inf\{c(x,y) : y \in A\}$, the lowest cost of transporting unit mass from $x$ to some point of $A$.
--   2. **Worst-case probability** (12): $$I = \sup\{P(A) : P \in P(S),\ d_c(\mu,P) \le \delta\}.$$
--   3. **Coupling form** of the same quantity for $f = 1_A$ (p. 9): $\sup\{\pi(S \times A) : \pi \in \Phi_{\mu,\delta}\}$.
--   4. **Objective of (13)**: for $\lambda \in \mathbb R$, $$g(\lambda) = \lambda\delta + E_\mu\big[(1 - \lambda c(X,A))^+\big].$$
--   5. **$\lambda^*$ attains the infimum in (13)**: $\lambda^* \ge 0$ and $g(\lambda^*) \le g(\lambda)$ for every $\lambda \ge 0$.
--   6. **The quantities (14)**, defined in terms of $\lambda^*$:
--   $$\underline c := \int_{\{x : c(x,A) < 1/\lambda^*\}} c(x,A)\,d\mu(x), \qquad \overline c := \int_{\{x : c(x,A) \le 1/\lambda^*\}} c(x,A)\,d\mu(x).$$
--
--   These are the objects in which the paper's worst-case probability results are stated: (13) reduces $I$ to a one-dimensional problem in $\lambda$, and $\underline c$, $\overline c$ locate the budget $\delta$ relative to the optimal $\lambda^*$.
--
--   **Formalization Note** $c(x,A)$ is an infimum over the subtype $A$ in $\mathbb R$; for nonempty $A$ and $c \ge 0$ it is the true infimum (on empty $A$ Lean returns $0$, so every theorem assumes $A \neq \emptyset$). The thresholds $c(x,A) \le 1/\lambda^*$ and $c(x,A) < 1/\lambda^*$ are written $\lambda^* c(x,A) \le 1$ and $\lambda^* c(x,A) < 1$: for $\lambda^* > 0$ these are the printed sets, and at $\lambda^* = 0$ they are all of $S$, which is the paper's reading $1/0 = \infty$ (Lean's $1/0 = 0$ would not be). All values live in $[0,\infty]$: the positive part $(\cdot)^+$ is `ENNReal.ofReal`, expectations are lower Lebesgue integrals and $\mu$ of a set is its outer measure. The function $x \mapsto c(x,A)$ is in general only universally measurable, and for such functions and sets these coincide with the integrals and probabilities under the completion of $\mu$, which is how the paper reads them (p. 4). No Bochner integral is used.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 8, Eq. (12); p. 9, c(x, A), Eqs. (13), (14)

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_TransportBall

open MeasureTheory
open scoped ENNReal

namespace ModelRiskOT.WorstProb

/-- `c(x, A) := inf {c(x, y) : y ∈ A}` (p. 9), the lowest cost of transporting unit mass from `x`
into `A`. Taken as an infimum over the subtype `A` in `ℝ`; for nonempty `A` and `c ≥ 0` the family
is nonempty and bounded below, so this is the true infimum. -/
noncomputable def costToSet {S : Type*} (c : S → S → ℝ) (A : Set S) (x : S) : ℝ :=
  ⨅ y : A, c x y

/-- The worst-case probability (12), p. 8, in its printed form:
`I = sup {P(A) : d_c(μ, P) ≤ δ}`, the supremum over probability measures `P` on `S`. -/
noncomputable def worstProb {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (μ : Measure S)
    (δ : ℝ) (A : Set S) : ℝ≥0∞ :=
  ⨆ (P : Measure S) (_ : IsProbabilityMeasure P ∧ transportCost c μ P ≤ ENNReal.ofReal δ), P A

/-- The worst-case probability in coupling form (3) for `f = 1_A` (p. 9):
`sup {π(S × A) : π ∈ Φ_{μ,δ}}`. -/
noncomputable def worstProbCoupling {S : Type*} [MeasurableSpace S] (c : S → S → ℝ)
    (μ : Measure S) (δ : ℝ) (A : Set S) : ℝ≥0∞ :=
  ⨆ π ∈ Phi c μ δ, π (Set.univ ×ˢ A)

/-- The objective of the univariate problem (13), p. 9:
`g(λ) = λδ + E_μ[(1 − λ c(X, A))⁺]`. `ENNReal.ofReal` truncates at `0`, i.e. takes the positive
part. -/
noncomputable def obj13 {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (μ : Measure S)
    (δ : ℝ) (A : Set S) (lam : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (lam * δ) + ∫⁻ x, ENNReal.ofReal (1 - lam * costToSet c A x) ∂μ

/-- "`λ* ∈ [0, ∞)` attains the infimum in (13)" (Lemma 2, Theorem 3, Lemma 4): `λ* ≥ 0` and
`g(λ*) ≤ g(λ)` for every `λ ≥ 0`. -/
def AttainsInf13 {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (μ : Measure S) (δ : ℝ)
    (A : Set S) (lamStar : ℝ) : Prop :=
  0 ≤ lamStar ∧ ∀ lam : ℝ, 0 ≤ lam → obj13 c μ δ A lamStar ≤ obj13 c μ δ A lam

/-- `c̲ := ∫_{x : c(x,A) < 1/λ*} c(x, A) dμ(x)` of (14), p. 9, with the threshold in multiplied
form `λ* c(x, A) < 1` (so that `1/λ* = ∞` at `λ* = 0`). -/
noncomputable def cLower {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (μ : Measure S)
    (A : Set S) (lamStar : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | lamStar * costToSet c A x < 1}, ENNReal.ofReal (costToSet c A x) ∂μ

/-- `c̄ := ∫_{x : c(x,A) ≤ 1/λ*} c(x, A) dμ(x)` of (14), p. 9, with the threshold in multiplied
form `λ* c(x, A) ≤ 1`. -/
noncomputable def cUpper {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (μ : Measure S)
    (A : Set S) (lamStar : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | lamStar * costToSet c A x ≤ 1}, ENNReal.ofReal (costToSet c A x) ∂μ

end ModelRiskOT.WorstProb


