-- Prove2me | Definitions.Def_AutomatedMarketStress557_Persistence_Supplement_FeedbackDetection
-- name    : AutomatedMarketStress557_Persistence_Supplement_FeedbackDetection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:43:06.959208+00:00
-- url     : https://prove2.me/theorems/fb5786da-8142-41ae-961c-24a773f628d0
-- title:
--   Observed return paths, the sign-agreement detector and test errors for feedback detection
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space carrying a real initial return $r_0$ and news variables $\xi_1,\xi_2,\ldots$. The **Gaussian experiment** hypothesis says: the $\xi_t$ are independent standard normal variables, $r_0$ is a random variable independent of the whole news sequence, $r_0\neq0$ almost surely, and the initial sign $D_0=\operatorname{sgn}(r_0)$ is uniform on $\{-1,+1\}$. Apart from this, the law of $r_0$ is arbitrary. This is Assumption 1 of the paper with $G=\Phi$, expressed through the published feedback model applied to the initial sign $D_0$.
--
--   For feedback $\beta\in\mathbb R$ and scale $s$, the **observed returns** are $r_0$ itself at time $0$ and, for $t\ge1$,
--
--   $$r_t=\beta D_{t-1}+s\xi_t,\qquad D_t=\operatorname{sgn}(r_t).$$
--
--   After $n$ transitions the observation is the path $(r_0,\ldots,r_n)\in\mathbb R^{n+1}$, and $P_\beta$ denotes its law. The same $r_0$ and news give the experiments $P_\beta$ and $P_{-\beta}$, so the two experiments share their initial law.
--
--   For a path $x=(x_0,\ldots,x_n)$ the **sign-agreement statistic** is
--
--   $$\hat q=\frac1n\sum_{t=1}^n\mathbf 1[\operatorname{sgn}x_t=\operatorname{sgn}x_{t-1}],$$
--
--   and the **detector** outputs $+1$ ("herding", positive feedback) if $\hat q>\tfrac12$ and $-1$ (negative feedback) otherwise; ties at $\hat q=\tfrac12$ are decided negative.
--
--   A (possibly randomized) **test** of the full path is a measurable $\psi:\mathbb R^{n+1}\to[0,1]$, read as the probability of answering "herding". Its **error** under feedback $\beta$ is $\int(1-\psi)\,dP_\beta$ when $\beta>0$ and $\int\psi\,dP_\beta$ when $\beta\le0$. Deterministic tests are the indicator functions of measurable sets.
--
--   These objects are the setting of the paper's Theorem 4.5 on the sample complexity of detecting the sign of feedback.
--
--   **Formalization Note** The sign function maps $0$ to $+1$; positive-time returns are nonzero almost surely, and $r_0\neq0$ almost surely by hypothesis. For $n=0$ the statistic is $0$, so the detector answers negative. Path laws are pushforward measures on `Fin (n+1) → ℝ`.
-- source:
--   Irene Aldridge, STOC 2027 submission #557 (October 2026), Theorem 4.5 and its proof, PDF pp. 3–4; equation (3), PDF p. 2; Assumption 1, PDF p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/557.pdf

import Mathlib
import Definitions.Def_AutomatedMarketStress557_Persistence_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace AutomatedMarketStress557.Persistence.Supplement

open AutomatedMarketStress557.Persistence

/-- The hypotheses of Theorem 4.5 (PDF pp. 3–4) on the randomness: Assumption 1
(PDF p. 3) with Gaussian news `G = Φ`, stated through the published `Model` with
initial sign `D₀ = sgn r₀`. The initial return `r₀` itself is a real random
variable, independent of the entire news sequence (Assumption 1), with
`r₀ ≠ 0` almost surely, which is what "D₀ uniform on {±1}" means for
`D₀ = sgn r₀`. Its law is otherwise arbitrary. Feedback and scale are not part
of the predicate; the same `r₀, ξ` serve the `+β` and `-β` experiments. -/
def GaussianExperiment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (r₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) : Prop :=
  Model P (gaussianReal 0 1) (fun ω => sign (r₀ ω)) ξ ∧ AEMeasurable r₀ P ∧
  IndepFun r₀ (fun ω n => ξ n ω) P ∧ (∀ᵐ ω ∂P, r₀ ω ≠ 0)

/-- The observed returns `r₀, r₁, …` of equation (3), PDF p. 2: time zero is the
actual real initial return, and every later return is the published recursion
started from the initial sign `sgn r₀`. -/
def observedReturn {Ω : Type*} (β s : ℝ) (r₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => r₀
  | t + 1 => returns β s (fun ω => sign (r₀ ω)) ξ (t + 1)

/-- The observation `(r₀, …, rₙ)` after `n` transitions. -/
def observedPath {Ω : Type*} (β s : ℝ) (r₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : Fin (n + 1) → ℝ :=
  fun i => observedReturn β s r₀ ξ i ω

/-- The law `P_β` of `(r₀, …, rₙ)` under feedback `β`. -/
def pathLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (β s : ℝ)
    (r₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) (n : ℕ) : Measure (Fin (n + 1) → ℝ) :=
  P.map (observedPath β s r₀ ξ n)

/-- The number of sign agreements `D_t = D_{t-1}`, `t = 1, …, n`, of a path. -/
def agreementCount (n : ℕ) (x : Fin (n + 1) → ℝ) : ℕ :=
  (Finset.univ.filter fun t : Fin n => sign (x t.succ) = sign (x t.castSucc)).card

/-- The sign-agreement statistic `q̂ = (1/n) ∑_{t=1}^n 1[D_t = D_{t-1}]`. -/
def agreementFraction (n : ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  (agreementCount n x : ℝ) / n

/-- The detector of Theorem 4.5: `+1` ("herding", positive feedback) iff
`q̂ > 1/2`, and `-1` (negative feedback) otherwise, ties included. -/
def agreementTest (n : ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  if 1 / 2 < agreementFraction n x then 1 else -1

/-- Misclassification probability of a (possibly randomized) test of the full
path under feedback `β`: `ψ x ∈ [0,1]` is the probability that the test outputs
"herding" (positive feedback) on the observation `x`. For `β > 0` an error is
the output "negative"; otherwise an error is the output "herding". -/
def testError {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (β s : ℝ)
    (r₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) (n : ℕ) (ψ : (Fin (n + 1) → ℝ) → ℝ) : ℝ :=
  if 0 < β then ∫ x, (1 - ψ x) ∂(pathLaw P β s r₀ ξ n)
  else ∫ x, ψ x ∂(pathLaw P β s r₀ ξ n)

end AutomatedMarketStress557.Persistence.Supplement


