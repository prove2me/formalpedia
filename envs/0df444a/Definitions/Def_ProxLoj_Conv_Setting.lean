-- Prove2me | Definitions.Def_ProxLoj_Conv_Setting
-- name    : ProxLoj_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:44.139499+00:00
-- url     : https://prove2.me/theorems/ec9bbdb3-8a58-46e7-a09a-e412236671eb
-- title:
--   §2.2–§3.1, pp. 3–4 — proper lsc f, (H1), (H2), the proximal run (2), step bounds, the Łojasiewicz inequality (5) with 0⁰ = 0, (H3), Łojasiewicz exponent
-- statement:
--   This file fixes the setting of Attouch and Bolte's analysis of the proximal algorithm. Points live in $\mathbb R^n$ with the Euclidean norm $|\cdot|$, and $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is an extended-real-valued function.
--
--   1. **Properness.** $f$ is *proper* if it never takes the value $-\infty$ and is finite at some point. Its domain is $\operatorname{dom} f=\{x : f(x)<+\infty\}$.
--   2. **(H1)** $\inf_{\mathbb R^n} f>-\infty$: there is a real $m$ with $m\le f(x)$ for all $x$.
--   3. **(H2)** The restriction of $f$ to $\operatorname{dom} f$ is continuous.
--   4. **Step sizes.** Fixed parameters $0<\lambda_-<\lambda_+<+\infty$, and a sequence $(\lambda_k)$ with $\lambda_k\in(\lambda_-,\lambda_+)$ for every $k$.
--   5. **Proximal run.** A sequence $(x^k)_{k\in\mathbb N}$ *complies with (2)* if, for every $k$,
--   $$x^{k+1}\in\operatorname{argmin}\Big\{f(u)+\frac{1}{2\lambda_k}|u-x^k|^2 : u\in\mathbb R^n\Big\},\qquad(2)$$
--   that is, $f(x^{k+1})+\frac{1}{2\lambda_k}|x^{k+1}-x^k|^2\le f(u)+\frac{1}{2\lambda_k}|u-x^k|^2$ for all $u$. The starting point $x^0$ is arbitrary, and any minimizer may be selected at each step.
--   6. **Łojasiewicz power.** For $\theta\ge0$ and $s\ge 0$, $s^\theta$ is the usual power, with the convention $0^0=0$ of Remark 4: for $\theta=0$, $s^0=1$ if $s\ne0$ and $0^0=0$.
--   7. **The Łojasiewicz inequality (5)** at $\hat x$ with constants $C,\varepsilon$ and exponent $\theta$:
--   $$|f(x)-f(\hat x)|^\theta\le C|x^*|\qquad\forall x\in B(\hat x,\varepsilon),\ \forall x^*\in\partial f(x),\qquad(5)$$
--   where $B(\hat x,\varepsilon)$ is the open ball and $\partial f$ the limiting subdifferential.
--   8. **(H3), the Łojasiewicz property.** For every limiting-critical point $\hat x$ (that is, $0\in\partial f(\hat x)$) there exist $C,\varepsilon>0$ and $\theta\in[0,1)$ such that (5) holds.
--   9. **Łojasiewicz exponent.** A number $\theta\in[0,1)$ is a Łojasiewicz exponent of a point $a$ if (5) holds at $a$ with exponent $\theta$ for some $C,\varepsilon>0$.
--   10. **Limit points.** $\omega(x^0)$ is the set of limit (cluster) points of the sequence $(x^k)$.
--
--   These objects are the hypotheses and the data of every theorem of the mission.
--
--   **Formalization Note** $\mathbb R\cup\{+\infty\}$ is `EReal`, with properness excluding $-\infty$. The limiting subdifferential and $\operatorname{crit} f$ are the published `NonconvexSplitting.Shared.LimitingSubdiff` and `NonsmoothLojasiewicz.Continuous.crit`. In (5) the values $f(x)$, $f(\hat x)$ are converted to reals; this is faithful because $x^*\in\partial f(x)$ forces $f(x)<+\infty$ and properness excludes $-\infty$. The power is `lojPow θ s := if s = 0 then 0 else s ^ θ`, never bare `Real.rpow` (whose $0^0=1$ would contradict Remark 4). The run (2) is a predicate on a sequence, not a proximal map, so no uniqueness of minimizers is assumed.
-- source:
--   Attouch & Bolte, On the convergence of the proximal algorithm for nonsmooth functions involving analytic features, author's version hal-00803898v1, pp. 3–4, 6, (2), (H1), (H2), (H3), (5), Remark 4, step bounds λ_k ∈ (λ₋, λ₊) on p. 3, Łojasiewicz exponent on p. 6

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope

open Filter Topology

namespace ProxLoj.Conv

open NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

/-- `f : ℝⁿ → ℝ ∪ {+∞}` is proper: it never takes the value `-∞` and is finite somewhere. -/
def IsProper {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤

/-- (H1), p. 3: `inf_{ℝⁿ} f > -∞`. -/
def H1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  ∃ m : ℝ, ∀ x, (m : EReal) ≤ f x

/-- (H2), p. 3: the restriction of `f` to its domain `dom f = {x | f x ≠ +∞}` is continuous. -/
def H2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  ContinuousOn f {x | f x ≠ ⊤}

/-- The step sizes, p. 3: `0 < λ₋ < λ₊ < +∞` and `λ_k ∈ (λ₋, λ₊)` for all `k`. -/
def StepBounds (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) : Prop :=
  0 < lamMinus ∧ lamMinus < lamPlus ∧ ∀ k, lam k ∈ Set.Ioo lamMinus lamPlus

/-- The proximal algorithm (2), p. 3, in selection form: for every `k`, `x (k+1)` is *some*
minimizer of `u ↦ f u + ‖u - x k‖² / (2 λ_k)` over `ℝⁿ`. The starting point `x 0` is arbitrary. -/
def IsProxRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (lam : ℕ → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, ∀ u, f (x (k + 1)) + ((‖x (k + 1) - x k‖ ^ 2 / (2 * lam k) : ℝ) : EReal) ≤
    f u + ((‖u - x k‖ ^ 2 / (2 * lam k) : ℝ) : EReal)

/-- The power `s ^ θ` with the convention `0 ^ 0 = 0` of Remark 4, p. 4. -/
noncomputable def lojPow (θ s : ℝ) : ℝ :=
  if s = 0 then 0 else s ^ θ

/-- The Łojasiewicz inequality (5), p. 4, at `x̂` with constants `C, ε` and exponent `θ`:
`|f(x) - f(x̂)|^θ ≤ C ‖x*‖` for all `x ∈ B(x̂, ε)` and all `x* ∈ ∂f(x)`. -/
def LojIneqAB {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (xh : EuclideanSpace ℝ (Fin n))
    (θ C ε : ℝ) : Prop :=
  ∀ x ∈ Metric.ball xh ε, ∀ v ∈ LimitingSubdiff f x,
    lojPow θ |(f x).toReal - (f xh).toReal| ≤ C * ‖v‖

/-- (H3), p. 4: the Łojasiewicz property. At every limiting-critical point `x̂` there are
`C, ε > 0` and `θ ∈ [0, 1)` such that (5) holds. -/
def HasLojProperty {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  ∀ xh ∈ crit f, ∃ C ε θ : ℝ, 0 < C ∧ 0 < ε ∧ 0 ≤ θ ∧ θ < 1 ∧ LojIneqAB f xh θ C ε

/-- p. 6: `θ ∈ [0, 1)` is a Łojasiewicz exponent of `a` if (5) holds at `a` with exponent `θ`
for some `C, ε > 0`. -/
def IsLojExponentAB {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (a : EuclideanSpace ℝ (Fin n)) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ θ < 1 ∧ ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ LojIneqAB f a θ C ε

/-- `ω(x⁰)`, the set of limit points (cluster points) of the sequence `x`. -/
def limitSet {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | MapClusterPt y atTop x}

end ProxLoj.Conv


