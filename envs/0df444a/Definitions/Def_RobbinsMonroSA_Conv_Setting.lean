-- Prove2me | Definitions.Def_RobbinsMonroSA_Conv_Setting
-- name    : RobbinsMonroSA_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:15:02.519851+00:00
-- url     : https://prove2.me/theorems/e305f0bc-9203-4d00-810d-bf588128fb56
-- title:
--   §2–§3, pp. 400–404 — the response kernel H, M(x) of (3), conditions (4), (5), (5′), (6), (26), the process (7)–(8), and b_n, d_n, e_n, A_n
-- statement:
--   This file fixes the objects of Robbins and Monro's stochastic approximation method.
--
--   **Responses.** To each level $x \in \mathbb R$ corresponds a random response $Y(x)$ with distribution function $H(y \mid x)$. The family $\{H(\cdot \mid x)\}_x$ is a Markov kernel $H$ from $\mathbb R$ to $\mathbb R$.
--
--   1. **Regression function (3).** $M(x) = \int_{-\infty}^{\infty} y \, dH(y \mid x)$, the expected response at level $x$.
--   2. **Bounded responses (4).** There is a constant $C > 0$ with $\Pr[|Y(x)| \le C] = \int_{-C}^{C} dH(y \mid x) = 1$ for all $x$.
--   3. **Condition (5).** $M(x) \le \alpha$ for $x < \theta$ and $M(x) \ge \alpha$ for $x > \theta$.
--   4. **Condition (5′).** For a given $\delta > 0$: $M(x) \le \alpha - \delta$ for $x < \theta$ and $M(x) \ge \alpha + \delta$ for $x > \theta$.
--   5. **Condition (6).** The step sizes $a_n$ are positive constants with $\sum_n a_n^2 < \infty$.
--   6. **Condition (26).** $$\sum_{n=2}^{\infty} \frac{a_n}{a_1 + \cdots + a_{n-1}} = \infty.$$
--   7. **Type $1/n$.** A sequence $\{a_n\}$ is *of type $1/n$* if it satisfies (6) and (26).
--   8. **The process (7)–(8).** On a probability space $(\Omega, P)$, $x_1$ is a constant and
--   $$x_{n+1} - x_n = a_n(\alpha - y_n), \qquad \Pr[y_n \le y \mid x_n] = H(y \mid x_n).$$
--   9. **The sequences (9), (12), (13), (21).**
--   $$b_n = E(x_n - \theta)^2,\quad d_n = E[(x_n - \theta)(M(x_n) - \alpha)],\quad e_n = E\Big[\int (y - \alpha)^2 \, dH(y \mid x_n)\Big],$$
--   $$A_n = |x_1 - \theta| + [C + |\alpha|](a_1 + \cdots + a_{n-1}).$$
--
--   These are the hypotheses and quantities of the paper's mean-square convergence theorems.
--
--   **Formalization Note** Indices are 0-based: Lean's `x 0`, `a 0`, `y 0` are the paper's $x_1, a_1, y_1$, and Lean index $n$ is the paper's $n+1$. Thus `bigA x1 θ C α a n` $= |x_1 - \theta| + (C + |\alpha|)\sum_{i<n} a_i$ is the paper's $A_{n+1}$, the bound for Lean's `x n`; (26) is the divergence of the partial sums of `a (n+1) / (a 0 + ⋯ + a n)`. "$=\infty$" for a nonnegative series is stated as divergence of its partial sums to $+\infty$. $H$ is a `Kernel ℝ ℝ`; theorems assume `IsMarkovKernel H` (each $H(\cdot\mid x)$ is a probability distribution and $x \mapsto H(\cdot\mid x)$ is measurable, implicit in the paper's integrals over $x$). Condition (8) is stated as the joint law: the law of $(x_n, y_n)$ equals the law of $x_n$ composed with $H$, i.e. $P(x_n \in A, y_n \in B) = \int_A H(B \mid x)\, dP_{x_n}(x)$; (7) holds surely, $x_1$ is constant, and $x_n, y_n$ are measurable. No Markov property beyond (8) is assumed (the paper's proofs use only (8)). (0 < A in (6) is automatic from $a_1 > 0$.)
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), pp. 400–404, (3)–(9), (12), (13), (21), (5′), (26), definition of type 1/n (p. 404)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- (3), p. 400: the regression function `M(x) = ∫ y dH(y | x)`, the expected value of the
response `Y(x)` whose law is `H x`. -/
noncomputable def regressionFn (H : Kernel ℝ ℝ) (x : ℝ) : ℝ :=
  ∫ y, y ∂(H x)

/-- (4), p. 401: there is a positive constant `C` with `Pr[|Y(x)| ≤ C] = 1` for all `x`. -/
def BoundedResponse (H : Kernel ℝ ℝ) (C : ℝ) : Prop :=
  0 < C ∧ ∀ x, H x (Set.Icc (-C) C) = 1

/-- (5), p. 401: `M(x) ≤ α` for `x < θ` and `M(x) ≥ α` for `x > θ`. -/
def CrossesAt (M : ℝ → ℝ) (α θ : ℝ) : Prop :=
  (∀ x, x < θ → M x ≤ α) ∧ (∀ x, θ < x → α ≤ M x)

/-- (5′), p. 404: for the given `δ > 0`, `M(x) ≤ α - δ` for `x < θ` and `M(x) ≥ α + δ` for
`x > θ`. -/
def CrossesWithGap (M : ℝ → ℝ) (α θ δ : ℝ) : Prop :=
  0 < δ ∧ (∀ x, x < θ → M x ≤ α - δ) ∧ (∀ x, θ < x → α + δ ≤ M x)

/-- (6), p. 401: the step sizes are positive constants with `Σ aₙ² < ∞`.
(Lean index `n` is the paper's index `n + 1`.) -/
def StepCond6 (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 < a n) ∧ Summable (fun n => a n ^ 2)

/-- (26), p. 403: `Σ_{n=2}^∞ aₙ / (a₁ + ⋯ + a_{n-1}) = ∞`, as divergence of the partial sums.
In 0-based indexing the paper's term `n ≥ 2` is `a m / (a 0 + ⋯ + a (m - 1))` with `m = n - 1 ≥ 1`. -/
def StepCond26 (a : ℕ → ℝ) : Prop :=
  Tendsto (fun N => ∑ n ∈ Finset.range N, a (n + 1) / ∑ i ∈ Finset.range (n + 1), a i)
    atTop atTop

/-- p. 404: a sequence of type `1/n` is one satisfying (6) and (26). -/
def IsTypeOneOverN (a : ℕ → ℝ) : Prop :=
  StepCond6 a ∧ StepCond26 a

/-- The Robbins–Monro process (7)–(8), p. 401, on the probability space `(Ω, P)`:
`x 0 = x₁` is a constant, `x (n+1) - x n = a n * (α - y n)` surely, and the conditional law of
`y n` given `x n` is `H(· | x n)`, expressed as the joint law of `(x n, y n)` being
`(law of x n) ⊗ₘ H`. -/
structure IsRMProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : Kernel ℝ ℝ)
    (a : ℕ → ℝ) (α x1 : ℝ) (x y : ℕ → Ω → ℝ) : Prop where
  init : ∀ ω, x 0 ω = x1
  step : ∀ n ω, x (n + 1) ω - x n ω = a n * (α - y n ω)
  measurable_x : ∀ n, Measurable (x n)
  measurable_y : ∀ n, Measurable (y n)
  law : ∀ n, P.map (fun ω => (x n ω, y n ω)) = (P.map (x n)) ⊗ₘ H

/-- (9), p. 401: `bₙ = E(xₙ - θ)²`. -/
noncomputable def msd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x : ℕ → Ω → ℝ)
    (θ : ℝ) (n : ℕ) : ℝ :=
  ∫ ω, (x n ω - θ) ^ 2 ∂P

/-- (12), p. 402: `dₙ = E[(xₙ - θ)(M(xₙ) - α)]`. -/
noncomputable def dSeq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : Kernel ℝ ℝ)
    (α θ : ℝ) (x : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, (x n ω - θ) * (regressionFn H (x n ω) - α) ∂P

/-- (13), p. 402: `eₙ = E[∫ (y - α)² dH(y | xₙ)]`. -/
noncomputable def eSeq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : Kernel ℝ ℝ)
    (α : ℝ) (x : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, ∫ y, (y - α) ^ 2 ∂(H (x n ω)) ∂P

/-- (21), p. 403: `Aₙ = |x₁ - θ| + [C + |α|](a₁ + ⋯ + a_{n-1})`. In 0-based indexing
`bigA x1 θ C α a n = |x1 - θ| + (C + |α|) * (a 0 + ⋯ + a (n - 1))` is the paper's `A_{n+1}`,
the bound for Lean's `x n`. -/
noncomputable def bigA (x1 θ C α : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  |x1 - θ| + (C + |α|) * ∑ i ∈ Finset.range n, a i

end RobbinsMonroSA.Conv


