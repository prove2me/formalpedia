-- Prove2me | Definitions.Def_ArmijoGrad_Conv_Setting
-- name    : ArmijoGrad_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:45:45.350715+00:00
-- url     : https://prove2.me/theorems/08d5e4f5-b034-4b61-9c44-550d987d7761
-- title:
--   §1–§2, pp. 1–2 — level set S(x₀), Conditions I–IV, the set S*(x, δ) of (1), and the runs of Corollaries 1–2
-- statement:
--   This file fixes the objects of Armijo's 1966 paper. Throughout, $E^n$ is real Euclidean $n$-space with the Euclidean norm $|\cdot|$, $f : E^n \to \mathbb{R}$, and $\nabla f(x)$ is the gradient of $f$ at $x$.
--
--   1. **Level set.** For $x_0 \in E^n$, $S(x_0) = \{x : f(x) \le f(x_0)\}$.
--   2. **$C^1$ on a set.** $f \in C^1$ on $s$ means: $f$ is differentiable at every point of $s$, and $\nabla f$ is continuous on $s$.
--   3. **Condition I** (for a point $x^*$): $x^*$ is the unique point with $f(x^*) = \inf_{x \in E^n} f(x)$.
--   4. **Condition II at $x_0$** (for $x^*$): $f \in C^1$ on $S(x_0)$, and for $x \in S(x_0)$, $\nabla f(x) = 0$ if and only if $x = x^*$.
--   5. **Condition III at $x_0$** (with constant $K$): $K > 0$, $f \in C^1$ on $S(x_0)$, and
--   $$|\nabla f(y) - \nabla f(x)| \le K\,|y - x| \qquad \text{for all } x, y \in S(x_0).$$
--   6. **Condition IV at $x_0$** (for $x^*$): $f \in C^1$ on $S(x_0)$, $f(x^*) = \inf_{E^n} f$, and for every $r > 0$,
--   $$m(r) = \inf_{x \in S_r(x_0)} |\nabla f(x)| > 0, \qquad S_r(x_0) = \{x \in S(x_0) : |x - x^*| \ge r\},$$
--   with the convention $m(r) = \infty$ when $S_r(x_0)$ is empty.
--   7. **The set $S^*(x, \delta)$ of display (1):**
--   $$S^*(x,\delta) = \{x_\lambda : x_\lambda = x - \lambda \nabla f(x),\ \lambda > 0,\ f(x_\lambda) - f(x) \le -\delta\,|\nabla f(x)|^2\}.$$
--   8. **Steepest descent run (Corollary 1):** a sequence with $x_{k+1} = x_k - \frac{1}{2K}\nabla f(x_k)$ for $k = 0, 1, 2, \dots$
--   9. **Step sizes and test (2) (Corollary 2):** for $\alpha > 0$, $\alpha_m = \alpha / 2^{m-1}$ ($m = 1, 2, \dots$), and $m$ passes test (2) at $y$ when
--   $$f(y - \alpha_m \nabla f(y)) - f(y) \le -\tfrac12 \alpha_m |\nabla f(y)|^2.$$
--   10. **Modified steepest descent run (Corollary 2):** $x_{k+1} = x_k - \alpha_{m_k}\nabla f(x_k)$, where $m_k$ is the smallest positive integer passing test (2) at $x_k$.
--
--   These are the hypotheses and algorithms of the convergence theorem and its two corollaries.
--
--   **Formalization Note** $E^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla f$ is Mathlib's `gradient f` (which is $0$ where $f$ is not differentiable; every statement evaluates it only on $S(x_0)$, where the conditions give differentiability). Conditions III and IV take $K$ and $x^*$ as explicit parameters. "$m(r) > 0$" is encoded as "there is $m > 0$ with $m \le |\nabla f(x)|$ for all $x \in S_r(x_0)$", which is exactly $m(r) > 0$ including the convention $m(r) = \infty$ on an empty set; no real infimum is used. $\alpha_m$ is only used with $m \ge 1$, and every quantifier over $m$ carries $1 \le m$.
-- source:
--   Armijo, Minimization of functions having Lipschitz continuous first partial derivatives, Pacific J. Math. 16 (1966), pp. 1–2, §1 Principal conditions, (1), Corollaries 1–2 and (2)

import Mathlib

namespace ArmijoGrad.Conv

/-- The level set `S(x₀) = {x : f(x) ≤ f(x₀)}` (§1, p. 1). -/
def levelSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | f x ≤ f x0}

/-- "`f ∈ C¹` on `s`": `f` is (Fréchet) differentiable on `Eⁿ` at every point of `s`, and its
gradient `∇f` is continuous on `s`. -/
def IsC1On {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    Prop :=
  (∀ x ∈ s, DifferentiableAt ℝ f x) ∧ ContinuousOn (gradient f) s

/-- Condition I (§1, p. 1): `x*` is the unique point with `f(x*) = inf_{Eⁿ} f`. -/
def ConditionI {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  (∀ y, f xstar ≤ f y) ∧ ∀ z, (∀ y, f z ≤ f y) → z = xstar

/-- Condition II at `x₀` (§1, p. 1): `f ∈ C¹` on `S(x₀)`, and for `x ∈ S(x₀)`,
`∇f(x) = 0` iff `x = x*`. -/
def ConditionII {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 xstar : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsC1On f (levelSet f x0) ∧ ∀ x ∈ levelSet f x0, (gradient f x = 0 ↔ x = xstar)

/-- Condition III at `x₀` (§1, p. 1): `f ∈ C¹` on `S(x₀)` and `∇f` is Lipschitz continuous on
`S(x₀)` with Lipschitz constant `K > 0`. -/
def ConditionIII {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n))
    (K : ℝ) : Prop :=
  0 < K ∧ IsC1On f (levelSet f x0) ∧
    ∀ x ∈ levelSet f x0, ∀ y ∈ levelSet f x0, ‖gradient f y - gradient f x‖ ≤ K * ‖y - x‖

/-- Condition IV at `x₀` (§1, p. 1), for the minimizer `x*`: `f ∈ C¹` on `S(x₀)`, `x*` minimizes
`f` over `Eⁿ`, and for every `r > 0`, `m(r) = inf {‖∇f(x)‖ : x ∈ S(x₀), ‖x - x*‖ ≥ r} > 0`
(with `m(r) = ∞` when that set is void), i.e. `‖∇f‖` has a positive lower bound on it. -/
def ConditionIV {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 xstar : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsC1On f (levelSet f x0) ∧ (∀ y, f xstar ≤ f y) ∧
    ∀ r : ℝ, 0 < r → ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ levelSet f x0, r ≤ ‖x - xstar‖ → m ≤ ‖gradient f x‖

/-- The set `S*(x, δ)` of display (1) (§2, p. 1):
`{x_λ : x_λ = x − λ∇f(x), λ > 0, f(x_λ) − f(x) ≤ −δ|∇f(x)|²}`. -/
def sdSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ t : ℝ, 0 < t ∧ y = x - t • gradient f x ∧ f y - f x ≤ -δ * ‖gradient f x‖ ^ 2}

/-- A run of the steepest descent algorithm of Corollary 1 (§2, p. 2):
`x_{k+1} = x_k − (1/2K)∇f(x_k)` for `k = 0, 1, 2, …`. -/
def IsSteepestDescentRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, x (k + 1) = x k - (1 / (2 * K)) • gradient f (x k)

/-- The step sizes `α_m = α / 2^{m−1}` of Corollary 2 (§2, p. 2); used only for `m ≥ 1`. -/
noncomputable def alphaSeq (α : ℝ) (m : ℕ) : ℝ :=
  α / 2 ^ (m - 1)

/-- Test (2) of Corollary 2 at the point `y` with index `m`:
`f(y − α_m∇f(y)) − f(y) ≤ −(1/2) α_m |∇f(y)|²`. -/
def armijoTest {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (m : ℕ) : Prop :=
  f (y - alphaSeq α m • gradient f y) - f y ≤ -(1 / 2) * alphaSeq α m * ‖gradient f y‖ ^ 2

/-- A run of the modified steepest descent algorithm of Corollary 2 (§2, p. 2):
`x_{k+1} = x_k − α_{m_k}∇f(x_k)`, where `m_k` is the smallest positive integer satisfying (2). -/
def IsModifiedSteepestDescentRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, ∃ m : ℕ, 1 ≤ m ∧ armijoTest f α (x k) m ∧
    (∀ j : ℕ, 1 ≤ j → j < m → ¬ armijoTest f α (x k) j) ∧
    x (k + 1) = x k - alphaSeq α m • gradient f (x k)

end ArmijoGrad.Conv


