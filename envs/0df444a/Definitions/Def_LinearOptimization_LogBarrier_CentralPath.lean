-- Prove2me | Definitions.Def_LinearOptimization_LogBarrier_CentralPath
-- name    : LinearOptimization_LogBarrier_CentralPath
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-06T14:45:21.120193+00:00
-- url     : https://prove2.me/theorems/2d5e4f0c-0fbd-4b64-84d2-430508f2af6c
-- title:
--   Logarithmic barrier and the central path
-- statement:
--   **(Section 9.4, pp. 419-421)** For the standard form primal $\min \mathbf{c}'\mathbf{x}$ s.t. $A\mathbf{x} = \mathbf{b}$, $\mathbf{x} \ge \mathbf{0}$ and its dual $\max \mathbf{p}'\mathbf{b}$ s.t. $\mathbf{p}'A + \mathbf{s}' = \mathbf{c}'$, $\mathbf{s} \ge \mathbf{0}$: for $\mu > 0$ the barrier function
--
--   $$B_\mu(\mathbf{x}) = \mathbf{c}'\mathbf{x} - \mu\sum_{j=1}^n \log x_j$$
--
--   (defined to be infinity if $x_j \le 0$ for some $j$); the barrier problems (9.15) $\min B_\mu(\mathbf{x})$ s.t. $A\mathbf{x} = \mathbf{b}$ with optimal solution $\mathbf{x}(\mu)$, and the dual barrier problem (9.16) $\max \mathbf{p}'\mathbf{b} + \mu\sum_{j=1}^n \log s_j$ s.t. $\mathbf{p}'A + \mathbf{s}' = \mathbf{c}'$ with optimum $(\mathbf{p}(\mu), \mathbf{s}(\mu))$; as $\mu$ varies the minimizers $\mathbf{x}(\mu)$ form the *central path* (with $\lim_{\mu\to 0}\mathbf{x}(\mu)$ an optimal solution of the LP, and the analytic center at $\mu \to \infty$).
--
--   Central-path points are encoded by the Karush-Kuhn-Tucker conditions (9.17):
--
--   $$A\mathbf{x}(\mu) = \mathbf{b},\ \mathbf{x}(\mu) \ge \mathbf{0},\quad A'\mathbf{p}(\mu) + \mathbf{s}(\mu) = \mathbf{c},\ \mathbf{s}(\mu) \ge \mathbf{0},\quad X(\mu)S(\mu)\mathbf{e} = \mu\mathbf{e},$$
--
--   where $X(\mu) = \mathrm{diag}(x_1(\mu), \dots, x_n(\mu))$, $S(\mu) = \mathrm{diag}(s_1(\mu), \dots, s_n(\mu))$ and $\mathbf{e} = (1, \dots, 1)$.
--
--   Also the proximity measure of Eq. (9.20): $(\mathbf{x}, \mathbf{s})$ is $\beta$-close to the central path at $\mu$ when
--
--   $$\big\|\frac{1}{\mu}XS\mathbf{e} - \mathbf{e}\big\| \le \beta.$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Section 9.4, pp. 419-421 (barrier p. 419, problems (9.15)/(9.16) p. 420, KKT (9.17) p. 421, proximity (9.20) p. 425)

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Mul

/-!
Logarithmic barrier, barrier problems, central path, and the proximity
measure.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §9.4 (pp. 419–425), for the standard-form primal
`min c'x, Ax = b, x ≥ 0` and its dual `max p'b, p'A + s' = c', s ≥ 0`:

- **Barrier function (p. 419).** For `μ > 0`,
  `B_μ(x) = c'x − μ ∑ⱼ log xⱼ`, defined by the book to be `+∞` when some
  `xⱼ ≤ 0`. Encoding: `logBarrier` is ℝ-valued using `Real.log` (whose
  junk value on nonpositive arguments is `0`); every statement about the
  barrier carries an explicit `x > 0` restriction, so the `+∞` extension
  is never consulted (Phase B decision, per the mission design note).
- **Barrier problems (9.15)/(9.16) (p. 420).** Primal: `min B_μ(x)`
  subject to `Ax = b` (optimal solution `x(μ)`); dual:
  `max p'b + μ ∑ⱼ log sⱼ` subject to `p'A + s' = c'` (optimum
  `(p(μ), s(μ))`). As `μ` varies, the minimizers `x(μ)` trace the
  *central path* (`μ → 0`: an optimal solution of the LP; `μ → ∞`: the
  analytic center).
- **KKT conditions (9.17) (p. 421).** Central-path points are encoded
  predicatively (no argmin choice function — the book itself assumes the
  minimizers exist, p. 420): `Ax = b`, `x ≥ 0`, `A'p + s = c`, `s ≥ 0`,
  `XSe = μe` — coordinatewise `xⱼ sⱼ = μ` — where `X = diag(x)`,
  `S = diag(s)`, `e = (1, …, 1)`. Lemma 9.5 makes this equivalent to
  barrier optimality.
- **Proximity measure (9.20) (p. 425).** `(x, s)` is `β`-close to the
  central path at `μ` when `‖(1/μ) XSe − e‖ ≤ β`; the Euclidean norm is
  spelled out as `√(∑ⱼ (xⱼsⱼ/μ − 1)²)`.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, §9.4 (p. 419).** The logarithmic barrier function
`B_μ(x) = c'x − μ ∑ⱼ log xⱼ` (ℝ-valued; the book's `+∞` off the positive
orthant is handled by explicit `x > 0` restrictions in every statement). -/
noncomputable def logBarrier {n : ℕ} (c : Fin n → ℝ) (mu : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  c ⬝ᵥ x - mu * ∑ j, Real.log (x j)

/-- **Bertsimas & Tsitsiklis, Eq. (9.16) (p. 420).** The objective of the dual barrier problem:
`p'b + μ ∑ⱼ log sⱼ`, maximized subject to `A'p + s = c` (statements carry
`s > 0`). -/
noncomputable def dualLogBarrier {m n : ℕ} (b : Fin m → ℝ) (mu : ℝ)
    (p : Fin m → ℝ) (s : Fin n → ℝ) : ℝ :=
  p ⬝ᵥ b + mu * ∑ j, Real.log (s j)

/-- **Bertsimas & Tsitsiklis, Eq. (9.17) (p. 421).** `(x, p, s)` is the central-path point at
parameter `μ`, encoded by the KKT conditions of the barrier problems
(9.15)/(9.16): `Ax = b`, `x ≥ 0`, `A'p + s = c`, `s ≥ 0`, and
`XSe = μe`, i.e. `xⱼ sⱼ = μ` for every `j`. -/
def IsCentralPathPoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (mu : ℝ)
    (x : Fin n → ℝ) (p : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  A.mulVec x = b ∧ 0 ≤ x ∧ Aᵀ.mulVec p + s = c ∧ 0 ≤ s ∧
    ∀ j, x j * s j = mu

/-- **Bertsimas & Tsitsiklis, Eq. (9.20) (p. 425).** The proximity of `(x, s)` to the central
path at `μ`: the Euclidean norm `‖(1/μ) XSe − e‖ = √(∑ⱼ (xⱼsⱼ/μ − 1)²)`.
`(x, s)` is `β`-close to the central path when this is `≤ β`. -/
noncomputable def centralPathProximity {n : ℕ} (mu : ℝ)
    (x s : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ j, (x j * s j / mu - 1) ^ 2)

end LinearOptimization


