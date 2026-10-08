-- Prove2me | Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
-- name    : RadGauss_Discrepancy_maxDiscrepancy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:08:26.616792+00:00
-- url     : https://prove2.me/theorems/0ec797cd-aec4-4f9e-ae14-c3207866ee90
-- title:
--   Definition 2 — the maximum discrepancy D̂_n(F) and its expectation D_n(F)
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\mathcal X$, let $F$ be a class of functions $\mathcal X \to \mathbb R$, and let the sample size be even, $n = 2m$. For a sample $x = (x_1,\dots,x_n)$ the **maximum discrepancy** of $F$ is
--
--   $$
--   \hat D_n(F)(x) = \sup_{f\in F}\left(\frac{2}{n}\sum_{i=1}^{n/2} f(x_i) - \frac{2}{n}\sum_{i=n/2+1}^{n} f(x_i)\right),
--   $$
--
--   and the **expected maximum discrepancy** is $D_n(F) = \mathbf E\,\hat D_n(F)(X_1,\dots,X_n)$ for $X_1,\dots,X_n$ i.i.d. from $\mu$.
--
--   $\hat D_n(F)$ quantifies how much the behaviour of the class on the first half of the sample can differ from its behaviour on the second half. There is no absolute value: for a class not closed under negation the maximum discrepancy can be negative.
--
--   **Formalization Note** The sample size is written $n = 2m$ because the half sums need $n$ even; coordinates are indexed by `Fin (2m)`, the first half being indices $0,\dots,m-1$. $\hat D_n(F)$ is a real supremum over the subtype $F$ (equal to the paper's supremum when $F$ is nonempty and bounded above, which the theorems assume), and $D_n(F)$ is a Bochner integral; the theorems carry the measurability hypotheses that make it a genuine expectation.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 464 (PDF p. 2), Definition 2

import Mathlib

open MeasureTheory

namespace RadGauss.Discrepancy

/-- The half-sample difference `(2/n) Σ_{i=1}^{n/2} f(x_i) − (2/n) Σ_{i=n/2+1}^{n} f(x_i)` of a
function `f` on a sample `x = (x_1, …, x_n)` of even size `n = 2m` (Definition 2, p. 464).
Coordinates are indexed by `Fin (2 * m)`: the first half is `i.val < m`, the second half
`m ≤ i.val`. -/
noncomputable def halfDiff {X : Type*} (m : ℕ) (f : X → ℝ) (x : Fin (2 * m) → X) : ℝ :=
  (2 / ((2 * m : ℕ) : ℝ)) * ∑ i : Fin (2 * m), (if i.val < m then f (x i) else 0) -
    (2 / ((2 * m : ℕ) : ℝ)) * ∑ i : Fin (2 * m), (if i.val < m then 0 else f (x i))

/-- **Definition 2** (p. 464), the maximum discrepancy
`D̂_n(F) = sup_{f ∈ F} ((2/n) Σ_{i=1}^{n/2} f(X_i) − (2/n) Σ_{i=n/2+1}^{n} f(X_i))` of a class
`F` at a sample of even size `n = 2m`. There is no absolute value (the page uses parentheses), so
the value is a signed real. A real supremum over the subtype `F`: it is the paper's supremum when
`F` is nonempty and the family is bounded above (e.g. `F` maps into `[−1, 1]`). -/
noncomputable def empiricalMaxDiscrepancy {X : Type*} (m : ℕ) (F : Set (X → ℝ))
    (x : Fin (2 * m) → X) : ℝ :=
  ⨆ f : F, halfDiff m (f : X → ℝ) x

/-- **Definition 2** (p. 464), the expected maximum discrepancy `D_n(F) = E D̂_n(F)` for
`n = 2m`, the (Bochner) expectation over an i.i.d. sample `X_1, …, X_n` drawn from `μ`. -/
noncomputable def expectedMaxDiscrepancy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (m : ℕ) (F : Set (X → ℝ)) : ℝ :=
  ∫ x, empiricalMaxDiscrepancy m F x ∂(Measure.pi fun _ : Fin (2 * m) => μ)

end RadGauss.Discrepancy


