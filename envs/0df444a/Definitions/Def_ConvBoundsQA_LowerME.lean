-- Prove2me | Definitions.Def_ConvBoundsQA_LowerME
-- name    : ConvBoundsQA_LowerME
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:03.081731+00:00
-- url     : https://prove2.me/theorems/ca02ae11-b817-455f-b5ca-db67e24fd9f2
-- title:
--   Lower and upper mutual exclusivity (Definition EC.1)
-- statement:
--   **Definition EC.1.** A random vector $(X_1,\dots,X_n)$ with $X_i\sim\mu_i$ is **lower mutually exclusive** if
--   $$
--   \mathbb P\bigl(X_i>q^+_0(\mu_i),\ X_j>q^+_0(\mu_j)\bigr)=0\quad\text{for all }i\ne j,
--   $$
--   and **upper mutually exclusive** if
--   $$
--   \mathbb P\bigl(X_i<q^-_1(\mu_i),\ X_j<q^-_1(\mu_j)\bigr)=0\quad\text{for all }i\ne j .
--   $$
--   That is, almost surely at most one component lies above its essential infimum (respectively below its essential supremum).
--
--   These dependence structures attain the convolution bounds in cases (iii) of Theorem 1 and (v) of Theorem 2.
--
--   **Formalization Note** The random vector is represented by its joint law $\pi$ on `Fin n → ℝ`; the requirement $X_i\sim\mu_i$ ($\pi\in\Gamma(\mu)$) is stated separately where the predicates are used. The comparisons with $q^+_0(\mu_i)\in[-\infty,\infty)$ and $q^-_1(\mu_i)\in(-\infty,\infty]$ are made in `EReal`.
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, Definition EC.1, p.41

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus

open MeasureTheory

namespace ConvBoundsQA

/-- Definition EC.1 (lower mutual exclusivity): a random vector `(X₁, …, Xₙ) ∼ π` with `Xᵢ ∼ μᵢ` is
lower mutually exclusive if `ℙ(Xᵢ > q⁺₀(μᵢ), Xⱼ > q⁺₀(μⱼ)) = 0` for all `i ≠ j`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, Definition EC.1, p.41).

**Formalization Note** The random vector is its joint law `π` on `Fin n → ℝ`; the requirement
`Xᵢ ∼ μᵢ` is `π ∈ Gam μ`, stated separately where the predicate is used. The comparison with
`q⁺₀(μᵢ) ∈ [−∞, ∞)` is made in `EReal`. -/
def LowerME {n : ℕ} (μ : Fin n → Measure ℝ) (π : Measure (Fin n → ℝ)) : Prop :=
  ∀ i j, i ≠ j →
    π {x | qPlus 0 (μ i) < ((x i : ℝ) : EReal) ∧ qPlus 0 (μ j) < ((x j : ℝ) : EReal)} = 0

/-- Definition EC.1 (upper mutual exclusivity): `ℙ(Xᵢ < q⁻₁(μᵢ), Xⱼ < q⁻₁(μⱼ)) = 0` for all
`i ≠ j` (Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, Definition EC.1, p.41).

**Formalization Note** As for `LowerME`; `q⁻₁(μᵢ) ∈ (−∞, ∞]` is compared in `EReal`. -/
def UpperME {n : ℕ} (μ : Fin n → Measure ℝ) (π : Measure (Fin n → ℝ)) : Prop :=
  ∀ i j, i ≠ j →
    π {x | ((x i : ℝ) : EReal) < qMinus 1 (μ i) ∧ ((x j : ℝ) : EReal) < qMinus 1 (μ j)} = 0

end ConvBoundsQA


