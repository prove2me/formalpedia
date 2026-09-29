-- Prove2me | Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk
-- name    : SupportVectorMachines_InfiniteSample_populationRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:52.267918+00:00
-- url     : https://prove2.me/theorems/aa8b326e-f7aa-4c20-b4c2-73493b01479f
-- title:
--   The L-risk and the empirical L-risk
-- statement:
--   Let $L : X \times Y \times \mathbb R \to [0,\infty)$ be a loss (Steinwart & Christmann,
--   *Support Vector Machines*, Springer 2008, Definition 2.2, p. 22). For a distribution $P$ on
--   $X \times \mathbb R$ and a measurable $f : X \to \mathbb R$, the **$L$-risk** of $f$ is
--
--   $$
--   R_{L,P}(f) := \int_{X \times Y} L\bigl(x,y,f(x)\bigr) \, dP(x,y),
--   $$
--
--   an integral that "always exists, although it is not necessarily finite" since $L \ge 0$. For
--   a finite sample $D := ((x_1,y_1),\dots,(x_n,y_n)) \in (X \times Y)^n$ with empirical measure
--   $\bar D := \tfrac1n \sum_{i=1}^n \delta_{(x_i,y_i)}$, the **empirical $L$-risk** of $f$ is
--
--   $$
--   R_{L,D}(f) := \frac1n \sum_{i=1}^n L\bigl(x_i,y_i,f(x_i)\bigr).
--   $$
--
--   These two risks are the objects this mission's regularized minimization problems
--   ($\lambda\|f\|_H^2 + R_{L,P}(f)$ and $\lambda\|f\|_H^2 + R_{L,D}(f)$) are built from.
--
--   **Formalization Note** `populationRisk` is represented as a lower Lebesgue integral
--   (`lintegral`) into $[0,\infty]$ (`ENNReal`) of the nonnegative integrand
--   $L(x,y,f(x))$: since $L \ge 0$, this integral is always well-defined, finite or not, with no
--   integrability hypothesis needed — exactly the book's own remark. `empiricalRisk` is the
--   manifestly finite average over `Fin n`. Restated locally rather than imported from the
--   `LossFunctions` chapter draft.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 22-23, Definition 2.2 and Eq. (2.1)

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- The **`L`-risk** of `f` with respect to a distribution `P` on `X × ℝ` (Definition 2.2, p. 22,
restated locally per Hard Rule 9), represented as the lower Lebesgue integral (`lintegral`) of
the nonnegative integrand `L(x,y,f(x))` into `ℝ≥0∞`, which — since `L ≥ 0` — always exists and
equals the book's `R_{L,P}(f) := ∫ L(x,y,f(x)) dP(x,y)` exactly, finite or not ("the above
integral … always exists, although it is not necessarily finite", p. 23), with no integrability
hypothesis needed. -/
noncomputable def populationRisk {X : Type*} [MeasurableSpace X] (L : Loss X)
    (P : Measure (X × ℝ)) (f : X → ℝ) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (L p.1 p.2 (f p.1)) ∂P

/-- The **empirical `L`-risk** of `f` with respect to a sample `D : Fin n → X × ℝ` (Definition
2.2, Eq. (2.1), p. 23): `R_{L,D}(f) := (1/n) ∑ᵢ L(xᵢ,yᵢ,f(xᵢ))`, the risk with respect to the
empirical measure `D̄ := (1/n) ∑ᵢ δ_{(xᵢ,yᵢ)}`. -/
noncomputable def empiricalRisk {X : Type*} (n : ℕ) (L : Loss X) (D : Fin n → X × ℝ)
    (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, L (D i).1 (D i).2 (f (D i).1)

end SupportVectorMachines.InfiniteSample


