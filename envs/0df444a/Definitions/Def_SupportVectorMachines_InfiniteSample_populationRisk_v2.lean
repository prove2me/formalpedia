-- Prove2me | Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk_v2
-- name    : SupportVectorMachines_InfiniteSample_populationRisk_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:35:28.15904+00:00
-- url     : https://prove2.me/theorems/be5c3e17-c42e-4ba8-aa0c-de203ec73ede
-- title:
--   $L$-risk and empirical $L$-risk (Definition 2.2, Eq. (2.1), Chapter 5 draft) — over bundled losses
-- statement:
--   The **$L$-risk** of $f$ with respect to a distribution $P$ on $X \times Y$ is $R_{L,P}(f) := \int L(x,y,f(x))\,dP(x,y) \in [0,\infty]$ (Definition 2.2, p. 22), and the **empirical $L$-risk** with respect to a sample $D = ((x_1,y_1),\dots,(x_n,y_n))$ is $R_{L,D}(f) := \frac1n \sum_{i=1}^n L(x_i,y_i,f(x_i))$ (Eq. (2.1)).
--
--   **Formalization Note.** Identical to the retired module except that $L$ ranges over the corrected bundled `Loss X`; with $L$ measurable and $f$ measurable the lower Lebesgue integral is the book's genuine integral (for a non-measurable integrand it was merely a lower integral, which is not convex in $f$ and broke Lemma 5.1 and Theorems 5.2, 5.6).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22-23, Definition 2.2 and Eq. (2.1)

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss_v2

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- The **`L`-risk** of `f` with respect to a distribution `P` on `X × ℝ` (Definition 2.2, p. 22,
restated locally per Hard Rule 9), represented as the Lebesgue integral (`lintegral`) of the
nonnegative integrand `L(x,y,f(x))` into `ℝ≥0∞`. Since `L` is measurable and nonnegative (bundled
in `Loss`), for every measurable `f` this is exactly the book's
`R_{L,P}(f) := ∫ L(x,y,f(x)) dP(x,y)`, finite or not ("the above integral … always exists,
although it is not necessarily finite", p. 23), with no integrability hypothesis needed. -/
noncomputable def populationRisk {X : Type*} [MeasurableSpace X] (L : Loss X)
    (P : Measure (X × ℝ)) (f : X → ℝ) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (L p.1 p.2 (f p.1)) ∂P

/-- The **empirical `L`-risk** of `f` with respect to a sample `D : Fin n → X × ℝ` (Definition
2.2, Eq. (2.1), p. 23): `R_{L,D}(f) := (1/n) ∑ᵢ L(xᵢ,yᵢ,f(xᵢ))`, the risk with respect to the
empirical measure `D̄ := (1/n) ∑ᵢ δ_{(xᵢ,yᵢ)}`. -/
noncomputable def empiricalRisk {X : Type*} [MeasurableSpace X] (n : ℕ) (L : Loss X)
    (D : Fin n → X × ℝ) (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, L (D i).1 (D i).2 (f (D i).1)

end SupportVectorMachines.InfiniteSample


