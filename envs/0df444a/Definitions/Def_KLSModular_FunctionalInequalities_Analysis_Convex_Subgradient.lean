-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:50:56.749198+00:00
-- url     : https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7
-- title:
--   Subgradient image of a set
-- statement:
--   For $u:E\to\mathbb{R}$ on a real inner-product space and $S\subset E$, `subgradientImage u S` is the set of all $p\in E$ for which there exists $x\in S$ such that $u(x)+\langle p,y-x\rangle\le u(y)$ for every $y\in E$. Thus it is the image, over $S$, of the pointwise subdifferential; the module also contains differentiability, gradient-image, and injectivity auxiliary results for convex functions.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Convex.Deriv
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   import Mathlib.Analysis.Calculus.FDeriv.Symmetric
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   import Mathlib.Analysis.Calculus.Rademacher
--   import Mathlib.Analysis.Convex.Continuous
--   import Mathlib.Analysis.Convex.Measure
--   import Mathlib.Analysis.InnerProductSpace.Dual
--   import FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def subgradientImage {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
--       (S : Set E) : Set E :=
--     {p | ∃ x ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y}
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/LegendreVariation/Attainment`](https://prove2.me/theorems/8fff00c5-0262-4f99-9cab-27221baba48b).
--
--   Theorems in source order:
--
--   - [`contDiff_one_of_convexOn_of_differentiable`](https://prove2.me/theorems/16eb9c9c-a99f-4109-be05-1626be515a47)
--   - [`subgradient_mem_of_ae_gradient_mem`](https://prove2.me/theorems/6f655218-b30e-46bf-be4f-c590531dd524)
--   - [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e)
--   - [`ConvexOn.ae_differentiableAt_of_isOpen`](https://prove2.me/theorems/b601dd62-f116-4daf-a684-024dc3b2b841)
--   - [`hasFDerivAt_of_convexOn_of_unique_subgradient`](https://prove2.me/theorems/690ed838-72ba-4da4-b243-c587f4147186)
--   - [`support_of_max`](https://prove2.me/theorems/755fde81-3294-4941-84e6-f374b8550b71)
--   - [`subgradientImage_subset_of_le`](https://prove2.me/theorems/48dd6fd6-70dd-48c0-b715-081cfd732396)
--   - [`volume_subgradient_two_points_eq_zero`](https://prove2.me/theorems/097fae72-0e02-4d52-bbb1-f4883ba49bd8)
--   - [`eventually_abs_sub_quadratic_le_of_subgradient_expansion`](https://prove2.me/theorems/4ddfd262-d82d-4fdf-95dc-67ccaaffbd1b)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean) · `FunctionalInequalities.Analysis.Convex.Subgradient` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L983-L987 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient`; the repository is private at upload time).

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT12ASubgradientImageMonotone
open Set
open scoped RealInnerProductSpace
open scoped Topology
namespace FunctionalInequalities
namespace Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The **subgradient image** `∂u(S) = {p | ∃ x ∈ S, p is a subgradient of u at x}` (weak Letwin
route, routes/letwin-weak-definitions.md item 2). -/
def subgradientImage {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
    (S : Set E) : Set E :=
  {p | ∃ x ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y}
end InnerProduct
end Analysis
end FunctionalInequalities
end LT12ASubgradientImageMonotone


