-- Prove2me | Definitions.Def_DistTransform_Distortion_Supplement_Orders
-- name    : DistTransform_Distortion_Supplement_Orders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T13:05:40.922863+00:00
-- url     : https://prove2.me/theorems/29c895ea-e684-4216-bc45-647a5523cffe
-- title:
--   §4 — increasing convex order and scale-location, order and subadditivity properties
-- statement:
--   For bounded laws F and G, increasing convex order is the condition
--
--   $$
--   F\preceq_{\mathrm{icx}}G\quad\Longleftrightarrow\quad\int u\,dF\le\int u\,dG\quad\text{for every increasing convex }u:\mathbb R\to\mathbb R.
--   $$
--
--   A transform is scale-location invariant when it commutes with A_{a,b} for every a≥0 and every b∈ℝ, and the domain is closed under these maps. It is increasing-convex monotone when F≼icxG implies T(F)≼icxT(G) for every pair of bounded laws. It is increasing-convex subadditive when
--
--   $$
--   T(F\oplus G)\preceq_{\mathrm{icx}}T(F)\oplus T(G),\qquad F,G\in M_\infty.
--   $$
--
--   These are the transform properties occurring in Theorem 3. The published increasing convex order is applied to identity random variables under F and G. Its integrability guards remove no test on bounded laws, since real convex functions on ℝ are continuous and bounded on each compact interval. No commutation with arbitrary shape transforms or additivity is required.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), pp. 13–15, increasing convex order, Definition 3, and subadditivity clause (ii)

import Mathlib
import Definitions.Def_DistTransform_Distortion_Supplement_Algebra
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder

namespace DistTransform.Distortion.Supplement

open MeasureTheory

/-- §4, p. 13, specialized to laws. On bounded laws every real convex test
function is integrable, so the published integrability guards omit no test. -/
def IcxLE (F G : ProbabilityMeasure ℝ) : Prop :=
  StochasticOrders.MonotoneConvex.IcxOrder (F : Measure ℝ) (G : Measure ℝ) id id

/-- Definition 3: the scale can be zero; domain closure is retained. -/
def IsScaleLocationInvariant (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ b : ℝ,
    Set.MapsTo (affineLaw a b) Minf Minf ∧
      ∀ F ∈ Minf, T (affineLaw a b F) = affineLaw a b (T F)

/-- Definition 3, p. 13. -/
def IsIcxMonotone (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∀ F ∈ Minf, ∀ G ∈ Minf, IcxLE F G → IcxLE (T F) (T G)

/-- p. 15, clause (ii) of subadditivity. -/
def IsIcxSubadditive (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∀ F ∈ Minf, ∀ G ∈ Minf, IcxLE (T (comonoSum F G)) (comonoSum (T F) (T G))

end DistTransform.Distortion.Supplement


