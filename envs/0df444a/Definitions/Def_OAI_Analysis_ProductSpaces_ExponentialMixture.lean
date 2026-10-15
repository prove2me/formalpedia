-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialMixture
-- name    : OAI_Analysis_ProductSpaces_ExponentialMixture
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:48:22.965127+00:00
-- url     : https://prove2.me/theorems/99e06ec3-4370-4ba2-8780-8cd304e62b13
-- title:
--   Exponential vectors and the Gaussian scale-mixture form of weighted Laplace sums
-- statement:
--   Throughout, $\iota$ is a finite index set and $\mathrm{Exp}(1)$ is the standard exponential law on $\mathbb{R}$ (density $e^{-w}$ for $w\ge0$). The file defines the following objects.
--
--   1. **Exponential vector law.** $\mathrm{Exp}_\iota=\mathrm{Exp}(1)^{\otimes\iota}$, the product measure on $\mathbb{R}^\iota$, i.e. the law of a vector $(U_i)_{i\in\iota}$ of independent standard exponential variables. It is registered as a probability measure.
--
--   2. **Exponential difference.** For a coefficient vector $a\in\mathbb{R}^\iota$ and a pair $(x,y)\in\mathbb{R}^\iota\times\mathbb{R}^\iota$,
--
--      $$D_a(x,y)=\sum_{i\in\iota}a_i\,(x_i-y_i).$$
--
--   3. **Mixing variance.** For $a\in\mathbb{R}^\iota$ and $u\in\mathbb{R}^\iota$,
--
--      $$V_a(u)=2\sum_{i\in\iota}a_i^2\,\max(u_i,0).$$
--
--   4. **Exponential mixture.** For $a\in\mathbb{R}^\iota$ and $(u,g)\in\mathbb{R}^\iota\times\mathbb{R}$,
--
--      $$M_a(u,g)=\sqrt{V_a(u)}\;g .$$
--
--   These definitions encode the classical fact that the difference of two independent $\mathrm{Exp}(1)$ variables has a Laplace law, and that the Laplace law is a Gaussian scale mixture. The intended identity, proved separately, is that the image of $\mathrm{Exp}_\iota\otimes\mathrm{Exp}_\iota$ under $D_a$ equals the image of $\mathrm{Exp}_\iota\otimes N(0,1)$ under $M_a$: in other words $\sum_ia_i(X_i-Y_i)$ has the same law as $\sqrt{2\sum_ia_i^2U_i}\,G$ with $G$ a standard Gaussian independent of $U$. This reduces scalar estimates in the exponential case to Gaussian estimates with a random variance.
--
--   **Formalization Note** The Lean names are `exponentialVector`, `exponentialDifference`, `exponentialVariance` and `exponentialMixture`; an unnamed instance makes `exponentialVector` a probability measure. The truncation $\max(u_i,0)$ makes $V_a$ nonnegative for every $u$, so that the real square root is the genuine one; it changes nothing almost surely, since exponential coordinates are nonnegative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ExponentialMixture.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ExponentialMixture.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients
import Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialLaw

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section ExponentialFinite
variable {ι : Type uι} [Fintype ι]

def exponentialVector : Measure (ι → ℝ) := Measure.pi (fun _ => exponentialLaw)
instance : IsProbabilityMeasure (exponentialVector (ι := ι)) := by
  unfold exponentialVector
  infer_instance

def exponentialDifference (a : ι → ℝ) (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  ∑ i, a i * (z.1 i - z.2 i)

def exponentialVariance (a : ι → ℝ) (u : ι → ℝ) : ℝ :=
  2 * ∑ i, a i ^ 2 * max (u i) 0

def exponentialMixture (a : ι → ℝ) (z : (ι → ℝ) × ℝ) : ℝ :=
  Real.sqrt (exponentialVariance a z.1) * z.2

end ExponentialFinite
end IndependentProducts

end

end OAI


