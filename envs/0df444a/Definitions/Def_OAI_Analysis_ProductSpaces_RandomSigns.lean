-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
-- name    : OAI_Analysis_ProductSpaces_RandomSigns
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:47.41422+00:00
-- url     : https://prove2.me/theorems/d9131693-d8dc-42dc-91af-55746f40a720
-- title:
--   Euclidean size, Rademacher signs, and selective coordinate swaps
-- statement:
--   Let $\iota$ be a finite index set.
--
--   1. **Euclidean size.** For $a\in\mathbb R^\iota$, $\|a\|_2=\sqrt{\sum_{i\in\iota}a_i^2}$.
--
--   2. **Fair sign law.** $\beta$ is the Bernoulli probability measure on the two-point set $\{\mathrm{false},\mathrm{true}\}$ giving mass $\tfrac12$ to each point.
--
--   3. **Random sign.** $\sigma(\mathrm{true})=1$ and $\sigma(\mathrm{false})=-1$; under $\beta$ this is a Rademacher variable (mean $0$, variance $1$).
--
--   4. **Sign vector law.** $\beta^{\otimes\iota}$ is the product law on $\{\mathrm{false},\mathrm{true}\}^\iota$, i.e. independent fair signs indexed by $\iota$.
--
--   5. **Selective swap.** For a sign pattern $s\in\{\mathrm{false},\mathrm{true}\}^\iota$ and $(x,y)\in\mathbb R^\iota\times\mathbb R^\iota$, $\operatorname{swap}_s(x,y)=(x',y')$ where
--
--      $$(x'_i,y'_i)=\begin{cases}(x_i,y_i)&\text{if } s_i=\mathrm{true},\\ (y_i,x_i)&\text{if } s_i=\mathrm{false}.\end{cases}$$
--
--   These are the ingredients of the symmetrization argument for sums of independent random variables: exchanging $x_i$ and $y_i$ in a pair of independent copies does not change their joint law and multiplies $x_i-y_i$ by the sign $\sigma(s_i)$, which leads to the bound of $\mathbb E\big|\sum_i(X_i-\mathbb E X_i)\big|$ by twice the expected Euclidean size $\mathbb E\,\|(X_i)_{i\in\iota}\|_2$.
--
--   **Formalization Note** The Lean names are `euclidSize`, `signLaw` (`bernoulliMeasure false true` with parameter $1/2$), `randomSign`, `signVector` and `selectivelySwap`; the probability-measure instances for `signLaw` and `signVector` are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/RandomSigns.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/RandomSigns.lean by skeleton subtraction
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

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

/-- The ordinary Euclidean size of a finite real coefficient list. -/
def euclidSize {ι : Type uι} [Fintype ι] (a : ι → ℝ) : ℝ := Real.sqrt (∑ i, a i ^ 2)

def signLaw : Measure Bool := bernoulliMeasure false true ⟨1 / 2, by norm_num, by norm_num⟩
instance signLaw_probability : IsProbabilityMeasure signLaw := by unfold signLaw; infer_instance

def randomSign (b : Bool) : ℝ := if b then 1 else -1

section SignVector
variable {ι : Type uι} [Fintype ι]

def signVector : Measure (ι → Bool) := Measure.pi (fun _ => signLaw)
instance : IsProbabilityMeasure (signVector (ι := ι)) := by unfold signVector; infer_instance

end SignVector
end IndependentProducts

namespace IndependentProducts
section Symmetrization
variable {ι : Type uι} [Fintype ι]

def selectivelySwap (ε : ι → Bool) (z : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (fun i => if ε i then z.1 i else z.2 i, fun i => if ε i then z.2 i else z.1 i)

end Symmetrization
end IndependentProducts

end

end OAI


