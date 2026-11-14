-- Prove2me | Definitions.Def_NarrowDNF_Influence
-- name    : NarrowDNF_Influence
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:43.576529+00:00
-- url     : https://prove2.me/theorems/8a77d63a-88b0-45ca-b017-27b59f9cf323
-- title:
--   Bernoulli variance and independent-coordinate resampling influence
-- statement:
--   Encode a Boolean value by $\operatorname{val}(\mathrm{false})=0$ and $\operatorname{val}(\mathrm{true})=1$. A two-point real fiber with values $a,b$ has mean $(1-p)a+pb$ and variance equal to the weighted mean squared deviation from that mean. The analogous Boolean fiber-resampling quantity is the expected disagreement of two independent Bernoulli choices of the fiber bit.
--
--   For a Boolean function $f$ on a finite cube, define
--   $$I_i^p(f)=\mathbb E_{X\sim\mu_p}\!\left[(1-p)\mathbf1_{\{f(X)\ne f(X^{i\leftarrow0})\}}+p\mathbf1_{\{f(X)\ne f(X^{i\leftarrow1})\}}\right],\qquad I_p(f)=\sum_i I_i^p(f).$$
--   This replaces coordinate $i$ by a fresh independent Bernoulli bit. A pivotal Boolean fiber therefore has resampling disagreement $2p(1-p)$; the normalization differs from deterministic bit flipping. For a real-valued function, the bundle also defines its global variance and its coordinate variance by averaging the two-point fiber variance over the remaining coordinates. Algebraic expressions are defined for real $p$; their probability interpretation uses $0\le p\le1$.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Influence.lean#L47-L51
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Influence.lean#L75-L78
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Influence.lean#L19-L20
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Influence.lean#L134-L139
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Influence.lean#L22-L23
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Influence.lean#L157-L161
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Influence.lean#L25-L27
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Influence.lean#L174-L176

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.Influence
end NarrowDNF.Influence


/-!
# Finite Bernoulli variance and resampling influence

The one-coordinate identities in this file use the paper's resampling
normalization: a pivotal Boolean fiber has influence `2 * p * (1 - p)`.
The endpoints `p = 0` and `p = 1` are included in the algebraic identities.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Influence

/-- The numerical encoding of a Boolean output. -/
def boolValue (b : Bool) : ℝ := if b then 1 else 0

/-- Mean of a two-point real-valued random variable. -/
def fiberMean (p a b : ℝ) : ℝ := (1 - p) * a + p * b

/-- Variance on a Bernoulli fiber, defined as the mean squared deviation. -/
def fiberVariance (p a b : ℝ) : ℝ :=
  (1 - p) * (a - fiberMean p a b) ^ 2 + p * (b - fiberMean p a b) ^ 2







/-- Expected disagreement when both the input bit and its independent replacement
are sampled from the same Bernoulli distribution. -/
def fiberResampling (p : ℝ) (a b : Bool) : ℝ :=
  (1 - p) * ((1 - p) * FiberShift.mismatch a a + p * FiberShift.mismatch a b) +
    p * ((1 - p) * FiberShift.mismatch b a + p * FiberShift.mismatch b b)










section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Variance as a finite expectation of squared deviations. -/
def variance (p : ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ProductMeasure.expectation p
    (fun x => (F x - ProductMeasure.expectation p F) ^ 2)











/-- Resampling influence: sample the original cube point and independently
replace the chosen coordinate by a fresh Bernoulli bit. -/
def resamplingInfluence (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ :=
  ProductMeasure.expectation p (fun x =>
    (1-p) * FiberShift.mismatch (f x) (f (Function.update x i false)) +
      p * FiberShift.mismatch (f x) (f (Function.update x i true)))





/-- Averaged conditional variance in one coordinate. -/
def coordinateVariance (p : ℝ) (F : (ι → Bool) → ℝ) (i : ι) : ℝ :=
  ProductMeasure.expectation p (fun z =>
    fiberVariance p (F (ProductMeasure.insertBit i false z))
      (F (ProductMeasure.insertBit i true z)))





/-- Total influence in the paper's resampling normalization. -/
def totalInfluence (p : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  ∑ i, resamplingInfluence p f i







end Cube
end NarrowDNF.Influence


