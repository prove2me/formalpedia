-- Prove2me | Definitions.Def_NarrowDNF_ProductMeasure
-- name    : NarrowDNF_ProductMeasure
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:10.312217+00:00
-- url     : https://prove2.me/theorems/c4f87df2-a383-45c4-879c-40bde38e5bea
-- title:
--   Explicit finite Bernoulli product weights, probabilities, and errors
-- statement:
--   Let $\iota$ be a finite coordinate set. For a real parameter $p$, a bit has weight $p$ when it is one and $1-p$ when it is zero. A cube point $x\in\{0,1\}^{\iota}$ has product weight
--   $$w_p(x)=\prod_{i\in\iota}\bigl(p\ \text{if }x_i=1,\ \text{else }1-p\bigr).$$
--   For a real-valued $F$, an event $E$, and Boolean functions $f,g$, define
--   $$\mathbb E_pF=\sum_x w_p(x)F(x),\qquad\Pr_p(E)=\mathbb E_p\mathbf1_E,\qquad\operatorname{err}_p(f,g)=\Pr_p[f\ne g].$$
--   When $0\le p\le1$, these are the finite Bernoulli product law and its expectation; the underlying algebraic sums are defined for all real $p$.
--
--   The bundle also supplies insertion of a specified bit into the one-coordinate complement and extension of a partial assignment by zeros outside a coordinate predicate. These operations let later proofs state fiber decompositions, marginalization, resampling, and adaptive restrictions directly in the same finite probability model.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L34-L36
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L38-L40
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L299-L301
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L42-L44
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L146-L148
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L25-L26
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ProductMeasure.lean#L31-L32

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure


/-!
# Finite Bernoulli product probability

The probability model is an explicit finite sum of product weights. Algebraic
identities hold for every real parameter; positivity claims state `0 ≤ p ≤ 1`.
No theorem here assumes a probability law or an analytic input without proof.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bernoulli mass of one bit. -/
def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p




/-- Probability mass of a cube point. -/
def weight (p : ℝ) (x : ι → Bool) : ℝ := ∏ i, bitWeight p (x i)

/-- Expectation under the finite product weights. -/
def expectation (p : ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ∑ x, weight p x * F x

/-- Probability of an arbitrary decidable predicate. -/
def probability (p : ℝ) (P : (ι → Bool) → Prop) [DecidablePred P] : ℝ :=
  expectation p (fun x => if P x then 1 else 0)

/-- Disagreement probability of two Boolean functions. -/
def error (p : ℝ) (f g : (ι → Bool) → Bool) : ℝ :=
  probability p (fun x => f x ≠ g x)











































/-- Insert a bit into the missing coordinate of a smaller cube. -/
def insertBit (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) : ι → Bool :=
  (Equiv.funSplitAt i Bool).symm (b,z)

























/-- Extend a partial cube input by zero outside its coordinate predicate. -/
def extendFalse (P : ι → Prop) [DecidablePred P] (z : {i // P i} → Bool) : ι → Bool :=
  fun i => if h : P i then z ⟨i,h⟩ else false







end NarrowDNF.ProductMeasure


