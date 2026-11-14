-- Prove2me | Definitions.Def_NarrowDNF_ConditionalExpectation
-- name    : NarrowDNF_ConditionalExpectation
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:28.849359+00:00
-- url     : https://prove2.me/theorems/a98212ab-c528-4623-ac34-e95fd673205a
-- title:
--   Finite conditional means, strict majority decoders, and adaptive partition codes
-- statement:
--   Let $\phi:A\to B$ partition finite sets, let $w:A\to\mathbb R$ be explicit weights, and let $F:A\to\mathbb R$. The mass and first moment of atom $b$ are $m_b=\sum_{\phi(a)=b}w(a)$ and $q_b=\sum_{\phi(a)=b}w(a)F(a)$. Its mean is $q_b/m_b$, using the real field's zero-division convention on empty or zero-mass atoms. Pulling this mean back along $\phi$ defines the conditional function. Squared error is the unnormalized sum $\sum_a w(a)(F(a)-G(a))^2$.
--
--   Boolean values are encoded by $0$ and $1$. The decoder returns true exactly when the conditional mean is strictly greater than $1/2$; ties return false. Boolean error is the corresponding weighted disagreement sum.
--
--   For a local activation family $J$, an adaptive atom is coded by $(A_J(x),x\mathbf1_{A_J(x)})$, preserving the original labels and setting labels outside the active union to zero. Bernoulli weights produce its adaptive mean and decoder. The bundle also constructs the equivalence between a fixed-coordinate restriction fiber and the cube on complementary coordinates, using an explicit merge of the two assignments.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L33-L35
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L250-L253
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L284-L287
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L289-L291
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L316-L319
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L321-L335
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L44-L45
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L47-L48
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L50-L52
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L54-L55
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L57-L58
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L21-L23
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L25-L27
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ConditionalExpectation.lean#L29-L31

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation


/-!
# Conditional expectation on a finite partition

A partition is represented by a map `φ : α → β`; each realized fiber has
positive mass when the input weights are strictly positive. This file derives
least-squares projection and Boolean threshold rounding from finite sums. It
does not assume Hatami's construction-specific residual bound.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ConditionalExpectation

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- Total weight of one partition atom. -/
def mass (φ : α → β) (w : α → ℝ) (b : β) : ℝ :=
  ∑ a : {a // φ a = b}, w a

/-- Weighted first moment on one partition atom. -/
def moment (φ : α → β) (w F : α → ℝ) (b : β) : ℝ :=
  ∑ a : {a // φ a = b}, w a * F a

/-- Atom mean. Unrealized atoms have value zero by the field's zero-division convention. -/
def mean (φ : α → β) (w F : α → ℝ) (b : β) : ℝ :=
  moment φ w F b / mass φ w b

/-- Conditional mean pulled back to the input space. -/
def conditional (φ : α → β) (w F : α → ℝ) (a : α) : ℝ :=
  mean φ w F (φ a)



/-- Weighted squared error, without any implicit normalization. -/
def squaredError (w F G : α → ℝ) : ℝ := ∑ a, w a * (F a - G a)^2

/-- Numeric encoding of a Boolean value. -/
def value (b : Bool) : ℝ := if b then 1 else 0

/-- Weighted Boolean disagreement. -/
def booleanError (w : α → ℝ) (f g : α → Bool) : ℝ :=
  ∑ a, w a * (if f a = g a then 0 else 1)

/-- Strict half-threshold, matching the convention in Appendix A of the paper. -/
def threshold (m : ℝ) : Bool := decide ((1 / 2 : ℝ) < m)

def decoder (φ : α → β) (w : α → ℝ) (f : α → Bool) (a : α) : Bool :=
  threshold (conditional φ w (fun x => value (f x)) a)































section Adaptive
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite coding of an adaptive atom, with actual labels retained on its active union. -/
def adaptiveCode (J : Activation ι) (x : Cube ι) : Finset ι × Cube ι := by
  classical
  exact (Finset.univ.filter (fun i => i ∈ J.active x), J.zeroOutside x)



/-- Conditional mean with respect to the actual adaptive atom partition. -/
def adaptiveMean (p : ℝ) (J : Activation ι) (f : Cube ι → Bool) : Cube ι → ℝ := by
  classical
  exact conditional (adaptiveCode J) (ProductMeasure.weight p) (fun x => value (f x))

/-- Threshold readout of the adaptive conditional mean. -/
def adaptiveDecoder (p : ℝ) (J : Activation ι) (f : Cube ι → Bool) : Cube ι → Bool :=
  fun x => threshold (adaptiveMean p J f x)





end Adaptive

section CoordinatePartition
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Combine assignments on complementary coordinate sets. -/
def merge (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) (y : {i // ¬ P i} → Bool) : Cube ι :=
  fun i => if h : P i then z ⟨i,h⟩ else y ⟨i,h⟩

/-- A fixed-coordinate fiber is exactly the cube on the complementary coordinates. -/
def restrictionFiberEquiv (P : ι → Prop) [DecidablePred P] (z : {i // P i} → Bool) :
    {x : Cube ι // (fun i : {i // P i} => x i) = z} ≃ ({i // ¬ P i} → Bool) where
  toFun x i := x.val i
  invFun y := ⟨merge P z y, by funext i; simp [merge, i.property]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : P i
    · have h := congrFun x.property (⟨i,hi⟩ : {i // P i})
      simpa [merge, hi] using h.symm
    · simp [merge, hi]
  right_inv y := by
    funext i
    simp [merge, i.property]















end CoordinatePartition
section Localization





variable {ι : Type*} [Fintype ι] [DecidableEq ι]











end Localization
end NarrowDNF.ConditionalExpectation


