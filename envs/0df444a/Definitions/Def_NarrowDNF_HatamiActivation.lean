-- Prove2me | Definitions.Def_NarrowDNF_HatamiActivation
-- name    : NarrowDNF_HatamiActivation
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T08:00:38.134209+00:00
-- url     : https://prove2.me/theorems/cabf4a53-51db-4fbb-a74e-0c9ef0bc39b7
-- title:
--   Local threshold activations from significant Fourier components
-- statement:
--   For a finite coordinate set $\iota$, a set $T\subseteq\iota$, and $x\in\{0,1\}^{\iota}$, write $\mu_p^T(x_T)$ for the Bernoulli product mass of the restriction $x_T$. Given a finite retained family $A$ and masses $m(S)$, put
--   $$b_T=\sum_{S\in A,\ T\subseteq S}m(S).$$
--   The threshold activation indexed by $T$ fires precisely when
--   $$|T|\le k\quad\text{and}\quad\delta\,\mu_p^T(x_T)\le b_T.$$
--   It depends only on the labels in $T$, and the bundle includes the locality proof required to construct an activation family.
--
--   For a real-valued $f$, take $A=\{S:|S|\le k,\ \exists x,\ |F_S(x)|>\eta\}$ and $m(S)=\Pr_p[|F_S(X)|\ge\eta]$. Thus the retained-family test is strict, whereas the tail event is non-strict. The paper-specific family applies this construction to the $0/1$ encoding of a Boolean $f$, with $k=1000C/a$, $\delta=\delta(k)$, and $\eta=\epsilon_1(k,a/1000)$. These definitions specify the actual activation tests; bounds on their arity, load, and approximation error are proved separately.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L237-L240
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L242-L244
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L33-L39
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L261-L263
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L50-L54
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L416-L421
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L25-L27
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiActivation.lean#L29-L31

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiParameters
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure


/-!
# Hatami's threshold activation family

The local activations and multiplicity-counted load calculation from Appendix A
of the 2026-11-06 STOC revision. The cutoff is real, as in the source. All threshold masses
are explicit finite sums; no activation-load guarantee is assumed.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiActivation

open ProductMeasure
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability mass of the input restricted to the activation's index set. -/
def localMass (p : ℝ) (T : Finset ι) (x : Cube ι) : ℝ :=
  weight p (fun i : T => x i)

/-- The mass attached to a set is the total retained mass of its supersets. -/
def bMass (retained : Finset (Finset ι)) (m : Finset ι → ℝ) (T : Finset ι) : ℝ :=
  ∑ S ∈ retained, if T ⊆ S then m S else 0

omit [Fintype ι] [DecidableEq ι] in
theorem localMass_congr (p : ℝ) (T : Finset ι) (x y : Cube ι)
    (hxy : ∀ i ∈ T, x i = y i) : localMass p T x = localMass p T y := by
  unfold localMass
  congr 1
  funext i
  exact hxy i i.property



/-- Precisely the threshold activation in Appendix A, including the arity gate. -/
def thresholdActivation (k p δ : ℝ) (retained : Finset (Finset ι))
    (m : Finset ι → ℝ) : Activation ι where
  fires T x := (T.card : ℝ) ≤ k ∧ δ * localMass p T x ≤ bMass retained m T
  locality T x y hxy := by rw [localMass_congr p T x y hxy]































/-- The retained Fourier family, using the finite-cube characterization
of `‖F_S‖∞ > η` as the existence of an input with magnitude greater than `η`. -/
def significantSets (p : ℝ) (f : Cube ι → ℝ) (k η : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter fun S => (S.card : ℝ) ≤ k ∧ ∃ x, η < |Fourier.component p f S x|

/-- The exact event probability appearing in the source's definition of `b_T`. -/
def componentTailMass (p : ℝ) (f : Cube ι → ℝ) (η : ℝ) (S : Finset ι) : ℝ :=
  probability p (fun x => η ≤ |Fourier.component p f S x|)



/-- The source's threshold activations, specialized to its actual Fourier masses. -/
def fourierActivation (k p δ η : ℝ) (f : Cube ι → ℝ) : Activation ι :=
  thresholdActivation k p δ (significantSets p f k η) (componentTailMass p f η)





























/-- Appendix A's activation family at its exact parameter values. -/
def paperActivation (a C p : ℝ) (f : Cube ι → Bool) : Activation ι :=
  fourierActivation (1000*C/a) p
    (HatamiParameters.delta (1000*C/a))
    (HatamiParameters.epsilonOne (1000*C/a) (a/1000))
    (fun x => Influence.boolValue (f x))











end NarrowDNF.HatamiActivation


