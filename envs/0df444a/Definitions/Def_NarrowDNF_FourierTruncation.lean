-- Prove2me | Definitions.Def_NarrowDNF_FourierTruncation
-- name    : NarrowDNF_FourierTruncation
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T08:00:20.187197+00:00
-- url     : https://prove2.me/theorems/1bd4143b-1cbe-4e07-9dd8-ee543d9a9301
-- title:
--   Retained Fourier sums and pointwise small-component energy
-- statement:
--   Let $\iota$ be a finite coordinate set, let $x\in\{0,1\}^{\iota}$, and let $F_S(x)$ denote the $S$-indexed $p$-biased Fourier component of a real-valued function $f$. For a finite family $A$ of coordinate subsets, the retained Fourier polynomial is
--   $$P_A f(x)=\sum_{S\in A}F_S(x).$$
--   For real cutoffs $k$ and $\eta$, define the small-component energy by
--   $$\operatorname{SmallMass}_{k,\eta}(f)=\sum_{S\subseteq\iota}\mathbb E_p\!\left[\mathbf1_{\{|S|\le k,\ |F_S(X)|\le\eta\}}F_S(X)^2\right].$$
--   The degree comparison uses the real number $k$ directly. The magnitude test is pointwise inside the expectation; it is not a condition on the supremum norm of an entire component. These explicit finite sums provide the objects used to separate retained Fourier mass from low-degree, small-amplitude mass in the approximation argument. Their probabilistic interpretation uses the Bernoulli product law; truncation estimates are separate theorem statements.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/FourierTruncation.lean#L60-L63
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/FourierTruncation.lean#L11-L12

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
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.FourierTruncation
end NarrowDNF.FourierTruncation

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure


noncomputable section
namespace NarrowDNF.FourierTruncation
open ProductMeasure Fourier
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def partialSum (p : ℝ) (f : Cube ι → ℝ) (retained : Finset (Finset ι)) (x : Cube ι) : ℝ :=
  ∑ S ∈ retained, component p f S x












/-- The small-component energy with the paper's real degree cutoff. -/
def smallMassReal (p : ℝ) (f : Cube ι → ℝ) (k η : ℝ) : ℝ :=
  ∑ S : Finset ι, expectation p (fun x =>
    if (S.card : ℝ) ≤ k ∧ |component p f S x| ≤ η then component p f S x ^ 2 else 0)



end NarrowDNF.FourierTruncation


