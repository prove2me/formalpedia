-- Prove2me | Definitions.Def_NarrowDNF_BourgainComponents
-- name    : NarrowDNF_BourgainComponents
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:56.515227+00:00
-- url     : https://prove2.me/theorems/9ceaffd5-5dd0-42a3-a15d-13bd26b1d1f8
-- title:
--   Truncated Fourier-component mass and large-coordinate square functions
-- statement:
--   Let $f:\{0,1\}^I\to\mathbb R$ on a finite cube. Write $f_S(x)=\widehat f_p(S)\chi_{p,S}(x)$ for its actual $p$-biased Fourier component. Given a degree cutoff $k$ and a real threshold $\eta$, the small-component mass is
--   $$\mathbb E_{\mu_p}\!\left[\sum_{|S|\le k}\mathbf1_{\{|f_S(x)|\le\eta\}}f_S(x)^2\right].$$
--   The empty support is included in this sum.
--
--   The bundle also defines a finite combinatorial version for a family $\mathcal F$ of coordinate sets and real numbers $(c_S)_{S\in\mathcal F}$. The coordinate square is $Q_i=\sum_{S\in\mathcal F:i\in S}c_S^2$; the truncated mass is $\sum_{S\in\mathcal F}\mathbf1_{\{|c_S|\le\eta\}}c_S^2$; and the set of large coordinates is $\{i:Q_i>\tau^2\}$. These quantities isolate the pointwise counting portion of Bourgain's component estimate from its analytic moment bounds. They do not encode an assumed square-function inequality.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L27-L29
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L31-L33
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L35-L37
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainComponents.lean#L20-L25

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.BourgainComponents
end NarrowDNF.BourgainComponents


/-!
# Finite combinatorial part of Bourgain's component estimate

The definitions use the actual biased Fourier components. The pointwise
lemmas below are independent of any analytic square-function hypothesis.
They are ingredients, not a claim to have proved Hatami (11) or (18).
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainComponents

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared mass of components of degree at most k whose pointwise values are
small. The empty support is included, exactly as in Hatami's displayed sum. -/
def smallComponentMass (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (η : ℝ) : ℝ :=
  ProductMeasure.expectation p (fun x =>
    ∑ S ∈ (Finset.univ.filter fun S : Finset ι => S.card ≤ k),
      if |Fourier.component p f S x| ≤ η then Fourier.component p f S x ^ 2 else 0)

/-- The coordinate square function, before taking a square root. -/
def coordinateSquare (F : Finset (Finset ι)) (c : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ S ∈ F, if i ∈ S then c S ^ 2 else 0

/-- Pointwise truncated mass of an arbitrary family of components. -/
def truncatedMass (F : Finset (Finset ι)) (c : Finset ι → ℝ) (η : ℝ) : ℝ :=
  ∑ S ∈ F, if |c S| ≤ η then c S ^ 2 else 0

/-- The coordinates with a square function exceeding the threshold. -/
def largeCoordinates (F : Finset (Finset ι)) (c : Finset ι → ℝ) (τ : ℝ) : Finset ι :=
  Finset.univ.filter fun i => τ ^ 2 < coordinateSquare F c i





















end NarrowDNF.BourgainComponents


