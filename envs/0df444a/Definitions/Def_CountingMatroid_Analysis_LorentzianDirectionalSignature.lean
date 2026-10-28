-- Prove2me | Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
-- name    : CountingMatroid_Analysis_LorentzianDirectionalSignature
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:07:35.360269+00:00
-- url     : https://prove2.me/theorems/873bf895-8b50-434c-998a-8e20db4de62f
-- title:
--   Support exchange and coordinate Lorentzian certificates
-- statement:
--   For a rational multivariate polynomial $p$ indexed by a type $\sigma$, write $\operatorname{supp}(p)$ for its nonzero natural exponent vectors and $e_i$ for the unit exponent at $i$. Support exchange means that whenever $x,y\in\operatorname{supp}(p)$ and $y_i<x_i$, there exists $j$ such that
--   $$x_j<y_j,\qquad x-e_i+e_j\in\operatorname{supp}(p).$$
--   Subtraction is coordinatewise natural subtraction. For finite $\sigma$, define the real constant-Hessian quadratic form
--   $$Q_p(v)=\sum_{i,j\in\sigma}v_iv_j[1](\partial_i\partial_jp),\qquad v\in\mathbb R^\sigma,$$
--   where $[1]$ is the constant coefficient, embedded in $\mathbb R$. A coordinate Lorentzian certificate of degree $d\in\mathbb N$ requires homogeneity of degree $d$, nonnegative coefficients, support exchange, and, for every coordinate list $i_1,\ldots,i_k$ with $k+2=d$,
--   $$\operatorname{sigPos}(Q_{\partial_{i_1}\cdots\partial_{i_k}p})\le1.$$
--   Positive signature measures the dimension of a maximal positive-definite subspace. Coordinates may repeat; only coordinate derivatives are quantified. Support exchange alone imposes no homogeneity.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/LorentzianDirectionalSignature.lean#L31-L38

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
section


set_option autoImplicit false

/-!
Coordinate certificates for the Lorentzian argument record homogeneous degree,
nonnegative coefficients, M-convex support, and the positive-signature bound
for every quadratic coordinate derivative. The directional signature theorem
is reduced to two independent obligations: M-convex support preservation under
nonnegative directional differentiation, and the cubic signature mixing step.
The coefficient/support calculations and the reduction through coordinate and
directional derivative lists are implemented. The two imported obligations
remain open, so the general theorem is not yet a completed proof. The original
degree-two proof is preserved.

The paper invokes the Brändén–Huh closure results at main.tex:340-348. The pinned
libraries contain homogeneous partial-derivative and quadratic-signature APIs,
but no applicable Lorentzian or M-convex directional-closure theorem was found.

-/

namespace CountingMatroid.Analysis.LorentzianDirectionalSignature

open scoped BigOperators

/-- INTERNAL: The exchange condition for the exponent support of a homogeneous
polynomial. Subtraction is coordinatewise natural subtraction; the strict
inequality at `i` ensures that the removed unit is present.
TEXLINE: main.tex:334-348 -/
def HasMConvexSupport {σ : Type} (p : MvPolynomial σ ℚ) : Prop :=
  ∀ x ∈ p.support, ∀ y ∈ p.support, ∀ i, y i < x i →
    ∃ j, x j < y j ∧
      x - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support

/-- INTERNAL: The real quadratic form attached to the rational constant
Hessian, including the zero polynomial.
TEXLINE: main.tex:326-348 -/
noncomputable def constantHessianForm {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) : QuadraticForm ℝ (σ → ℝ) := by
  classical
  exact Matrix.toQuadraticForm' (fun i j =>
    ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j p)) : ℚ) : ℝ))

/-- INTERNAL: A coordinate certificate separates the matroid-specific base
result from the general Lorentzian directional-closure result. In particular,
its last field quantifies only over coordinate derivatives, not directions.
TEXLINE: main.tex:334-348 -/
structure CoordinateLorentzian {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) : Prop where
  homogeneous : p.IsHomogeneous n
  coeff_nonneg : ∀ m, 0 ≤ p.coeff m
  exchange : HasMConvexSupport p
  coordinate_signature : ∀ xs : List σ, xs.length + 2 = n →
    sigPos (constantHessianForm
      (xs.foldr (fun s f => MvPolynomial.pderiv s f) p)) ≤ 1

















end CountingMatroid.Analysis.LorentzianDirectionalSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · validated parallel handoff · request agent1-directional-cubic-support-20261009-1 accepted at semantic-use stage; NonnegativeDirectionalMConvexSupport and CubicDirectionalSignature transferred to scheduler ownership. The unchanged target has a complete proof body using both children; its remaining mathematical proof debt is explicitly retained in those two open obligations.
* 2026-10-09 · decomposed · directional signature reduced to independently stated support-exchange preservation and cubic signature mixing; proved coefficient positivity, exact directional support membership, coordinate commutation, and the parent reduction. The two child obligations remain open pending live handoff.
* 2026-10-09 · blocked · preserved the degree-two proof; statement-shape searches of pinned Mathlib and Arlib found no Lorentzian directional closure result. Stdin applications of the degree-two and hyperplane bounds exposed, respectively, a degree-two certificate/length mismatch and a missing common nonpositive hyperplane. Proposed the unchanged borrowed directional signature declaration as prior input; added no helper, assumption, or import.
-/

end


