-- Prove2me | Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
-- name    : CountingMatroid_Analysis_RankWeightQuadraticSignature
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:10:12.571298+00:00
-- url     : https://prove2.me/theorems/69fbe210-b2c7-45d3-8dcc-da44b32a060a
-- title:
--   Rank-weight polynomials and their differential descendants
-- statement:
--   Let $\alpha$ be a finite type, let $N$ be a matroid on $\alpha$, and let $q\in\mathbb Q$. With homogenizing variable $z_0$ and label variables $z_a$, define
--   $$F_{N,q}(z)=\sum_{A\subseteq\alpha}
--   \bigl(q^{r_N(A)}\bigr)^{-1}
--   z_0^{|\alpha|-|A|}\prod_{a\in A}z_a,$$
--   where $r_N(A)$ is the finite natural rank of $A$. The definition does not assume $q>0$, and inversion at zero is the rational field's total inverse.
--
--   For variable types $\sigma,\tau$ with $\tau$ finite, a rational coefficient family $a_{st}$ defines linear substitution by $z_s\mapsto\sum_{t\in\tau}a_{st}x_t$. A polynomial is a descendant of a starting polynomial if it is obtainable by finitely many coordinate partial derivatives, such substitutions with all $a_{st}\geq0$, and multiplication by nonnegative rational scalars, including zero. The starting polynomial is itself a descendant; substitution may change its variable type. The substitution operation alone is defined for arbitrary rational coefficients.
--
--   For a rational polynomial $g$ in variables indexed by $\tau$, the matrix called its Hessian in this interface is
--   $$H(g)_{st}=\operatorname{const}\!\left(\partial_s\partial_tg\right)\in\mathbb R.$$
--   This is the Hessian evaluated at the origin, and equals the constant Hessian when $g$ is quadratic. Finally, for a list of rational directions on a finite variable type, define
--   $$D_{[]}p=p,\qquad
--   D_{d::L}p=\sum_s d(s)\,\partial_s(D_Lp).$$
--   The head direction is applied last. This bundle defines the polynomial operations and descendant relation; it does not itself provide the quadratic signature theorem.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RankWeightQuadraticSignature.lean#L44-L53

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Model_Prelude
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
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
namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
section


set_option autoImplicit false

/-!
The precise external signature input, separate from the operational rank
correspondence and coefficient extraction proved in the counting paper.
`Descendant` records only partial derivatives, nonnegative linear
substitutions, and nonnegative scalar multiplication. The signature uses
Mathlib's maximum dimension of a positive definite subspace over the reals.
The empty- and singleton-ground signature cases are proved, using the
homogeneous-degree invariant of every descendant. The two-element ground
case is proved by rank submodularity and a two-square calculation, with
the resulting hyperplane transported through every allowed substitution.
The signature case with at most one output variable follows from the ambient
dimension bound. The remaining
Bränden–Huh input is the unresolved borrowed mixed-derivative prerequisite
in `MixedDirectionalRankWeightSignature`. The exact normal
form of a descendant is proved: nonnegative directional derivatives in the
original variables, followed by one nonnegative linear substitution and a
nonnegative scalar. A nonzero quadratic uses exactly ground-set size minus
two derivatives. The unresolved signature bound is applied to this normal
form. A proved nonpositive-hyperplane invariant transports the Hessian
through the final substitution and scaling and recovers the exact orthogonal
kernel used by the signature bound. Only its establishment for the original
mixed directional derivative on ground sets of size at least three remains
open in that support module; no Lorentzian assumption has been introduced.
-/

namespace CountingMatroid.Analysis.RankWeightQuadraticSignature

open scoped BigOperators

/-- PAPER: main.tex:334-339
The homogenized rank-weight polynomial in the cited Bränden–Huh theorem.
The extra `none` variable is the paper's homogenizing variable z₀. -/
noncomputable def tuttePolynomial {α : Type} [Fintype α]
    (N : Matroid α) (q : ℚ) : MvPolynomial (Option α) ℚ := by
  classical
  exact ∑ A : Finset α,
    MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
      MvPolynomial.X none ^ (Fintype.card α - A.card) *
        ∏ a ∈ A, MvPolynomial.X (some a)

/-- INTERNAL: Encode the paper's allowed nonnegative linear substitutions
as polynomial evaluation, including zero columns and identified variables.
TEXLINE: main.tex:326-343 -/
noncomputable def linearSubstitution {σ τ : Type} [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) : MvPolynomial τ ℚ :=
  MvPolynomial.aeval (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p

/-- INTERNAL: A finite derivation by exactly the operations used in the
paper's quadratic extraction; the variable type can change on substitution.
TEXLINE: main.tex:326-373 -/
inductive Descendant {σ : Type} (p : MvPolynomial σ ℚ) :
    (τ : Type) → MvPolynomial τ ℚ → Prop
  | initial : Descendant p σ p
  | derivative {τ : Type} {g : MvPolynomial τ ℚ} (t : τ) :
      Descendant p τ g → Descendant p τ (MvPolynomial.pderiv t g)
  | substitute {τ υ : Type} [Fintype υ] {g : MvPolynomial τ ℚ}
      (a : τ → υ → ℚ) (ha : ∀ s t, 0 ≤ a s t) :
      Descendant p τ g → Descendant p υ (linearSubstitution a g)
  | scale {τ : Type} {g : MvPolynomial τ ℚ} (c : ℚ) (hc : 0 ≤ c) :
      Descendant p τ g → Descendant p τ (MvPolynomial.C c * g)

/-- INTERNAL: Hessian of a quadratic polynomial, with rational entries
cast to the real field in which the signature theorem is stated.
TEXLINE: main.tex:326-343 -/
noncomputable def hessian {τ : Type} (g : MvPolynomial τ ℚ) : Matrix τ τ ℝ :=
  fun s t => (MvPolynomial.constantCoeff
    (MvPolynomial.pderiv s (MvPolynomial.pderiv t g)) : ℚ)















/-- INTERNAL: Iterated directional differentiation in the original variable
space. The list head is the last derivative applied.
TEXLINE: main.tex:326-348 -/
noncomputable def iteratedDirectionalDerivative {σ : Type} [Fintype σ]
    (ds : List (σ → ℚ)) (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  match ds with
  | [] => p
  | d :: ds => ∑ s, MvPolynomial.C (d s) *
      MvPolynomial.pderiv s (iteratedDirectionalDerivative ds p)













end CountingMatroid.Analysis.RankWeightQuadraticSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · handoff-ready · after the live scheduler opened capacity, isolated the sole remaining original-variable invariant in MixedDirectionalRankWeightSignature and proved the fold identity connecting it to the parent. All other children are proved; the parent uses the independent prerequisite and contains no remaining proof hole of its own. The prerequisite still has the mixed-directional compatibility gap, so this is a proof boundary, not a completed Bränden–Huh proof.
* 2026-10-09 · partial · proved Hessian congruence under linear substitution and scalar scaling, and the nonpositive-hyperplane invariant with its pullback, scaling, signature and positive-vector orthogonal-kernel consequences. Proved the two-element Tutte quadratic by the exact rank-weight pair bound and a two-square identity, so the parent closes every descendant on ground sets of size at most two. Its single remaining gap is establishment of the invariant for |α|≥3 after exactly |α|-2 nonnegative directional derivatives; all subsequent transport is proved. No new assumption or open child was introduced.
* 2026-10-09 · partial · proved the linear polynomial chain rule and substitution composition in LinearPolynomialChainRule, then proved finite intermediate variables, the exact directional normal form, and its homogeneous degree. The parent uses this representation and proves that its direction list has length |α|-2 and its scalar is positive. The original nonpositive-kernel gap now concerns this normalized expression. A stdin application of eRk_submod failed by statement shape; separate checked stdin examples show that adding two signature-one forms can produce signature two. The unresolved cited input is compatibility of mixed nonnegative directional derivatives of the common matroid polynomial, not the algebraic normalization. No assumption or new open helper was introduced.
* 2026-10-09 · partial · proved the at-most-one-output-variable branch using sigPos_le_finrank and Module.finrank_pi; preserved all earlier homogeneous-degree, coefficient-cone and small-ground proofs. Current statement-shape searches found no matroid-polynomial, Lorentzian closure or substitute spectral declaration supplying nonpositivity on the positive-vector orthogonal complement. The remaining cited Bränden–Huh input stays open in its original theorem, without new helpers or assumptions.
* 2026-10-09 · blocked · preserved the proved empty-ground branch; searched project, pinned Mathlib and Arlib for Lorentzian rank-weight base, closure and quadratic signature results without finding an applicable declaration. A stdin application of descendant_constant to the nonempty branch fails because its initial polynomial must be constant. Proposed the unchanged cited Bränden–Huh consequence as prior input; introduced no helper or assumption.
-/

end


