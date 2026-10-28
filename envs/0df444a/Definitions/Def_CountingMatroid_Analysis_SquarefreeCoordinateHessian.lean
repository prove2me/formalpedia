-- Prove2me | Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
-- name    : CountingMatroid_Analysis_SquarefreeCoordinateHessian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:09:16.70661+00:00
-- url     : https://prove2.me/theorems/f5ec74c6-e70c-484b-a467-f7aa39364311
-- title:
--   Explicit residual Hessian for squarefree coordinate extraction
-- statement:
--   Let $\alpha$ have decidable equality, let $w$ assign a rational coefficient to every finite subset of $\alpha$, let $S\subseteq\alpha$ be finite, and let $k\in\mathbb N$. The residual Hessian is the real matrix indexed by a distinguished coordinate $\ast$ and the elements of $\alpha$, with entries
--   $$\begin{aligned}
--   H_{\ast\ast}&=(k+2)(k+1)w(S),\\
--   H_{\ast a}=H_{a\ast}&=
--   \begin{cases}0&a\in S,\\(k+1)w(S\cup\{a\})&a\notin S,\end{cases}\\
--   H_{ab}&=
--   \begin{cases}0&a\in S\ \text{or}\ b\in S\ \text{or}\ a=b,\\
--   w(S\cup\{a,b\})&\text{otherwise}.
--   \end{cases}
--   \end{aligned}$$
--   Rational coefficients are cast to real numbers. This definition records the squarefree extraction matrix before the common factorial factor $k!$; it imposes no sign condition on the weights and makes no signature assertion.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SquarefreeCoordinateHessian.lean#L17-L28

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Powerset
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
section


set_option autoImplicit false

/-! Coordinate differentiation of a homogeneous polynomial whose label
variables are squarefree reduces its constant Hessian to a residual matrix.
The matrix records the selected labels and the number of homogenizer
derivatives. This calculation concerns arbitrary subset coefficients and
does not assume a matroid signature bound. -/

namespace CountingMatroid.Analysis.SquarefreeCoordinateHessian

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: The residual Hessian before multiplication by the factorial of
the number of homogenizer derivatives. Selected label rows are zero.
TEXLINE: main.tex:334-339 -/
noncomputable def squarefreeResidualHessian {α : Type} [DecidableEq α]
    (w : Finset α → ℚ) (S : Finset α) (k : ℕ) :
    Matrix (Option α) (Option α) ℝ := fun i j =>
  match i, j with
  | none, none => (k + 2 : ℝ) * (k + 1 : ℝ) * (w S : ℝ)
  | none, some a => if a ∈ S then 0 else (k + 1 : ℝ) * (w (insert a S) : ℝ)
  | some a, none => if a ∈ S then 0 else (k + 1 : ℝ) * (w (insert a S) : ℝ)
  | some a, some b =>
      if a ∈ S ∨ b ∈ S ∨ a = b then 0 else (w (insert a (insert b S)) : ℝ)











end CountingMatroid.Analysis.SquarefreeCoordinateHessian

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed the coordinate Hessian identity using the full-derivative coefficient formula; all four entries have the common homogenizer factorial, and repeated labels give zero.

* 2026-10-09 · partial · after live handoff deferral, proved coordinate-fold commutation and monomial annihilation when a derivative count exceeds its exponent. This closes the normal form for repeated labels anywhere in the list. Only the distinct-label factorial coefficient identity remains open.
* 2026-10-09 · decomposed · defined the exact residual Hessian and proved the derivative-list cardinality identity; instantiated the distinct-label witnesses and reduced the normal form to monomial coefficient extraction. Repeated-label annihilation remains part of the same polynomial obligation.
-/

end


