-- Prove2me | Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
-- name    : CountingMatroid_Analysis_RankWeightSupportExchange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:08:09.031194+00:00
-- url     : https://prove2.me/theorems/9aa9a84b-fb3e-45ae-b57a-81f5ec2d058d
-- title:
--   Homogenized exponent vector of a subset
-- statement:
--   Let $\alpha$ be a finite type and $A\subseteq\alpha$. Use a distinct homogenizing coordinate $*$ together with label coordinates indexed by $\alpha$. Define
--   $$m_A=(|\alpha|-|A|)e_*+\sum_{a\in A}e_a.$$
--   Thus the label exponents are the membership indicators of $A$, while the remaining degree is assigned to the homogenizer. The vector has natural finite support; subtraction is natural subtraction, with $|A|\le|\alpha|$. This definition supplies an exponent encoding and does not assert any matroid or coefficient property.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RankWeightSupportExchange.lean#L14-L19

import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
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

/-! The subset exponent description of the rank-weight polynomial support.
The exchange condition depends only on the subsets, not on matroid ranks. -/

namespace CountingMatroid.Analysis.RankWeightSupportExchange

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: Encode a subset by its squarefree label exponents and the
remaining homogenizing degree. TEXLINE: main.tex:334-339 -/
noncomputable def subsetExponent {α : Type} [Fintype α] (A : Finset α) :
    Option α →₀ ℕ :=
  Finsupp.single none (Fintype.card α - A.card) +
    ∑ a ∈ A, Finsupp.single (some a) 1













end CountingMatroid.Analysis.RankWeightSupportExchange

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · identified the support with all subset exponents and proved unit exchange by insert, erase, and swap; the argument needs only positive coefficients and no matroid exchange or rank-signature theorem.
-/

end


