-- Prove2me | Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
-- name    : CountingMatroid_Analysis_CubicTensorContraction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:06:56.743998+00:00
-- url     : https://prove2.me/theorems/b8d30175-57da-4e2d-990f-e3aec44f7449
-- title:
--   Exponent support associated with a cubic tensor
-- statement:
--   Let $\sigma$ have decidable equality and let $T:\sigma^3\to\mathbb Q$ be any tensor. Its cubic exponent support is
--   $$\mathcal S(T)=\{e_i+e_j+e_s:\ s,i,j\in\sigma,\ T(s,i,j)\ne0\}.$$
--   Each $e_i$ is a unit natural exponent vector. Repeated indices produce exponents larger than one; the exponent vector forgets the order of the three indices. No finiteness or symmetry of $T$ is assumed. The definition uses existence of a nonzero tensor entry, not a sum of entries over permutations, so it does not impose cancellation rules from an associated polynomial.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CubicTensorContraction.lean#L30-L35

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

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
section


set_option autoImplicit false

/-!
The spectral part of cubic directional closure, stated independently of
polynomial calculus. A symmetric nonnegative tensor carries the exchange
support of a homogeneous cubic. The coordinate slices have at most one
positive direction; the remaining obligation is to propagate that bound to
every nonnegative contraction. Arbitrary sums of such slices have no such
closure property without the tensor and support hypotheses.

The remaining obligation is the degree-three instance of the nonnegative
directional-derivative closure cited in the paper. Brändén–Huh, Corollary
2.11, states this closure for the recursively defined classes of polynomials
with M-convex support and Lorentzian quadratic derivatives. The proof here
separates the proved exchange-to-connectivity argument from the analytic
Rayleigh contraction lemma, whose normalized spectral and boundary steps
remain open. The parent reduction does not assume an aggregate signature
bound or alter the theorem hypotheses.
-/

namespace CountingMatroid.Analysis.CubicTensorContraction

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- INTERNAL: Read a cubic tensor's nonzero entries as unordered exponent triples.
TEXLINE: main.tex:340-348 -/
def cubicTensorSupport {σ : Type} [DecidableEq σ] (T : σ → σ → σ → ℚ) :
    Set (σ →₀ ℕ) :=
  {m | ∃ s i j, T s i j ≠ 0 ∧
    m = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single s 1}



end CountingMatroid.Analysis.CubicTensorContraction

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · verified handoff · agent5-cubic-rayleigh-20261009-1 was accepted after semantic-use validation; ownership of CubicExchangeCut and CubicTensorRayleighContraction transferred to the scheduler. The parent reduction elaborates; the analytic child remains the proof obligation.
* 2026-10-09 · decomposed · proved exchange forces connectivity across every active-coordinate cut in CubicExchangeCut; the parent now supplies that proved invariant and its existing slice Rayleigh estimates to CubicTensorRayleighContraction. The analytic spectral and boundary obligation remains open.
* 2026-10-09 · prior proposal · identified the remaining contraction bound as the cubic specialization of Brändén–Huh Corollary 2.11, explicitly cited at main.tex:346-347; no Lorentzian closure API was found in the pinned dependencies. Preserved all existing proofs and the unchanged open statement.
* 2026-10-09 · partial · proved each slice's reverse Cauchy–Schwarz estimate from its nonpositive hyperplane. Handoff agent2-cubic-tensor-20261009-1 was deferred at the validation deadline; ownership remains local pending settled-boundary revalidation.
* 2026-10-09 · decomposed · stated the tensor-only contraction boundary; proved zero-direction and single-coordinate-direction cases. The general compatible-tensor spectral step remains open.
-/

end


