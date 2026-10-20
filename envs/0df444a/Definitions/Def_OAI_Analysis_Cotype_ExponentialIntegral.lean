-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
-- name    : OAI_Analysis_Cotype_ExponentialIntegral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:04:02.709982+00:00
-- url     : https://prove2.me/theorems/40b2773e-d7b7-46bc-878e-1732975bb92f
-- title:
--   Integrals of operator exponentials
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $A$ be a complete normed algebra and $L\in A$.
--
--   1. **Exponential integral.**
--   $$
--   \mathcal I_L(t)=\int_0^te^{sL}\,ds .
--   $$
--   It satisfies $L\,\mathcal I_L(t)=e^{tL}-1$, which is used to invert shifted generators over finite times.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ExponentialIntegral.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ExponentialIntegral.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse

namespace OAI

noncomputable section
namespace Cotype
open MeasureTheory
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def exponentialIntegral (L : A) (t : ℝ) : A :=
  ∫ s in (0 : ℝ)..t, NormedSpace.exp (s • L)

end Cotype

end

end OAI


