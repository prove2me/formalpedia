-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_FiniteContour
-- name    : OAI_Analysis_Cotype_FiniteContour
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:15:21.078423+00:00
-- url     : https://prove2.me/theorems/75df0b0b-8f07-48ea-9a3c-41fc40f33480
-- title:
--   Finite resolvents, Laplace sums and logarithmic kernels
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\lambda_i\in\mathbb R$ and $v_i$ be finitely many vectors in a complex normed space.
--
--   1. **Resolvent.** $\mathcal R(z)=\sum_i(z-\lambda_i)^{-1}v_i$.
--   2. **Laplace sum.** $\mathcal L(w)=\sum_ie^{-w\lambda_i}v_i$, the semigroup at complex time $w$.
--   3. **Logarithmic kernel.** $K(w,q)=e^qe^{-we^q}\mathcal R(e^q)$, the resolvent in the logarithmic variable $z=e^q$. Integrating it along vertical lines in $q$ represents the Laplace sum through the resolvent, so resolvent bounds in a sector give bounds on the semigroup at complex times.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FiniteContour.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FiniteContour.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent

namespace OAI

open Complex Set MeasureTheory Filter
open scoped BigOperators Interval Topology

namespace FiniteContour

noncomputable def resolvent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E) (z : ℂ) : E :=
  ∑ i, (z - (lam i : ℂ))⁻¹ • v i

noncomputable def laplace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E) (w : ℂ) : E :=
  ∑ i, exp (-(w * (lam i : ℂ))) • v i

noncomputable def logKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E) (w q : ℂ) : E :=
  (exp q * exp (-(w * exp q))) • resolvent lam v (exp q)

end FiniteContour

end OAI


