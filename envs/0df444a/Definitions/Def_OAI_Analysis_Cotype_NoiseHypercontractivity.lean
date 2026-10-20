-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
-- name    : OAI_Analysis_Cotype_NoiseHypercontractivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:17:39.193496+00:00
-- url     : https://prove2.me/theorems/d0f0c1f0-d58f-4069-b482-8d32b6432f0c
-- title:
--   Monotonicity of averages
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections.
--
--   1. **Monotone averages.** If $f\le g$ pointwise on a finite set, then
--   $$
--   \mathbb Ef\le\mathbb Eg .
--   $$
--   This is the basic tool for the hypercontractive estimate of the noise operator, $\mathbb E(Nf)^4\le(\mathbb Ef^2)^2$, which is proved by induction on the dimension.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/NoiseHypercontractivity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/NoiseHypercontractivity.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem average_mono {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    average f ≤ average g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

end Cotype

end

end OAI


