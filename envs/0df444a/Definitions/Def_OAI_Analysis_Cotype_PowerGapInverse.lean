-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
-- name    : OAI_Analysis_Cotype_PowerGapInverse
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:01:10.840355+00:00
-- url     : https://prove2.me/theorems/04e954ea-7505-4388-a094-9d7f932dce41
-- title:
--   Inverse bounds from a power gap
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections.
--
--   1. **Power-gap inverse bound.** For $N\ge1$, $b\ge0$ and $q<1$,
--   $$
--   \beta(N,b,q)=\frac{\sum_{k<N}b^k}{1-q} .
--   $$
--   If $\|S\|\le b$ and $\|S^N\|\le q<1$, then $1-S$ is invertible with $\|(1-S)^{-1}\|\le\beta(N,b,q)$, because $(1-S)^{-1}=\bigl(\sum_{k<N}S^k\bigr)(1-S^N)^{-1}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/PowerGapInverse.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/PowerGapInverse.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

def powerGapInverseBound (N : ℕ) (b q : ℝ) : ℝ :=
  (∑ k ∈ Finset.range N, b^k) / (1-q)

end Cotype

end

end OAI


