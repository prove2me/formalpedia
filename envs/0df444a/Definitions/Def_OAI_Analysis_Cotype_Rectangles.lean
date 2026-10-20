-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_Rectangles
-- name    : OAI_Analysis_Cotype_Rectangles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:46:51.657995+00:00
-- url     : https://prove2.me/theorems/c11ffb32-9472-4e84-b517-980254550e43
-- title:
--   Rectangular Fourier coefficients on matrix cubes
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Consider functions on $\{0,1\}^{\iota\times\kappa}$ (Boolean matrices).
--
--   1. **Rectangles.** For $s\subseteq\iota$ and $t\subseteq\kappa$, the indicator of $s\times t$, viewed as a frequency.
--   2. **Rectangular indices.** All rectangles with $|s|=k$ and $|t|=l$.
--   3. **Rectangular sums.**
--   $$
--   C_{k,l}(f)=\sum_{|s|=k,\ |t|=l}\hat f(s\times t),
--   $$
--   the total Fourier mass of $f$ on rank-one frequencies of size $k\times l$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/Rectangles.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Rectangles.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def rectangle (s : Finset ι) (t : Finset κ) : (ι × κ) → Bool :=
  fun ij => decide (ij.1 ∈ s ∧ ij.2 ∈ t)

def rectangularIndices (k l : ℕ) : Finset ((ι × κ) → Bool) :=
  ((Finset.univ.powersetCard k) ×ˢ (Finset.univ.powersetCard l)).image
    (fun st => rectangle st.1 st.2)

def Ckl (f : ((ι × κ) → Bool) → ℝ) (k l : ℕ) : ℝ :=
  ∑ P ∈ rectangularIndices k l, fourier f P

end Cotype

end

end OAI


