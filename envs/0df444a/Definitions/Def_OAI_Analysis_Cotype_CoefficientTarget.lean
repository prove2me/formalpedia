-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_CoefficientTarget
-- name    : OAI_Analysis_Cotype_CoefficientTarget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:57:34.594858+00:00
-- url     : https://prove2.me/theorems/d411763f-1baf-4de2-af35-d1e489c44cd6
-- title:
--   The scalar coefficient target
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Sign matrices are Boolean $m\times m$ matrices $S$, viewed as points of the cube $\{0,1\}^{m\times m}$; $\mathrm{row}(\sigma)$ and $\mathrm{col}(\tau)$ are the row- and column-constant matrices. Let $m\in\mathbb N$ and $a,b>0$.
--
--   1. **Degree cutoff.** $k(m)=\lceil2\log_2m\rceil$.
--   2. **Scalar admissibility.** Odd functions $\Psi$ on sign matrices and $f,g$ on $\{0,1\}^m$, bounded by $4$, whose degree-one Fourier coefficients are $\hat f(e_i)=a$ and $\hat g(e_j)=b$. They are linked by
--   $$
--   \mathbb E_\sigma\,\sigma_i\,\Psi(\mathrm{row}(\sigma)\oplus S)=a\,g(S_{i\cdot}),\qquad\mathbb E_\tau\,\tau_j\,\Psi(\mathrm{col}(\tau)\oplus S)=b\,f(S_{\cdot j}).
--   $$
--   3. **Coefficient target.** If $4\le k(m)<m$ and $80k(k+1)^2\le\min(ma,mb)$, there is $c>0$ such that every admissible $\Psi$ has a Fourier coefficient $|\hat\Psi(P)|\ge c$ at a frequency $P$ of $\mathbb F_2$-rank at least $2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/CoefficientTarget.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CoefficientTarget.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient
import Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
import Definitions.Def_OAI_Analysis_Cotype_PatternPairing
import Definitions.Def_OAI_Analysis_Cotype_TaggedFrames

namespace OAI

noncomputable section
namespace Cotype

abbrev SignMatrix (m : ℕ) := (Fin m × Fin m) → Bool

def degreeCutoff (m : ℕ) : ℕ := ⌈2 * Real.logb 2 (m : ℝ)⌉₊

def ScalarAdmissible (m : ℕ) (a b : ℝ) (Ψ : SignMatrix m → ℝ)
    (f g : Cube m → ℝ) : Prop :=
  IsOdd Ψ ∧ IsOdd f ∧ IsOdd g ∧
  (∀ S, |Ψ S| ≤ 4) ∧ (∀ s, |f s| ≤ 4) ∧ (∀ t, |g t| ≤ 4) ∧
  (∀ i, fourier f (unitIndex i) = a) ∧ (∀ j, fourier g (unitIndex j) = b) ∧
  (∀ (i : Fin m) (S : SignMatrix m),
    average (fun σ : Cube m => sign (σ i) * Ψ (xorCube (rowCube σ) S)) =
      a * g (fun j => S (i,j))) ∧
  (∀ (j : Fin m) (S : SignMatrix m),
    average (fun τ : Cube m => sign (τ j) * Ψ (xorCube (columnCube τ) S)) =
      b * f (fun i => S (i,j)))

def CoefficientTarget : Prop := ∀ (m : ℕ) (a b : ℝ),
  4 ≤ degreeCutoff m → degreeCutoff m < m → 0 < a → 0 < b →
  80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤ min ((m : ℝ)*a) ((m : ℝ)*b) →
  ∃ c : ℝ, 0 < c ∧ ∀ (Ψ : SignMatrix m → ℝ) (f g : Cube m → ℝ),
    ScalarAdmissible m a b Ψ f g →
      ∃ P : SignMatrix m, 2 ≤ (binaryMatrix P).rank ∧ c ≤ |fourier Ψ P|

end Cotype

end

end OAI


