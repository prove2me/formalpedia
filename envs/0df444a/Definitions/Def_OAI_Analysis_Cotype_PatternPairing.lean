-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_PatternPairing
-- name    : OAI_Analysis_Cotype_PatternPairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:53:14.110024+00:00
-- url     : https://prove2.me/theorems/17eb05ec-c0d7-4c40-81ad-a4669b020371
-- title:
--   Pairing functions indexed by sign patterns
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Growth pairing data for $T:X\to Y$ consist of unit families $x(u)$, $y(v)$ with $y(v)(Tx(u))=\gamma\,w_v(u)$, and unit lifts $P_U(\varepsilon)$, $Z_V(\delta)$ indexed by $m$-tuples $U,V$ of cube points whose coordinate moments are fixed multiples of $x(U_i)$ and $y(V_i)$. Sign matrices are Boolean $m\times m$ matrices $S$, viewed as points of the cube $\{0,1\}^{m\times m}$; $\mathrm{row}(\sigma)$ and $\mathrm{col}(\tau)$ are the row- and column-constant matrices.
--
--   1. **Sign-frame realizations.** For a sign pattern $S\in\{0,1\}^{r\times s}$ and $r+s\le n$, chosen binary frames $U,V$ with $w_{V_j}(U_i)=\mathrm{sgn}(S_{ij})$.
--   2. **Pattern pairing.** $\Psi_S(\varepsilon,\delta)=\Pi_{U,V}(\varepsilon,\delta)$ for the frames realizing $S$ (with $m+m\le n$).
--   3. **Pattern slices.** $f_s(\varepsilon)$ and $g_t(\delta)$, the primal and dual slices for frames realizing a single column or row pattern.
--
--   By the symmetry of the data, these depend only on the pattern, which turns operator estimates into scalar functions on sign matrices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/PatternPairing.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/PatternPairing.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace Cotype

structure SignFrameRealization (n r s : ℕ) (S : Fin r × Fin s → Bool) where
  U : Fin r → Cube n
  V : Fin s → Cube n
  U_frame : BinaryFrame U
  V_frame : BinaryFrame V
  pairing : ∀ i j, character (V j) (U i) = sign (S (i,j))

def signFrameChoice {n r s : ℕ} (hn : r+s ≤ n) (S : Fin r × Fin s → Bool) :
    SignFrameRealization n r s S := by
  apply Classical.choice
  obtain ⟨U,V,hU,hV,hUV⟩ := sign_frames_feasible hn S
  exact ⟨⟨U,V,hU,hV,hUV⟩⟩

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {n m : ℕ} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

def patternPairing (hn : m+m ≤ n) (S : Fin m × Fin m → Bool) (ε δ : Cube m) : ℝ :=
  let q := signFrameChoice hn S
  d.tuplePairing q.U q.V ε δ

def patternPrimal (hn : m+1 ≤ n) (s : Cube m) (ε : Cube m) : ℝ :=
  let q := signFrameChoice hn (fun ij : Fin m × Fin 1 => s ij.1)
  d.primalSlice q.U (q.V 0) ε

def patternDual (hn : 1+m ≤ n) (s : Cube m) (δ : Cube m) : ℝ :=
  let q := signFrameChoice hn (fun ij : Fin 1 × Fin m => s ij.2)
  d.dualSlice (q.U 0) q.V δ

end GrowthPairingData
end Cotype

end

end OAI


