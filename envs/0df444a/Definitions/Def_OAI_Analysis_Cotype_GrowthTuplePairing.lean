-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
-- name    : OAI_Analysis_Cotype_GrowthTuplePairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:48:32.783728+00:00
-- url     : https://prove2.me/theorems/65dd9812-27e3-45cd-9e52-88f717881a61
-- title:
--   Pairings of tuple lifts
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Growth pairing data for $T:X\to Y$ consist of unit families $x(u)$, $y(v)$ with $y(v)(Tx(u))=\gamma\,w_v(u)$, and unit lifts $P_U(\varepsilon)$, $Z_V(\delta)$ indexed by $m$-tuples $U,V$ of cube points whose coordinate moments are fixed multiples of $x(U_i)$ and $y(V_i)$. Let $\widetilde T$ be the amplified operator on growth spaces.
--
--   1. **Tuple pairing.** $\Pi_{U,V}(\varepsilon,\delta)=Z_V(\delta)\bigl(\widetilde TP_U(\varepsilon)\bigr)$.
--   2. **Slices.**
--   $$
--   \pi_U(v;\varepsilon)=y(v)\bigl(\widetilde TP_U(\varepsilon)\bigr),\qquad\rho_V(u;\delta)=Z_V(\delta)\bigl(\widetilde Tx(u)\bigr),
--   $$
--   pairing a tuple lift against a single dual or primal vector. Their coordinate Fourier coefficients reproduce the pairings $\gamma\,w_{V_j}(U_i)$ scaled by the moment constants.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/GrowthTuplePairing.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/GrowthTuplePairing.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {n m : ℕ} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

abbrev amplifiedOperator (_d : GrowthPairingData T n m Dg Df) : GrowthSpace n X →L[ℝ] GrowthSpace n Y :=
  l2Amplification (l2Amplification T)

def tuplePairing (U V : Fin m → Cube n) (ε δ : Cube m) : ℝ :=
  d.Z V δ (d.amplifiedOperator (d.P U ε))

def primalSlice (U : Fin m → Cube n) (v : Cube n) (ε : Cube m) : ℝ :=
  d.y v (d.amplifiedOperator (d.P U ε))

def dualSlice (u : Cube n) (V : Fin m → Cube n) (δ : Cube m) : ℝ :=
  d.Z V δ (d.amplifiedOperator (d.x u))

end GrowthPairingData
end Cotype

end

end OAI


