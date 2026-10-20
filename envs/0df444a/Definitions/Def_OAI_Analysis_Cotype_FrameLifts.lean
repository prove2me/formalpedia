-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_FrameLifts
-- name    : OAI_Analysis_Cotype_FrameLifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:27:25.311794+00:00
-- url     : https://prove2.me/theorems/731f9f04-129c-4b93-a1c2-230813e9d284
-- title:
--   Growth pairing data for Walsh norms
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $T:X\to Y$ be bounded, and let the growth space be $\ell_2(\Gamma_n;\ell_2(\{0,1\}^{2n};X))$.
--
--   1. **Tuple actions.** The Walsh symmetry group acts on $m$-tuples of cube points through its primal and dual components.
--   2. **Growth pairing data.** A number $\gamma>\mathcal W_n(T)/2$ and unit families $x(u)$ and $y(v)$ in the growth spaces with the exact pairing
--   $$
--   y(v)\bigl(T\,x(u)\bigr)=\gamma\,w_v(u),
--   $$
--   where $T$ acts coordinatewise. It also contains unit lifts $P_U(\varepsilon)$ and $Z_V(\delta)$ indexed by tuples, whose coordinate moments are $\frac{1}{48D\sqrt m}$ times $x(U_i)$ and $y(V_i)$. All of these are equivariant under the symmetry group, and the Walsh norms of the amplified operator equal those of $T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FrameLifts.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FrameLifts.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {n m : ℕ}

@[instance_reducible] def primalTupleAction : MulAction (WalshSymmetry n) (Fin m → Cube n) where
  smul g U := fun i => primalSymmetry g (U i)
  one_smul U := by funext i; rfl
  mul_smul g h U := by funext i; rfl

@[instance_reducible] def dualTupleAction : MulAction (WalshSymmetry n) (Fin m → Cube n) where
  smul g U := fun i => dualSymmetry g (U i)
  one_smul U := by funext i; rfl
  mul_smul g h U := by funext i; rfl

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

abbrev GrowthSpace (n : ℕ) (X : Type*) : Type _ := SymmetryL2 n (PiLp 2 (fun _ : Cube (n+n) => X))

structure GrowthPairingData (T : X →L[ℝ] Y) (n m : ℕ) (Dg Df : ℝ) where
  gamma : ℝ
  gamma_half : walshNorm n T / 2 < gamma
  gamma_pos : 0 < gamma
  x : Cube n → GrowthSpace n X
  y : Cube n → (GrowthSpace n Y →L[ℝ] ℝ)
  P : (Fin m → Cube n) → Cube m → GrowthSpace n X
  Z : (Fin m → Cube n) → Cube m → (GrowthSpace n Y →L[ℝ] ℝ)
  x_norm : ∀ u, ‖x u‖ ≤ 1
  y_norm : ∀ v, ‖y v‖ ≤ 1
  P_norm : ∀ U ε, ‖P U ε‖ ≤ 1
  Z_norm : ∀ V δ, ‖Z V δ‖ ≤ 1
  exact_pairing : ∀ u v, y v (l2Amplification (l2Amplification T) (x u)) = gamma * character v u
  P_moment : ∀ U i, moment (GrowthSpace n X) (P U) i = (1/(2*24*Dg*Real.sqrt m)) • x (U i)
  Z_moment : ∀ V i, moment (GrowthSpace n Y →L[ℝ] ℝ) (Z V) i = (1/(2*24*Df*Real.sqrt m)) • y (V i)
  x_equivariant : ∀ g u, rightTranslation g (x u) = x (primalSymmetry g u)
  y_equivariant : ∀ g v, dualAction (rightTranslation (X := PiLp 2 (fun _ : Cube (n+n) => Y))) g (y v) = y (dualSymmetry g v)
  P_equivariant : ∀ g U ε, P (fun i => primalSymmetry g (U i)) ε = rightTranslation g (P U ε)
  Z_equivariant : ∀ g V δ, Z (fun i => dualSymmetry g (V i)) δ =
    dualAction (rightTranslation (X := PiLp 2 (fun _ : Cube (n+n) => Y))) g (Z V δ)
  walsh_norms : ∀ k, walshNorm k (l2Amplification (Ω := WalshSymmetry n)
    (l2Amplification (Ω := Cube (n+n)) T)) = walshNorm k T

end Cotype

end

end OAI


