-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
-- name    : OAI_Analysis_Cotype_EquivariantPairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:25:22.173428+00:00
-- url     : https://prove2.me/theorems/10674539-df6c-45a4-bd7d-78f70165ab61
-- title:
--   Symmetrized vectors over the Walsh symmetry group
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\Gamma_n$ be the Walsh symmetry group.
--
--   1. **Probability vectors.** For finite $\Omega$, $f\mapsto|\Omega|^{-1/2}f\in\ell_2(\Omega;X)$, and the matching normalized dual tuples.
--   2. **Symmetry space.** $\ell_2(\Gamma_n;X)$.
--   3. **Symmetrized families.** For $x:\{0,1\}^n\to X$ and $y:\{0,1\}^n\to Y^*$,
--   $$
--   \tilde x(u)=\bigl(x(g_1u)\bigr)_{g\in\Gamma_n},\qquad\tilde y(v)=\bigl(y(g_2v)\bigr)_{g\in\Gamma_n},
--   $$
--   normalized. Right translation by $g$ maps $\tilde x(u)$ to $\tilde x(g_1u)$, so the families are equivariant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/EquivariantPairing.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/EquivariantPairing.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def finiteProbabilityVector (f : Ω → X) : PiLp 2 (fun _ : Ω => X) :=
  Real.sqrt ((Fintype.card Ω : ℝ)⁻¹) • toLp 2 f

def finiteProbabilityDual (f : Ω → (Y →L[ℝ] ℝ)) : (PiLp 2 (fun _ : Ω => Y) →L[ℝ] ℝ) :=
  Real.sqrt ((Fintype.card Ω : ℝ)⁻¹) • finiteL2Dual f

variable {n : ℕ}
abbrev SymmetryL2 (n : ℕ) (X : Type*) : Type _ := PiLp 2 (fun _ : WalshSymmetry n => X)

def symmetryVector (x : Cube n → X) (u : Cube n) : SymmetryL2 n X :=
  finiteProbabilityVector (fun R : WalshSymmetry n => x (primalSymmetry R u))

def symmetryDual (y : Cube n → (Y →L[ℝ] ℝ)) (v : Cube n) : SymmetryL2 n Y →L[ℝ] ℝ :=
  finiteProbabilityDual (fun R : WalshSymmetry n => y (dualSymmetry R v))

@[simp] theorem symmetryVector_equivariant (x : Cube n → X) (g : WalshSymmetry n) (u : Cube n) :
    rightTranslation g (symmetryVector x u) = symmetryVector x (primalSymmetry g u) := by
  ext R
  rfl

end Cotype

end

end OAI


