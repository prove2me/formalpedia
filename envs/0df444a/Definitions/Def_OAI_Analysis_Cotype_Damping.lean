-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_Damping
-- name    : OAI_Analysis_Cotype_Damping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:55:00.276985+00:00
-- url     : https://prove2.me/theorems/5389ff4d-6753-4adc-9684-6f43b13170da
-- title:
--   Damped samples of matrix cubes
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Consider Boolean matrices indexed by $\iota\times\kappa$.
--
--   1. **Operations.** Bitwise xor of cubes, the indicator vector of a set, and the row-constant and column-constant matrices built from $\sigma\in\{0,1\}^\iota$ and $\tau\in\{0,1\}^\kappa$.
--   2. **Damped sample.** $(\sigma,\tau,R)\mapsto\mathrm{row}(\sigma)\oplus\mathrm{col}(\tau)\oplus R$.
--   3. **Damped expectation.** For biases $a,b,c$, the iterated biased expectation
--   $$
--   \mathbb E_{\sigma\sim a}\,\mathbb E_{\tau\sim b}\,\mathbb E_{R\sim c}\,f(\mathrm{row}(\sigma)\oplus\mathrm{col}(\tau)\oplus R),
--   $$
--   which damps each Fourier coefficient according to its row and column structure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/Damping.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Damping.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def xorCube (ε η : ι → Bool) : ι → Bool := fun i => Bool.xor (ε i) (η i)

@[simp] theorem sign_xor (a b : Bool) : sign (Bool.xor a b) = sign a * sign b := by
  cases a <;> cases b <;> norm_num [Bool.xor]

def setIndex (s : Finset ι) : ι → Bool := fun i => decide (i ∈ s)

def rowCube (σ : ι → Bool) : (ι × κ) → Bool := fun ij => σ ij.1

def columnCube (τ : κ → Bool) : (ι × κ) → Bool := fun ij => τ ij.2

def dampedSample (σ : ι → Bool) (τ : κ → Bool) (R : (ι × κ) → Bool) :
    (ι × κ) → Bool := xorCube (rowCube σ) (xorCube (columnCube τ) R)

def dampedExpectation (f : ((ι × κ) → Bool) → ℝ) (a b c : ℝ) : ℝ :=
  biasedExpectation (fun σ => biasedExpectation (fun τ => biasedExpectation
    (fun R => f (dampedSample σ τ R)) (fun _ => c)) (fun _ => b)) (fun _ => a)

end Cotype

end

end OAI


