-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
-- name    : OAI_Analysis_Cotype_BinaryCoordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:12:09.966981+00:00
-- url     : https://prove2.me/theorems/ea934c5f-7439-4ae4-b9db-53b709698f74
-- title:
--   The cube as a vector space over the two-element field
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections.
--
--   1. **Binary space.** $\mathbb F_2^n$, identified with the cube $\{0,1\}^n$ bitwise.
--   2. **Binary signs.** $\mathrm{sgn}(z)=1$ for $z=0$ and $-1$ for $z=1$. It is a homomorphism: $\mathrm{sgn}(a+b)=\mathrm{sgn}(a)\,\mathrm{sgn}(b)$.
--   3. **Characters.**
--   $$
--   w_v(u)=\mathrm{sgn}\bigl(\langle v,u\rangle\bigr),
--   $$
--   with the $\mathbb F_2$ dot product.
--   4. **Binary frames.** Tuples $U_1,\dots,U_r$ of cube points that are linearly independent over $\mathbb F_2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/BinaryCoordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/BinaryCoordinates.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
abbrev BinarySpace (n : ℕ) := Fin n → ZMod 2

def binaryBit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem binary_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hlt := z.val_lt
  have hval : z.val = 0 ∨ z.val = 1 := by omega
  exact hval.imp (ZMod.val_eq_zero z).mp (ZMod.val_eq_one (by decide) z).mp

def bitEquiv : Bool ≃ ZMod 2 where
  toFun := binaryBit
  invFun z := decide (z = 1)
  left_inv b := by cases b <;> simp [binaryBit]
  right_inv z := by rcases binary_eq_zero_or_one z with rfl | rfl <;> decide

def cubeBinaryEquiv (n : ℕ) : Cube n ≃ BinarySpace n :=
  Equiv.piCongrRight (fun _ => bitEquiv)

@[simp] theorem cubeBinaryEquiv_apply {n : ℕ} (u : Cube n) (i : Fin n) :
    cubeBinaryEquiv n u i = binaryBit (u i) := rfl

def binarySign (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by simp [binarySign]
@[simp] theorem binarySign_one : binarySign 1 = -1 := by simp [binarySign]

theorem binarySign_add (a b : ZMod 2) :
    binarySign (a+b) = binarySign a * binarySign b := by
  have ha := binary_eq_zero_or_one a
  have hb := binary_eq_zero_or_one b
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [show (1 + 1 : ZMod 2) = 0 by decide]

theorem binarySign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    binarySign (∑ i ∈ s, f i) = ∏ i ∈ s, binarySign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, binarySign_add, ih]

theorem character_binary_dot {n : ℕ} (u v : Cube n) :
    character v u = binarySign (coordinateDual (cubeBinaryEquiv n v) (cubeBinaryEquiv n u)) := by
  rw [coordinateDual_apply, binarySign_sum]
  apply Finset.prod_congr rfl
  intro i hi
  cases hu : u i <;> cases hv : v i <;> simp [binaryBit, sign, hu, hv]

def BinaryFrame {n r : ℕ} (U : Fin r → Cube n) : Prop :=
  LinearIndependent (ZMod 2) (fun i => cubeBinaryEquiv n (U i))

end Cotype

end

end OAI


