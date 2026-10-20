-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
-- name    : OAI_Analysis_Cotype_WalshSymmetry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:01:43.726994+00:00
-- url     : https://prove2.me/theorems/cb0fb29c-9c80-48b0-8f59-2a1fc46a2e04
-- title:
--   The symmetry group of the Walsh pairing
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Walsh characters are $w_v(u)=(-1)^{\langle u,v\rangle}$ for $u,v\in\{0,1\}^n\cong\mathbb F_2^n$.
--
--   1. **Walsh symmetries.** Pairs $(g_1,g_2)$ of permutations of the cube with
--   $$
--   w_{g_2v}(g_1u)=w_v(u)\quad\text{for all }u,v .
--   $$
--   They form a finite group, whose components act on primal and dual indices.
--   2. **Reindexing isometries.** A permutation $e$ of a finite set induces the isometry $z\mapsto z\circ e$ of $\ell_2(\Omega;X)$.
--   3. **Right translation.** For a finite group $\Gamma$, $h\mapsto(z\mapsto z(\cdot\,h))$, a representation of $\Gamma$ by isometries of $\ell_2(\Gamma;X)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshSymmetry.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshSymmetry.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

def walshSymmetryGroup (n : ℕ) : Subgroup (Equiv.Perm (Cube n) × Equiv.Perm (Cube n)) where
  carrier := {g | ∀ u v, character (g.2 v) (g.1 u) = character v u}
  one_mem' := by intro u v; rfl
  mul_mem' := by
    intro g h hg hh u v
    change character (g.2 (h.2 v)) (g.1 (h.1 u)) = _
    rw [hg, hh]
  inv_mem' := by
    intro g hg u v
    have h := hg (g.1⁻¹ u) (g.2⁻¹ v)
    simpa using h.symm

abbrev WalshSymmetry (n : ℕ) : Type := walshSymmetryGroup n
instance (n : ℕ) : Fintype (WalshSymmetry n) := Fintype.ofFinite _
instance (n : ℕ) : DecidableEq (WalshSymmetry n) := Classical.decEq _

def primalSymmetry {n : ℕ} (g : WalshSymmetry n) : Equiv.Perm (Cube n) := g.val.1
def dualSymmetry {n : ℕ} (g : WalshSymmetry n) : Equiv.Perm (Cube n) := g.val.2

variable {Γ Ω X : Type*} [Fintype Ω] [NormedAddCommGroup X] [NormedSpace ℝ X]
open WithLp

def l2Reindex (e : Ω ≃ Ω) : PiLp 2 (fun _ : Ω => X) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Ω => X) where
  toFun z := toLp 2 (fun a => z (e a))
  invFun z := toLp 2 (fun a => z (e.symm a))
  left_inv z := by ext a; simp
  right_inv z := by ext a; simp
  map_add' z w := by ext a; rfl
  map_smul' c z := by ext a; rfl
  norm_map' z := by
    simp only [PiLp.norm_eq_of_L2]
    congr 1
    exact Equiv.sum_comp e (fun a => ‖z a‖^2)

@[simp] theorem l2Reindex_apply (e : Ω ≃ Ω) (z : PiLp 2 (fun _ : Ω => X)) (a : Ω) :
    l2Reindex e z a = z (e a) := rfl

variable [Group Γ] [Fintype Γ]

def rightTranslation : Γ →* (PiLp 2 (fun _ : Γ => X) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Γ => X)) where
  toFun h := l2Reindex (Equiv.mulRight h)
  map_one' := by ext z a; simp
  map_mul' g h := by ext z a; simp [mul_assoc]

@[simp] theorem rightTranslation_apply (h : Γ) (z : PiLp 2 (fun _ : Γ => X)) (a : Γ) :
    rightTranslation h z a = z (a*h) := rfl

end Cotype

end

end OAI


