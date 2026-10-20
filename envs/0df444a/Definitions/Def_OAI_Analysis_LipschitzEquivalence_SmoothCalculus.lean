-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
-- name    : OAI_Analysis_LipschitzEquivalence_SmoothCalculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:02:48.339587+00:00
-- url     : https://prove2.me/theorems/846e2cf3-fc65-499f-bdb9-942f7237b21a
-- title:
--   Smooth functions on a Hilbert space and gradient energies of molecules
-- statement:
--   Smooth test functions on a real Hilbert space $H$ and integrals of their gradients along molecular edges.
--
--   1. **Smooth functions.** $C^\infty(H)$ is the vector space of smooth real functions on $H$, with evaluation at $p$, gradient at $p$ (a linear map into $H$), and pointwise products.
--   2. **Edges.** For $p,q\in H$ the edge is the segment $t\mapsto q+t(p-q)$, $t\in[0,1]$.
--   3. **Gradient integrals.** For molecular data with coefficients $c_i$ and pairs $(p_i,q_i)$, and smooth $f$,
--   $$
--   \mathrm{energy}(f)=\sum_i|c_i|\,\|p_i-q_i\|\int_0^1\|\nabla f(q_i+t(p_i-q_i))\|^2\,dt ,
--   $$
--   and the mass is the same expression with $\|\nabla f\|$ in place of $\|\nabla f\|^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SmoothCalculus.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothCalculus.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def smoothSubmodule (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Submodule ℝ (H → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by exact (contDiff_const : ContDiff ℝ ∞ (fun _ : H => (0:ℝ)))
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  smul_mem' := by
    intro c f hf
    exact (show ContDiff ℝ ∞ f from hf).const_smul c

abbrev Smooth (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H] : Type _ := ↥(smoothSubmodule H)

namespace Smooth

def eval (p : H) : Smooth H →ₗ[ℝ] ℝ where
  toFun f := (f : H → ℝ) p
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem contDiff {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : Smooth H) : ContDiff ℝ ∞ (f : H → ℝ) := f.property

theorem differentiable (f : Smooth H) : Differentiable ℝ (f : H → ℝ) :=
  f.contDiff.differentiable (by simp)

def grad (p : H) : Smooth H →ₗ[ℝ] H where
  toFun f := gradient (f : H → ℝ) p
  map_add' f g := by
    change (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ ((f : H → ℝ)+(g : H → ℝ)) p) = _
    rw [fderiv_add (f.differentiable p) (g.differentiable p),map_add]
    rfl
  map_smul' c f := by
    change (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (c • (f : H → ℝ)) p) = _
    rw [fderiv_const_smul (f.differentiable p) c,map_smul]
    rfl

def mul (f g : Smooth H) : Smooth H := ⟨fun p => (f : H → ℝ) p*(g : H → ℝ) p,
  f.contDiff.mul g.contDiff⟩

@[simp] theorem mul_apply (f g : Smooth H) (p : H) : (f.mul g : H → ℝ) p = f.val p*g.val p := rfl

end Smooth

def edge (p q : H) (t : ℝ) : H := q+t • (p-q)

open FreeSpace

def gradEnergy (a : MolecularData H) (f : Smooth H) : ℝ :=
  ∑ i, (|a.coeff i| *dist (a.p i) (a.q i)) *
    ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖^2

def gradMass (a : MolecularData H) (f : Smooth H) : ℝ :=
  ∑ i, (|a.coeff i| *dist (a.p i) (a.q i)) *
    ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖

end LipschitzCounterexample.CompactWSC
end

end OAI


