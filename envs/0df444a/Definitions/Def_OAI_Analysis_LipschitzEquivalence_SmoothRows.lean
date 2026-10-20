-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
-- name    : OAI_Analysis_LipschitzEquivalence_SmoothRows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:07:07.827005+00:00
-- url     : https://prove2.me/theorems/22f3edf3-3b59-4101-8241-20a51515544b
-- title:
--   Triangular rows of smooth test functions and molecules
-- statement:
--   Rows of pairs (test function, molecule) used to detect weakly Cauchy sequences in the free space $\mathcal F(H)$ of a Hilbert space.
--
--   1. **Pairings.** Molecular data $a$ pair with a function $f$ by
--   $$
--   \langle a,f\rangle=\sum_ic_i\bigl(f(p_i)-f(q_i)\bigr),
--   $$
--   a linear functional on functions and on smooth functions.
--   2. **Row items.** For a set $K$, constants $C,\rho$ and a sequence $\mu$ in $\mathcal F(H)$, a row item is a $1$-Lipschitz smooth $f$ with $f(0)=0$, together with molecular data supported in $K$ of cost at most $C$ and within $\rho$ of some $\mu_n$.
--   3. **Triangular rows.** For $\alpha>0$, a finite row of items $v_0,\dots,v_{n-1}$ is triangular if $\langle a_i,f_j\rangle\ge4\alpha$ for $j\le i$ and $|\langle a_i,f_j\rangle|\le\alpha$ for $i<j$. Being triangular is inherited by subrows, so these rows form a hereditary row family.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SmoothRows.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothRows.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

local instance instNormedAddCommGroupSpace : NormedAddCommGroup (Space H) := inferInstance
local instance instNormedSpaceRealSpace : NormedSpace ℝ (Space H) := inferInstance
local instance instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported (K : Set H) : NormedAddCommGroup (supported K) := inferInstance
local instance instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported (K : Set H) : NormedSpace ℝ (supported K) := inferInstance
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeSpaceMemSubmoduleSupported (K : Set H) : NormedAddCommGroup ((supported K) →L[ℝ] ℝ) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeSpaceMemSubmoduleSupported (K : Set H) : NormedSpace ℝ ((supported K) →L[ℝ] ℝ) := inferInstance

def molPair (a : MolecularData H) : (H → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ i, a.coeff i*(f (a.p i)-f (a.q i))
  map_add' f g := by simp only [Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring
  map_smul' c f := by simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]; congr 1; funext i; ring

def smoothPair (a : MolecularData H) : Smooth H →ₗ[ℝ] ℝ := (molPair a).comp (smoothSubmodule H).subtype

@[simp] theorem smoothPair_apply {H : Type uH} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (a : MolecularData H) (f : Smooth H) :
    smoothPair a f = molPair a f.val := rfl

structure RowItem (K : Set H) (C ρ : ℝ) (μ : ℕ → Space H) where
  f : Smooth H
  lip : LipschitzWith 1 f.val
  zero : f.val 0 = 0
  a : MolecularData H
  support : ∀ i, a.p i ∈ K ∧ a.q i ∈ K
  cost_le : a.cost ≤ C
  close : ∃ n, ‖μ n-a.vector‖ < ρ

def triangularRows (K : Set H) (C ρ α : ℝ) (μ : ℕ → Space H) :
    RowFamily (RowItem K C ρ μ) where
  accepts v := (∀ i j, j ≤ i → 4*α ≤ smoothPair (v i).a (v j).f) ∧
    (∀ i j, i < j → |smoothPair (v i).a (v j).f| ≤ α)
  hereditary e _ hv := ⟨fun i j h => hv.1 (e i) (e j) (e.monotone h),
    fun i j h => hv.2 (e i) (e j) (e.strictMono h)⟩

end LipschitzCounterexample.CompactWSC
end

end OAI


