-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCOperator
-- name    : OAI_Analysis_LipschitzEquivalence_WUCOperator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:19:05.478054+00:00
-- url     : https://prove2.me/theorems/b05b541a-7c8f-4d5f-8286-60d9bf2ff30b
-- title:
--   Operators into ℓ¹ from weakly unconditionally Cauchy functionals
-- statement:
--   Let $T_i$ be bounded functionals on a real normed space $E$ such that all signed partial sums are uniformly bounded:
--   $$
--   \Bigl|\sum_{i<n}c_i\,T_i(x)\Bigr|\le2\|x\|\qquad\text{whenever }|c_i|\le1 .
--   $$
--
--   Then $\sum_{i<n}|T_i(x)|\le2\|x\|$ for all $n$, by choosing $c_i$ to be the signs of $T_i(x)$. Hence $x\mapsto(T_i(x))_i$ is a bounded operator $E\to\ell^1$ with $i$-th coordinate $T_i(x)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/WUCOperator.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WUCOperator.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothMultiplier
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_DetectingSequence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCFunctions
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCDuals

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample.WeakSequences
open scoped BigOperators NNReal ENNReal Topology
open Filter
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sum_abs_le_of_signed_bound (T : ℕ → E →L[ℝ] ℝ)
    (hT : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ x : E,
      |∑ i ∈ Finset.range n, c i*T i x| ≤ 2*‖x‖) (n : ℕ) (x : E) :
    (∑ i ∈ Finset.range n, |T i x|) ≤ 2*‖x‖ := by
  classical
  let c : ℕ → ℝ := fun i => if 0 ≤ T i x then 1 else -1
  have hc (i : ℕ) : |c i| ≤ 1 := by unfold c; split_ifs <;> norm_num
  have he (i : ℕ) : c i*T i x = |T i x| := by
    unfold c
    split_ifs with h
    · rw [one_mul,abs_of_nonneg h]
    · rw [neg_one_mul,abs_of_neg (lt_of_not_ge h)]
  have h := hT n c hc x
  simpa only [he,abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (T i x)))] using h

def wucOperator (T : ℕ → E →L[ℝ] ℝ)
    (hT : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ x : E,
      |∑ i ∈ Finset.range n, c i*T i x| ≤ 2*‖x‖) : E →L[ℝ] RealL1 :=
  ({ toFun := fun x => ⟨fun i => T i x,memℓp_gen (by
       simp only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs]
       exact summable_of_sum_range_le (fun i => abs_nonneg _)
         (fun n => sum_abs_le_of_signed_bound T hT n x))⟩
     map_add' := by intro x y; apply lp.ext; funext i; exact map_add (T i) x y
     map_smul' := by intro c x; apply lp.ext; funext i; exact map_smul (T i) c x } : E →ₗ[ℝ] RealL1).mkContinuous 2 (by
       intro x
       rw [sumL1_norm]
       change (∑' i, ‖T i x‖) ≤ 2*‖x‖
       simp only [Real.norm_eq_abs]
       exact Real.tsum_le_of_sum_range_le (fun i => abs_nonneg _)
         (fun n => sum_abs_le_of_signed_bound T hT n x))

@[simp] theorem wucOperator_apply (T : ℕ → E →L[ℝ] ℝ) (hT) (x : E) (i : ℕ) :
    wucOperator T hT x i = T i x := rfl

end LipschitzCounterexample.WeakSequences
end

end OAI


