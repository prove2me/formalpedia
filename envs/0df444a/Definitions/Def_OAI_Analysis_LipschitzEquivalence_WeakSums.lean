-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
-- name    : OAI_Analysis_LipschitzEquivalence_WeakSums
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:11:38.419582+00:00
-- url     : https://prove2.me/theorems/99dad2c2-06c0-4627-814e-f3c6551865d5
-- title:
--   ℓ¹-sums of normed spaces and their head and tail projections
-- statement:
--   Tools for $\ell^1$-sums $\bigl(\bigoplus_iG_i\bigr)_{\ell^1}$ of real normed spaces.
--
--   1. **Norm.** An element $x=(x_i)$ has $\|x\|=\sum_i\|x_i\|$, which is summable.
--   2. **Coordinate tests.** For functionals $f_i$ on $G_i$ with $\|f_i\|\le1$, the map $x\mapsto(f_i(x_i))_i$ is a bounded operator into real $\ell^1$:
--   $$
--   \sum_i|f_i(x_i)|\le\sum_i\|x_i\| .
--   $$
--   3. **Head and tail.** $\mathrm{head}_N$ keeps the coordinates $i<N$ and $\mathrm{tail}_N=\mathrm{id}-\mathrm{head}_N$ keeps those with $i\ge N$.
--   4. **Initial ones.** In the scalar space $c_0$, $\mathbf 1_{[0,N)}=\sum_{i<N}e_i$ has entries $1$ for $i<N$ and $0$ otherwise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uG

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev SumL1 (E : ℕ → Type uE) [∀ i, NormedAddCommGroup (E i)] := lp E 1
variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

omit [∀ i, NormedSpace ℝ (G i)] in
theorem sumL1_norm (x : SumL1 G) : ‖x‖ = ∑' i, ‖x i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x

omit [∀ i, NormedSpace ℝ (G i)] in
theorem sumL1_summable (x : SumL1 G) : Summable (fun i => ‖x i‖) := by
  simpa using (lp.hasSum_norm (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x).summable

def coordinateTests (f : ∀ i, G i →L[ℝ] ℝ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    SumL1 G →L[ℝ] RealL1 :=
  ({ toFun := fun x => ⟨fun i => f i (x i), memℓp_gen (by
       simp only [ENNReal.toReal_one, Real.rpow_one]
       apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ (sumL1_summable x)
       intro i
       simpa using (f i).le_of_opNorm_le (hf i) (x i))⟩
     map_add' := by intro x y; apply lp.ext; funext i; exact map_add (f i) _ _
     map_smul' := by intro c x; apply lp.ext; funext i; exact map_smul (f i) c _ } :
       SumL1 G →ₗ[ℝ] RealL1).mkContinuous 1 (by
         intro x
         simp only [one_mul]
         rw [sumL1_norm, sumL1_norm]
         apply Summable.tsum_le_tsum _ (sumL1_summable _) (sumL1_summable x)
         intro i
         simpa using (f i).le_of_opNorm_le (hf i) (x i))

@[simp] theorem coordinateTests_apply (f : ∀ i, G i →L[ℝ] ℝ) (hf : ∀ i, ‖f i‖ ≤ 1)
    (x : SumL1 G) (i : ℕ) : coordinateTests f hf x i = f i (x i) := rfl

def headL1 (N : ℕ) : SumL1 G →L[ℝ] SumL1 G :=
  ∑ i ∈ Finset.range N, (lp.singleContinuousLinearMap ℝ G 1 i).comp (lp.evalCLM ℝ G 1 i)

def tailL1 (N : ℕ) : SumL1 G →L[ℝ] SumL1 G := ContinuousLinearMap.id ℝ _ - headL1 N

theorem headL1_eq_sum (N : ℕ) (x : SumL1 G) :
    headL1 N x = ∑ i ∈ Finset.range N, lp.single 1 i (x i) := by
  unfold headL1
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

@[simp] theorem headL1_apply (N : ℕ) (x : SumL1 G) (i : ℕ) :
    headL1 N x i = if i < N then x i else 0 := by
  rw [headL1_eq_sum, lp.coeFn_sum]
  simp [Finset.sum_apply, lp.single_apply]

@[simp] theorem tailL1_apply (N : ℕ) (x : SumL1 G) (i : ℕ) :
    tailL1 N x i = if N ≤ i then x i else 0 := by
  change x i - headL1 N x i = _
  rw [headL1_apply]
  split_ifs <;> simp_all
  all_goals omega

end WeakSequences

namespace WeakSequences
open Filter Topology
open scoped NNReal ENNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev ScalarC0 := NullSequences.C0 (H := ℝ)
open NullSequences

def initialOnes (N : ℕ) : ScalarC0 := ∑ i ∈ Finset.range N, single i (1 : ℝ)

@[simp] theorem initialOnes_apply (N i : ℕ) : initialOnes N i = if i < N then 1 else 0 := by
  simp [initialOnes, NullSequences.sum_apply, single_apply]

end WeakSequences

end LipschitzCounterexample
end

end OAI


