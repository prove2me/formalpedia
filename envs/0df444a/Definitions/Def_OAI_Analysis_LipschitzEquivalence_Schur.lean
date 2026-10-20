-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
-- name    : OAI_Analysis_LipschitzEquivalence_Schur
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:09:32.359496+00:00
-- url     : https://prove2.me/theorems/b647f00f-566d-48be-9d60-762b976c6137
-- title:
--   Weakly null sequences, completely continuous operators and real ℓ¹
-- statement:
--   Weak sequential notions for real normed spaces and basic tools on $\ell^1=\ell^1(\mathbb N,\mathbb R)$.
--
--   1. **Weak notions.** A sequence $u_n$ is weakly null if $f(u_n)\to0$ for every bounded functional $f$, and weakly Cauchy if every $(f(u_n))_n$ is Cauchy. An operator $T$ is completely continuous if it maps weakly null sequences to norm-null sequences, $\|Tu_n\|\to0$. A space is weakly sequentially complete if every weakly Cauchy sequence converges weakly to some $x$.
--   2. **Pairings.** For a sequence $b$ with $|b_i|\le1$, the pairing $x\mapsto\sum_ib_ix_i$ is a bounded functional on $\ell^1$:
--   $$
--   \Bigl|\sum_ib_ix_i\Bigr|\le\sum_i|x_i| .
--   $$
--   3. **Truncation.** $\mathrm{trunc}_N(x)=\sum_{i<N}x_ie_i$ keeps the first $N$ coordinates and is a bounded operator on $\ell^1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/Schur.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/Schur.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def WeakNull (u : ℕ → E) : Prop :=
  ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 0)

def CompletelyContinuous (T : E →L[ℝ] F) : Prop :=
  ∀ u : ℕ → E, WeakNull u → Tendsto (fun n => T (u n)) atTop (𝓝 0)

def WeakCauchy (u : ℕ → E) : Prop :=
  ∀ f : E →L[ℝ] ℝ, CauchySeq (fun n => f (u n))

def WeakSequentiallyComplete (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ u : ℕ → E, WeakCauchy u → ∃ x : E,
    ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))

abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

theorem summable_norm (x : RealL1) : Summable (fun i => |x i|) := by
  simpa using (lp.hasSum_norm (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x).summable

theorem summable_pair (b : ℕ → ℝ) (hb : ∀ i, |b i| ≤ 1) (x : RealL1) :
    Summable (fun i => b i * x i) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ (summable_norm x)
  intro i
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hb i)

def pairing (b : ℕ → ℝ) (hb : ∀ i, |b i| ≤ 1) : RealL1 →L[ℝ] ℝ :=
  ({ toFun := fun x => ∑' i, b i * x i
     map_add' := by
       intro x y
       change (∑' i, b i * (x i + y i)) = _
       simp_rw [mul_add]
       exact (summable_pair b hb x).tsum_add (summable_pair b hb y)
     map_smul' := by
       intro c x
       change (∑' i, b i * (c * x i)) = c * ∑' i, b i * x i
       simp_rw [mul_left_comm (b _) c]
       exact tsum_mul_left } : RealL1 →ₗ[ℝ] ℝ).mkContinuous 1 (by
         intro x
         simp only [one_mul]
         calc
           ‖∑' i, b i * x i‖ ≤ ∑' i, |b i * x i| :=
             norm_tsum_le_tsum_norm (summable_pair b hb x).norm
           _ ≤ ∑' i, |x i| := Summable.tsum_le_tsum
             (fun i => by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hb i))
             (summable_pair b hb x).abs (summable_norm x)
           _ = ‖x‖ := (WeightedGraph.norm_l1 x).symm)

@[simp] theorem pairing_apply (b : ℕ → ℝ) (hb : ∀ i, |b i| ≤ 1) (x : RealL1) :
    pairing b hb x = ∑' i, b i * x i := rfl

def trunc (N : ℕ) : RealL1 →L[ℝ] RealL1 :=
  ∑ i ∈ Finset.range N,
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 1 i).comp
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i)

theorem trunc_eq_sum (N : ℕ) (x : RealL1) :
    trunc N x = ∑ i ∈ Finset.range N, lp.single 1 i (x i) := by
  unfold trunc
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

@[simp] theorem trunc_apply (N : ℕ) (x : RealL1) (i : ℕ) :
    trunc N x i = if i < N then x i else 0 := by
  rw [trunc_eq_sum, lp.coeFn_sum]
  simp [Finset.sum_apply, lp.single_apply]

end WeakSequences

end LipschitzCounterexample
end

end OAI


