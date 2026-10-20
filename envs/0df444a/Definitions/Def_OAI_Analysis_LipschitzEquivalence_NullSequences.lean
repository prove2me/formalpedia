-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
-- name    : OAI_Analysis_LipschitzEquivalence_NullSequences
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:07:03.428232+00:00
-- url     : https://prove2.me/theorems/faa4bca3-4250-42a9-889d-378292a74840
-- title:
--   Null sequences in a normed group
-- statement:
--   The space $c_0(H)$ of sequences in a normed group $H$ tending to $0$, realized as continuous functions on $\mathbb N$ vanishing at infinity with the sup norm.
--
--   1. **Basic facts.** Every sequence $s$ with $s_i\to0$ defines an element of $c_0(H)$, $\|s_i\|\le\|s\|$, and $\|s\|\le c$ iff $\|s_i\|\le c$ for all $i$ (for $c\ge0$). Evaluation at $i$ is additive, and for real normed spaces it is a bounded linear map of norm at most $1$.
--   2. **Single entries.** For $i\in\mathbb N$ and $x\in H$, $\mathrm{single}_i(x)$ is the sequence with $x$ in place $i$ and $0$ elsewhere; it is an isometry in $x$:
--   $$
--   \|\mathrm{single}_i(x)\|=\|x\| .
--   $$
--   3. **Truncation.** $\mathrm{trunc}_N(s)=\sum_{i<N}\mathrm{single}_i(s_i)$ keeps the first $N$ entries; $\|s-\mathrm{trunc}_N s\|\le c$ whenever $\|s_i\|\le c$ for all $i\ge N$, and $\mathrm{trunc}_N s\to s$.
--   4. **Separability.** $c_0(H)$ is separable when $H$ is.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/NullSequences.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/NullSequences.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace

namespace OAI

universe uH uIndex

noncomputable section
namespace LipschitzCounterexample

namespace NullSequences

open Filter
open scoped Topology
variable {H : Type uH} [NormedAddCommGroup H]

abbrev C0 := ZeroAtInftyContinuousMap ℕ H

def ofTendsto (s : ℕ → H) (hs : Tendsto s atTop (𝓝 0)) : C0 (H := H) where
  toFun := s
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by simpa [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using hs

theorem tendsto_zero (s : C0 (H := H)) : Tendsto s atTop (𝓝 0) := by
  simpa [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using zero_at_infty s

theorem norm_apply_le (s : C0 (H := H)) (i : ℕ) : ‖s i‖ ≤ ‖s‖ :=
  BoundedContinuousFunction.norm_coe_le_norm s.toBCF i

theorem norm_le {s : C0 (H := H)} {c : ℝ} (hc : 0 ≤ c) :
    ‖s‖ ≤ c ↔ ∀ i, ‖s i‖ ≤ c :=
  BoundedContinuousFunction.norm_le hc

def evalAddHom (i : ℕ) : C0 (H := H) →+ H where
  toFun := fun s => s i
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[simp] theorem sum_apply {ι : Type uIndex} (f : ι → C0 (H := H)) (S : Finset ι) (i : ℕ) :
    (∑ j ∈ S, f j) i = ∑ j ∈ S, f j i := map_sum (evalAddHom i) _ _

def single (i : ℕ) (x : H) : C0 (H := H) :=
  ofTendsto (fun j => if j = i then x else 0) (by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with j hj
    simp [ne_of_gt hj])

@[simp] theorem single_apply (i j : ℕ) (x : H) :
    single i x j = if j = i then x else 0 := rfl

@[simp] theorem single_zero (i : ℕ) : single i (0 : H) = 0 := by
  ext j
  simp

@[simp] theorem single_sub (i : ℕ) (x y : H) :
    single i (x - y) = single i x - single i y := by
  ext j
  by_cases hj : j = i <;> simp [hj]

@[simp] theorem norm_single (i : ℕ) (x : H) : ‖single i x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (norm_le (norm_nonneg x)).2
    intro j
    by_cases hj : j = i <;> simp [hj]
  · simpa using norm_apply_le (single i x) i

theorem isometry_single (i : ℕ) : Isometry (single (H := H) i) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← single_sub, norm_single, dist_eq_norm]

def trunc (N : ℕ) (s : C0 (H := H)) : C0 (H := H) :=
  ∑ i ∈ Finset.range N, single i (s i)

@[simp] theorem trunc_apply (N i : ℕ) (s : C0 (H := H)) :
    trunc N s i = if i < N then s i else 0 := by
  simp [trunc, sum_apply, single_apply]

theorem norm_sub_trunc_le (s : C0 (H := H)) (N : ℕ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i ≥ N, ‖s i‖ ≤ c) : ‖s - trunc N s‖ ≤ c := by
  apply (norm_le hc).2
  intro i
  by_cases hi : i < N
  · simp [hi, hc]
  · simpa [hi] using h i (Nat.le_of_not_gt hi)

theorem tendsto_trunc (s : C0 (H := H)) : Tendsto (fun N => trunc N s) atTop (𝓝 s) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hs := (tendsto_zero s).norm
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hs (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_comm, dist_eq_norm]
  apply lt_of_le_of_lt (norm_sub_trunc_le s n (le_of_lt (half_pos hε)) ?_)
    (half_lt_self hε)
  intro i hi
  have h := hN i (hn.trans hi)
  simpa only [norm_zero, Real.dist_eq, sub_zero, abs_norm] using h.le

variable [NormedSpace ℝ H]

def evalCLM (i : ℕ) : C0 (H := H) →L[ℝ] H :=
  ({ toFun := fun s => s i
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : C0 (H := H) →ₗ[ℝ] H).mkContinuous
    1 (fun s => by simpa using norm_apply_le s i)

instance [TopologicalSpace.SeparableSpace H] : TopologicalSpace.SeparableSpace (C0 (H := H)) := by
  let S : Set (C0 (H := H)) := ⋃ i : ℕ, Set.range (single (H := H) i)
  have hs : TopologicalSpace.IsSeparable S :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (isometry_single i).continuous)
  have hd : Dense (Submodule.span ℝ S : Set (C0 (H := H))) := by
    intro s
    apply isClosed_closure.mem_of_tendsto (tendsto_trunc s)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    exact Set.mem_iUnion.2 ⟨i, ⟨s i, rfl⟩⟩
  exact hd.isSeparable_iff.mp hs.span

end NullSequences

end LipschitzCounterexample
end

end OAI


