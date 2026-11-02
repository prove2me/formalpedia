-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_CompactStrongConvergenceCleanV1
-- name    : MarkovProcess_V3HRepair_CompactStrongConvergenceCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:44:48.207916+00:00
-- url     : https://prove2.me/theorems/bd659292-5b75-4188-b336-014b5fa8af28
-- title:
--   Verified MarkovProcess source repair: CompactStrongConvergenceCleanV1
-- statement:
--   A compactness-based bound gives eventual uniform control of a family of semigroup operators over a compact set. The module proves the exact quantified Lean convergence lemma.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted axiom-clean proof module V3HRepaired.CompactStrongConvergenceCleanV1, archived SHA-256 1e15c1079066a2a84c2abef5ad2325009f283b730343aeab428e28b7313c6f5f.

import Mathlib
open Filter Topology

namespace MarkovProcess.Semigroup

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Equibounded strong convergence to zero is uniform on compact sets.**  If the operators
`T i` share the bound `‖T i‖ ≤ C` and `T i x → 0` for every vector `x`, then for every compact
set `K` and every `ε > 0` the estimate `‖T i x‖ ≤ ε` holds for all `x ∈ K` simultaneously,
eventually along the index filter. -/
theorem eventually_forall_mem_norm_apply_le_of_isCompact {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] F) {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C)
    (hT : ∀ x, Tendsto (fun i ↦ T i x) l (𝓝 0))
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x ∈ K, ‖T i x‖ ≤ ε := by
  have hCpos : (0 : ℝ) < |C| + 1 := by positivity
  set δ : ℝ := ε / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨s, -, hsfin, hcover⟩ :=
    hK.elim_finite_subcover_image (c := fun y : E ↦ Metric.ball y δ)
      (fun _ _ ↦ Metric.isOpen_ball)
      (fun y hy ↦ Set.mem_iUnion₂.2 ⟨y, hy, Metric.mem_ball_self hδ⟩)
  have hfin : ∀ᶠ i in l, ∀ y ∈ s, ‖T i y‖ ≤ ε / 2 := by
    rw [Filter.eventually_all_finite hsfin]
    intro y _
    filter_upwards [NormedAddGroup.tendsto_nhds_zero.mp (hT y) (ε / 2) (by positivity)]
      with i hi
    exact hi.le
  filter_upwards [hfin] with i hi x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  have hdist : ‖x - y‖ ≤ δ := by
    rw [← dist_eq_norm]
    exact (Metric.mem_ball.1 hxy).le
  have hsplit : T i x = T i y + T i (x - y) := by
    rw [← map_add]
    congr 1
    abel
  have hbound : ‖T i (x - y)‖ ≤ ε / 2 := by
    calc
      ‖T i (x - y)‖ ≤ ‖T i‖ * ‖x - y‖ := (T i).le_opNorm _
      _ ≤ (|C| + 1) * δ := by
        refine mul_le_mul ?_ hdist (norm_nonneg _) hCpos.le
        exact (hC i).trans (by linarith [le_abs_self C])
      _ = ε / 2 := by
        rw [hδdef]
        field_simp
  calc
    ‖T i x‖ = ‖T i y + T i (x - y)‖ := by rw [hsplit]
    _ ≤ ‖T i y‖ + ‖T i (x - y)‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hi y hy) hbound
    _ = ε := add_halves ε

end MarkovProcess.Semigroup

#print axioms MarkovProcess.Semigroup.eventually_forall_mem_norm_apply_le_of_isCompact


