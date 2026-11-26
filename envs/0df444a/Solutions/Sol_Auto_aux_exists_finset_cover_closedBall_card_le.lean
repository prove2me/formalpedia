-- Prove2me | solution 1 for Auto.aux_exists_finset_cover_closedBall_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:39.437277+00:00
-- url     : https://prove2.me/submissions/c015f75b-a2d1-48c8-974c-a364dc27fc25

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_card_le_sharp_packing

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin d)),
      ((closedBall (0 : EuclideanSpace ℝ (Fin d)) s : Set _) ⊆
        ⋃ c ∈ t, closedBall c r) ∧
      (t.card : ℝ) ≤ (3 * s / r) ^ d := by
  let E := EuclideanSpace ℝ (Fin d)
  let A : Set E := closedBall 0 s
  let ε : NNReal := r.toNNReal / 2
  have hε : ε ≠ 0 := by
    dsimp [ε]
    exact div_ne_zero (ne_of_gt (Real.toNNReal_pos.mpr hr)) (by norm_num)
  obtain ⟨C, hCA, hCfin, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hε (isCompact_closedBall (0 : E) s)
  have htwo : 2 * ε = r.toNNReal := by
    dsimp [ε]
    field_simp
  have hpack : Metric.packingNumber r.toNNReal A ≤ C.encard := by
    rw [← htwo]
    exact (Metric.packingNumber_two_mul_le_externalCoveringNumber ε A).trans
      hCcover.externalCoveringNumber_le_encard
  have hpack_lt : Metric.packingNumber r.toNNReal A < ⊤ :=
    hpack.trans_lt hCfin.encard_lt_top
  have hpack_ne : Metric.packingNumber r.toNNReal A ≠ ⊤ := ne_of_lt hpack_lt
  let S : Set E := Metric.maximalSeparatedSet r.toNNReal A
  have hSfin : S.Finite := by
    apply Set.encard_lt_top_iff.mp
    rw [show S = Metric.maximalSeparatedSet r.toNNReal A from rfl,
      Metric.encard_maximalSeparatedSet hpack_ne]
    exact hpack_lt
  refine ⟨hSfin.toFinset, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hcS, hxc⟩ := Metric.isCover_maximalSeparatedSet hpack_ne hx
    refine Set.mem_iUnion₂.2 ⟨c, hSfin.mem_toFinset.mpr hcS, ?_⟩
    rw [Metric.mem_closedBall]
    simpa only [coe_nndist, Real.coe_toNNReal r hr.le] using
      (NNReal.coe_le_coe.mpr (edist_le_coe.mp hxc))
  · apply aux_card_le_sharp_packing hr hrs
    · intro c hc
      have hcA : c ∈ A := Metric.maximalSeparatedSet_subset (hSfin.mem_toFinset.mp hc)
      simpa [A, Metric.mem_closedBall, dist_zero_right] using hcA
    · intro c hc e he hce
      have hsep : (r.toNNReal : ℝ≥0∞) < edist c e :=
        Metric.isSeparated_maximalSeparatedSet
          (hSfin.mem_toFinset.mp hc) (hSfin.mem_toFinset.mp he) hce
      rw [edist_nndist] at hsep
      have hsepNN : r.toNNReal < nndist c e := ENNReal.coe_lt_coe.mp hsep
      simpa only [coe_nndist, Real.coe_toNNReal r hr.le, dist_eq_norm] using
        le_of_lt (NNReal.coe_lt_coe.mpr hsepNN)
end Auto
