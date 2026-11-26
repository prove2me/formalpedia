-- Prove2me | solution 1 for Auto.aux_integral_wienerEnvelope_le_card_mul_of_addHaar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:26.044802+00:00
-- url     : https://prove2.me/submissions/c263f970-8ff1-41a2-b30e-4f892616bc67

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_wienerEnvelope_le_sum_of_cover
public import Theorems.Thm_P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F : Type*}
    [NormedAddCommGroup E] [ProperSpace E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddRightInvariant (volume : Measure E)] [NormedAddCommGroup F]
    {f : E → F} (hf : Continuous f) {r s : ℝ} (hr : 0 < r)
    (hs : 0 ≤ s) (hfr : Integrable (wienerEnvelope f r)) (t : Finset E)
    (hcover : ∀ y ∈ closedBall (0 : E) s, ∃ z ∈ t, y ∈ closedBall z r) :
    (∫ x, wienerEnvelope f s x) ≤ (t.card : ℝ) * ∫ x, wienerEnvelope f r x := by
  have hsint : Integrable (wienerEnvelope f s) :=
    aux_integrable_wienerEnvelope_of_integrable' hf hr hs hfr
  have hsum : Integrable (fun x : E => ∑ z ∈ t, wienerEnvelope f r (x + z)) := by
    exact integrable_finsetSum t fun z hz => hfr.comp_add_right z
  calc
    (∫ x, wienerEnvelope f s x) ≤ ∫ x, ∑ z ∈ t, wienerEnvelope f r (x + z) :=
      integral_mono hsint hsum (fun x =>
        aux_wienerEnvelope_le_sum_of_cover hf (le_of_lt hr) hs t hcover x)
    _ = ∑ z ∈ t, ∫ x, wienerEnvelope f r (x + z) :=
      integral_finsetSum t fun z hz => hfr.comp_add_right z
    _ = ∑ _z ∈ t, ∫ x, wienerEnvelope f r x := by
      simp_rw [integral_add_right_eq_self]
    _ = (t.card : ℝ) * ∫ x, wienerEnvelope f r x := by simp
end Auto
