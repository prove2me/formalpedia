-- Prove2me | solution 1 for Auto.aux_integral_wienerEnvelope_le_max_one_three_mul_div_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:43.725798+00:00
-- url     : https://prove2.me/submissions/8a2c96b5-70c5-46eb-879e-c657db77e280

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_wienerEnvelope_mono_radius
public import Theorems.Thm_Auto_aux_exists_finset_cover_closedBall_card_le
public import Theorems.Thm_Auto_aux_integrable_wienerEnvelope_of_integrable
public import Theorems.Thm_Auto_aux_integral_wienerEnvelope_le_card_mul

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hfr : Integrable (wienerEnvelope f r)) :
    (∫ x, wienerEnvelope f s x) ≤
      max 1 ((3 * s / r) ^ d) * ∫ x, wienerEnvelope f r x := by
  have hnon : 0 ≤ ∫ x, wienerEnvelope f r x :=
    integral_nonneg fun x ↦ aux_wienerEnvelope_nonneg hf (le_of_lt hr) x
  by_cases hsr : s ≤ r
  · have hsint : Integrable (wienerEnvelope f s) :=
      aux_integrable_wienerEnvelope_of_integrable hf hr (le_of_lt hs) hfr
    calc
      (∫ x, wienerEnvelope f s x) ≤ ∫ x, wienerEnvelope f r x :=
        integral_mono hsint hfr
          (fun x ↦ aux_wienerEnvelope_mono_radius hf (le_of_lt hs) hsr x)
      _ = 1 * ∫ x, wienerEnvelope f r x := (one_mul _).symm
      _ ≤ max 1 ((3 * s / r) ^ d) * ∫ x, wienerEnvelope f r x :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnon
  · have hrs : r ≤ s := le_of_not_ge hsr
    obtain ⟨t, htcover, htcard⟩ := aux_exists_finset_cover_closedBall_card_le hr hrs
    have hcover : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) s,
        ∃ z ∈ t, y ∈ closedBall z r := by
      intro y hy
      obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (htcover hy)
      exact ⟨z, hzt, hyz⟩
    calc
      (∫ x, wienerEnvelope f s x) ≤ (t.card : ℝ) * ∫ x, wienerEnvelope f r x :=
        aux_integral_wienerEnvelope_le_card_mul hf hr (le_of_lt hs) hfr t hcover
      _ ≤ (3 * s / r) ^ d * ∫ x, wienerEnvelope f r x :=
        mul_le_mul_of_nonneg_right htcard hnon
      _ ≤ max 1 ((3 * s / r) ^ d) * ∫ x, wienerEnvelope f r x :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hnon
end Auto
