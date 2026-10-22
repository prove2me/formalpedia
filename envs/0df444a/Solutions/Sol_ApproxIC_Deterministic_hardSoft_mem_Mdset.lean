-- Prove2me | solution 1 for ApproxIC.Deterministic.hardSoft_mem_Mdset
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:31:34.673379+00:00
-- url     : https://prove2.me/submissions/367babf4-993e-4a75-a50d-e270e9e73334

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft

set_option autoImplicit false
open ApproxIC.Deterministic

theorem solution (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 ≤ ε)
    (r : ℝ) (hr : r ∈ Set.Icc 0 M.vbar) :
    hardSoft r (r + ε) ∈ Mdset M ε := by
  obtain ⟨hr0, hrv⟩ := hr
  have hxm : Measurable (hardSoft r (r + ε)).x := by
    show Measurable (fun v : ℝ => if r ≤ v then (1 : ℝ) else 0)
    exact Measurable.ite measurableSet_Ici measurable_const measurable_const
  have htm : Measurable (hardSoft r (r + ε)).t := by
    show Measurable (fun v : ℝ => if v < r then (0 : ℝ) else if v < r + ε then v else r + ε)
    exact Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Iio measurable_id measurable_const)
  have hx01 : ∀ v : ℝ, (hardSoft r (r + ε)).x v = 0 ∨ (hardSoft r (r + ε)).x v = 1 := by
    intro v
    show (if r ≤ v then (1 : ℝ) else 0) = 0 ∨ (if r ≤ v then (1 : ℝ) else 0) = 1
    split_ifs <;> simp
  refine ⟨⟨⟨hxm, htm, fun v _ => ?_⟩, ?_, ?_⟩, fun v _ => hx01 v⟩
  · rcases hx01 v with h | h <;> rw [h] <;> simp
  · intro v hv
    show 0 ≤ v * (if r ≤ v then (1 : ℝ) else 0) - (if v < r then (0 : ℝ) else if v < r + ε then v else r + ε)
    split_ifs <;> nlinarith [hv.1]
  · intro v hv v' hv'
    show v * (if r ≤ v' then (1 : ℝ) else 0) - (if v' < r then (0 : ℝ) else if v' < r + ε then v' else r + ε) - ε ≤
      v * (if r ≤ v then (1 : ℝ) else 0) - (if v < r then (0 : ℝ) else if v < r + ε then v else r + ε)
    split_ifs <;> nlinarith
