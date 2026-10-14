-- Prove2me | solution 1 for ActuarialValuation.ipInfinitePanjer_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:16:27.449987+00:00
-- url     : https://prove2.me/submissions/b0078c05-054a-4dbb-946a-89b0673855e8

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_actuarial_ipPoisson
import Definitions.Def_actuarial_ipGeo
import Definitions.Def_actuarial_ipCompound
import Definitions.Def_actuarial_ipGeoRHS
import Definitions.Def_actuarial_ipPoiRHS
import Theorems.Thm_ActuarialValuation_ipPoi_zero_atom
import Theorems.Thm_ActuarialValuation_ipGeometric_Panjer
import Theorems.Thm_ActuarialValuation_ipPoisson_Panjer

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

/-- Assemble the zero-atom identity and both corrected Panjer recursions. -/
theorem solution (q l : ℝ) (f : ℕ → ℝ) (k : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hl : 0 ≤ l)
    (hf : ∀ n, 0 ≤ f n) (hs : (∑' n : ℕ, f n) = 1)
    (hk : 0 < k) :
    (ipCompound (ipPoisson l) f 0 = Real.exp (-l*(1-f 0))) ∧
    ((1-q*f 0)*ipCompound (ipGeo q) f k =
      ipGeoRHS q f (ipCompound (ipGeo q) f) k) ∧
    (ipCompound (ipPoisson l) f k =
      ipPoiRHS l f (ipCompound (ipPoisson l) f) k) := by
  have hsf : Summable f := by
    by_contra hn
    have hz : (∑' n : ℕ, f n) = 0 := tsum_eq_zero_of_not_summable hn
    linarith
  have hf1 : f 0 ≤ 1 := by
    have hb : f 0 ≤ ∑' n : ℕ, f n := by
      simpa using hsf.sum_le_tsum ({0} : Finset ℕ)
        (by intro n hn; exact hf n)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact ipPoi_zero_atom l f (hf 0) hf1
  · exact ipGeometric_Panjer q f k hq0 hq1 hf hs hk
  · exact ipPoisson_Panjer l f k hl hf hs hk
