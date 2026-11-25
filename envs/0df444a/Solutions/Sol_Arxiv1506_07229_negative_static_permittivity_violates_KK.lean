-- Prove2me | solution 1 for Arxiv1506_07229.negative_static_permittivity_violates_KK
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:31:24.985881+00:00
-- url     : https://prove2.me/submissions/a0d91150-5e2f-4c4e-9777-6782643bea99

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem negative_static_permittivity_violates_KK (R : ℝ → ℂ)
    (hinf : Tendsto R atTop (𝓝 1)) (him : ∀ ω : ℝ, 0 ≤ ω → 0 ≤ (R ω).im)
    (hneg : (R 0).re < 0) :
    ¬ KKRelations R := by
  rintro ⟨Rinf, hR, hall⟩
  have h1 : (Rinf : ℂ) = 1 := tendsto_nhds_unique hR hinf
  have h1' : Rinf = 1 := by exact_mod_cast h1
  obtain ⟨hre, -⟩ := hall 0 le_rfl
  have hge : ∀ δ : ℝ, (1 : ℝ) ≤ Rinf + (2 / π) *
      ∫ x in Set.Ioi (0 : ℝ) \ Set.Ioo (0 - δ) (0 + δ), x * (R x).im / (x ^ 2 - 0 ^ 2) := by
    intro δ
    rw [h1']
    have : 0 ≤ ∫ x in Set.Ioi (0 : ℝ) \ Set.Ioo (0 - δ) (0 + δ), x * (R x).im / (x ^ 2 - 0 ^ 2) := by
      refine setIntegral_nonneg (measurableSet_Ioi.diff measurableSet_Ioo) ?_
      intro x hx
      have hx0 : 0 < x := hx.1
      have := him x hx0.le
      have hx2 : 0 < x ^ 2 - 0 ^ 2 := by nlinarith
      exact div_nonneg (mul_nonneg hx0.le this) hx2.le
    have : 0 ≤ (2 / π) * ∫ x in Set.Ioi (0 : ℝ) \ Set.Ioo (0 - δ) (0 + δ), x * (R x).im / (x ^ 2 - 0 ^ 2) := by
      have : 0 < π := Real.pi_pos
      positivity
    linarith
  have : (1 : ℝ) ≤ (R 0).re := ge_of_tendsto hre (Eventually.of_forall hge)
  linarith

end Arxiv1506_07229
open Arxiv1506_07229 in
theorem solution (R : ℝ → ℂ)
    (hinf : Tendsto R atTop (𝓝 1)) (him : ∀ ω : ℝ, 0 ≤ ω → 0 ≤ (R ω).im)
    (hneg : (R 0).re < 0) :
    ¬ KKRelations R := negative_static_permittivity_violates_KK R hinf him hneg
