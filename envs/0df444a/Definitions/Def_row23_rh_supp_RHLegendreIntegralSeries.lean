-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreIntegralSeries
-- name    : row23_rh_supp_RHLegendreIntegralSeries
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:09:20.09717+00:00
-- url     : https://prove2.me/theorems/46c8651c-387b-4459-b1f3-23e331bf47e4
-- title:
--   Row 23 RH support: RHLegendreIntegralSeries
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSmoothing
set_option autoImplicit false
namespace DusartLegendreSmoothing
open MeasureTheory intervalIntegral
 theorem interval_tsum_of_finite_norm_bound {ι : Type*} [Countable ι]
    (F : ι → ℝ → ℂ) (g : ℝ → ℝ)
    (hF : ∀ i, IntervalIntegrable (F i) volume 0 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hbound : ∀ S : Finset ι, ∀ t ∈ Set.Ioc (0:ℝ) 1, (∑ i ∈ S, ‖F i t‖) ≤ g t) :
    (∫ t : ℝ in 0..1, ∑' i, F i t) = ∑' i, ∫ t : ℝ in 0..1, F i t := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  let μ := volume.restrict (Set.Ioc (0:ℝ) 1)
  have hFi (i : ι) : Integrable (F i) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp (hF i)
  have hgi : Integrable g μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp hg
  have hs : Summable (fun i => ∫ t, ‖F i t‖ ∂μ) := by
    apply summable_of_sum_le (c := ∫ t, g t ∂μ) (fun i => integral_nonneg (fun t => norm_nonneg _))
    intro S
    have hsum : Integrable (fun t => ∑ i ∈ S, ‖F i t‖) μ :=
      integrable_finsetSum S (fun i hi => (hFi i).norm)
    rw [←MeasureTheory.integral_finsetSum S (fun i hi => (hFi i).norm)]
    apply integral_mono_ae hsum hgi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hbound S t ht
  have h := integral_tsum_of_summable_integral_norm hFi hs
  simpa only [intervalIntegral.integral_of_le h01] using h.symm
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.interval_tsum_of_finite_norm_bound


