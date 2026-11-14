-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreSeriesIntegrable
-- name    : row23_rh_supp_RHLegendreSeriesIntegrable
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:09:53.990707+00:00
-- url     : https://prove2.me/theorems/8e6b89c1-8d94-4fa7-b619-684f95962075
-- title:
--   Row 23 RH support: RHLegendreSeriesIntegrable
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreIntegralSeries
set_option autoImplicit false
namespace DusartLegendreSmoothing
open MeasureTheory intervalIntegral Filter
open scoped Topology
 theorem interval_tsum_integrable_of_finite_norm_bound {ι : Type*} [Countable ι]
    (F : ι → ℝ → ℂ) (g : ℝ → ℝ)
    (hF : ∀ i, IntervalIntegrable (F i) volume 0 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hbound : ∀ S : Finset ι, ∀ t ∈ Set.Ioc (0:ℝ) 1, (∑ i ∈ S, ‖F i t‖) ≤ g t) :
    IntervalIntegrable (fun t : ℝ => ∑' i, F i t) volume 0 1 := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  let μ := volume.restrict (Set.Ioc (0:ℝ) 1)
  have hFi (i : ι) : Integrable (F i) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp (hF i)
  have hgi : Integrable g μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp hg
  have hs (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) : Summable (fun i => ‖F i t‖) :=
    summable_of_sum_le (fun i => norm_nonneg _) (fun S => hbound S t ht)
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun S : Finset ι => ∑ i ∈ S, F i t) atTop (𝓝 (∑' i, F i t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hs t ht).of_norm.hasSum
  have hmeas : AEStronglyMeasurable (fun t => ∑' i, F i t) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun S : Finset ι => S.aestronglyMeasurable_fun_sum (fun i hi => (hFi i).aestronglyMeasurable)) hlim
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mpr
  apply hgi.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (norm_tsum_le_tsum_norm (hs t ht)).trans
    (Real.tsum_le_of_sum_le (fun i => norm_nonneg _) (fun S => hbound S t ht))
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.interval_tsum_integrable_of_finite_norm_bound


