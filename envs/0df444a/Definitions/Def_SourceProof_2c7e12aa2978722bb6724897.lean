-- Prove2me | Definitions.Def_SourceProof_2c7e12aa2978722bb6724897
-- name    : SourceProof_2c7e12aa2978722bb6724897
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:41:39.263359+00:00
-- url     : https://prove2.me/theorems/b445453d-ece7-4fcf-a066-a229f9cd6837
-- title:
--   LevyStochCalc source module: SourceProof_2c7e12aa2978722bb6724897
-- statement:
--   The original source theorem `LevyStochCalc.Driver.ae_eq_zero_of_perp_joint` comes from the `LevyStochCalc.Driver.JointComplement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPBrownian_F000
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000
import Definitions.Def_LevyStochCalc_Driver_JointMultidim_F000
import Definitions.Def_LevyStochCalc_Poisson_PerpBridge_F000
import Definitions.Def_SourceProof_200c032984224ec4322972ff
import Definitions.Def_SourceProof_e989b49717429f35e3149a35

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The orthogonal complement of the joint ranges

The times of a finite family of Brownian coordinate values, together with the horizon, sort into
an increasing grid whose last point is the horizon, and a finite family of window sets sits
inside a single window of finite mark intensity. A product of a Brownian cylinder character and a
window character is therefore a value character along the grid, and the joint grid induction
applies. The clamping horizon of that induction is strictly beyond the last grid point, so the
orthogonality hypothesis is carried up by the marked perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν] {T : ℝ}

section MarkSet

end MarkSet

section Complement

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)


theorem _root_.Prove2MeSourceProof.h_2c7e12aa2978722bb6724897 [Nonempty E] (D : LevyDriver P d ν) (hd : 0 < d) (hT : 0 < T)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hperp : ∀ i, PerpItoIntegrals (D.W.W i) (Brownian.augFiltration D.filtration P)
      (D.isBrownianFiltration_aug i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T,
      ∫ ω, Z ω * G'.integral D.N D.isPoissonFiltration_aug ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    Z =ᵐ[P] 0 := by
  have hfeq : LevyStochCalc.Brownian.augFiltration D.filtration P T
      = LevyStochCalc.Probability.aug (D.filtration T) ‹MeasurableSpace Ω› P := by
    change LevyStochCalc.Probability.aug (D.filtration (max T 0)) ‹MeasurableSpace Ω› P = _
    rw [max_eq_left hT.le]
  have hZ2C : MemLp (fun ω => ((Z ω : ℝ) : ℂ)) 2 P := by
    refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hZ2.1, ?_⟩
    rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ω => Complex.norm_real (Z ω))]
    exact hZ2.2
  have hZmC : AEStronglyMeasurable[LevyStochCalc.Probability.aug (D.filtration T) ‹MeasurableSpace Ω› P]
      (fun ω => ((Z ω : ℝ) : ℂ)) P := by
    rw [← hfeq]
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable hZm
  have hzero := (_root_.Prove2MeSourceProof.h_200c032984224ec4322972ff D) T (hZ2C.integrable (by norm_num)) hZmC
    fun F G w v => _root_.Prove2MeSourceProof.h_e989b49717429f35e3149a35 D.W D.N (LevyStochCalc.Brownian.augFiltration D.filtration P)
      hd D.isBrownianFiltration_aug (fun hc => D.isBrownianFiltration_combineBM_aug hc)
      D.isPoissonFiltration_aug (fun _ ht => D.augFiltration_le_of_nonpos ht)
      (fun _ hs h0 => D.measurableSet_augFiltration_of_null hs h0) hT hZ2 hZm hperp hZcomp hZ0
      F G w v
  filter_upwards [hzero] with ω hω
  have hc : ((Z ω : ℝ) : ℂ) = 0 := hω
  exact_mod_cast hc
end Complement

end LevyStochCalc.Driver


