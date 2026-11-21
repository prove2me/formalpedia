-- Prove2me | Definitions.Def_SourceProof_e0bce38e6a65980ddb5abfb5
-- name    : SourceProof_e0bce38e6a65980ddb5abfb5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:05:51.054203+00:00
-- url     : https://prove2.me/theorems/05de41af-fdd5-43c8-a677-b1a9326bcf85
-- title:
--   LevyStochCalc source module: SourceProof_e0bce38e6a65980ddb5abfb5
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped` comes from the `LevyStochCalc.Brownian.ItoOptionalStopping` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F001
import Definitions.Def_SourceProof_4158bbe01732caa4bdb467b2
import Definitions.Def_SourceProof_426ff55101b7b0df983e6be6
import Definitions.Def_SourceProof_56b29bc4b89062640594e854
import Definitions.Def_SourceProof_92bec27d240f0e5702c6d539

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Optional stopping for the Itô integral, for a stopping time of finite range

Cutting the integrand off at a stopping time that takes finitely many values below the horizon
subtracts, for each of those values `c`, the increment of the integral across `(c, T]` weighted
by the event `{τ = c}`. That weight is known at `c` and the cut integrand is carried by `(c, T]`,
so it passes inside the integral; the resulting sum telescopes into the integral evaluated at
`τ ∧ T`.

## Main statements

* `LevyStochCalc.Brownian.Ito.hitInd`, `cutTerm` — the weight and the cut integrand.
* `LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum` — the pathwise decomposition of the cut
  integrand.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped` — the identity.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Stopped

variable (τ : Ω → WithTop ℝ)

section Identity

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_e0bce38e6a65980ddb5abfb5
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
        (Probability.measurable_uncurry_stopped hτ hm)
        (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hp)
        (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
        - ∑ c ∈ J, hitInd τ c ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω) := by
  classical
  have hmS := LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm
  have hpS := _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hp
  have hqS := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P) (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H ω s) hq
  have hmI0 := LevyStochCalc.Brownian.Ito.measurable_indTerm hm 0 t
  have hpI0 := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indTerm ℱ hp (le_refl (0 : ℝ)) ht
  have hqI0 := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P) (fun ω s => LevyStochCalc.Brownian.Ito.abs_indTerm_le (H := H) 0 t ω s) hq
  have hmW := LevyStochCalc.Brownian.Ito.measurable_indTerm hmS 0 t
  have hpW := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indTerm ℱ hpS (le_refl (0 : ℝ)) ht
  have hqW := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P)
    (fun ω s => LevyStochCalc.Brownian.Ito.abs_indTerm_le (H := LevyStochCalc.Probability.stopped τ H) 0 t ω s) hqS
  set ι := {c : ℝ // c ∈ J} with hι
  have hmF : ∀ i : ι, Measurable (Function.uncurry (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t)) :=
    fun i => LevyStochCalc.Brownian.Ito.measurable_cutTerm τ hτ hm i.1 t
  have hpF : ∀ i : ι, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) :=
    fun i => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_cutTerm τ ℱ hτ hp (hJ0 i.1 i.2) (hJt i.1 i.2)
  have hqF : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P)
      (fun ω s => LevyStochCalc.Brownian.Ito.abs_cutTerm_le τ (H := H) i.1 t ω s) hq
  obtain ⟨hmSum, hpSum, hqSum, hSum⟩ := _root_.Prove2MeSourceProof.h_4158bbe01732caa4bdb467b2 W ℱ hℱ
    (fun i : ι => LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) hmF hpF hqF (Finset.univ : Finset ι) ht
  have hmD : Measurable (Function.uncurry fun ω u =>
      LevyStochCalc.Brownian.Ito.indTerm H 0 t ω u - ∑ i : ι, LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω u) := hmI0.sub hmSum
  have hpD : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      (fun ω u => LevyStochCalc.Brownian.Ito.indTerm H 0 t ω u - ∑ i : ι, LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω u) := hpI0.sub hpSum
  have hqD : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.indTerm H 0 t ω u - ∑ i : ι, LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293 (fun ω u => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hmI0 hmSum
      hqI0 hqSum
  have hpath : LevyStochCalc.Brownian.Ito.indTerm (LevyStochCalc.Probability.stopped τ H) 0 t
      = fun ω u => LevyStochCalc.Brownian.Ito.indTerm H 0 t ω u - ∑ i : ι, LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t ω u := by
    rw [_root_.Prove2MeSourceProof.h_56b29bc4b89062640594e854 τ H J hJ0 hJt hτJ]
    funext ω u
    congr 1
    exact (Finset.sum_coe_sort J fun c => LevyStochCalc.Brownian.Ito.cutTerm τ H c t ω u).symm
  have hterm : ∀ i : ι,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) (hmF i) (hpF i) (hqF i) t
        =ᵐ[P] fun ω => LevyStochCalc.Brownian.Ito.hitInd τ i.1 ω
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq i.1 ω) := by
    intro i
    have hc0 : 0 ≤ i.1 := hJ0 i.1 i.2
    have hct : i.1 < t := hJt i.1 i.2
    have hmIc := LevyStochCalc.Brownian.Ito.measurable_indTerm hm i.1 t
    have hpIc := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indTerm ℱ hp hc0 hct
    have hqIc := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P)
      (fun ω s => LevyStochCalc.Brownian.Ito.abs_indTerm_le (H := H) i.1 t ω s) hq
    have hpull := _root_.Prove2MeSourceProof.h_92bec27d240f0e5702c6d539 W ℱ hℱ hc0 hct
      (V := LevyStochCalc.Brownian.Ito.hitInd τ i.1) ⟨1, LevyStochCalc.Brownian.Ito.abs_hitInd_le_one τ i.1⟩ (LevyStochCalc.Brownian.Ito.measurable_hitInd τ hτ i.1)
      (LevyStochCalc.Brownian.Ito.stronglyMeasurable_hitInd τ hτ i.1) H hm hp hq hmIc hpIc hqIc
      (hmF i) (hpF i) (hqF i) ht
    have hloc := _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 W ℱ hℱ H hm hp hq hc0 hct
      hmIc hpIc hqIc ht
    filter_upwards [hpull, hloc] with ω hpullω hlocω
    have hpull' : LevyStochCalc.Brownian.Ito.hitInd τ i.1 ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.indTerm H i.1 t) hmIc hpIc hqIc t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) (hmF i) (hpF i) (hqF i) t ω :=
      hpullω
    have hloc' : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.indTerm H i.1 t) hmIc hpIc hqIc t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min t t) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min i.1 t) ω := hlocω
    rw [← hpull', hloc', min_self, min_eq_left hct.le]
  have hstep := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indTerm_zero W ℱ hℱ ht hmS hpS hqS hmW hpW hqW
  have hcongr := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hpath hmW hpW hqW hmD hpD hqD t
  have hsub := _root_.Prove2MeSourceProof.h_426ff55101b7b0df983e6be6 W ℱ hℱ hmI0 hmSum hpI0 hpSum hqI0 hqSum
    hmD hpD hqD ht
  have hI0 := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indTerm_zero W ℱ hℱ ht hm hp hq hmI0 hpI0 hqI0
  have hall : ∀ᵐ ω ∂P, ∀ i : ι,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Brownian.Ito.cutTerm τ H i.1 t) (hmF i) (hpF i) (hqF i) t ω
        = LevyStochCalc.Brownian.Ito.hitInd τ i.1 ω * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq i.1 ω) :=
    MeasureTheory.ae_all_iff.mpr hterm
  filter_upwards [hstep, hsub, hI0, hSum, hall] with ω h1 h3 h4 h5 h6
  have h2 := congrFun hcongr ω
  rw [← h1, h2, h3, h4, h5, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h6 i,
    Finset.sum_coe_sort J fun c => LevyStochCalc.Brownian.Ito.hitInd τ c ω
      * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω)]
end Identity

end Stopped

end LevyStochCalc.Brownian.Ito


