-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F001
-- name    : LevyStochCalc_Ito_PicardContractionFixedPoint_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:05:41.027158+00:00
-- url     : https://prove2.me/theorems/8dc51640-0f33-493d-b683-abb44ce4b7e7
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardContractionFixedPoint
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardContractionFixedPoint. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F000
import Definitions.Def_SourceProof_34982f0b1ca1f7510c2d1e94
import Definitions.Def_SourceProof_7ac7f2227657b4f9e275e978
import Definitions.Def_SourceProof_b732528cf57a7c0dad8dceb7
import Definitions.Def_SourceProof_e264a15a5a2a191954307942
import Definitions.Def_SourceProof_eb0e2237c948399f92e4f8c8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The fixed point of the Picard step

The limit `picardLimit` of the Picard iterates is jointly measurable, progressively measurable and
of finite Bielecki norm, and the Bielecki distance between the step taken along it and the limit
itself vanishes, so the step and the limit agree almost surely at every time of the window. The
step contracts between two raw state processes and therefore respects almost sure equality of its
input, which promotes that agreement to the statement that the process built over the limit solves
the Picard equation along its own path.

## Main statements

* `picardLimit` — the limit of the Picard iterates.
* `bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero` — the limit is a fixed point in norm.
* `picardSelfMapRaw_picardLimit_ae_eq` — the fixed point is realised by a process of the space.
* `picardSelfMapRaw_isFixedPoint` — the fixed point solves its own Picard equation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-! ### The fixed point -/

variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)

/-- **The fixed point is realised by a process of the space.** The raw self-map applied to the
Picard limit is a jointly measurable, adapted, almost surely càdlàg process which agrees with the
limit almost surely at every time of the window. -/
theorem picardSelfMapRaw_picardLimit_ae_eq {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
          (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
          (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
            x₀ hT X₀)
          (_root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
            hβ hT X₀ hq)).X t ω i
        = picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i := by
  have hYm := measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hYa := progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hYb := _root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  have hslice : ∀ (u : ℝ) (i : Fin n), Measurable fun ω =>
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT.le x₀ u ω i
        - picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ u ω i :=
    fun u i => (_root_.Prove2MeSourceProof.h_e264a15a5a2a191954307942 W N ℱ' hℱW hℱN coeffs hReg hLip x₀
      hYm hYa hYb hT.le u i).sub (measurable_slice_of_uncurry hYm u i)
  have hzero := _root_.Prove2MeSourceProof.h_eb0e2237c948399f92e4f8c8 (P := P) hslice
    (_root_.Prove2MeSourceProof.h_7ac7f2227657b4f9e275e978 W N ℱ' hℱW hℱN hℱ0 hnull coeffs
      hReg hLip x₀ hβ hT X₀ hq) ht
  filter_upwards [_root_.Prove2MeSourceProof.h_b732528cf57a7c0dad8dceb7 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
    hYm hYa hYb t, hzero] with ω hmod hz i
  rw [congrFun hmod i, ← sub_eq_zero]
  exact hz i
/-! ### The step respects almost sure equality of its input -/

/-! ### The fixed point solves its own Picard equation -/

end LevyStochCalc.Ito.Picard


