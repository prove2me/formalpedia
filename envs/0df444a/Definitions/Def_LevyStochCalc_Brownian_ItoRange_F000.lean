-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoRange_F000
-- name    : LevyStochCalc_Brownian_ItoRange_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:46:38.369011+00:00
-- url     : https://prove2.me/theorems/94663667-fd15-4530-ae88-bfb85b680510
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoRange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoRange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_SourceProof_0a844334f53895dbf4245fb6
import Definitions.Def_SourceProof_6afbd3f9a4aa317ea9c9ba3c
import Definitions.Def_SourceProof_7aea30f549f53f05062f1907
import Definitions.Def_SourceProof_8b64fc95ec4c1a34f817a2e0
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8
import Definitions.Def_SourceProof_f0468e0adacb16d8cd5e45b1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the Itô integral on a horizon

An integrand supported in `[0, T]`, jointly and progressively measurable and of finite energy,
is admissible for the Itô integral up to `T`. Such integrands are closed under sums and scalar
multiples, and the integral is additive and homogeneous on them, so their integrals form a
submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence of integrands to
an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- An integrand admissible for the Itô integral, supported in the horizon `[0, T]`. -/
structure HorizonIntegrand (P : Measure Ω) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) where
  /-- The underlying process. -/
  toFun : Ω → ℝ → ℝ
  /-- Joint measurability in the sample point and the time. -/
  measurable_uncurry : Measurable (Function.uncurry toFun)
  /-- Progressive measurability for the filtration. -/
  progressive : Probability.ProgressivelyMeasurable ℱ toFun
  /-- The process vanishes off the horizon. -/
  vanishing : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → toFun ω s = 0
  /-- The energy on the horizon is finite. -/
  energy_ne_top : energy P T toFun ≠ ⊤
section Energy

variable {T : ℝ}

/-- A deterministic constant process is progressively measurable. -/
theorem progressivelyMeasurable_const (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (c : ℝ) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => c) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  exact Measurable.stronglyMeasurable
    ((measurable_const.indicator measurableSet_Iic).comp measurable_snd)
omit [IsProbabilityMeasure P] in
/-- An integrand dominated by twice the sum of two finite energies has finite energy. -/
theorem energy_ne_top_of_bound {H₁ H₂ K : Ω → ℝ → ℝ}
    (hbound : ∀ ω s, (‖K ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (h1 : energy P T H₁ ≠ ⊤) (h2 : energy P T H₂ ≠ ⊤) :
    energy P T K ≠ ⊤ := by
  have e1 := measurable_energyDensity hm₁ T
  have e2 := measurable_energyDensity hm₂ T
  have hstep : energy P T K
      ≤ 2 * energy P T H₁ + 2 * energy P T H₂ := by
    rw [energy, energy, energy, ← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
      ← lintegral_add_left (e1.const_mul 2)]
    refine lintegral_mono fun ω => ?_
    have h1' : Measurable fun s => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm₁.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    have h2' : Measurable fun s => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm₂.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    rw [← lintegral_const_mul 2 h1', ← lintegral_const_mul 2 h2',
      ← lintegral_add_left (h1'.const_mul 2)]
    refine lintegral_mono fun s => ?_
    calc (‖K ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) := hbound ω s
      _ = 2 * (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 := by ring
  refine ne_top_of_le_ne_top ?_ hstep
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by simp) h1, ENNReal.mul_ne_top (by simp) h2⟩
omit [IsProbabilityMeasure P] in
/-- The energy of a sum is finite when both energies are. -/
theorem energy_add_ne_top {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (h1 : energy P T H₁ ≠ ⊤) (h2 : energy P T H₂ ≠ ⊤) :
    energy P T (fun ω s => H₁ ω s + H₂ ω s) ≠ ⊤ :=
  energy_ne_top_of_bound (fun _ _ => sq_nnnorm_add_le_two_mul _ _) hm₁ hm₂ h1 h2
omit [IsProbabilityMeasure P] in
/-- The energy of a scalar multiple is finite when the energy is. -/
theorem energy_const_mul_ne_top {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (h : energy P T H ≠ ⊤) (c : ℝ) :
    energy P T (fun ω s => c * H ω s) ≠ ⊤ := by
  rw [energy, _root_.Prove2MeSourceProof.h_8b64fc95ec4c1a34f817a2e0 hm c T]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h
end Energy

namespace HorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

omit [IsProbabilityMeasure P] in
/-- The global square-integrability the Itô integral asks for. -/
theorem sq_int_global (G : HorizonIntegrand P ℱ T) :
    ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.toFun ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T' _ =>
  lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_6afbd3f9a4aa317ea9c9ba3c G.vanishing T')
    (lt_top_iff_ne_top.mpr G.energy_ne_top)
/-- The Itô integral of an admissible integrand over the horizon. -/
noncomputable def integral (W : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration W ℱ) (G : HorizonIntegrand P ℱ T) : Ω → ℝ :=
  stochasticIntegralBrownian W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global T
/-- The zero integrand. -/
def zero (P : Measure Ω) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) :
    HorizonIntegrand P ℱ T where
  toFun := fun _ _ => 0
  measurable_uncurry := measurable_const
  progressive := progressivelyMeasurable_const ℱ 0
  vanishing := fun _ _ _ => rfl
  energy_ne_top := by simp [energy]
/-- The sum of two admissible integrands. -/
noncomputable def add (G₁ G₂ : HorizonIntegrand P ℱ T) : HorizonIntegrand P ℱ T where
  toFun := fun ω s => G₁.toFun ω s + G₂.toFun ω s
  measurable_uncurry := G₁.measurable_uncurry.add G₂.measurable_uncurry
  progressive := G₁.progressive.add G₂.progressive
  vanishing := fun ω s hs => by rw [G₁.vanishing ω s hs, G₂.vanishing ω s hs, add_zero]
  energy_ne_top := energy_add_ne_top G₁.measurable_uncurry G₂.measurable_uncurry
    G₁.energy_ne_top G₂.energy_ne_top
/-- A scalar multiple of an admissible integrand. -/
noncomputable def smul (c : ℝ) (G : HorizonIntegrand P ℱ T) : HorizonIntegrand P ℱ T where
  toFun := fun ω s => c * G.toFun ω s
  measurable_uncurry := measurable_const.mul G.measurable_uncurry
  progressive := Probability.ProgressivelyMeasurable.mul
    (progressivelyMeasurable_const ℱ c) G.progressive
  vanishing := fun ω s hs => by rw [G.vanishing ω s hs, mul_zero]
  energy_ne_top := energy_const_mul_ne_top G.measurable_uncurry G.energy_ne_top c
section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

/-- The Itô integral of an admissible integrand is square integrable. -/
theorem memLp (G : HorizonIntegrand P ℱ T) : MemLp (G.integral W hℱ) 2 P :=
  stochasticIntegralBrownian_memLp W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global T
/-- The isometry of differences in terms of the energy. -/
theorem lintegral_sq_integral_sub (hT : 0 < T) (G₁ G₂ : HorizonIntegrand P ℱ T) :
    ∫⁻ ω, (‖G₁.integral W hℱ ω - G₂.integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = energy P T (fun ω s => G₁.toFun ω s - G₂.toFun ω s) :=
  _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ G₁.toFun G₂.toFun
    G₁.measurable_uncurry G₂.measurable_uncurry G₁.progressive G₂.progressive
    G₁.sq_int_global G₂.sq_int_global hT
/-- The integral of the zero integrand vanishes. -/
theorem integral_zero (hT : 0 < T) :
    (HorizonIntegrand.zero P ℱ T).integral W hℱ =ᵐ[P] 0 := by
  have hiso := _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ
    (HorizonIntegrand.zero P ℱ T).toFun (HorizonIntegrand.zero P ℱ T).measurable_uncurry
    (HorizonIntegrand.zero P ℱ T).progressive (HorizonIntegrand.zero P ℱ T).sq_int_global hT
  have h0 : energy P T (HorizonIntegrand.zero P ℱ T).toFun = 0 := by
    simp [energy, HorizonIntegrand.zero]
  have hzero : ∫⁻ ω, (‖(HorizonIntegrand.zero P ℱ T).integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    hiso.trans h0
  have hae : AEMeasurable
      (fun ω => (‖(HorizonIntegrand.zero P ℱ T).integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    ((((memLp W hℱ (HorizonIntegrand.zero P ℱ T)).aestronglyMeasurable.aemeasurable).nnnorm
      ).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hzero] with ω hω
  have h2 : (‖(HorizonIntegrand.zero P ℱ T).integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2 = 0 := hω
  have h3 : (‖(HorizonIntegrand.zero P ℱ T).integral W hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  simpa using h3
/-- Additivity of the integral on admissible integrands. -/
theorem integral_add (hT : 0 < T) (G₁ G₂ : HorizonIntegrand P ℱ T) :
    (G₁.add G₂).integral W hℱ
      =ᵐ[P] fun ω => G₁.integral W hℱ ω + G₂.integral W hℱ ω :=
  _root_.Prove2MeSourceProof.h_0a844334f53895dbf4245fb6 W ℱ hℱ G₁.measurable_uncurry G₂.measurable_uncurry
    G₁.progressive G₂.progressive G₁.sq_int_global G₂.sq_int_global
    (G₁.add G₂).measurable_uncurry (G₁.add G₂).progressive (G₁.add G₂).sq_int_global hT
/-- Homogeneity of the integral on admissible integrands. -/
theorem integral_smul (hT : 0 < T) (c : ℝ) (G : HorizonIntegrand P ℱ T) :
    (G.smul c).integral W hℱ =ᵐ[P] fun ω => c * G.integral W hℱ ω :=
  _root_.Prove2MeSourceProof.h_f0468e0adacb16d8cd5e45b1 W ℱ hℱ G.measurable_uncurry G.progressive
    G.sq_int_global c (G.smul c).measurable_uncurry (G.smul c).progressive
    (G.smul c).sq_int_global hT
end Integral

end HorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Representation

end LevyStochCalc.Brownian.Ito


