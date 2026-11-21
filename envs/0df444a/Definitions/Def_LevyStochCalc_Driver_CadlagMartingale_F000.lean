-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CadlagMartingale_F000
-- name    : LevyStochCalc_Driver_CadlagMartingale_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:47:44.624054+00:00
-- url     : https://prove2.me/theorems/75027924-f46a-45a4-9ec2-978cd2edb5f6
-- title:
--   Source declarations: LevyStochCalc.Driver.CadlagMartingale
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CadlagMartingale. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_GermIndep_F001
import Definitions.Def_LevyStochCalc_Driver_GermIndep_F002
import Definitions.Def_LevyStochCalc_Probability_CondExpModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg conditional-expectation martingale of a Lévy driver

`Probability/CondExpModification.lean` builds a right-continuous modification of
`t ↦ 𝔼[ξ | ℱ₊ t]` indexed by `ℝ≥0`, the index type the càdlàg machinery needs. Reindexing by `ℝ`
means saying what happens before time `0`, where the constant `𝔼 ξ` is the right answer: it is
`𝔼[ξ | ℱ₊ t]` there by Blumenthal's 0-1 law (`Driver/GermIndep.lean`), and being constant it is
measurable for every σ-algebra, which the modification's value at `0` is not.

## Main statements

* `LevyDriver.cadlagCondExp` — the reindexed process.
* `LevyDriver.martingale_cadlagCondExp` — it is a martingale for `ℱ₊`.
* `LevyDriver.cadlagCondExp_ae_eq` — it agrees with `𝔼[ξ | ℱ₊ t]` at every fixed `t`.
* `LevyDriver.tendsto_cadlagCondExp_nhdsGT`, `LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT`
  — right continuity of every path, and left limits almost surely.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν) (ξ : Ω → ℝ)

/-- The càdlàg conditional-expectation martingale of `ξ`, indexed by `ℝ`: the `ℝ≥0`-indexed
modification before time `0` replaced by the constant `𝔼 ξ`. -/
noncomputable def cadlagCondExp : ℝ → Ω → ℝ := fun t ω =>
  if 0 ≤ t then Probability.condExpModif P D.filtration.rightCont ξ (Real.toNNReal t) ω
  else ∫ ω', ξ ω' ∂P
variable {D ξ}

theorem cadlagCondExp_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    D.cadlagCondExp ξ t
      = Probability.condExpModif P D.filtration.rightCont ξ (Real.toNNReal t) := by
  funext ω; simp only [cadlagCondExp, if_pos ht]
theorem cadlagCondExp_of_neg {t : ℝ} (ht : t < 0) :
    D.cadlagCondExp ξ t = fun _ => ∫ ω', ξ ω' ∂P := by
  funext ω; simp only [cadlagCondExp, if_neg (not_le.2 ht)]
/-- At every fixed time the process agrees with the conditional expectation. -/
theorem cadlagCondExp_ae_eq (hξ : MemLp ξ 2 P) (hSM : StronglyMeasurable ξ) (t : ℝ) :
    D.cadlagCondExp ξ t =ᵐ[P] P[ξ | D.filtration.rightCont t] := by
  rcases le_or_gt 0 t with ht | ht
  · rw [cadlagCondExp_of_nonneg ht]
    have h := Probability.condExpModif_ae_eq (ℱ := D.filtration.rightCont) hξ (Real.toNNReal t)
    rwa [Real.coe_toNNReal t ht] at h
  · rw [cadlagCondExp_of_neg ht]
    exact (D.condExp_rightCont_nonpos hSM ht.le).symm
theorem stronglyMeasurable_cadlagCondExp (t : ℝ) :
    StronglyMeasurable[D.filtration.rightCont t] (D.cadlagCondExp ξ t) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [cadlagCondExp_of_nonneg ht]
    have h := Probability.adapted_condExpModif (μ := P) (ℱ := D.filtration.rightCont) (ξ := ξ)
      (Real.toNNReal t)
    rw [Probability.restrictNNReal_apply, Real.coe_toNNReal t ht] at h
    exact h.stronglyMeasurable
  · rw [cadlagCondExp_of_neg ht]
    exact stronglyMeasurable_const
/-- **The reindexed process is a martingale for the right-continuous joint filtration.** -/
theorem martingale_cadlagCondExp (hξ : MemLp ξ 2 P) (hSM : StronglyMeasurable ξ) :
    Martingale (D.cadlagCondExp ξ) D.filtration.rightCont P := by
  refine ⟨fun t => stronglyMeasurable_cadlagCondExp t, fun s t hst => ?_⟩
  calc P[D.cadlagCondExp ξ t | D.filtration.rightCont s]
      =ᵐ[P] P[P[ξ | D.filtration.rightCont t] | D.filtration.rightCont s] :=
        condExp_congr_ae (cadlagCondExp_ae_eq hξ hSM t)
    _ =ᵐ[P] P[ξ | D.filtration.rightCont s] :=
        condExp_condExp_of_le (D.filtration.rightCont.mono hst) (D.filtration.rightCont.le t)
    _ =ᵐ[P] D.cadlagCondExp ξ s := (cadlagCondExp_ae_eq hξ hSM s).symm
end LevyDriver

end LevyStochCalc.Driver


