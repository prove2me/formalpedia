-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_StandardBorel_F000
-- name    : LevyStochCalc_Brownian_StandardBorel_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:41:48.184117+00:00
-- url     : https://prove2.me/theorems/74953232-1fa6-402a-aa55-4d73e93f0fd8
-- title:
--   Source declarations: LevyStochCalc.Brownian.StandardBorel
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.StandardBorel. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Transport_F000
import Mathlib.Topology.Homeomorph.Lemmas

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian motion on a standard Borel space

The Wiener measure `wienerMeasure` lives on `C(ℝ≥0, ℝ)` with its Borel σ-algebra. The space
`C(ℝ≥0, ℝ)` is Polish, so this σ-algebra is standard Borel, and the coordinate process
`(t, f) ↦ f t` has the finite-dimensional laws of Brownian motion (it has law `gaussianLimit`
as a random element of `ℝ≥0 → ℝ`). Its real-time extension is therefore a Brownian motion on a
standard Borel probability space, `BrownianMotion.wiener`.

`d` independent copies of a Brownian motion on `Fin d → Ω₀` under the product measure form a
`d`-dimensional Brownian motion (`MultidimBrownianMotion.pi`). Standard Borel spaces are closed
under `ULift` and countable products, so both constructions exist on a standard Borel space in
every universe.

## Main definitions

* `LevyStochCalc.Brownian.BrownianMotion.wiener`: the Brownian motion `t ↦ f (t⁺) − f 0` on
  `(C(ℝ≥0, ℝ), wienerMeasure)`.
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.pi`: the `d`-dimensional Brownian motion
  on `Fin d → Ω₀` under `Measure.pi fun _ => P₀` whose `i`-th coordinate reads `W₀` off the `i`-th
  factor.

## Main statements

* `StandardBorelSpace.ulift`: `ULift α` is standard Borel when `α` is.
* `LevyStochCalc.Brownian.hasLaw_coe_wienerMeasure`: under `wienerMeasure` the path
  `f ↦ ⇑f : ℝ≥0 → ℝ` has law `gaussianLimit`.
* `LevyStochCalc.Brownian.BrownianMotion.exists_standardBorel`: some standard Borel probability
  space carries a Brownian motion.
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_standardBorel`: the same for a
  `d`-dimensional Brownian motion.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u v

/-- A lift of a standard Borel space to a higher universe is standard Borel. -/
instance StandardBorelSpace.ulift {α : Type u} [MeasurableSpace α] [StandardBorelSpace α] :
    StandardBorelSpace (ULift.{v} α) := by
  letI := upgradeStandardBorel α
  haveI : PolishSpace (ULift.{v} α) := Homeomorph.ulift.isClosedEmbedding.polishSpace
  infer_instance
namespace LevyStochCalc.Brownian

/-- The map sending a point of `ℝ≥0 → ℝ` to the continuous path of `brownian` at that point is
measurable. -/
private lemma measurable_brownian_subtype :
    Measurable (fun ω : ℝ≥0 → ℝ ↦
      (⟨fun t ↦ brownian t ω, continuous_brownian ω⟩ : {f : ℝ≥0 → ℝ // Continuous f})) :=
  Measurable.subtype_mk (measurable_pi_lambda _ fun t ↦ measurable_brownian t)
instance isProbabilityMeasure_wienerMeasure : IsProbabilityMeasure wienerMeasure := by
  haveI : IsProbabilityMeasure wienerMeasureAux :=
    Measure.isProbabilityMeasure_map measurable_brownian_subtype.aemeasurable
  exact Measure.isProbabilityMeasure_map MeasurableEquiv.continuousMap.measurable.aemeasurable
/-- The coercion `C(ℝ≥0, ℝ) → (ℝ≥0 → ℝ)` is measurable for the Borel σ-algebra of the compact-open
topology and the product σ-algebra. -/
lemma measurable_coe_continuousMap : Measurable (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)) := by
  rw [measurable_pi_iff]
  exact fun t => (continuous_eval_const t).measurable
/-- Under the Wiener measure the path `f ↦ ⇑f` has law `gaussianLimit`. -/
theorem hasLaw_coe_wienerMeasure :
    HasLaw (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)) gaussianLimit wienerMeasure := by
  refine ⟨measurable_coe_continuousMap.aemeasurable, ?_⟩
  unfold wienerMeasure wienerMeasureAux
  rw [Measure.map_map measurable_coe_continuousMap MeasurableEquiv.continuousMap.measurable,
    Measure.map_map (measurable_coe_continuousMap.comp MeasurableEquiv.continuousMap.measurable)
      measurable_brownian_subtype]
  exact hasLaw_brownian.map_eq
/-- The coordinate process of the Wiener measure is a pre-Brownian motion. -/
theorem isPreBrownianReal_wienerMeasure :
    IsPreBrownianReal (fun t (f : C(ℝ≥0, ℝ)) => f t) wienerMeasure :=
  HasLaw.IsPreBrownianReal hasLaw_coe_wienerMeasure
/-- The Brownian motion `(t, f) ↦ f (t⁺) − f 0` on `(C(ℝ≥0, ℝ), wienerMeasure)`. -/
noncomputable def BrownianMotion.wiener : BrownianMotion wienerMeasure :=
  BrownianMotion.ofIsPreBrownianReal isPreBrownianReal_wienerMeasure
    (fun t => (continuous_eval_const t).measurable) (fun f => f.continuous)
@[simp]
lemma BrownianMotion.wiener_apply (t : ℝ) (f : C(ℝ≥0, ℝ)) :
    BrownianMotion.wiener.W t f = f (Real.toNNReal t) - f 0 := rfl
/-- **Brownian motion on a standard Borel space.** In every universe, some standard Borel
probability space carries a Brownian motion: the lift of `BrownianMotion.wiener` to
`ULift C(ℝ≥0, ℝ)`. -/
theorem BrownianMotion.exists_standardBorel :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      StandardBorelSpace Ω ∧ Nonempty (BrownianMotion P) := by
  let e : ULift.{u} C(ℝ≥0, ℝ) ≃ᵐ C(ℝ≥0, ℝ) := MeasurableEquiv.ulift
  let P : Measure (ULift.{u} C(ℝ≥0, ℝ)) := wienerMeasure.map e.symm
  have hP : IsProbabilityMeasure P :=
    Measure.isProbabilityMeasure_map e.symm.measurable.aemeasurable
  have hdown : HasLaw e wienerMeasure P :=
    ⟨e.measurable.aemeasurable, by simp [P, Measure.map_map e.measurable e.symm.measurable]⟩
  refine ⟨ULift.{u} C(ℝ≥0, ℝ), inferInstance, P, hP, inferInstance, ⟨?_⟩⟩
  refine BrownianMotion.ofIsPreBrownianReal (X := fun t ω => (e ω) t) ?_ ?_ ?_
  · exact HasLaw.IsPreBrownianReal (hasLaw_coe_wienerMeasure.comp hdown)
  · exact fun t => (continuous_eval_const t).measurable.comp e.measurable
  · exact fun ω => (e ω).continuous
namespace Multidim

variable {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

/-- The `d`-dimensional Brownian motion on `Fin d → Ω₀` under `Measure.pi fun _ => P₀` whose
`i`-th coordinate is `W₀` read off the `i`-th factor. -/
noncomputable def MultidimBrownianMotion.pi (W₀ : BrownianMotion P₀) (d : ℕ) :
    MultidimBrownianMotion (Measure.pi fun _ : Fin d => P₀) d where
  W i := W₀.comap (measurePreserving_eval (fun _ : Fin d => P₀) i)
  components_independent :=
    iIndepFun_pi (X := fun _ : Fin d => fun (ω₀ : Ω₀) (t : ℝ) => W₀.W t ω₀)
      (μ := fun _ : Fin d => P₀)
      fun _ => (measurable_pi_iff.mpr fun t => W₀.measurable_eval t).aemeasurable
  joint_continuous_paths := by
    have h : ∀ᵐ ω ∂(Measure.pi fun _ : Fin d => P₀), ∀ i : Fin d,
        Continuous fun t : ℝ => W₀.W t (ω i) :=
      ae_all_iff.mpr fun i =>
        (measurePreserving_eval (fun _ : Fin d => P₀) i).quasiMeasurePreserving.ae
          W₀.continuous_paths
    filter_upwards [h] with ω hω
    exact continuous_pi hω
@[simp]
lemma MultidimBrownianMotion.pi_apply (W₀ : BrownianMotion P₀) (d : ℕ) (i : Fin d) (t : ℝ)
    (ω : Fin d → Ω₀) : ((MultidimBrownianMotion.pi W₀ d).W i).W t ω = W₀.W t (ω i) := rfl
/-- **`d`-dimensional Brownian motion on a standard Borel space.** For every `d`, in every
universe, some standard Borel probability space carries a `d`-dimensional Brownian motion. -/
theorem MultidimBrownianMotion.exists_standardBorel (d : ℕ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      StandardBorelSpace Ω ∧ Nonempty (MultidimBrownianMotion P d) := by
  obtain ⟨Ω₀, _, P₀, _, h₀, ⟨W₀⟩⟩ := BrownianMotion.exists_standardBorel.{u}
  exact ⟨Fin d → Ω₀, inferInstance, Measure.pi fun _ => P₀, inferInstance,
    StandardBorelSpace.pi_countable, ⟨MultidimBrownianMotion.pi W₀ d⟩⟩
end Multidim

end LevyStochCalc.Brownian


