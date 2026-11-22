-- Prove2me | Definitions.Def_SourceProof_7b4e5977b4bcff46a7cd24ec
-- name    : SourceProof_7b4e5977b4bcff46a7cd24ec
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:49:29.612769+00:00
-- url     : https://prove2.me/theorems/598226cf-21c4-4bc9-b04c-210d5b2725a2
-- title:
--   LevyStochCalc source module: SourceProof_7b4e5977b4bcff46a7cd24ec
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJAe.exists_modification_indistinguishable` comes from the `LevyStochCalc.BSDEJ.SolvesAe` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SolvesAe_F000
import Definitions.Def_SourceProof_278d9c0e5e32e44766ed3963

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of a BSDEJ up to a null set of sample points

`SolvesBSDEJAe D f ξ T Y Z U` is the solution predicate `SolvesBSDEJ D f ξ T Y Z U` with its
three everywhere-quantified path conditions — right-continuity with left limits of `Y`, and the
vanishing of `Z` and of `U` off the horizon — asked only for almost every sample point.

The two predicates describe the same solutions: setting the three processes to `0` on a
measurable null superset of the exceptional set produces a `SolvesBSDEJ` triple whose paths agree
with the given ones off that null set (`SolvesBSDEJAe.exists_modification`), so the value
processes of two almost-everywhere solutions of the same equation remain indistinguishable on the
horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

open LevyStochCalc.Brownian.Multidim LevyStochCalc.Poisson in

theorem _root_.Prove2MeSourceProof.h_7b4e5977b4bcff46a7cd24ec
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJAe D f ξ T Y Z U) :
    ∃ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ),
      SolvesBSDEJ D f ξ T Y' Z' U' ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, Y' t ω = Y t ω)
        ∧ (∀ᵐ ω ∂P, ∀ s : ℝ, Z' s ω = Z s ω) ∧ ∀ᵐ ω ∂P, ∀ s : ℝ, U' s ω = U s ω := by
  classical
  have hSae : ∀ᵐ ω ∂P, (∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
          ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L))
      ∧ (∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
      ∧ ∀ (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0 := by
    filter_upwards [h.Y_cadlag, h.Z_vanish, h.U_vanish] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨N, hsub, hNmeas, hNzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hSae)
  have hout : ∀ ω : Ω, ω ∉ N → (∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
          ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L))
      ∧ (∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
      ∧ ∀ (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0 := by
    intro ω hω
    by_contra hc
    exact hω (hsub hc)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hNzero] with ω hω
    exact Set.notMem_of_mem_compl hω
  have hN0 : MeasurableSet[LevyStochCalc.BSDEJ.Solves.augJoint D 0] N := D.measurableSet_augFiltration_of_null hNmeas hNzero
  have hNt : ∀ t : ℝ, MeasurableSet[LevyStochCalc.BSDEJ.Solves.augJoint D t] N := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact (LevyStochCalc.BSDEJ.Solves.augJoint D).mono ht _ hN0
    · exact D.augFiltration_le_of_nonpos ht.le _ hN0
  obtain ⟨Y', hY'def⟩ : ∃ Y' : ℝ → Ω → ℝ,
      ∀ (t : ℝ) (ω : Ω), Y' t ω = if ω ∈ N then (0 : ℝ) else Y t ω :=
    ⟨fun t ω => if ω ∈ N then (0 : ℝ) else Y t ω, fun _ _ => rfl⟩
  obtain ⟨Z', hZ'def⟩ : ∃ Z' : ℝ → Ω → (Fin d → ℝ),
      ∀ (s : ℝ) (ω : Ω), Z' s ω = if ω ∈ N then (0 : Fin d → ℝ) else Z s ω :=
    ⟨fun s ω => if ω ∈ N then (0 : Fin d → ℝ) else Z s ω, fun _ _ => rfl⟩
  obtain ⟨U', hU'def⟩ : ∃ U' : ℝ → Ω → E → ℝ,
      ∀ (s : ℝ) (ω : Ω), U' s ω = if ω ∈ N then (0 : E → ℝ) else U s ω :=
    ⟨fun s ω => if ω ∈ N then (0 : E → ℝ) else U s ω, fun _ _ => rfl⟩
  have hY'out : ∀ (t : ℝ) (ω : Ω), ω ∉ N → Y' t ω = Y t ω := by
    intro t ω hω
    rw [hY'def t ω, if_neg hω]
  have hZ'out : ∀ (s : ℝ) (ω : Ω), ω ∉ N → Z' s ω = Z s ω := by
    intro s ω hω
    rw [hZ'def s ω, if_neg hω]
  have hU'out : ∀ (s : ℝ) (ω : Ω), ω ∉ N → U' s ω = U s ω := by
    intro s ω hω
    rw [hU'def s ω, if_neg hω]
  have hZ'coord : ∀ (s : ℝ) (ω : Ω) (i : Fin d),
      Z' s ω i = if ω ∈ N then (0 : ℝ) else Z s ω i := by
    intro s ω i
    by_cases hω : ω ∈ N
    · rw [hZ'def s ω, if_pos hω, if_pos hω]
      rfl
    · rw [hZ'def s ω, if_neg hω, if_neg hω]
  have hU'mark : ∀ (s : ℝ) (ω : Ω) (e : E),
      U' s ω e = if ω ∈ N then (0 : ℝ) else U s ω e := by
    intro s ω e
    by_cases hω : ω ∈ N
    · rw [hU'def s ω, if_pos hω, if_pos hω]
      rfl
    · rw [hU'def s ω, if_neg hω, if_neg hω]
  have hZ'meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z' s ω i) := by
    intro i
    have he : (Function.uncurry fun ω s => Z' s ω i)
        = fun p : Ω × ℝ => if p.1 ∈ N then (0 : ℝ) else Z p.2 p.1 i :=
      funext fun p => hZ'coord p.2 p.1 i
    rw [he]
    exact Measurable.ite (measurable_fst hNmeas) measurable_const (h.Z_meas i)
  have hZ'prog : ∀ i : Fin d,
      LevyStochCalc.Probability.ProgressivelyMeasurable (LevyStochCalc.BSDEJ.Solves.augJoint D) fun ω s => Z' s ω i := by
    intro i t
    have hNti := hNt t
    have hbase := h.Z_prog i t
    letI : MeasurableSpace Ω := LevyStochCalc.BSDEJ.Solves.augJoint D t
    have he : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => Z' s p.1 i) p.2)
        = fun p : Ω × ℝ => if p.1 ∈ N then (0 : ℝ)
            else (Set.Iic t).indicator (fun s => Z s p.1 i) p.2 := by
      funext p
      by_cases hp : p.1 ∈ N
      · rw [if_pos hp]
        by_cases hq : p.2 ∈ Set.Iic t
        · rw [Set.indicator_of_mem hq, hZ'coord, if_pos hp]
        · rw [Set.indicator_of_notMem hq]
      · rw [if_neg hp]
        by_cases hq : p.2 ∈ Set.Iic t
        · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, hZ'coord, if_neg hp]
        · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
    rw [he]
    exact StronglyMeasurable.ite (measurable_fst hNti) stronglyMeasurable_const hbase
  have hZ'van : ∀ (ω : Ω) (s : ℝ), s ∉ Set.Icc (0 : ℝ) T → Z' s ω = 0 := by
    intro ω s hs
    by_cases hω : ω ∈ N
    · rw [hZ'def s ω, if_pos hω]
    · rw [hZ'def s ω, if_neg hω]
      exact (hout ω hω).2.1 s hs
  have hZ'sq : ∀ i : Fin d,
      LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z' s ω i) ≠ ⊤ := by
    intro i
    have he : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z' s ω i)
        = LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hNae] with ω hω
      exact lintegral_congr fun s => by rw [hZ'coord s ω i, if_neg hω]
    rw [he]
    exact h.Z_sq i
  have hU'meas : Measurable fun p : Ω × ℝ × E => U' p.2.1 p.1 p.2.2 := by
    have he : (fun p : Ω × ℝ × E => U' p.2.1 p.1 p.2.2)
        = fun p : Ω × ℝ × E => if p.1 ∈ N then (0 : ℝ) else U p.2.1 p.1 p.2.2 :=
      funext fun p => hU'mark p.2.1 p.1 p.2.2
    rw [he]
    exact Measurable.ite (measurable_fst hNmeas) measurable_const h.U_meas
  have hU'prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable (LevyStochCalc.BSDEJ.Solves.augJoint D)
      fun ω s e => U' s ω e := by
    intro t
    have hNti := hNt t
    have hbase := h.U_prog t
    letI : MeasurableSpace Ω := LevyStochCalc.BSDEJ.Solves.augJoint D t
    have he : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => U' s p.1 p.2.2) p.2.1)
        = fun p : Ω × ℝ × E => if p.1 ∈ N then (0 : ℝ)
            else (Set.Iic t).indicator (fun s => U s p.1 p.2.2) p.2.1 := by
      funext p
      by_cases hp : p.1 ∈ N
      · rw [if_pos hp]
        by_cases hq : p.2.1 ∈ Set.Iic t
        · rw [Set.indicator_of_mem hq, hU'mark, if_pos hp]
        · rw [Set.indicator_of_notMem hq]
      · rw [if_neg hp]
        by_cases hq : p.2.1 ∈ Set.Iic t
        · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, hU'mark, if_neg hp]
        · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
    rw [he]
    exact StronglyMeasurable.ite (measurable_fst hNti) stronglyMeasurable_const hbase
  have hU'van : ∀ (ω : Ω) (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U' s ω e = 0 := by
    intro ω s e hs
    rw [hU'mark s ω e]
    by_cases hω : ω ∈ N
    · rw [if_pos hω]
    · rw [if_neg hω]
      exact (hout ω hω).2.2 s e hs
  have hU'sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => U' s ω e) ≠ ⊤ := by
    have he : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U' s ω e)
        = LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hNae] with ω hω
      exact lintegral_congr fun s => lintegral_congr fun e => by
        rw [hU'mark s ω e, if_neg hω]
    rw [he]
    exact h.U_sq
  have hY'meas : Measurable (Function.uncurry Y') := by
    have he : Function.uncurry Y' = fun p : ℝ × Ω => if p.2 ∈ N then (0 : ℝ) else Y p.1 p.2 :=
      funext fun p => hY'def p.1 p.2
    rw [he]
    exact Measurable.ite (measurable_snd hNmeas) measurable_const h.Y_meas
  have hY'adapted : MeasureTheory.Adapted (LevyStochCalc.BSDEJ.Solves.augJoint D).rightCont Y' := by
    intro t
    have hNrc : MeasurableSet[(LevyStochCalc.BSDEJ.Solves.augJoint D).rightCont t] N :=
      D.rightCont_augFiltration_zero_le_rightCont t _
        (D.measurableSet_rightCont_augFiltration_of_null N hNmeas hNzero)
    have hbase := h.Y_adapted t
    letI : MeasurableSpace Ω := (LevyStochCalc.BSDEJ.Solves.augJoint D).rightCont t
    have he : Y' t = fun ω => if ω ∈ N then (0 : ℝ) else Y t ω := funext fun ω => hY'def t ω
    rw [he]
    exact Measurable.ite hNrc measurable_const hbase
  have hY'cadlag : ∀ (ω : Ω) (t : ℝ),
      Filter.Tendsto (fun s => Y' s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y' t ω))
        ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y' s ω) (nhdsWithin t (Set.Iio t)) (nhds L) := by
    intro ω t
    by_cases hω : ω ∈ N
    · have hfun : (fun s => Y' s ω) = fun _ : ℝ => (0 : ℝ) :=
        funext fun s => by rw [hY'def s ω, if_pos hω]
      have hval : Y' t ω = 0 := by rw [hY'def t ω, if_pos hω]
      rw [hfun, hval]
      exact ⟨tendsto_const_nhds, 0, tendsto_const_nhds⟩
    · have hfun : (fun s => Y' s ω) = fun s => Y s ω := funext fun s => hY'out s ω hω
      rw [hfun, hY'out t ω hω]
      exact (hout ω hω).1 t
  have hY'sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y' t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
    have he : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y' t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
        = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hNae] with ω hω
      exact iSup_congr fun t => iSup_congr fun _ => by rw [hY'out t ω hω]
    rw [he]
    exact h.Y_sup
  have hWeq : ∀ r : ℝ, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (LevyStochCalc.BSDEJ.Solves.augJoint D) D.isBrownianFiltration_aug
          Z' hZ'meas hZ'prog (LevyStochCalc.BSDEJ.Solves.sq_int_global_of_vanishing hZ'van hZ'sq) r ω
        = LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (LevyStochCalc.BSDEJ.Solves.augJoint D) D.isBrownianFiltration_aug
          Z h.Z_meas h.Z_prog (LevyStochCalc.BSDEJ.Solves.sq_int_global_of_vanishing_ae h.Z_vanish h.Z_sq) r ω := by
    intro r
    rcases le_or_gt r 0 with hr | hr
    · have a1 := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W (LevyStochCalc.BSDEJ.Solves.augJoint D)
        D.isBrownianFiltration_aug Z' hZ'meas hZ'prog
        (LevyStochCalc.BSDEJ.Solves.sq_int_global_of_vanishing hZ'van hZ'sq) hr
      have a2 := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W (LevyStochCalc.BSDEJ.Solves.augJoint D)
        D.isBrownianFiltration_aug Z h.Z_meas h.Z_prog
        (LevyStochCalc.BSDEJ.Solves.sq_int_global_of_vanishing_ae h.Z_vanish h.Z_sq) hr
      filter_upwards [a1, a2] with ω b1 b2
      rw [b1, b2]
    · refine _root_.Prove2MeSourceProof.h_278d9c0e5e32e44766ed3963 D.W (LevyStochCalc.BSDEJ.Solves.augJoint D)
        D.isBrownianFiltration_aug hZ'meas hZ'prog (LevyStochCalc.BSDEJ.Solves.sq_int_global_of_vanishing hZ'van hZ'sq)
        h.Z_meas h.Z_prog (LevyStochCalc.BSDEJ.Solves.sq_int_global_of_vanishing_ae h.Z_vanish h.Z_sq) hr ?_
      filter_upwards [hNae] with ω hω
      exact Filter.Eventually.of_forall fun s => hZ'out s ω hω
  have hJeq : ∀ r : ℝ, ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (LevyStochCalc.BSDEJ.Solves.augJoint D) D.isPoissonFiltration_aug
          (fun ω' s e => U' s ω' e) hU'meas hU'prog
          (LevyStochCalc.BSDEJ.Solves.marked_sq_int_global_of_vanishing hU'van hU'sq) r ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (LevyStochCalc.BSDEJ.Solves.augJoint D) D.isPoissonFiltration_aug
          (fun ω' s e => U s ω' e) h.U_meas h.U_prog
          (LevyStochCalc.BSDEJ.Solves.marked_sq_int_global_of_vanishing_ae h.U_vanish h.U_sq) r ω := by
    intro r
    rcases le_or_gt r 0 with hr | hr
    · have a1 := LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos D.N
        D.isPoissonFiltration_aug (φ := fun ω' s e => U' s ω' e) hU'meas hU'prog
        (LevyStochCalc.BSDEJ.Solves.marked_sq_int_global_of_vanishing hU'van hU'sq) hr
      have a2 := LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos D.N
        D.isPoissonFiltration_aug (φ := fun ω' s e => U s ω' e) h.U_meas h.U_prog
        (LevyStochCalc.BSDEJ.Solves.marked_sq_int_global_of_vanishing_ae h.U_vanish h.U_sq) hr
      filter_upwards [a1, a2] with ω b1 b2
      rw [b1, b2]
    · refine _root_.Prove2MeSourceProof.h_ba87322c9970bc59472f4ba2 D.N D.isPoissonFiltration_aug
        (fun ω' s e => U' s ω' e) (fun ω' s e => U s ω' e) hU'meas h.U_meas hU'prog h.U_prog
        (LevyStochCalc.BSDEJ.Solves.marked_sq_int_global_of_vanishing hU'van hU'sq)
        (LevyStochCalc.BSDEJ.Solves.marked_sq_int_global_of_vanishing_ae h.U_vanish h.U_sq) hr ?_
      refine LevyStochCalc.Ito.markedEnergyMeasure_ae_eq_of_ae_ae
        (φ := fun ω' s e => U' s ω' e) (ψ := fun ω' s e => U s ω' e) hU'meas h.U_meas r ?_
      filter_upwards [hNae] with ω hω
      refine Filter.Eventually.of_forall fun s e => ?_
      rw [hU'mark s ω e, if_neg hω]
  refine ⟨Y', Z', U', ?_, ?_, ?_, ?_⟩
  · refine
      { Z_meas := hZ'meas
        Z_prog := hZ'prog
        Z_vanish := hZ'van
        Z_sq := hZ'sq
        U_meas := hU'meas
        U_prog := hU'prog
        U_vanish := hU'van
        U_sq := hU'sq
        Y_meas := hY'meas
        Y_adapted := hY'adapted
        Y_cadlag := hY'cadlag
        Y_sup := hY'sup
        eqn := ?_ }
    intro t ht
    have hdrift : ∀ ω : Ω, ω ∉ N →
        (∫ s in Set.Icc t T, f s (Y' s ω) (Z' s ω) (U' s ω))
          = ∫ s in Set.Icc t T, f s (Y s ω) (Z s ω) (U s ω) := by
      intro ω hω
      have hfun : (fun s => f s (Y' s ω) (Z' s ω) (U' s ω))
          = fun s => f s (Y s ω) (Z s ω) (U s ω) :=
        funext fun s => by rw [hY'out s ω hω, hZ'out s ω hω, hU'out s ω hω]
      rw [hfun]
    filter_upwards [h.eqn t ht, hNae, hWeq T, hWeq t, hJeq T, hJeq t] with ω hω hωN e1 e2 e3 e4
    rw [hY'out t ω hωN, hdrift ω hωN, e1, e2, e3, e4]
    exact hω
  · filter_upwards [hNae] with ω hω
    exact fun t => hY'out t ω hω
  · filter_upwards [hNae] with ω hω
    exact fun s => hZ'out s ω hω
  · filter_upwards [hNae] with ω hω
    exact fun s => hU'out s ω hω
end LevyStochCalc.BSDEJ.Solves


