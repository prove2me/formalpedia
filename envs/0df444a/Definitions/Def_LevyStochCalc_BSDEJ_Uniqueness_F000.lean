-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_Uniqueness_F000
-- name    : LevyStochCalc_BSDEJ_Uniqueness_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:08:32.440603+00:00
-- url     : https://prove2.me/theorems/72b342e3-d43b-43b1-abb4-2ab01537fee8
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.Uniqueness
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.Uniqueness. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Uniqueness of solutions of a backward equation with jumps

A solution of a backward equation with jumps over the augmented joint filtration of a Lévy
driver is its own Picard output, so the difference of two solutions with the same generator,
terminal value and horizon is a fixed point of the Picard contraction: its exponentially
weighted norm at the Young weight `max 2 (24 L²)` is at most a quarter of itself and finite,
hence zero. The value processes then agree almost surely at almost every time of the horizon,
and, both being right-continuous, at every time of the horizon; the diffusion coordinates and
the jump integrand agree up to sets of zero energy.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.toPicardOutput` — a solution is its own Picard output.
* `LevyStochCalc.BSDEJ.Solves.exists_drift_of_solvesBSDEJ` — the generator evaluated along a
  solution has a jointly and progressively measurable version of finite energy.
* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique` — the weighted norm of the difference of two
  solutions vanishes.
* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_ae`,
  `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_Icc`,
  `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Z`,
  `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_U` — the three components of two solutions
  agree.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Auxiliary facts -/

/-- A finite extended nonnegative real bounded by a quarter of itself is zero. -/
theorem eq_zero_of_le_inv_four_mul {w : ℝ≥0∞} (hw : w ≠ ⊤) (hle : w ≤ 4⁻¹ * w) : w = 0 := by
  have h4 : (4 : ℝ≥0∞)⁻¹ * w ≠ ⊤ := by finiteness
  have hr : w.toReal ≤ ((4 : ℝ≥0∞)⁻¹ * w).toReal := ENNReal.toReal_mono h4 hle
  rw [ENNReal.toReal_mul] at hr
  have hc : ((4 : ℝ≥0∞)⁻¹).toReal = (4 : ℝ)⁻¹ := by simp
  rw [hc] at hr
  have hnn : (0 : ℝ) ≤ w.toReal := ENNReal.toReal_nonneg
  have hz : w.toReal = 0 := by linarith
  rcases (ENNReal.toReal_eq_zero_iff w).mp hz with h | h
  · exact h
  · exact absurd h hw

omit [SigmaFinite ν] in
/-- The energy of the value, the energies of the diffusion coordinates and the marked energy of
the jump integrand of a triple of vanishing weighted norm all vanish. -/
theorem energies_eq_zero_of_wNorm_eq_zero {β T : ℝ} (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (h0 : wNorm P ν β T Y Z U = 0) :
    Brownian.Ito.energy P T (fun ω s => Y s ω) = 0
      ∧ (∀ j, Brownian.Ito.energy P T (fun ω s => Z s ω j) = 0)
      ∧ Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) = 0 := by
  classical
  have hle : Brownian.Ito.energy P T (fun ω s => Y s ω)
      + (∑ j, Brownian.Ito.energy P T (fun ω s => Z s ω j))
      + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≤ 0 := by
    rw [← _root_.Prove2MeSourceProof.h_869b93343dd8836d1387ab78 hYm hZm, ← h0]
    exact lintegral_density_le_wNorm hβ
  set A := Brownian.Ito.energy P T (fun ω s => Y s ω) with hA
  set B := ∑ j, Brownian.Ito.energy P T (fun ω s => Z s ω j) with hB
  set C := Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) with hC
  have hsum : A + B + C = 0 := le_antisymm hle zero_le
  have hAB : A + B = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hsum]
    exact self_le_add_right _ _
  have hA0 : A = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hAB]
    exact self_le_add_right _ _
  have hB0 : B = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hAB]
    exact self_le_add_left _ _
  have hC0 : C = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← hsum]
    exact self_le_add_left _ _
  refine ⟨hA0, fun j => ?_, hC0⟩
  have hj : Brownian.Ito.energy P T (fun ω s => Z s ω j) ≤ B :=
    Finset.single_le_sum (f := fun j => Brownian.Ito.energy P T (fun ω s => Z s ω j))
      (fun i _ => zero_le) (Finset.mem_univ j)
  rw [hB0] at hj
  exact le_antisymm hj zero_le
/-! ### A solution is its own Picard output -/

/-- A solution of the backward equation is the output of the Picard step taken along itself. -/
theorem SolvesBSDEJ.toPicardOutput {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJ D f ξ T Y Z U)
    (hT : 0 < T) : PicardOutput D f ξ T Y Z U Y Z U where
  Z_meas := h.Z_meas
  Z_prog := h.Z_prog
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_meas := h.U_meas
  U_prog := h.U_prog
  U_vanish := h.U_vanish
  U_sq := h.U_sq
  Y_meas := h.Y_meas
  Y_adapted := h.Y_adapted
  Y_cadlag := h.Y_cadlag
  Y_sup := h.Y_sup
  eqn := h.eqn
  Y_terminal := by
    filter_upwards [h.eqn T ⟨hT.le, le_rfl⟩] with ω hω
    have hI : (∫ s in Set.Icc T T, f s (Y s ω) (Z s ω) (U s ω)) = 0 := by
      rw [integral_Icc_eq_integral_Ioc, Set.Ioc_self, setIntegral_empty]
    rw [hω, hI]
    ring
/-! ### The drift along a solution -/

/-- The generator evaluated along a solution of the backward equation has a jointly measurable
version, progressively measurable for the augmented joint filtration, of finite energy and
vanishing off the horizon. -/
theorem exists_drift_of_solvesBSDEJ {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJ D f ξ T Y Z U)
    (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    ∃ b : Ω → ℝ → ℝ, Measurable (Function.uncurry b)
      ∧ Probability.ProgressivelyMeasurable (augJoint D) b
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
      ∧ Brownian.Ito.energy P T b ≠ ⊤
      ∧ ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          b p.1 p.2 = f p.2 (Y p.2 p.1) (Z p.2 p.1) (U p.2 p.1) := by
  have hYp : Probability.ProgressivelyMeasurable (augJoint D).rightCont fun ω s => Y s ω :=
    _root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421
      h.Y_adapted fun ω t => (h.Y_cadlag ω t).1
  have hYe : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.Y_sup.ne)
      _root_.Prove2MeSourceProof.h_8bb8c09ab790bf7a224b8ffd
  obtain ⟨b, hbm, hbp, hbz, hbq, hbae⟩ :=
    _root_.Prove2MeSourceProof.h_be0f56f10988c86fe4ec7fca (P := P) (ν := ν) D.N
      (augJoint D).rightCont hf hlip hT hf0 h.Y_meas hYp hYe h.Z_meas
      (fun i => (h.Z_prog i).mono fun t => (augJoint D).le_rightCont t) h.Z_sq h.U_meas
      (h.U_prog.mono fun t => (augJoint D).le_rightCont t)
      (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq)
  obtain ⟨b', hb'm, hb'p, hb'z, hb'q, hb'ae⟩ :=
    _root_.Prove2MeSourceProof.h_ee2057ecba7f5d9e6355867b (ℱ := augJoint D) hbm hbp hbz hbq
  refine ⟨b', hb'm, hb'p, hb'z, hb'q, ?_⟩
  filter_upwards [hb'ae, hbae] with p h1 h2
  rw [h1, h2]
/-! ### Uniqueness -/

/-- **Uniqueness of solutions of a backward equation with jumps.** The exponentially weighted
norm of the difference of two solutions with the same generator, terminal value and horizon
vanishes at the Young weight `max 2 (24 L²)`. -/
theorem SolvesBSDEJ.unique {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : SolvesBSDEJ D f ξ T Y₁ Z₁ U₁) (h₂ : SolvesBSDEJ D f ξ T Y₂ Z₂ U₂) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    wNorm P ν (max 2 (24 * L ^ 2)) T (fun t ω => Y₁ t ω - Y₂ t ω)
      (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) = 0 := by
  classical
  have hYm₁ : Measurable (Function.uncurry fun ω s => Y₁ s ω) :=
    h₁.Y_meas.comp (measurable_snd.prodMk measurable_fst)
  have hYm₂ : Measurable (Function.uncurry fun ω s => Y₂ s ω) :=
    h₂.Y_meas.comp (measurable_snd.prodMk measurable_fst)
  have hYm : Measurable (Function.uncurry fun ω s => Y₁ s ω - Y₂ s ω) := hYm₁.sub hYm₂
  have hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j) :=
    fun j => (h₁.Z_meas j).sub (h₂.Z_meas j)
  have hUm : Measurable fun p : Ω × ℝ × E => U₁ p.2.1 p.1 p.2.2 - U₂ p.2.1 p.1 p.2.2 :=
    h₁.U_meas.sub h₂.U_meas
  have hEY₁ : Brownian.Ito.energy P T (fun ω s => Y₁ s ω) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₁.Y_sup.ne)
      _root_.Prove2MeSourceProof.h_8bb8c09ab790bf7a224b8ffd
  have hEY₂ : Brownian.Ito.energy P T (fun ω s => Y₂ s ω) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₂.Y_sup.ne)
      _root_.Prove2MeSourceProof.h_8bb8c09ab790bf7a224b8ffd
  have hEY : Brownian.Ito.energy P T (fun ω s => Y₁ s ω - Y₂ s ω) ≠ ⊤ :=
    _root_.Prove2MeSourceProof.h_21431cc356d9363f35d4c54e hYm₁ hYm₂ hEY₁ hEY₂
  have hEZ : ∀ j, Brownian.Ito.energy P T (fun ω s => Z₁ s ω j - Z₂ s ω j) ≠ ⊤ :=
    fun j => _root_.Prove2MeSourceProof.h_21431cc356d9363f35d4c54e (h₁.Z_meas j) (h₂.Z_meas j) (h₁.Z_sq j) (h₂.Z_sq j)
  have hEU : Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => U₁ s ω e - U₂ s ω e) ≠ ⊤ :=
    (_root_.Prove2MeSourceProof.h_388a40baa407d0b0ae15b23c (φ := fun ω s e => U₁ s ω e)
      (ψ := fun ω s e => U₂ s ω e) h₁.U_meas h₂.U_meas
      (lt_top_iff_ne_top.mpr h₁.U_sq) (lt_top_iff_ne_top.mpr h₂.U_sq)).ne
  have hβ0 : (0 : ℝ) ≤ max 2 (24 * L ^ 2) := le_trans (by norm_num) (le_max_left _ _)
  have hfin : wNorm P ν (max 2 (24 * L ^ 2)) T (fun t ω => Y₁ t ω - Y₂ t ω)
      (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ≠ ⊤ :=
    _root_.Prove2MeSourceProof.h_74549f342024460457cb4481 hβ0 hYm hZm hEY hEZ hEU
  obtain ⟨b₁, hb₁m, hb₁p, hb₁z, hb₁q, hb₁⟩ := exists_drift_of_solvesBSDEJ h₁ hT hf hlip hf0
  obtain ⟨b₂, hb₂m, hb₂p, hb₂z, hb₂q, hb₂⟩ := exists_drift_of_solvesBSDEJ h₂ hT hf hlip hf0
  have hle := wNorm_sub_le_of_picardOutput hL hlip hT (h₁.toPicardOutput hT)
    (h₂.toPicardOutput hT) hYm hZm hUm hb₁m hb₁p hb₁z hb₁q hb₁ hb₂m hb₂p hb₂z hb₂q hb₂ hfin
  exact eq_zero_of_le_inv_four_mul hfin hle
/-! ### Consequences -/

/-- The value processes of two solutions of the same backward equation agree almost surely at
almost every time of the horizon. -/
theorem SolvesBSDEJ.unique_Y_ae {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : SolvesBSDEJ D f ξ T Y₁ Z₁ U₁) (h₂ : SolvesBSDEJ D f ξ T Y₂ Z₂ U₂) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Y₁ s =ᵐ[P] Y₂ s := by
  have hYm₁ : Measurable (Function.uncurry fun ω s => Y₁ s ω) :=
    h₁.Y_meas.comp (measurable_snd.prodMk measurable_fst)
  have hYm₂ : Measurable (Function.uncurry fun ω s => Y₂ s ω) :=
    h₂.Y_meas.comp (measurable_snd.prodMk measurable_fst)
  have hYm : Measurable (Function.uncurry fun ω s => Y₁ s ω - Y₂ s ω) := hYm₁.sub hYm₂
  have hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j) :=
    fun j => (h₁.Z_meas j).sub (h₂.Z_meas j)
  have hβ0 : (0 : ℝ) ≤ max 2 (24 * L ^ 2) := le_trans (by norm_num) (le_max_left _ _)
  have h0 := (energies_eq_zero_of_wNorm_eq_zero hβ0 hYm hZm
    (SolvesBSDEJ.unique h₁ h₂ hT hf hL hlip hf0)).1
  have hm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (‖Y₁ s ω - Y₂ s ω‖₊ : ℝ≥0∞) ^ 2) := hYm.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Y₁ s ω - Y₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ s in Set.Icc (0 : ℝ) T,
        (∫⁻ ω, (‖Y₁ s ω - Y₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      hm.aemeasurable
  have h0' : ∫⁻ s in Set.Icc (0 : ℝ) T,
      (∫⁻ ω, (‖Y₁ s ω - Y₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume = 0 := by
    rw [← hswap]
    exact h0
  have hmt : Measurable fun s : ℝ => ∫⁻ ω, (‖Y₁ s ω - Y₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    hm.lintegral_prod_left'
  rw [lintegral_eq_zero_iff hmt] at h0'
  filter_upwards [h0'] with s hs
  have hslice : Measurable fun ω : Ω => (‖Y₁ s ω - Y₂ s ω‖₊ : ℝ≥0∞) ^ 2 :=
    hm.comp (measurable_id.prodMk measurable_const)
  have hs0 : ∫⁻ ω, (‖Y₁ s ω - Y₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := hs
  rw [lintegral_eq_zero_iff hslice] at hs0
  filter_upwards [hs0] with ω hω
  have hω0 : (‖Y₁ s ω - Y₂ s ω‖₊ : ℝ≥0∞) ^ 2 = 0 := hω
  have hn : (‖Y₁ s ω - Y₂ s ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hω0
  have : Y₁ s ω - Y₂ s ω = 0 := by simpa using hn
  linarith [this]
/-- The diffusion coordinates of two solutions of the same backward equation differ by a
process of zero energy on the horizon. -/
theorem SolvesBSDEJ.unique_Z {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : SolvesBSDEJ D f ξ T Y₁ Z₁ U₁) (h₂ : SolvesBSDEJ D f ξ T Y₂ Z₂ U₂) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    ∀ j, Brownian.Ito.energy P T (fun ω s => Z₁ s ω j - Z₂ s ω j) = 0 := by
  have hYm₁ : Measurable (Function.uncurry fun ω s => Y₁ s ω) :=
    h₁.Y_meas.comp (measurable_snd.prodMk measurable_fst)
  have hYm₂ : Measurable (Function.uncurry fun ω s => Y₂ s ω) :=
    h₂.Y_meas.comp (measurable_snd.prodMk measurable_fst)
  have hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j) :=
    fun j => (h₁.Z_meas j).sub (h₂.Z_meas j)
  have hβ0 : (0 : ℝ) ≤ max 2 (24 * L ^ 2) := le_trans (by norm_num) (le_max_left _ _)
  exact (energies_eq_zero_of_wNorm_eq_zero hβ0 (hYm₁.sub hYm₂) hZm
    (SolvesBSDEJ.unique h₁ h₂ hT hf hL hlip hf0)).2.1
/-- The jump integrands of two solutions of the same backward equation differ by a marked
process of zero marked energy on the horizon. -/
theorem SolvesBSDEJ.unique_U {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : SolvesBSDEJ D f ξ T Y₁ Z₁ U₁) (h₂ : SolvesBSDEJ D f ξ T Y₂ Z₂ U₂) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ s ω e - U₂ s ω e) = 0 := by
  have hYm₁ : Measurable (Function.uncurry fun ω s => Y₁ s ω) :=
    h₁.Y_meas.comp (measurable_snd.prodMk measurable_fst)
  have hYm₂ : Measurable (Function.uncurry fun ω s => Y₂ s ω) :=
    h₂.Y_meas.comp (measurable_snd.prodMk measurable_fst)
  have hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j) :=
    fun j => (h₁.Z_meas j).sub (h₂.Z_meas j)
  have hβ0 : (0 : ℝ) ≤ max 2 (24 * L ^ 2) := le_trans (by norm_num) (le_max_left _ _)
  exact (energies_eq_zero_of_wNorm_eq_zero hβ0 (hYm₁.sub hYm₂) hZm
    (SolvesBSDEJ.unique h₁ h₂ hT hf hL hlip hf0)).2.2
end LevyStochCalc.BSDEJ.Solves


