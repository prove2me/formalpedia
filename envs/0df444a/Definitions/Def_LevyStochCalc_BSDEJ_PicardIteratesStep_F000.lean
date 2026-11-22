-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesStep_F000
-- name    : LevyStochCalc_BSDEJ_PicardIteratesStep_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:47:51.806476+00:00
-- url     : https://prove2.me/theorems/22eb0cf8-cf8f-4d3c-acb2-b54eb8219853
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardIteratesStep
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardIteratesStep. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F001
import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorModification_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionBounds_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionContraction_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F001
import Definitions.Def_LevyStochCalc_Probability_MarkedProgressiveSlice_F000
import Definitions.Def_SourceProof_8bb8c09ab790bf7a224b8ffd
import Definitions.Def_SourceProof_92f1c4f0edeefcc7ea434347
import Definitions.Def_SourceProof_be0f56f10988c86fe4ec7fca
import Definitions.Def_SourceProof_ee2057ecba7f5d9e6355867b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissible triples and the Picard iterates of a backward equation with jumps

An admissible triple carries the measurability, progressive measurability and square
integrability the Picard step of the backward equation driven by a Lévy driver consumes. The
generator frozen along an admissible triple then has a jointly and progressively measurable
version of finite energy that vanishes off the horizon, the output triple of the step along an
admissible triple is again admissible, and so the step iterates from any admissible starting
triple, giving the sequence of Picard iterates.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Admissible triples -/

/-- `(Y, Z, U)` is an admissible triple for the horizon `T`: the triples on which the Picard
step of the backward equation driven by `D` is defined. -/
structure Admissible (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (T : ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop where
  /-- `Y` is jointly measurable. -/
  Y_meas : Measurable (Function.uncurry Y)
  /-- `Y` is progressively measurable for the right-continuous augmented joint filtration. -/
  Y_prog : LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D).rightCont
    fun ω s => Y s ω
  /-- `Y` has finite energy on the horizon. -/
  Y_sq : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i)
  /-- Each coordinate of `Z` is progressively measurable for the augmented joint filtration. -/
  Z_prog : ∀ i : Fin d,
    LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D) fun ω s => Z s ω i
  /-- `Z` vanishes off the horizon. -/
  Z_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤
  /-- `U` is jointly measurable in the sample point, the time and the mark. -/
  U_meas : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2
  /-- `U` is marked progressively measurable for the augmented joint filtration. -/
  U_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable (augJoint D)
    fun ω s e => U s ω e
  /-- `U` vanishes off the horizon. -/
  U_vanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0
  /-- `U` has finite marked energy on the horizon. -/
  U_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤
/-- The output triple of a Picard step is admissible. -/
theorem PicardOutput.admissible {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y' Y : ℝ → Ω → ℝ} {Z' Z : ℝ → Ω → (Fin d → ℝ)} {U' U : ℝ → Ω → E → ℝ}
    (h : PicardOutput D f ξ T Y' Z' U' Y Z U) : Admissible D T Y Z U where
  Y_meas := h.Y_meas
  Y_prog := _root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421
    (fun t => h.Y_adapted t) fun ω t => (h.Y_cadlag ω t).1
  Y_sq := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.Y_sup.ne) _root_.Prove2MeSourceProof.h_8bb8c09ab790bf7a224b8ffd
  Z_meas := h.Z_meas
  Z_prog := h.Z_prog
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_meas := h.U_meas
  U_prog := h.U_prog
  U_vanish := h.U_vanish
  U_sq := h.U_sq
/-! ### The drift of an admissible triple -/

/-- The generator frozen along an admissible triple has a jointly and progressively measurable
version of finite energy that vanishes off the horizon. -/
theorem Admissible.exists_drift {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : Admissible D T Y Z U) (hT : 0 < T)
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
  have hle : ∀ t : ℝ, (augJoint D) t ≤ (augJoint D).rightCont t := fun t =>
    Filtration.le_rightCont _ t
  obtain ⟨b, hbm, hbp, hbz, hbq, hb⟩ :=
    _root_.Prove2MeSourceProof.h_be0f56f10988c86fe4ec7fca (L := L) D.N (augJoint D).rightCont hf
      hlip hT hf0 h.Y_meas h.Y_prog h.Y_sq h.Z_meas (fun i => (h.Z_prog i).mono hle) h.Z_sq
      h.U_meas (h.U_prog.mono hle)
      (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq)
  obtain ⟨b', hb'm, hb'p, hb'z, hb'q, hb'⟩ :=
    _root_.Prove2MeSourceProof.h_ee2057ecba7f5d9e6355867b (P := P) (ℱ := augJoint D)
      hbm hbp hbz hbq
  refine ⟨b', hb'm, hb'p, hb'z, hb'q, ?_⟩
  filter_upwards [hb', hb] with p h1 h2
  rw [h1, h2]
/-! ### The Picard step on admissible triples -/

/-- A triple of a value process, a diffusion integrand and a jump integrand. -/
abbrev Triple (Ω : Type u) (E : Type v) (d : ℕ) : Type max u v :=
  (ℝ → Ω → ℝ) × (ℝ → Ω → (Fin d → ℝ)) × (ℝ → Ω → E → ℝ)
/-- `(Y₁, Z₁, U₁)` is an output of the Picard step along `(Y, Z, U)`: it is a `PicardOutput`
for a drift that is jointly and progressively measurable, has finite energy, vanishes off the
horizon and agrees almost everywhere with the generator frozen along `(Y, Z, U)`. -/
def IsStep (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) (ξ : Ω → ℝ) (T : ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
    (Y₁ : ℝ → Ω → ℝ) (Z₁ : ℝ → Ω → (Fin d → ℝ)) (U₁ : ℝ → Ω → E → ℝ) : Prop :=
  ∃ b : Ω → ℝ → ℝ, Measurable (Function.uncurry b)
    ∧ Probability.ProgressivelyMeasurable (augJoint D) b
    ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    ∧ Brownian.Ito.energy P T b ≠ ⊤
    ∧ (∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
        b p.1 p.2 = f p.2 (Y p.2 p.1) (Z p.2 p.1) (U p.2 p.1))
    ∧ PicardOutput D f ξ T Y Z U Y₁ Z₁ U₁
/-- The Picard step along an admissible triple has an admissible output triple. -/
theorem Admissible.exists_step {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : Admissible D T Y Z U) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P) :
    ∃ (Y₁ : ℝ → Ω → ℝ) (Z₁ : ℝ → Ω → (Fin d → ℝ)) (U₁ : ℝ → Ω → E → ℝ),
      Admissible D T Y₁ Z₁ U₁ ∧ IsStep D f ξ T Y Z U Y₁ Z₁ U₁ := by
  obtain ⟨b, hbm, hbp, hbz, hbq, hb⟩ := h.exists_drift (L := L) hT hf hlip hf0
  obtain ⟨Y₁, Z₁, U₁, hout⟩ := _root_.Prove2MeSourceProof.h_92f1c4f0edeefcc7ea434347 D f hT hξ2 hξm Y Z U hbm
    (hbp.mono fun t => Filtration.le_rightCont _ t) hbz hbq hb
  exact ⟨Y₁, Z₁, U₁, hout.admissible, b, hbm, hbp, hbz, hbq, hb, hout⟩
/-- The Picard step along an admissible triple, as an existential over triples. -/
theorem Admissible.exists_stepTriple {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ} {p : Triple Ω E d}
    (h : Admissible D T p.1 p.2.1 p.2.2) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun q : ℝ × ℝ × (Fin d → ℝ) => f q.1 q.2.1 q.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P) :
    ∃ q : Triple Ω E d, Admissible D T q.1 q.2.1 q.2.2
      ∧ IsStep D f ξ T p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := by
  obtain ⟨Y₁, Z₁, U₁, hA, hS⟩ := h.exists_step (L := L) hT hf hlip hf0 hξ2 hξm
  exact ⟨(Y₁, Z₁, U₁), hA, hS⟩
/-! ### The sequence of Picard iterates -/

section Iterates

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}

/-- The admissible triples of the backward equation driven by `D` over the horizon `T`. -/
abbrev AdmTriple (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (T : ℝ) :
    Type max u v :=
  {p : Triple Ω E d // Admissible D T p.1 p.2.1 p.2.2}
variable (hT : 0 < T)
  (hf : ∀ u : E → ℝ, Measurable fun q : ℝ × ℝ × (Fin d → ℝ) => f q.1 q.2.1 q.2.2 u)
  (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
    (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
  (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
  (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)

/-- One Picard step, as a map on admissible triples. -/
noncomputable def stepAdm (q : AdmTriple D T) : AdmTriple D T :=
  ⟨Classical.choose (q.2.exists_stepTriple (L := L) hT hf hlip hf0 hξ2 hξm),
    (Classical.choose_spec (q.2.exists_stepTriple (L := L) hT hf hlip hf0 hξ2 hξm)).1⟩
/-- The sequence of Picard iterates from an admissible starting triple. -/
noncomputable def picardSeq (p₀ : AdmTriple D T) (n : ℕ) : Triple Ω E d :=
  ((stepAdm hT hf hlip hf0 hξ2 hξm)^[n] p₀).val
/-- The Picard iterates start at the given triple. -/
theorem picardSeq_zero (p₀ : AdmTriple D T) :
    picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0 = p₀.val := rfl
/-- Every Picard iterate is admissible. -/
theorem picardSeq_admissible (p₀ : AdmTriple D T) (n : ℕ) :
    Admissible D T (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 :=
  ((stepAdm hT hf hlip hf0 hξ2 hξm)^[n] p₀).2
/-- Each Picard iterate is an output of the Picard step along its predecessor. -/
theorem picardSeq_succ_isStep (p₀ : AdmTriple D T) (n : ℕ) :
    IsStep D f ξ T (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 := by
  have hsucc : picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)
      = (stepAdm hT hf hlip hf0 hξ2 hξm
          ((stepAdm hT hf hlip hf0 hξ2 hξm)^[n] p₀)).val :=
    congrArg Subtype.val (Function.iterate_succ_apply' _ n p₀)
  rw [hsucc]
  exact (Classical.choose_spec
    ((((stepAdm hT hf hlip hf0 hξ2 hξm)^[n] p₀).2).exists_stepTriple
      (L := L) hT hf hlip hf0 hξ2 hξm)).2
/-- Each Picard iterate is a `PicardOutput` along its predecessor. -/
theorem picardSeq_succ_picardOutput (p₀ : AdmTriple D T) (n : ℕ) :
    PicardOutput D f ξ T (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 := by
  obtain ⟨b, -, -, -, -, -, hout⟩ := picardSeq_succ_isStep hT hf hlip hf0 hξ2 hξm p₀ n
  exact hout
end Iterates

end LevyStochCalc.BSDEJ.Solves


