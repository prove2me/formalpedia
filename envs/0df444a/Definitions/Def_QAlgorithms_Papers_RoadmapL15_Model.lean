-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapL15_Model
-- name    : QAlgorithms_Papers_RoadmapL15_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:23.677987+00:00
-- url     : https://prove2.me/theorems/b8977f6e-0b4b-413f-b35b-c036759a8d6c
-- title:
--   Shadow Tomography of Quantum States: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Shadow Tomography of Quantum States, arXiv:1711.01053v2, https://arxiv.org/abs/1711.01053v2. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_ShadowTomographyPrograms
noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.RoadmapL15

open CopyMeasurements ShadowTomography

/-- Substitute physical outcome-dependent programs at the leaves of a finite adaptive
measurement program. This does not postselect on the unknown state. -/
def followMeasurement {I A B : Type} [Fintype I] [DecidableEq I]
    (P : AdaptiveMeasurementProcedure I A) (next : A → AdaptiveMeasurementProcedure I B) :
    AdaptiveMeasurementProcedure I B :=
  match P with
  | .output a => next a
  | .measure o K rest => .measure o K (fun j => followMeasurement (rest j) next)

/-- Aaronson, arXiv:1711.01053v2, PDF p.16: signed amplified deviation effects.
True searches for an underestimate; false searches for an overestimate. -/
def deviationEffect {D M : ℕ} (E : Fin M → Matrix (Fin D) (Fin D) ℂ)
    (sigma : Matrix (Fin D) (Fin D) ℂ) (eps : ℝ) (q : ℕ) (candidate : Fin M × Bool) :
    Matrix (Fin q → Fin D) (Fin q → Fin D) ℂ :=
  ∑ b : Fin q → Bool,
    if (if candidate.2 then
        (effectProb (E candidate.1) sigma + 3 * eps / 4) * q ≤ (hammingWeight b : ℝ)
      else (hammingWeight b : ℝ) ≤ (effectProb (E candidate.1) sigma - 3 * eps / 4) * q)
    then Matrix.of (fun x y => ∏ i : Fin q,
      (if b i then E candidate.1 else 1 - E candidate.1) (x i) (y i))
    else 0

/-- The classical matrix-multiplicative-weights replacement on PDF p.19, instantiated
with signed linear losses. An underestimate adds loss -E_j; an overestimate adds E_j.
The empty history gives the maximally mixed hypothesis. -/
def onlineHypothesis {D M T : ℕ} (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (eta : ℝ)
    (history : Fin T → Option (Fin M × Bool)) : Matrix (Fin D) (Fin D) ℂ :=
  gibbsState (-(eta : ℂ) • ∑ i : Fin T, match history i with
    | none => 0
    | some (j, sign) => if sign then -E j else E j)

/-- Known-data construction data for the source composition (PDF pp.13--19).
The OR subroutine is an actual finite adaptive quantum-instrument program on the copies,
not a correctness assumption or an oracle for the unknown state. Its arguments are
amplified known effects, threshold, gap, and failure tolerance. Round and search path
allow fresh registers for successive calls. Instrument Kraus data include temporary
ancillas. No runtime or finite encoding of arbitrary complex effects is imposed. -/
structure SourceComposition (D M : ℕ) where
  copies : ℕ
  rounds : ℕ
  amplification : ℕ
  amplification_pos : 0 < amplification
  eta : ℝ
  eta_pos : 0 < eta
  orProgram : ℕ → List Bool →
    List (Matrix (Fin amplification → Fin D) (Fin amplification → Fin D) ℂ) →
    ℝ → ℝ → ℝ → AdaptiveMeasurementProcedure ((Fin copies → Fin D) × Fin 1) Bool

/-- Apply the physical OR subprogram to the constructed deviation effects. -/
def runOr {D M : ℕ} (S : SourceComposition D M)
    (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (eps : ℝ)
    (sigma : Matrix (Fin D) (Fin D) ℂ) (t : ℕ) (path : List Bool)
    (candidates : List (Fin M × Bool)) (threshold gap failure : ℝ) :
    AdaptiveMeasurementProcedure ((Fin S.copies → Fin D) × Fin 1) Bool :=
  S.orProgram t path
    (candidates.map (deviationEffect E sigma eps S.amplification)) threshold gap failure

/-- Lemma 15, PDF pp.14--15: binary search, losing gap in the threshold at each level.
Each decision call is a physical adaptive measurement program. -/
def gentleBinarySearch {D M : ℕ} (S : SourceComposition D M)
    (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (eps : ℝ)
    (sigma : Matrix (Fin D) (Fin D) ℂ) (t : ℕ) (gap failure : ℝ) :
    ℕ → List Bool → List (Fin M × Bool) → ℝ →
      AdaptiveMeasurementProcedure ((Fin S.copies → Fin D) × Fin 1)
        (Option (Fin M × Bool))
  | 0, _, candidates, _ => .output candidates.head?
  | fuel + 1, path, candidates, threshold =>
      if candidates.length ≤ 1 then .output candidates.head?
      else
        let left := candidates.take ((candidates.length + 1) / 2)
        let right := candidates.drop ((candidates.length + 1) / 2)
        followMeasurement (runOr S E eps sigma t path left threshold gap failure) fun accepted =>
          gentleBinarySearch S E eps sigma t gap failure fuel (path ++ [accepted])
            (if accepted then left else right) (threshold - gap)

/-- First test for a discrepancy, then search the signed list. PDF p.16 supplies the gap
5/6 - 2/3 = 1/6. Ceiling-log depth covers lists whose length is not a power of two.
The classical error budget is allocated across rounds and decision calls. -/
def gentleRound {D M : ℕ} (S : SourceComposition D M)
    (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (eps delta : ℝ)
    (sigma : Matrix (Fin D) (Fin D) ℂ) (t : ℕ) :
    AdaptiveMeasurementProcedure ((Fin S.copies → Fin D) × Fin 1)
      (Option (Fin M × Bool)) :=
  let candidates := (List.finRange M).flatMap fun j => [(j, true), (j, false)]
  let depth := Nat.clog 2 (2 * M)
  let gap := (1 / 6 : ℝ) / (max 1 depth : ℕ)
  let failure := delta / (2 * (max 1 S.rounds : ℕ) * (depth + 1))
  followMeasurement (runOr S E eps sigma t [] candidates (5 / 6) gap failure) fun found =>
    if found then gentleBinarySearch S E eps sigma t gap failure depth [true] candidates (5 / 6)
    else .output none

/-- Execute the gentle-search/online-update composition of PDF p.19. Only measurement
outcomes determine the history; the constructor does not receive the unknown state. -/
def onlineLoop {D M : ℕ} (S : SourceComposition D M)
    (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (eps delta : ℝ) :
    ℕ → ℕ → (Fin S.rounds → Option (Fin M × Bool)) →
      AdaptiveMeasurementProcedure ((Fin S.copies → Fin D) × Fin 1)
        (Fin S.rounds → Option (Fin M × Bool))
  | 0, _, history => .output history
  | fuel + 1, t, history =>
      if ht : t < S.rounds then
        followMeasurement
          (gentleRound S E eps delta (onlineHypothesis E S.eta history) t) fun candidate =>
            match candidate with
            | none => .output history
            | some c => onlineLoop S E eps delta fuel (t + 1)
                (Function.update history ⟨t, ht⟩ (some c))
      else .output history

/-- Predictions in the source's interval [0,1]. Clipping is immaterial for valid effects
and density hypotheses and defines the unused bad-data branches without assumptions. -/
def intervalPrediction (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨min 1 (max 0 x), le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- Compile the source composition to the frozen procedure interface. Outcomes encode
the complete finite history; decoding executes the same classical online updates.
The auxiliary dimension is one: temporary ancillas are absorbed into Kraus instruments. -/
def sourceProcedure {D M : ℕ} (S : SourceComposition D M)
    (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (eps delta : ℝ) : TomographyProcedure D M where
  copies := S.copies
  ancillas := 1
  outcomes := Fintype.card (Fin S.rounds → Option (Fin M × Bool))
  initialAncilla := 1
  initial_density := ⟨Matrix.PosSemidef.one, by simp⟩
  procedure := followMeasurement (onlineLoop S E eps delta S.rounds 0 (fun _ => none))
    (fun history => .output ((Fintype.equivFin _) history))
  decode := fun o i => intervalPrediction
    (effectProb (E i) (onlineHypothesis E S.eta ((Fintype.equivFin _).symm o)))

/-- One known-data constructor for the composition. Its inputs contain no unknown state,
success assumptions, or Boolean computability flags. -/
structure SourceCompositionFamily where
  construct : (D M : ℕ) → (Fin M → Matrix (Fin D) (Fin D) ℂ) →
    ℝ → ℝ → SourceComposition D M


end QAlgorithms.Papers.RoadmapL15


