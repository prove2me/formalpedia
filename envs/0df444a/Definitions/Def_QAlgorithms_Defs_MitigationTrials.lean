-- Prove2me | Definitions.Def_QAlgorithms_Defs_MitigationTrials
-- name    : QAlgorithms_Defs_MitigationTrials
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:21:29.79848+00:00
-- url     : https://prove2.me/theorems/37191e3e-f598-4233-9fe2-677d1056ac99
-- title:
--   MitigationTrials
-- statement:
--   MitigationTrials
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MitigationTrials.lean

import Definitions.Def_QAlgorithms_Defs_MitigationPhysicalExperiments
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.ErrorMitigation

/-- Full coefficient-choice space (1712.09271 pp.4,19). -/
abbrev CircuitChoice {n : ℕ} (D : MitigationDesign n) := (j : Fin D.slots) → Fin (D.choices j)

/-- Actual joint outcome, including zero-observable bypass and physical rejects
(1712.09271 pp.5,19). -/
abbrev Trial {n : ℕ} (D : MitigationDesign n) :=
  Option ((choice : CircuitChoice D) × Option (Fin (modifiedCircuit D choice).readout.outcomes))

/-- Overhead is the product of absolute coefficient masses (1712.09271 p.19, I15). -/
def overhead {n : ℕ} (D : MitigationDesign n) : ℝ := ∏ j, coefficientMass (D.coefficient j)

/-- arxiv-1712.09271v2 PDF p.4; arxiv-1712.09271v2 PDF p.5; arxiv-1712.09271v2 PDF p.19. -/
def trialLaw {n : ℕ} (D : MitigationDesign n) : Trial D → ℝ :=
  fun trial => if overhead D = 0 then (if trial = none then 1 else 0) else
    match trial with
    | none => 0
    | some result => (∏ j, |D.coefficient j (result.1 j)|/coefficientMass (D.coefficient j)) *
        executeModifiedCircuit (modifiedCircuit D result.1) result.2

/-- arxiv-1712.09271v2 PDF p.4; arxiv-1712.09271v2 PDF p.19. -/
def effectiveEstimator {n : ℕ} (D : MitigationDesign n) : Trial D → ℝ
  | none => 0
  | some result => (Real.sign (∏ j, D.coefficient j (result.1 j))) *
      (match result.2 with | none => 0 | some o => (modifiedCircuit D result.1).readout.value o)

/-- arxiv-1712.09271v2 PDF p.4; arxiv-1712.09271v2 PDF p.19. -/
def repeatedTrialLaw {n : ℕ} (D : MitigationDesign n) (R : ℕ) (_hR : 0 < R) :
    (Fin R → Trial D) → ℝ := fun trials => ∏ i, trialLaw D (trials i)

/-- The reported C/R times signed mean (1712.09271 pp.4,19). -/
def reportedEstimator {n : ℕ} (D : MitigationDesign n) (R : ℕ) (_hR : 0 < R)
    (trials : Fin R → Trial D) : ℝ := overhead D/(R : ℝ)*∑ i, effectiveEstimator D (trials i)

/-- Sanity check for the source model (arxiv-1712.09271v2 PDF p.4). -/
example {n : ℕ} (D : MitigationDesign n) : effectiveEstimator D none = 0 := rfl

/-- Sanity check for the source model (arxiv-1712.09271v2 PDF p.4). -/
example {n : ℕ} (D : MitigationDesign n) (h : overhead D = 0) : trialLaw D none = 1 := by
  simp [trialLaw,h]

end QAlgorithms.ErrorMitigation


