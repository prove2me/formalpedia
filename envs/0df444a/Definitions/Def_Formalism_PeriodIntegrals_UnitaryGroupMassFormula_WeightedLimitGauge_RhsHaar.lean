-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:46.852299+00:00
-- url     : https://prove2.me/theorems/f99b85d7-ba29-44af-bd4e-8b1c2c403897
-- title:
--   Rhs Haar
-- statement:
--   Definitions and structural lemmas for Rhs Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsHaar.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
def RhsWInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ s ∈ UWb k r, ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      rhsW k r z z' μW μW' μsec (fun x => φ (lmulM s x)) = rhsW k r z z' μW μW' μsec φ
namespace ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
def secP (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  if Tz k r z * Tz k r z' < Complex.normSq ζ then μsec ζ else 1
def wD (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : ℝ≥0∞ :=
  if Tz k r z * Tz k r z' < Complex.normSq ζ then ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) else 0
def chartF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (q : ℂ × Mt k r × Mt k r) : Mt k r :=
  fun i j => (Matrix.of q.2.1 * embWb k r (secP k r z z' μsec q.1) * (Matrix.of q.2.2)⁻¹) i j
def srcM (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) :
    Measure (ℂ × Mt k r × Mt k r) :=
  ((volume : Measure ℂ).withDensity (wD k r z z')).prod (μW.prod μW')
def nuR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Measure (Mt k r) :=
  (srcM k r z z' μW μW').map (chartF k r z z' μsec)
def zF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : ℂ := herm (Hpk k r) (Matrix.of x *ᵥ z') z
def goodS (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (ℂ × Mt k r × Mt k r) :=
  {q | Tz k r z * Tz k r z' < Complex.normSq q.1 ∧ Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ UWset k r z'}
def gC (k r : ℕ) (p : (Fin (k + 1) → Fin (k + 1) → ℂ) × Mt k r × Mt k r) : Mt k r :=
  fun i j => (Matrix.of p.2.1 * embWb k r (Matrix.of p.1) * Matrix.of p.2.2) i j
end ZetaZeros
end PI.RhsWLim.W


