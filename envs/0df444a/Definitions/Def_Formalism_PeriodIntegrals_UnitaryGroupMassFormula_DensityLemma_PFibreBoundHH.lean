-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundHH
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundHH
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T20:52:41.436297+00:00
-- url     : https://prove2.me/theorems/ff38b677-7686-4cf8-b38f-230914220716
-- title:
--   PFibre Bound HH
-- statement:
--   Definitions and structural lemmas for PFibre Bound HH, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFibreBoundHH.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm
def UnipotentSetIsClosedSubgroup : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → B2.IsClosedSubgroup (C2.N0set k r z)
def NuConc : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → nuZ k r z (C2.N0set k r z)ᶜ = 0
def NuLeft : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z →
    ∀ a ∈ C2.N0set k r z, (nuZ k r z).map (lmulM a) = nuZ k r z
def NuFin : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z →
    ∀ K : Set (Mt k r), IsCompact K → nuZ k r z K < ∞
def NuNeZero : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → nuZ k r z ≠ 0
end PI.UnitaryGroupMassFormula.DLm


