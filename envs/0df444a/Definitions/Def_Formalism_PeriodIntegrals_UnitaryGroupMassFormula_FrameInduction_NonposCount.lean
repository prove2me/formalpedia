-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T15:18:42.027259+00:00
-- url     : https://prove2.me/theorems/9bfe7fe7-67ed-43ee-8fbc-68668f9394d3
-- title:
--   Nonpos Count
-- statement:
--   Definitions and structural lemmas for Nonpos Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/NonposCount.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
namespace PI.FrameInd
lemma isHerm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    (gramM k r z z' g).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [gramM]
  exact (ggHerm_swap _ (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r) _ _).symm
def PosCount : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 →
    Fintype.card {i // 0 < (isHerm k r z z' γ).eigenvalues i} ≤ r + 1
def NonposCount : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 →
    Fintype.card {i // ¬ 0 < (isHerm k r z z' γ).eigenvalues i} ≤ r + 1
end PI.FrameInd


