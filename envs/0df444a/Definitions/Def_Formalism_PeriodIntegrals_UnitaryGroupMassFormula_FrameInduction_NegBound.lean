-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:37:31.309518+00:00
-- url     : https://prove2.me/theorems/4223ac05-e97f-443b-8313-b19342934ce7
-- title:
--   Neg Bound
-- statement:
--   Definitions and structural lemmas for Neg Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/NegBound.lean

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
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
def NegBound : Prop :=
  ∀ (k r : ℕ) (S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ)),
    (∀ x ∈ S, (herm (Hpk k r) x x).re ≤ 0) → Module.finrank ℂ S ≤ r + 1
def SignQ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Prop :=
  ∃ Q : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ, IsUnit Q.det ∧
    Qᴴ * gramM k r z z' γ * Q = Matrix.fromBlocks 1 0 0 (-1)
def SignStep : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 → SignQ k r z z' γ
def UPos : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 → SignQ k r z z' γ →
    ∀ v ∈ Uperp k r z z' γ, v ≠ 0 → 0 < (herm (Hpk k r) v v).re
end PI.FrameInd


