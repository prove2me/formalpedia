-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanFubini
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanFubini
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:24.762677+00:00
-- url     : https://prove2.me/theorems/9ba007cd-cb66-4f8f-b0f9-9de8fa77f6c8
-- title:
--   PSphere Mean Fubini
-- statement:
--   Definitions and structural lemmas for PSphere Mean Fubini, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanFubini.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set
noncomputable section
namespace SphereMeanFubini
def groupSplit (k n : ℕ) : Fin n ⊕ (Fin k × Fin n) ≃ Fin (k + 1) × Fin n where
  toFun := Sum.elim (fun j => (0, j)) (fun p => (p.1.succ, p.2))
  invFun p := Fin.cases (motive := fun _ => Fin n ⊕ (Fin k × Fin n)) (Sum.inl p.2)
    (fun i => Sum.inr (i, p.2)) p.1
  left_inv := by rintro (j | ⟨i, j⟩) <;> simp
  right_inv := by
    rintro ⟨i, j⟩
    cases i using Fin.cases <;> simp
def consEquiv {n : ℕ} (k : ℕ) : ((Fin n → ℂ) × (Fin k × Fin n → ℂ)) ≃ᵐ (Fin (k + 1) × Fin n → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ (Fin k × Fin n) => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (groupSplit k n))
end SphereMeanFubini
end
end GroundTheory.Heights₂.Heights


