-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:36.905264+00:00
-- url     : https://prove2.me/theorems/5649d83f-2a9d-4db7-b2a1-43f7a7908a3d
-- title:
--   Curv Sub Quot Taut Pair Gram
-- statement:
--   Definitions and structural lemmas for Curv Sub Quot Taut Pair Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CurvSubQuotTautPairGram.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero


set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
namespace GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
def pairFrame (z : ℂ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  fromBlocks 1 0 (of fun _ _ => z) 1
example : wedge (fun ξ η : Fin 2 → ℂ => ξ 0 * conj (η 0)) (fun ξ η => ξ 1 * conj (η 1))
      ![1, 0] ![1, 0] ![0, 1] ![0, 1] = 1 ∧
    wedge (fun ξ η : Fin 2 → ℂ => ξ 0 * conj (η 0)) (fun ξ η => ξ 1 * conj (η 1))
      ![1, 0] ![0, 1] ![0, 1] ![1, 0] = -1 := by
  simp [wedge]
example (C : ℝ) : ¬ OneFormBound {0} (fun _ : Fin 1 → ℂ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
    (fun _ => 1) (fun _ _ => 1) C := fun h => by
  simpa using (h 0 rfl).1.diag_pos (i := 0)
end GlobalTheory.HermFrame.Model


