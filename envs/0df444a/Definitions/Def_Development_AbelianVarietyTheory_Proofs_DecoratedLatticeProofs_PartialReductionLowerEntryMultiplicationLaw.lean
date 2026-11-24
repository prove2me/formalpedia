-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLaw
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLaw
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:50.425037+00:00
-- url     : https://prove2.me/theorems/d0d4ecd4-b523-45b9-a5a1-4d10c33189db
-- title:
--   Partial Reduction Lower Entry Multiplication Law
-- statement:
--   Definitions and structural lemmas for Partial Reduction Lower Entry Multiplication Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionLowerEntryMultiplicationLaw.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
namespace GlobalTheory.PartRed.LowLaw
section Alg
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def elem (r l : Fin c) (h : r ≠ l) (a : k) : GL (Fin c) k :=
  ⟨transvection r l a, transvection r l (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩
end Alg
end GlobalTheory.PartRed.LowLaw


