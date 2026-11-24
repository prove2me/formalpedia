-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLaw
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLaw
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:38.854025+00:00
-- url     : https://prove2.me/theorems/33d6d2f6-c1f4-4ce8-88c3-31db3eb59e0e
-- title:
--   Partial Reduction Upper Free Entry Translation Law
-- statement:
--   Definitions and structural lemmas for Partial Reduction Upper Free Entry Translation Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionUpperFreeEntryTranslationLaw.lean

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
namespace GlobalTheory.PartRed.UpperLaw
open GlobalTheory.PartRed
section Alg
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def elem (l m : Fin c) (h : l ≠ m) (a : k) : GL (Fin c) k :=
  ⟨transvection l m a, transvection l m (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩
variable {ρ : ℕ} {I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))}
def shear (ρ : ℕ) (I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (l m : Fin c) (a : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k) : I → k :=
  fun e => if e.1.1 = Sum.inr l then
    a * fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y (Sum.inr m) e.1.2 else 0
end Alg
end GlobalTheory.PartRed.UpperLaw


