-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqFlatMapFourierJacobiRow
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqFlatMapFourierJacobiRow
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:41.529634+00:00
-- url     : https://prove2.me/theorems/f8b1a70b-c9cc-407a-a6ac-76a5e5e04e59
-- title:
--   Partial Reduction Eq Flat Map Fourier Jacobi Row
-- statement:
--   Definitions and structural lemmas for Partial Reduction Eq Flat Map Fourier Jacobi Row, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEqFlatMapFourierJacobiRow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
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
namespace GlobalTheory.RedFlatRow
open GlobalTheory.PartRed GlobalTheory.LocFlat
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
theorem mem_transSet_union_upSet (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) ↔ Free (ρ + 1) e := by
  rcases e with ⟨r | l, s | i⟩ <;> simp only [transSet, upSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] <;> simp [Free] <;> omega
def freeEquiv (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) :
    {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} ≃
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} :=
  Equiv.subtypeEquivRight (mem_transSet_union_upSet ρ)
end GlobalTheory.RedFlatRow


