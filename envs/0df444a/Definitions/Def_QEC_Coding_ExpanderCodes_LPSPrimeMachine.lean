-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
-- name    : QEC_Coding_ExpanderCodes_LPSPrimeMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:31:04.658977+00:00
-- url     : https://prove2.me/theorems/1f590ec0-489b-4176-be1b-7a00dc866760
-- title:
--   LPSPrime Machine
-- statement:
--   Definitions and structural lemmas for LPSPrime Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPrimeMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryResiduePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_q_le_two_mul_card_psl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Turing StateTransition
open QEC.Coding.BitTuring
open QEC.Coding.BitTuring.UnaryArithmetic
def lpsPrimeMachine {p : ℕ} (hp : p.Prime) : Machine :=
  ResiduePrime.fullMachine (4*p) (Nat.mul_pos (by norm_num) hp.pos)
noncomputable def lpsPrimeMachineExec {p : ℕ} (hp : p.Prime) (B : ℕ) :
    EvalsToInTime (TM2.step (lpsPrimeMachine hp).program) ((lpsPrimeMachine hp).init (unary B))
      (some ((lpsPrimeMachine hp).halt (unary (lpsLeastPrimeAbove hp B))))
      (ResiduePrime.fullTime.eval (lpsLeastPrimeAbove hp B)) := by
  have h := lpsLeastPrimeAbove_spec hp B
  exact ResiduePrime.fullExec (4*p) (Nat.mul_pos (by norm_num) hp.pos) B _ h.1 h.2
    (fun n hB hn he => Nat.find_min (exists_lpsPrimeCandidate hp B) hn ⟨hB,he⟩)
open scoped MatrixGroups
noncomputable def lpsPrimeMachineBlockExec {p : ℕ} (hp : p.Prime) (hp4 : p%4=1) (B : ℕ) :
    EvalsToInTime (TM2.step (lpsPrimeMachine hp).program) ((lpsPrimeMachine hp).init (unary B))
      (some ((lpsPrimeMachine hp).halt (unary (lpsEffectiveResiduePrimeAt hp hp4 B).q)))
      (ResiduePrime.fullTime.eval (2*Fintype.card PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q))) := by
  have h := lpsPrimeMachineExec hp B
  rw [← lpsEffectiveResiduePrimeAt_q hp hp4 B] at h
  refine {h with steps_le_m := h.steps_le_m.trans ?_}
  exact Composition.polynomial_eval_monotone ResiduePrime.fullTime
    (lpsEffectiveResiduePrimeAt hp hp4 B).q_le_two_mul_card_psl
noncomputable def lpsPrimeMachineOutputsInTime {p : ℕ} (hp : p.Prime) (hp4 : p%4=1) (B : ℕ) :
    TM2OutputsInTime (lpsPrimeMachine hp).toFinTM2 (unary B)
      (some (unary (lpsEffectiveResiduePrimeAt hp hp4 B).q))
      (ResiduePrime.fullTime.eval (2*Fintype.card PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q))) :=
  Machine.outputsInTime _ _ _ _ (lpsPrimeMachineBlockExec hp hp4 B)
end QEC.Coding.TannerLiftedProduct


