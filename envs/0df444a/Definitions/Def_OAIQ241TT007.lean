-- Prove2me | Definitions.Def_OAIQ241TT007
-- name    : OAIQ241TT007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:20.664202+00:00
-- url     : https://prove2.me/theorems/1e0abee1-c6f9-492a-863e-568dc6229a26
-- title:
--   Definitions bundle OAIQ241TT007 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 162 declarations of OpenAI's Lean: 10 definitions and 152 theorems. The definitions and types are `OAI.KS.W13.RationalAdd.totalTicks`, `OAI.KS.W13.RationalSubtract.changeSignTicks`, `OAI.KS.W13.RationalSubtract.prepareTicks`, `OAI.KS.W13.RationalSubtract.totalTicks`, `OAI.KS.W15.RationalMultiply.canonicalNormalizeTicks`, `OAI.KS.W15.RationalMultiply.rawCanonicalProduct`, `OAI.KS.W15.RationalMultiply.totalTicks`, `OAI.KS.W16.RationalSignAction.ticks`, `OAI.KS.W19.DivisionInput.loopStage`, `OAI.KS.W19.DivisionInput.secondStage`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_ArithmeticEncodingSize`, `MatrixSigning_Arithmetic_BinaryGCD`, `MatrixSigning_Arithmetic_BorrowSubtractor`, `MatrixSigning_Arithmetic_DivisionBodyTime`, `MatrixSigning_Arithmetic_DivisionInput`, `MatrixSigning_Arithmetic_DivisionLoopRun`, `MatrixSigning_Arithmetic_DivisionMachine`, `MatrixSigning_Arithmetic_FixedSubtraction`, `MatrixSigning_Arithmetic_GCDMachine`, `MatrixSigning_Arithmetic_GCDMachineRun`, `MatrixSigning_Arithmetic_GCDMachineStep`, `MatrixSigning_Arithmetic_RationalAddCorrect`, `MatrixSigning_Arithmetic_RationalAddModel`, `MatrixSigning_Arithmetic_RationalAddProgram`, `MatrixSigning_Arithmetic_RationalAddSigned`, `MatrixSigning_Arithmetic_RationalMagnitudeCorrect`, `MatrixSigning_Arithmetic_RationalMagnitudeDivision`, `MatrixSigning_Arithmetic_RationalMagnitudePositive`, `MatrixSigning_Arithmetic_RationalMagnitudeSetup`, `MatrixSigning_Arithmetic_RationalMagnitudeSign`, `MatrixSigning_Arithmetic_RationalMultiplicationMachine`, `MatrixSigning_Arithmetic_RationalMultiplyNormalize`, `MatrixSigning_Arithmetic_RationalMultiplyProducts`, `MatrixSigning_Arithmetic_RationalSignAction`, `MatrixSigning_Arithmetic_RationalSubtractCorrect`, `MatrixSigning_Arithmetic_RationalSubtractProgram`, `MatrixSigning_Arithmetic_SingleRationalParser`, `MatrixSigning_Complexity_BinaryGCDCost`, `MatrixSigning_Complexity_GCDMachinePolynomial`, `MatrixSigning_Machines_BorrowActivity`, `MatrixSigning_Machines_FixedCopyRestore`, `MatrixSigning_Machines_FixedDotPrimitives`, `MatrixSigning_Machines_FixedRun`, `MatrixSigning_Realization_FixedSubroutineBridge`.
--
--   **Imports.** It imports the bundles `OAIQ241TT004` and `OAIQ241TT005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ241TT010` and `OAIQ241TT011`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ241TT004
import Definitions.Def_OAIQ241TT005

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ArithmeticEncodingSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

theorem rational_parts_size_le_length (q : ℚ) :
    Nat.size q.num.natAbs ≤ ratLength q ∧ Nat.size q.den ≤ ratLength q := by
  have hn := natAbs_size_le_payload_size_add_one q.num
  unfold ratLength
  rw [length_encodeRat]
  simp only [natPayloadLength_eq_size]
  constructor <;> omega

theorem rational_parts_le_two_pow_length (q : ℚ) :
    q.num.natAbs ≤ 2 ^ ratLength q ∧ q.den ≤ 2 ^ ratLength q := by
  have hs := rational_parts_size_le_length q
  constructor
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hs.1)
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hs.2)

theorem ratLength_le_of_parts (q : ℚ) (b c : ℕ)
    (hn : q.num.natAbs ≤ 2 ^ b) (hd : q.den ≤ 2 ^ c) :
    ratLength q ≤ 2 * (b + c) + 7 := by
  have hnum := Nat.size_le_size ((intPayload_le_natAbs q.num).trans hn)
  have hden := Nat.size_le_size hd
  simp only [Nat.size_pow] at hnum hden
  unfold ratLength
  rw [length_encodeRat]
  simp only [natPayloadLength_eq_size]
  omega

theorem ratLength_add_le (q r : ℚ) :
    ratLength (q + r) ≤ 4 * (ratLength q + ratLength r) + 9 := by
  obtain ⟨hqnum, hqden⟩ := rational_parts_le_two_pow_length q
  obtain ⟨hrnum, hrden⟩ := rational_parts_le_two_pow_length r
  obtain ⟨hn, hd⟩ := KS.W30.add_parts_le_two_pow q r (ratLength q) (ratLength r)
    hqnum hqden hrnum hrden
  have h := ratLength_le_of_parts (q + r) _ _ hn hd
  omega

theorem ratLength_neg_le (q : ℚ) : ratLength (-q) ≤ 4 * ratLength q + 7 := by
  obtain ⟨hn, hd⟩ := rational_parts_le_two_pow_length q
  have h := ratLength_le_of_parts (-q) (ratLength q) (ratLength q)
    (by simpa using hn) (by simpa using hd)
  omega

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.BinaryGCD
open KS.W19

theorem gcdBits_length_le_right (xs ys : List Bool) (hy : 0 < bitsValue ys) :
    (gcdBits xs ys).length ≤ ys.length := by
  rw [gcdBits_eq_encodeNat, encodeNat_length_eq_size]
  exact (Nat.size_le_size (Nat.gcd_le_right _ hy)).trans
    (Nat.size_le.mpr (bitsValue_lt_two_pow_length ys))

end KS.W30.BinaryGCD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BorrowSubtractor
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BorrowSubtractor
open KS.W29
open KS.W19 (bitsValue digit differenceDigit nextBorrow subtractBits)

theorem table_lookup (s : Fin 2) (c : Config 2) (coin : Bool) :
    machine.table.getD (transitionIndex s c coin) (Instruction.halt 2) =
      if topCode (c.«stacks» 0) = 0 ∧ topCode (c.«stacks» 1) = 0 then
        finishEntry (s.val == 1)
      else subEntry (s.val == 1) (topCode (c.«stacks» 0) == 2)
        (topCode (c.«stacks» 1) == 2) := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  have h2 := topCode_lt_three (c.«stacks» 2)
  have hl : headCode c % 3 = topCode (c.«stacks» 0) := by unfold headCode; omega
  have hr : headCode c / 3 % 3 = topCode (c.«stacks» 1) := by unfold headCode; omega
  unfold machine
  rw [FiniteDispatch.lookup_compile]
  simp only [dispatch, hl, hr]
  rfl

theorem step_left_cons (c a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (borrowState c)) (a :: xs) ys zs) coin =
      cfg (some (borrowState (nextBorrow a (ys.headD false) c))) xs ys.tail
        (differenceDigit a (ys.headD false) c :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> cases a <;> cases ys with
  | nil =>
      change Config.mk _ _ = Config.mk _ _
      congr 1
      funext j
      fin_cases j <;> rfl
  | cons b ys =>
      cases b <;> change Config.mk _ _ = Config.mk _ _
      all_goals
        congr 1
        funext j
        fin_cases j <;> rfl

theorem step_right_cons (c b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (borrowState c)) [] (b :: ys) zs) coin =
      cfg (some (borrowState (nextBorrow false b c))) [] ys
        (differenceDigit false b c :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_done (c : Bool) (zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (borrowState c)) [] [] zs) coin =
      cfg none [c] [] zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> change Config.mk none _ = Config.mk none _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem run_sub (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    machine.run (cfg (some (borrowState c)) xs ys zs) bits =
      cfg none [subtractionBorrow xs ys c] [] ((subtractBits xs ys c).reverse ++ zs) := by
  induction xs generalizing c ys zs bits with
  | nil =>
      induction ys generalizing c zs bits with
      | nil =>
          cases bits with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest = [] := by
                apply List.length_eq_zero_iff.mp
                simp only [List.length_cons, List.length_nil, max_self] at hlen
                omega
              subst rest
              erw [BinaryMachine.run.eq_2, step_done]
              cases c <;> simp [BinaryMachine.run, subtractBits, subtractionBorrow] <;> rfl
      | cons b ys ih =>
          cases bits with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest.length = max ([] : List Bool).length ys.length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.zero_max] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_right_cons, ih _ _ _ hr]
              simp [subtractBits, subtractionBorrow, List.reverse_cons, List.append_assoc]
              rfl
  | cons a xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          cases ys with
          | nil =>
              have hr : rest.length = max xs.length ([] : List Bool).length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.max_zero] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_left_cons]
              simp only [List.headD_nil, List.tail_nil]
              erw [ih _ _ _ _ hr]
              simp [subtractBits, subtractionBorrow, List.reverse_cons, List.append_assoc]
              rfl
          | cons b ys =>
              have hr : rest.length = max xs.length ys.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run.eq_2, step_left_cons]
              simp only [List.headD_cons, List.tail_cons]
              erw [ih _ _ _ _ hr]
              simp [subtractBits, subtractionBorrow, List.reverse_cons, List.append_assoc]
              rfl

end KS.W19.BorrowSubtractor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BorrowActivity
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BorrowSubtractor
open KS.W29
open KS.W29.Sequential

theorem activeFor_sub (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    ActiveFor machine (cfg (some (borrowState c)) xs ys zs) bits := by
  induction xs generalizing c ys zs bits with
  | nil =>
    induction ys generalizing c zs bits with
    | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
        have hr : rest = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons, List.length_nil, max_self] at hlen
          omega
        subst rest
        exact ⟨Option.some_ne_none _, trivial⟩
    | cons b ys ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
        have hr : rest.length = max ([] : List Bool).length ys.length + 1 := by
          simp only [List.length_cons, List.length_nil, Nat.zero_max] at hlen ⊢
          omega
        refine ⟨Option.some_ne_none _, ?_⟩
        rw [step_right_cons]
        exact ih _ _ _ hr
  | cons a xs ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin rest =>
      refine ⟨Option.some_ne_none _, ?_⟩
      cases ys with
      | nil =>
        have hr : rest.length = max xs.length ([] : List Bool).length + 1 := by
          simp only [List.length_cons, List.length_nil, Nat.max_zero] at hlen ⊢
          omega
        rw [step_left_cons]
        simp only [List.headD_nil, List.tail_nil]
        exact ih _ _ _ _ hr
      | cons b ys =>
        have hr : rest.length = max xs.length ys.length + 1 := by
          simp only [List.length_cons] at hlen
          omega
        rw [step_left_cons]
        simp only [List.headD_cons, List.tail_cons]
        exact ih _ _ _ _ hr

theorem haltsAfter_sub (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    HaltsAfter machine (cfg (some (borrowState c)) xs ys zs) bits := by
  refine ⟨activeFor_sub c xs ys zs bits hlen, ?_⟩
  rw [run_sub c xs ys zs bits hlen]
  rfl

end KS.W19.BorrowSubtractor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FixedSubroutineBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29.FixedSequential

theorem activeFor_lift3_iff {k : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : KS.W01.FixedStack.Config k M.states) (bits : List Bool) :
    ActiveFor (ofMachine (KS.W01.FixedStack.lift3 M ports)) c bits ↔
      KS.W29.Sequential.ActiveFor M (KS.W01.FixedStack.project ports c) bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      simp only [ActiveFor, KS.W29.Sequential.ActiveFor]
      have ht := ih ((KS.W01.FixedStack.lift3 M ports).step c b)
      erw [KS.W01.FixedStack.lift3_project_step] at ht
      exact and_congr Iff.rfl ht

theorem haltsAfter_lift3_iff {k : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : KS.W01.FixedStack.Config k M.states) (bits : List Bool) :
    HaltsAfter (ofMachine (KS.W01.FixedStack.lift3 M ports)) c bits ↔
      KS.W29.Sequential.HaltsAfter M (KS.W01.FixedStack.project ports c) bits := by
  unfold HaltsAfter KS.W29.Sequential.HaltsAfter
  apply and_congr (activeFor_lift3_iff M ports c bits)
  change ((KS.W01.FixedStack.lift3 M ports).run c bits).state = none ↔ _
  rw [lift3_run_state]
  rfl

end KS.W29.FixedSequential

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedCopyRestore
attribute [-simp] _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W01.FixedCopy
open KS.W29

theorem reverse_active (xs ys zs bits : List Bool) (hlen : bits.length = xs.length) :
    Sequential.ActiveFor CopyInput.machine (CopyInput.cfg (some 0) xs ys zs) bits := by
  induction xs generalizing zs bits with
  | nil =>
      have hb : bits = [] := List.length_eq_zero_iff.mp hlen
      subst bits
      trivial
  | cons x xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bs =>
          constructor
          · exact Option.some_ne_none _
          · rw [CopyInput.reverse_step]
            exact ih _ _ (by simpa using hlen)

theorem restore_active (xs ys zs bits : List Bool) (hlen : bits.length ≤ zs.length + 1) :
    Sequential.ActiveFor CopyInput.machine (CopyInput.cfg (some 1) xs ys zs) bits := by
  induction bits generalizing xs ys zs with
  | nil => trivial
  | cons b bs ih =>
      constructor
      · exact Option.some_ne_none _
      · cases zs with
        | nil =>
            have hb : bs = [] := by
              apply List.length_eq_zero_iff.mp
              simp only [List.length_cons, List.length_nil] at hlen
              omega
            subst bs
            trivial
        | cons z zs =>
            rw [CopyInput.copy_step]
            apply ih
            simp only [List.length_cons] at hlen
            omega

theorem copy_haltsAfter (xs bits : List Bool) (hlen : bits.length = 2 * xs.length + 2) :
    Sequential.HaltsAfter CopyInput.machine (CopyInput.machine.init xs) bits := by
  constructor
  · obtain ⟨left, a, right, b, rfl, hl, hr⟩ := CopyInput.split_copy_fuel bits xs.length hlen
    have hi : CopyInput.machine.init xs = CopyInput.cfg (some 0) xs [] [] := by
      simp [BinaryMachine.init, CopyInput.cfg, CopyInput.machine]
    rw [hi]
    apply (activeFor_append CopyInput.machine (CopyInput.cfg (some 0) xs [] [])
      left (a :: (right ++ [b]))).mpr
    constructor
    · exact reverse_active xs [] [] left hl
    · rw [CopyInput.run_reverse xs [] [] left hl]
      simp only [List.append_nil, Sequential.ActiveFor]
      constructor
      · exact Option.some_ne_none _
      · rw [CopyInput.reverse_done]
        apply restore_active
        simp [hr]
  · rw [CopyInput.run_eq_copy xs bits hlen]
    rfl

theorem haltsAfter {k : ℕ} (ports : Fin 3 ↪ Fin k) («stacks» : Fin k → List Bool)
    (xs bits : List Bool) (hsrc : «stacks» (ports 0) = xs)
    (hdst : «stacks» (ports 1) = []) (hscratch : «stacks» (ports 2) = [])
    (hlen : bits.length = 2 * xs.length + 2) :
    FixedSequential.HaltsAfter (program ports) (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits := by
  apply (FixedSequential.haltsAfter_lift3_iff CopyInput.machine ports
    (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits).mpr
  erw [project_start ports «stacks» xs hsrc hdst hscratch]
  exact copy_haltsAfter xs bits hlen

end KS.W01.FixedCopy

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.FixedRun
open KS.W01.FixedStack

theorem run_pack {k : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : KS.W29.Config M.states) (rest : Fin k → List Bool) (bits : List Bool) :
    (lift3 M ports).run (pack ports c rest) bits = pack ports (M.run c bits) rest := by
  have hp := lift3_project_run M ports (pack ports c rest) bits
  rw [project_pack] at hp
  apply config_ext
  · exact congrArg KS.W29.Config.state hp
  · intro j
    by_cases h0 : j = ports 0
    · subst j
      rw [pack_on_port]
      exact congrArg (fun d : KS.W29.Config M.states => d.«stacks» 0) hp
    by_cases h1 : j = ports 1
    · subst j
      rw [pack_on_port]
      exact congrArg (fun d : KS.W29.Config M.states => d.«stacks» 1) hp
    by_cases h2 : j = ports 2
    · subst j
      rw [pack_on_port]
      exact congrArg (fun d : KS.W29.Config M.states => d.«stacks» 2) hp
    have hj : ∀ r : Fin 3, j ≠ ports r := by
      intro r
      fin_cases r <;> assumption
    have hrun := lift3_run_preserves_other M ports (pack ports c rest) bits j hj
    have hc : (pack ports c rest).«stacks» j = rest j :=
      (ite_eq_right h0).trans ((ite_eq_right h1).trans (ite_eq_right h2))
    have hout : (pack ports (M.run c bits) rest).«stacks» j = rest j :=
      (ite_eq_right h0).trans ((ite_eq_right h1).trans (ite_eq_right h2))
    exact hrun.trans (hc.trans hout.symm)

end KS.W19.FixedRun

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionMachine
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

theorem copyTrial_run (d pending q r coins : List Bool) (hc : coins.length = 2 * r.length + 2) :
    copyTrial.toMachine.run ⟨some copyTrial.initial, «stacks» d pending q r [] [] [] []⟩ coins =
      ⟨none, «stacks» d pending q r r [] [] []⟩ := by
  have h := KS.W01.FixedCopy.run_copy_restore trialPorts («stacks» d pending q r [] [] [] []) r coins
    rfl rfl rfl hc
  refine (KS.W19.MachineTransport.run_ofMachine (KS.W01.FixedCopy.machine trialPorts) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [Function.update, «stacks», trialPorts] <;> rfl

theorem copyTrial_halts (d pending q r coins : List Bool) (hc : coins.length = 2 * r.length + 2) :
    HaltsAfter copyTrial ⟨some copyTrial.initial, «stacks» d pending q r [] [] [] []⟩ coins :=
  KS.W01.FixedCopy.haltsAfter trialPorts _ r coins rfl rfl rfl hc

theorem copyDivisor_run (d pending q r coins : List Bool) (hc : coins.length = 2 * d.length + 2) :
    copyDivisor.toMachine.run ⟨some copyDivisor.initial, «stacks» d pending q r r [] [] []⟩ coins =
      ⟨none, «stacks» d pending q r r d [] []⟩ := by
  have h := KS.W01.FixedCopy.run_copy_restore divisorPorts («stacks» d pending q r r [] [] []) d coins
    rfl rfl rfl hc
  refine (KS.W19.MachineTransport.run_ofMachine (KS.W01.FixedCopy.machine divisorPorts) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [Function.update, «stacks», divisorPorts] <;> rfl

theorem copyDivisor_halts (d pending q r coins : List Bool) (hc : coins.length = 2 * d.length + 2) :
    HaltsAfter copyDivisor ⟨some copyDivisor.initial, «stacks» d pending q r r [] [] []⟩ coins :=
  KS.W01.FixedCopy.haltsAfter divisorPorts _ d coins rfl rfl rfl hc

theorem subtract_start (d pending q r : List Bool) :
    (⟨some subtract.initial, «stacks» d pending q r r d [] []⟩ : Config 10 subtract.states) =
      pack subtractPorts (BorrowSubtractor.cfg (some 0) r d [])
        («stacks» d pending q r [] [] [] []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem subtract_run (d pending q r coins : List Bool) (hc : coins.length = max r.length d.length + 1) :
    subtract.toMachine.run ⟨some subtract.initial, «stacks» d pending q r r d [] []⟩ coins =
      ⟨none, «stacks» d pending q r [subtractionBorrow r d false] [] (subtractBits r d false).reverse []⟩ := by
  erw [subtract_start]
  refine (KS.W19.MachineTransport.run_ofMachine (lift3 BorrowSubtractor.machine subtractPorts) _ coins).trans ?_
  refine (run_pack BorrowSubtractor.machine subtractPorts _ _ coins).trans ?_
  refine (congrArg (fun c => pack subtractPorts c («stacks» d pending q r [] [] [] []))
    (BorrowSubtractor.run_sub false r d [] coins hc)).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp only [List.append_nil] <;> rfl

theorem prepare_run (d pending q r first second third : List Bool)
    (h₁ : first.length = 2 * r.length + 2) (h₂ : second.length = 2 * d.length + 2)
    (h₃ : third.length = max r.length d.length + 1) :
    prepare.toMachine.run ⟨some prepare.initial, «stacks» d pending q r [] [] [] []⟩
      (first ++ (second ++ third)) =
      ⟨none, «stacks» d pending q r [subtractionBorrow r d false] [] (subtractBits r d false).reverse []⟩ := by
  change (compose copyTrial prepareTail).toMachine.run
    (liftLeft copyTrial prepareTail ⟨some copyTrial.initial, _⟩) _ = _
  erw [run_compose copyTrial prepareTail _ first _ (copyTrial_halts d pending q r first h₁),
    copyTrial_run d pending q r first h₁]
  change liftRight copyTrial prepareTail ((compose copyDivisor subtract).toMachine.run
    (liftLeft copyDivisor subtract ⟨some copyDivisor.initial, _⟩) _) = _
  erw [run_compose copyDivisor subtract _ second _ (copyDivisor_halts d pending q r second h₂),
    copyDivisor_run d pending q r second h₂, subtract_run d pending q r third h₃]
  rfl

theorem choose_step_borrowed (d pending q r candidate : List Bool) (coin : Bool) :
    choose.toMachine.step
      ⟨some choose.initial, «stacks» d pending q r [true] [] candidate []⟩ coin =
      KS.W29.FixedBranch.liftLeft keepTrial useCandidate
        ⟨some keepTrial.initial, «stacks» d pending (false :: q) r [] [] candidate []⟩ := by
  unfold choose
  erw [KS.W29.FixedBranch.step_start]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem choose_step_candidate (d pending q r candidate : List Bool) (coin : Bool) :
    choose.toMachine.step
      ⟨some choose.initial, «stacks» d pending q r [false] [] candidate []⟩ coin =
      KS.W29.FixedBranch.liftRight keepTrial useCandidate
        ⟨some useCandidate.initial, «stacks» d pending (true :: q) r [] [] candidate []⟩ := by
  unfold choose
  erw [KS.W29.FixedBranch.step_start]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem keepTrial_run (d pending q r candidate coins : List Bool)
    (hc : coins.length = candidate.length + 1) :
    keepTrial.toMachine.run ⟨some keepTrial.initial, «stacks» d pending q r [] [] candidate []⟩ coins =
      ⟨none, «stacks» d pending q r [] [] [] []⟩ := by
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (8 : Fin 10)
    («stacks» d pending q r [] [] candidate []) coins hc
  refine (KS.W19.MachineTransport.run_ofMachine (KS.W04.BinaryStackMoves.clearMachine (8 : Fin 10)) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem trim_start (d pending q candidate : List Bool) :
    (⟨some trimCandidate.initial, «stacks» d pending q [] [] [] candidate []⟩ : Config 10 trimCandidate.states) =
      pack trimPorts (BinaryTrimMachine.cfg (some 0) [] [] candidate)
        («stacks» d pending q [] [] [] [] []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem trim_run (d pending q candidate coins : List Bool)
    (hc : coins.length = candidate.length + 1) :
    trimCandidate.toMachine.run ⟨some trimCandidate.initial, «stacks» d pending q [] [] [] candidate []⟩ coins =
      ⟨none, «stacks» d pending q (trimBits candidate.reverse) [] [] [] []⟩ := by
  erw [trim_start]
  refine (KS.W19.MachineTransport.run_ofMachine (lift3 BinaryTrimMachine.machine trimPorts) _ coins).trans ?_
  refine (run_pack BinaryTrimMachine.machine trimPorts _ _ coins).trans ?_
  refine (congrArg (fun c => pack trimPorts c («stacks» d pending q [] [] [] [] []))
    (BinaryTrimMachine.run_trim [] [] candidate coins hc)).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp only [List.append_nil] <;> rfl

theorem useCandidate_run (d pending q r candidate first second : List Bool)
    (hf : first.length = r.length + 1) (hs : second.length = candidate.length + 1) :
    useCandidate.toMachine.run ⟨some useCandidate.initial, «stacks» d pending q r [] [] candidate []⟩
      (first ++ second) =
      ⟨none, «stacks» d pending q (trimBits candidate.reverse) [] [] [] []⟩ := by
  have hh := KS.W04.BinaryStackMoves.clear_haltsAfter_stacks (4 : Fin 10)
    («stacks» d pending q r [] [] candidate []) first hf
  change (compose (KS.W04.BinaryStackMoves.clearProgram (4 : Fin 10)) trimCandidate).toMachine.run
    (liftLeft _ _ ⟨some (0 : Fin 1), _⟩) _ = _
  erw [run_compose _ _ _ first second hh, clearRemainder_run d pending q r candidate first hf,
    trim_run d pending q candidate second hs]
  rfl

theorem choose_run_borrowed (d pending q r candidate coins : List Bool) (coin : Bool)
    (hc : coins.length = candidate.length + 1) :
    choose.toMachine.run ⟨some choose.initial, «stacks» d pending q r [true] [] candidate []⟩
      (coin :: coins) = ⟨none, «stacks» d pending (false :: q) r [] [] [] []⟩ := by
  erw [Machine.run, choose_step_borrowed]
  change (KS.W29.FixedBranch.branch keepTrial useCandidate 5 select).toMachine.run _ _ = _
  erw [KS.W29.FixedBranch.run_left, keepTrial_run d pending (false :: q) r candidate coins hc]
  rfl

theorem choose_run_candidate (d pending q r candidate first second : List Bool) (coin : Bool)
    (hf : first.length = r.length + 1) (hs : second.length = candidate.length + 1) :
    choose.toMachine.run ⟨some choose.initial, «stacks» d pending q r [false] [] candidate []⟩
      (coin :: (first ++ second)) =
      ⟨none, «stacks» d pending (true :: q) (trimBits candidate.reverse) [] [] [] []⟩ := by
  erw [Machine.run, choose_step_candidate]
  change (KS.W29.FixedBranch.branch keepTrial useCandidate 5 select).toMachine.run _ _ = _
  erw [KS.W29.FixedBranch.run_right,
    useCandidate_run d pending (true :: q) r candidate first second hf hs]
  rfl

theorem subtract_halts (d pending q r coins : List Bool) (hc : coins.length = max r.length d.length + 1) :
    HaltsAfter subtract ⟨some subtract.initial, «stacks» d pending q r r d [] []⟩ coins := by
  erw [subtract_start]
  apply (haltsAfter_lift3_iff BorrowSubtractor.machine subtractPorts _ coins).2
  erw [project_pack]
  exact BorrowSubtractor.haltsAfter_sub false r d [] coins hc

theorem prepare_halts (d pending q r first second third : List Bool)
    (h₁ : first.length = 2 * r.length + 2) (h₂ : second.length = 2 * d.length + 2)
    (h₃ : third.length = max r.length d.length + 1) :
    HaltsAfter prepare ⟨some prepare.initial, «stacks» d pending q r [] [] [] []⟩
      (first ++ (second ++ third)) := by
  apply compose_haltsAfter copyTrial prepareTail _ first (second ++ third)
    (copyTrial_halts d pending q r first h₁)
  erw [copyTrial_run d pending q r first h₁]
  apply compose_haltsAfter copyDivisor subtract _ second third
    (copyDivisor_halts d pending q r second h₂)
  erw [copyDivisor_run d pending q r second h₂]
  exact subtract_halts d pending q r third h₃

theorem body_run_borrowed (d pending q r first second third cleanup : List Bool) (coin : Bool)
    (hborrow : subtractionBorrow r d false = true)
    (h₁ : first.length = 2 * r.length + 2) (h₂ : second.length = 2 * d.length + 2)
    (h₃ : third.length = max r.length d.length + 1)
    (hc : cleanup.length = max r.length d.length + 1) :
    body.toMachine.run ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩
      ((first ++ (second ++ third)) ++ (coin :: cleanup)) =
      ⟨none, «stacks» d pending (false :: q) r [] [] [] []⟩ := by
  change (compose prepare choose).toMachine.run (liftLeft prepare choose ⟨some prepare.initial, _⟩) _ = _
  erw [run_compose prepare choose _ _ _ (prepare_halts d pending q r first second third h₁ h₂ h₃),
    prepare_run d pending q r first second third h₁ h₂ h₃, hborrow]
  erw [choose_run_borrowed d pending q r (subtractBits r d false).reverse cleanup coin
    (by simpa only [List.length_reverse, subtractBits_length] using hc)]
  rfl

theorem body_run_candidate (d pending q r first second third clear trim : List Bool) (coin : Bool)
    (hborrow : subtractionBorrow r d false = false)
    (h₁ : first.length = 2 * r.length + 2) (h₂ : second.length = 2 * d.length + 2)
    (h₃ : third.length = max r.length d.length + 1)
    (hc : clear.length = r.length + 1) (ht : trim.length = max r.length d.length + 1) :
    body.toMachine.run ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩
      ((first ++ (second ++ third)) ++ (coin :: (clear ++ trim))) =
      ⟨none, «stacks» d pending (true :: q) (trimBits (subtractBits r d false)) [] [] [] []⟩ := by
  change (compose prepare choose).toMachine.run (liftLeft prepare choose ⟨some prepare.initial, _⟩) _ = _
  erw [run_compose prepare choose _ _ _ (prepare_halts d pending q r first second third h₁ h₂ h₃),
    prepare_run d pending q r first second third h₁ h₂ h₃, hborrow]
  erw [choose_run_candidate d pending q r (subtractBits r d false).reverse clear trim coin hc
    (by simpa only [List.length_reverse, subtractBits_length] using ht)]
  simp only [List.reverse_reverse, liftRight]
  rfl

end KS.W19.DivisionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionBodyTime
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionMachine
open KS.W01.FixedStack KS.W29.FixedSequential

theorem body_run_exact (d pending q r bits : List Bool) (hb : bits.length = bodyFuel d r) :
    body.toMachine.run ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩ bits =
      ⟨none, «stacks» d pending (trialResult d q r).1 (trialResult d q r).2 [] [] [] []⟩ := by
  unfold bodyFuel at hb
  obtain ⟨first, rest, rfl, h₁, hrest⟩ := split_exact bits (2 * r.length + 2) _ hb
  obtain ⟨second, rest, rfl, h₂, hrest⟩ := split_exact rest (2 * d.length + 2) _ hrest
  obtain ⟨third, last, rfl, h₃, hlast⟩ := split_exact rest (max r.length d.length + 1) _ hrest
  cases last with
  | nil =>
    simp only [List.length_nil] at hlast
    omega
  | cons coin tail =>
    cases hc : subtractionBorrow r d false
    · have ht : tail.length = (r.length + 1) + (max r.length d.length + 1) := by
        simp only [hc, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hlast
        omega
      obtain ⟨clear, trim, rfl, hclear, htrim⟩ := split_exact tail (r.length + 1) _ ht
      simpa only [trialResult, hc, Bool.false_eq_true, ↓reduceIte, List.append_assoc] using
        body_run_candidate d pending q r first second third clear trim coin hc h₁ h₂ h₃ hclear htrim
    · have ht : tail.length = max r.length d.length + 1 := by
        simp only [hc, ↓reduceIte, List.length_cons] at hlast
        omega
      simpa only [trialResult, hc, ↓reduceIte, List.append_assoc] using
        body_run_borrowed d pending q r first second third tail coin hc h₁ h₂ h₃ ht

theorem body_run_of_length_ge (d pending q r bits : List Bool) (hb : bodyFuel d r ≤ bits.length) :
    body.toMachine.run ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩ bits =
      ⟨none, «stacks» d pending (trialResult d q r).1 (trialResult d q r).2 [] [] [] []⟩ := by
  have hh := body_run_exact d pending q r (bits.take (bodyFuel d r))
    (by simp [List.length_take, Nat.min_eq_left hb])
  conv_lhs => rw [← List.take_append_drop (bodyFuel d r) bits]
  rw [Machine.run_append, hh]
  exact body.toMachine.run_halted _ rfl _

theorem body_halts_linear (d pending q r : List Bool) :
    HaltsFromWithin body ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩
      (8 * (r.length + d.length + 1)) := by
  intro bits hb
  exact congrArg Config.state
    (body_run_of_length_ge d pending q r bits (by rw [hb]; exact bodyFuel_linear d r))

end KS.W19.DivisionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionLoopRun
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

theorem guard_cons (d pending q r : List Bool) (b coin : Bool) :
    loop.toMachine.step ⟨some loop.initial, «stacks» d (b :: pending) q r [] [] [] []⟩ coin =
      KS.W29.FixedLoop.liftBody body
        ⟨some body.initial, «stacks» d pending q (b :: r) [] [] [] []⟩ := by
  unfold loop
  erw [KS.W29.FixedLoop.step_guard]
  cases b <;> apply config_ext
  all_goals
    first | rfl | (intro j; fin_cases j <;> rfl)

theorem guard_nil (d q r : List Bool) (coin : Bool) :
    loop.toMachine.step ⟨some loop.initial, «stacks» d [] q r [] [] [] []⟩ coin =
      ⟨none, «stacks» d [] q r [] [] [] []⟩ := by
  unfold loop
  erw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem loop_run (d pending q r bits : List Bool) (R : Nat)
    (hr : r.length + pending.length ≤ R) (hd : d.length + pending.length ≤ R)
    (hb : pending.length * (8 * (R + d.length + 2) + 1) + 1 ≤ bits.length) :
    loop.toMachine.run ⟨some loop.initial, «stacks» d pending q r [] [] [] []⟩ bits =
      ⟨none, «stacks» d [] (DivisionLoop.process d pending q r).1
        (DivisionLoop.process d pending q r).2 [] [] [] []⟩ := by
  induction pending generalizing q r bits with
  | nil =>
    cases bits with
    | nil => simp at hb
    | cons coin tail =>
      rw [Machine.run, guard_nil, loop.toMachine.run_halted _ rfl tail]
      rfl
  | cons b bs ih =>
    cases bits with
    | nil => simp at hb
    | cons coin tail =>
      let B := 8 * (R + d.length + 2)
      have ht : B ≤ tail.length := by
        simp only [List.length_cons] at hb
        dsimp [B]
        nlinarith
      have hsmall : 8 * ((b :: r).length + d.length + 1) ≤ B := by
        simp only [List.length_cons] at hr ⊢
        dsimp [B]
        omega
      have hhalt := haltsFromWithin_mono body
        ⟨some body.initial, «stacks» d bs q (b :: r) [] [] [] []⟩
        (body_halts_linear d bs q (b :: r)) hsmall
      obtain ⟨first, rest, he, hfirst, _, hrun⟩ :=
        KS.W29.FixedLoop.run_body_within body guard
          ⟨some body.initial, «stacks» d bs q (b :: r) [] [] [] []⟩ B hhalt tail ht
      have htake : (tail.take B).length = B := by simp [List.length_take, Nat.min_eq_left ht]
      have hout := body_run_of_length_ge d bs q (b :: r) (tail.take B)
        (by rw [htake]; exact (bodyFuel_linear d (b :: r)).trans hsmall)
      have hrest : bs.length * (8 * (R + d.length + 2) + 1) + 1 ≤ rest.length := by
        have hh := congrArg List.length he
        simp only [List.length_append] at hh
        simp only [List.length_cons] at hb
        dsimp [B] at hfirst
        nlinarith
      have hnr : (DivisionLoop.advance d b q r).2.length + bs.length ≤ R := by
        have hlen := DivisionLoop.advance_remainder_length d b q r
        simp only [List.length_cons] at hr hd
        omega
      have hnd : d.length + bs.length ≤ R := by
        simp only [List.length_cons] at hd
        omega
      rw [Machine.run, guard_cons]
      change (KS.W29.FixedLoop.loop body guard).toMachine.run _ tail = _
      erw [hrun, hout]
      change loop.toMachine.run
        ⟨some loop.initial, «stacks» d bs (trialResult d q (b :: r)).1
          (trialResult d q (b :: r)).2 [] [] [] []⟩ rest = _
      rw [trialResult_advance]
      simpa only [DivisionLoop.process] using
        ih (DivisionLoop.advance d b q r).1 (DivisionLoop.advance d b q r).2 rest hnr hnd hrest

theorem loop_payload (d xs bits : List Bool)
    (hb : xs.length * (8 * (xs.length + 2 * d.length + 2) + 1) + 1 ≤ bits.length) :
    loop.toMachine.run ⟨some loop.initial, «stacks» d xs.reverse [] [] [] [] [] []⟩ bits =
      ⟨none, «stacks» d [] (DivisionLoop.process d xs.reverse [] []).1
        (DivisionLoop.process d xs.reverse [] []).2 [] [] [] []⟩ := by
  apply loop_run d xs.reverse [] [] bits (xs.length + d.length)
  · simp
  · simp; omega
  · simpa only [List.length_reverse, Nat.add_assoc, two_mul] using hb

end KS.W19.DivisionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionInput
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

def loopStage : Program 10 := compose reverseInput DivisionMachine.loop
def secondStage : Program 10 := compose parseSecond loopStage

end KS.W19.DivisionInput

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_FixedSubtraction
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.FixedSubtraction
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

theorem subtract_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) (hsub : bitsValue ys ≤ bitsValue xs) :
    RunSpec (program ports) (registers ports spare xs ys [])
      (registers ports spare [] (Computability.encodeNat (bitsValue xs - bitsValue ys)) [])
      (2 * (max xs.length ys.length + 1)) := by
  intro bits hb
  let n := max xs.length ys.length + 1
  have hl : (bits.take n).length = n := by simp only [List.length_take, hb]; dsimp [n]; omega
  have hr : (bits.drop n).length = n := by simp only [List.length_drop, hb]; dsimp [n]; omega
  have hcall := CanonicalSubtraction.run_exact xs ys (bits.take n) (bits.drop n) hl hr
  rw [List.take_append_drop] at hcall
  have hnum := subtractBits_correct xs ys false (by simpa only [digit_false, Nat.add_zero] using hsub)
  have hv : bitsValue (subtractBits xs ys false) = bitsValue xs - bitsValue ys := by
    simp only [digit_false, Nat.add_zero] at hnum
    omega
  change (lift3 CanonicalSubtraction.machine ports).run
    ⟨some (0 : Fin 4), registers ports spare xs ys []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (0 : Fin 4), registers ports spare xs ys []⟩ : Config k 4) =
        KS.W29.Sequential.liftLeft BinarySubtractor.machine BinaryTrimMachine.machine
          (BinarySubtractor.cfg (some 0) xs ys []) := by
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 4)))
      funext j
      fin_cases j <;> simp [BinarySubtractor.cfg]
    have hr' := congrArg (fun c => CanonicalSubtraction.machine.run c bits) hp
    refine hr'.trans (hcall.trans ?_)
    apply congrArg₂ KS.W29.Config.mk
    · rfl
    · funext j
      fin_cases j <;> simp [BinaryTrimMachine.cfg, hv]
  · intro j hj
    exact (registers_other ports spare _ _ _ j hj).trans
      (registers_other ports spare _ _ _ j hj).symm

end KS.W19.FixedSubtraction

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_GCDMachine
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem clearQuotient_spec (d q r : List Bool) :
    RunSpec clearQuotient (DivisionMachine.«stacks» d [] q r [] [] [] [])
      (DivisionMachine.«stacks» d [] [] r [] [] [] []) (q.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (5 : Fin 10)
    (DivisionMachine.«stacks» d [] q r [] [] [] []) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.clearMachine (5 : Fin 10)) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem advanceDividend_spec (d r : List Bool) :
    RunSpec advanceDividend (DivisionMachine.«stacks» d [] [] r [] [] [] [])
      (DivisionMachine.«stacks» [] d.reverse [] r [] [] [] []) (d.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (2 : Fin 10) 3 (by decide)
    (DivisionMachine.«stacks» d [] [] r [] [] [] []) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (2 : Fin 10) 3) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [DivisionMachine.«stacks», KS.W04.BinaryStackMoves.twoConfig]

theorem reverseRemainder_spec (pending r : List Bool) :
    RunSpec reverseRemainder (DivisionMachine.«stacks» [] pending [] r [] [] [] [])
      (DivisionMachine.«stacks» [] pending [] [] [] [] r.reverse []) (r.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (4 : Fin 10) 8 (by decide)
    (DivisionMachine.«stacks» [] pending [] r [] [] [] []) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (4 : Fin 10) 8) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [DivisionMachine.«stacks», KS.W04.BinaryStackMoves.twoConfig]

theorem trimRemainder_start (pending r : List Bool) :
    (⟨some trimRemainder.initial, DivisionMachine.«stacks» [] pending [] [] [] [] r.reverse []⟩ :
      Config 10 trimRemainder.states) =
      pack remainderPorts (BinaryTrimMachine.cfg (some 0) [] [] r.reverse)
        (DivisionMachine.«stacks» [] pending [] [] [] [] [] []) := by
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem trimRemainder_spec (pending r : List Bool) :
    RunSpec trimRemainder (DivisionMachine.«stacks» [] pending [] [] [] [] r.reverse [])
      (DivisionMachine.«stacks» (trimBits r) pending [] [] [] [] [] []) (r.length + 1) := by
  intro bits hlen
  erw [trimRemainder_start]
  refine (KS.W19.MachineTransport.run_ofMachine
    (lift3 BinaryTrimMachine.machine remainderPorts) _ bits).trans ?_
  refine (run_pack BinaryTrimMachine.machine remainderPorts _ _ bits).trans ?_
  refine (congrArg (fun c => pack remainderPorts c
    (DivisionMachine.«stacks» [] pending [] [] [] [] [] []))
    (BinaryTrimMachine.run_trim [] [] r.reverse bits
      (by simpa only [List.length_reverse] using hlen))).trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp only [List.reverse_reverse, List.append_nil] <;> rfl

theorem cleanup_spec (d q r : List Bool) :
    RunSpec cleanup (DivisionMachine.«stacks» d [] q r [] [] [] [])
      (state d (trimBits r)) (q.length + d.length + 2 * r.length + 4) := by
  have h := (clearQuotient_spec d q r).compose
    ((advanceDividend_spec d r).compose
      ((reverseRemainder_spec d.reverse r).compose (trimRemainder_spec d.reverse r)))
  have ht : (q.length+1)+((d.length+1)+((r.length+1)+(r.length+1))) =
      q.length+d.length+2*r.length+4 := by omega
  rw [ht] at h
  exact h

end KS.W30.GCDMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_BinaryGCDCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.BinaryGCD
open KS.W19

lemma trimmed_remainder_length_le (ys xs : List Bool) (hy : 0 < bitsValue ys) :
    (trimBits (divideBits ys xs).2).length ≤ ys.length := by
  apply trimBits_length_le_of_value_lt
  exact lt_trans (divideBits_correct ys xs hy).2 (bitsValue_lt_two_pow_length ys)

end KS.W30.BinaryGCD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_GCDMachineStep
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W08.denseMatrixBinaryCursor_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem body_spec (x y : List Bool) (L : ℕ) (hx : x.length ≤ L) (hy : y.length ≤ L)
    (hyp : 0 < bitsValue y) :
    RunSpec body (state x y) (state y (trimBits (divideBits y x).2))
      (40 * (L + 1) ^ 2) := by
  let qr := DivisionLoop.process y x.reverse [] []
  have hd : RunSpec DivisionMachine.loop (state x y)
      (DivisionMachine.«stacks» y [] qr.1 qr.2 [] [] [] [])
      (x.length * (8 * (x.length + 2 * y.length + 2) + 1) + 1) := by
    intro bits hlen
    exact DivisionMachine.loop_payload y x bits (by omega)
  have hc := cleanup_spec y qr.1 qr.2
  have h := hd.compose hc
  have hq : qr.1.length = x.length := by
    simpa only [qr, List.length_reverse, List.length_nil, Nat.add_zero] using
      process_quotient_length y x.reverse [] []
  have hr : qr.2.length ≤ x.length + y.length := by
    apply process_remainder_length y x.reverse [] [] (x.length + y.length)
    · simp
    · simp; omega
  have ht : x.length * (8 * (x.length + 2 * y.length + 2) + 1) + 1 +
      (qr.1.length + y.length + 2 * qr.2.length + 4) ≤ 40 * (L + 1) ^ 2 := by
    rw [hq]
    have hm : x.length * (8 * (x.length + 2 * y.length + 2) + 1) ≤
        L * (8 * (3 * L + 2) + 1) := Nat.mul_le_mul hx (by omega)
    nlinarith
  have ho : trimBits qr.2 = trimBits (divideBits y x).2 :=
    KS.W30.BinaryRational.divisionLoop_trim_remainder y x hyp
  simpa only [body, ho] using h.mono ht

theorem guard_zero (x : List Bool) (coin : Bool) :
    loop.toMachine.step ⟨some loop.initial, state x []⟩ coin = ⟨none, state x []⟩ := by
  unfold loop
  erw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem guard_nonzero (x y : List Bool) (hy : y ≠ []) (coin : Bool) :
    loop.toMachine.step ⟨some loop.initial, state x y⟩ coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial, state x y⟩ := by
  cases y with
  | nil => exact (hy rfl).elim
  | cons b bs =>
    unfold loop
    erw [KS.W29.FixedLoop.step_guard]
    cases b <;> apply config_ext
    all_goals first | rfl | (intro j; fin_cases j <;> rfl)

end KS.W30.GCDMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_GCDMachineRun
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19 KS.W30.BinaryGCD

theorem loop_advance (x y bits : List Bool) (L : ℕ)
    (hx : x.length ≤ L) (hy : y.length ≤ L) (hyp : 0 < bitsValue y)
    (hlen : 40 * (L + 1) ^ 2 + 1 ≤ bits.length) :
    ∃ rest : List Bool, bits.length - (40 * (L + 1) ^ 2 + 1) ≤ rest.length ∧
      loop.toMachine.run ⟨some loop.initial, state x y⟩ bits =
        loop.toMachine.run ⟨some loop.initial, state y (trimBits (divideBits y x).2)⟩ rest := by
  cases bits with
  | nil => simp at hlen
  | cons coin tail =>
    have hne : y ≠ [] := by intro h; simp [h, bitsValue] at hyp
    have ht : 40 * (L + 1) ^ 2 ≤ tail.length := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨rest, hrest, he⟩ := (body_spec x y L hx hy hyp).loop_body_then guard tail ht
    refine ⟨rest, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · rw [Machine.run, guard_nonzero x y hne coin]
      exact he

lemma loop_zero (x bits : List Bool) (hlen : 1 ≤ bits.length) :
    loop.toMachine.run ⟨some loop.initial, state x []⟩ bits = ⟨none, state x []⟩ := by
  cases bits with
  | nil => simp at hlen
  | cons coin tail => rw [Machine.run, guard_zero, Machine.run_halted _ _ rfl]

theorem loop_run (k : ℕ) (x y bits : List Bool) (L : ℕ)
    (hxc : CanonicalBits x) (hyc : CanonicalBits y)
    (hx : x.length ≤ L) (hy : y.length ≤ L) (hyb : bitsValue y < 2 ^ k)
    (hlen : (2 * k + 1) * (40 * (L + 1) ^ 2 + 1) ≤ bits.length) :
    loop.toMachine.run ⟨some loop.initial, state x y⟩ bits =
      ⟨none, state (Computability.encodeNat (Nat.gcd (bitsValue x) (bitsValue y))) []⟩ := by
  induction k generalizing x y bits with
  | zero =>
    have hyv : bitsValue y = 0 := by simpa using hyb
    have hy0 : y = [] := by
      apply canonicalBits_injective hyc (by simp [CanonicalBits])
      simpa only [bitsValue] using hyv
    subst y
    have hh : 1 ≤ bits.length := by
      simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] at hlen
      omega
    rw [loop_zero x bits hh]
    simp only [bitsValue, Nat.gcd_zero_right, ← canonical_eq_encode x hxc]
  | succ k ih =>
    by_cases hy0 : y = []
    · subst y
      have hpos : 1 ≤ (2 * (k + 1) + 1) * (40 * (L + 1) ^ 2 + 1) := by
        have hp : 0 < (2 * (k + 1) + 1) * (40 * (L + 1) ^ 2 + 1) :=
          Nat.mul_pos (by omega) (by omega)
        omega
      rw [loop_zero x bits (hpos.trans hlen)]
      simp only [bitsValue, Nat.gcd_zero_right, ← canonical_eq_encode x hxc]
    · have hyp : 0 < bitsValue y := canonicalBits_value_pos y hyc hy0
      let T := 40 * (L + 1) ^ 2 + 1
      have hbudget : (2 * (k + 1) + 1) * T = 2 * T + (2 * k + 1) * T := by ring
      have hlen' : 2 * T + (2 * k + 1) * T ≤ bits.length := by
        change (2 * (k + 1) + 1) * T ≤ bits.length at hlen
        rwa [hbudget] at hlen
      have hT : 1 ≤ T := by dsimp [T]; omega
      obtain ⟨rest, hrest, hstep⟩ := loop_advance x y bits L hx hy hyp (by dsimp [T] at *; omega)
      let r := trimBits (divideBits y x).2
      have hrlen : r.length ≤ L := (trimmed_remainder_length_le y x hyp).trans hy
      have hrc : CanonicalBits r := trimBits_canonical _
      have hrv : bitsValue r = bitsValue x % bitsValue y := by
        dsimp only [r]
        rw [trimBits_value, remainder_value y x hyp]
      have hrest' : T + (2 * k + 1) * T ≤ rest.length := by
        change bits.length - T ≤ rest.length at hrest
        omega
      rw [hstep]
      change loop.toMachine.run ⟨some loop.initial, state y r⟩ rest = _
      by_cases hr0 : r = []
      · have hm : bitsValue x % bitsValue y = 0 := by simpa [hr0, bitsValue] using hrv.symm
        have hg : Nat.gcd (bitsValue x) (bitsValue y) = bitsValue y := by
          rw [Nat.gcd_comm, Nat.gcd_rec, hm, Nat.gcd_zero_left]
        rw [hr0, loop_zero y rest (by omega), hg, ← canonical_eq_encode y hyc]
      · have hrp : 0 < bitsValue r := canonicalBits_value_pos r hrc hr0
        obtain ⟨last, hlast, hstep'⟩ := loop_advance y r rest L hy hrlen hrp (by change T ≤ rest.length; omega)
        let s := trimBits (divideBits r y).2
        have hslen : s.length ≤ L := (trimmed_remainder_length_le r y hrp).trans hrlen
        have hsc : CanonicalBits s := trimBits_canonical _
        have hsv : bitsValue s = bitsValue y % bitsValue r := by
          dsimp only [s]
          rw [trimBits_value, remainder_value r y hrp]
        have hsb : bitsValue s < 2 ^ k := by
          rw [hsv]
          have hrb : bitsValue r < bitsValue y := by rw [hrv]; exact Nat.mod_lt _ hyp
          exact remainder_below_half hrp hrb (by simpa [pow_succ, Nat.mul_comm] using hyb)
        have hlast' : (2 * k + 1) * (40 * (L + 1) ^ 2 + 1) ≤ last.length := by
          change rest.length - T ≤ last.length at hlast
          change (2 * k + 1) * T ≤ last.length
          omega
        rw [hstep']
        have hi := ih r s last hrc hsc hrlen hslen hsb hlast'
        change loop.toMachine.run ⟨some loop.initial, state r s⟩ last = _
        rw [hi]
        have hg : Nat.gcd (bitsValue x) (bitsValue y) = Nat.gcd (bitsValue r) (bitsValue s) := by
          rw [hsv, hrv]
          exact gcd_two_reductions _ _
        rw [hg]

end KS.W30.GCDMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddModel
attribute [-simp] _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder _root_.OAI.KS.W30.BinaryRational.encodeMagnitude_value _root_.OAI.KS.W30.BinaryRational.inverseRat_canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.RationalAdd

open KS.W19 KS.W30.BinaryRational

theorem rawSum_encoded_value (q r : ℚ) :
    (rawSum (KS.W06.RationalCompare.negativeBit q.num)
      (KS.W06.RationalCompare.magnitude (KS.W06.RationalCompare.negativeBit q.num)
        (KS.W06.RationalCompare.constructorBits q.num)) (Computability.encodeNat q.den)
      (KS.W06.RationalCompare.negativeBit r.num)
      (KS.W06.RationalCompare.magnitude (KS.W06.RationalCompare.negativeBit r.num)
        (KS.W06.RationalCompare.constructorBits r.num)) (Computability.encodeNat r.den)).value = q + r := by
  rw [rawSum_value _ _ _ _ _ _ (by simpa only [bitsValue_encodeNat] using q.den_ne_zero)
    (by simpa only [bitsValue_encodeNat] using r.den_ne_zero)]
  have hq : (RatBits.mk (KS.W06.RationalCompare.negativeBit q.num)
      (KS.W06.RationalCompare.magnitude (KS.W06.RationalCompare.negativeBit q.num)
        (KS.W06.RationalCompare.constructorBits q.num)) (Computability.encodeNat q.den)).value = q := by
    simpa [RatBits.value, RatBits.magnitude, KS.W06.RationalCompare.signedFraction,
      KS.W06.RationalCompare.magnitude_constructor_value, bitsValue_encodeNat, ite_div, neg_div] using
      KS.W06.RationalCompare.signedFraction_num_den q
  have hr : (RatBits.mk (KS.W06.RationalCompare.negativeBit r.num)
      (KS.W06.RationalCompare.magnitude (KS.W06.RationalCompare.negativeBit r.num)
        (KS.W06.RationalCompare.constructorBits r.num)) (Computability.encodeNat r.den)).value = r := by
    simpa [RatBits.value, RatBits.magnitude, KS.W06.RationalCompare.signedFraction,
      KS.W06.RationalCompare.magnitude_constructor_value, bitsValue_encodeNat, ite_div, neg_div] using
      KS.W06.RationalCompare.signedFraction_num_den r
  rw [hq, hr]

end KS.W13.RationalAdd

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplyProducts
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (workFields product productProgram productTicks runSpec_liftPorts)

theorem products_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec productsProgram (workFields [sa] na da [sb] nb db [] [])
      (productsAfter sa na da sb nb db) (productTicks na nb + productTicks da db) := by
  let middle : Fin 13 → List Bool :=
    ![[],[sa],[],da,[sb],KS.W03.MultiplicationLoop.advance na nb,db,product na nb,[],[],[],[],[]]
  have hn : RunSpec (KS.W29.FixedSequential.liftPorts productProgram numeratorPorts)
      (workFields [sa] na da [sb] nb db [] []) middle (productTicks na nb) := by
    have hl : RunSpec productProgram
        (fun i => workFields [sa] na da [sb] nb db [] [] (numeratorPorts i))
        (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance na nb)
          (product na nb) [] [] []) (productTicks na nb) := by
      convert KS.W06.RationalCompare.product_spec [] na nb using 1 <;>
        first | rfl | (funext j; fin_cases j <;> rfl)
    have h := runSpec_liftPorts productProgram numeratorPorts
      (workFields [sa] na da [sb] nb db [] []) _ _ hl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hd : RunSpec (KS.W29.FixedSequential.liftPorts productProgram denominatorPorts)
      middle (productsAfter sa na da sb nb db) (productTicks da db) := by
    have hl : RunSpec productProgram (fun i => middle (denominatorPorts i))
        (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance da db)
          (product da db) [] [] []) (productTicks da db) := by
      convert KS.W06.RationalCompare.product_spec [] da db using 1 <;>
        first | rfl | (funext j; fin_cases j <;> rfl)
    have h := runSpec_liftPorts productProgram denominatorPorts middle _ _ hl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  exact hn.compose hd

theorem xor_spec (before : Fin 13 → List Bool) (sa sb : Bool)
    (ha : before 1 = [sa]) (hb : before 4 = [sb]) (ho : before 12 = []) :
    RunSpec xorProgram before (xorAfter before sa sb) 1 := by
  unfold xorProgram
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hlen
  rcases bits with _ | ⟨coin, tail⟩
  · simp at hlen
  have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
  subst tail
  change (compile (0 : Fin 1) 1 12 xorDispatch).step
    (⟨some (0 : Fin 1), before⟩ : Config 13 1) coin = _
  erw [step_compile]
  apply congrArg (Config.mk none)
  funext j
  fin_cases j <;> cases sa <;> cases sb <;>
    simp [xorDispatch, xorAfter, Instruction.action, observedHeads, KS.W29.topCode,
      KS.W29.StackAction.apply, ha, hb, ho]

theorem cleanup_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec cleanupProgram (productsAfter sa na da sb nb db)
      (KS.W30.RationalMagnitudeMachine.state (product na nb) (product da db) (sa ^^ sb))
      (cleanupTicks na da nb db) := by
  let s0 := productsAfter sa na da sb nb db
  let s1 := clearAfter 5 s0
  let s2 := clearAfter 6 s1
  let s3 := xorAfter s2 sa sb
  let s4 := moveAfter 7 0 s3
  let s5 := moveAfter 0 10 s4
  let s6 := moveAfter 8 0 s5
  have h1 := clear_spec (5 : Fin 13) s0
  have h2 := clear_spec (6 : Fin 13) s1
  have h3 := xor_spec s2 sa sb rfl rfl rfl
  have h4 := move_spec (7 : Fin 13) 0 (by decide) s3
  have h5 := move_spec (0 : Fin 13) 10 (by decide) s4
  have h6 := move_spec (8 : Fin 13) 0 (by decide) s5
  have h7 := move_spec (0 : Fin 13) 11 (by decide) s6
  have h := (((((h1.compose h2).compose h3).compose h4).compose h5).compose h6).compose h7
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j
    fin_cases j <;> simp [s0,s1,s2,s3,s4,s5,s6,productsAfter,clearAfter,moveAfter,xorAfter,
      KS.W30.RationalMagnitudeMachine.state,KS.W30.RationalMagnitudeMachine.«stacks»]
  · simp [s0,s1,s2,s3,s4,s5,s6,productsAfter,clearAfter,moveAfter,xorAfter,cleanupTicks]
    omega

end KS.W15.RationalMultiply

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddSigned
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalAdd
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.RationalMultiply (move_spec moveAfter clear_spec clearAfter)
open KS.W06.RationalCompare (sign_spec signAfter signProgram branch_spec_left branch_spec_right)
open KS.W19.UnsignedPairSerializer (registers)

theorem equal_spec (sa sb : Bool) (xs ys den : List Bool) :
    RunSpec equalProgram (signedState sa xs sb ys den) (readyState sa (addResult xs ys) den)
      (arithmeticBudget xs ys den) := by
  have ha : RunSpec (canonicalAddProgram addPorts) (signedState sa xs sb ys den)
      (numeratorAt sa sb 8 (addResult xs ys) den) (canonicalAddTicks xs ys) := by
    convert canonicalAdd_spec addPorts (signedState sa xs sb ys den) xs ys using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  have hf := finishNumerator_spec sa sb 8 1 (addResult xs ys) den (Or.inr rfl) (Or.inl rfl)
  apply (ha.compose hf).mono
  have ht := canonicalAddTicks_le xs ys
  have hl := addResult_length_le xs ys
  unfold arithmeticBudget
  omega

theorem leftLarge_spec (sa sb : Bool) (xs ys den : List Bool)
    (horder : KS.W19.bitsValue ys ≤ KS.W19.bitsValue xs) :
    RunSpec leftLargeProgram (signedState sa xs sb ys den)
      (readyState sa (Computability.encodeNat (KS.W19.bitsValue xs - KS.W19.bitsValue ys)) den)
      (arithmeticBudget xs ys den) := by
  let num := Computability.encodeNat (KS.W19.bitsValue xs - KS.W19.bitsValue ys)
  have hs : RunSpec (KS.W19.FixedSubtraction.program addPorts) (signedState sa xs sb ys den)
      (numeratorAt sa sb 8 num den) (2 * (max xs.length ys.length + 1)) := by
    convert KS.W19.FixedSubtraction.subtract_spec addPorts (signedState sa xs sb ys den) xs ys horder using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  have hf := finishNumerator_spec sa sb 8 1 num den (Or.inr rfl) (Or.inl rfl)
  apply (hs.compose hf).mono
  have hl := subtractResult_length_le xs ys horder
  unfold arithmeticBudget
  dsimp [num] at *
  omega

theorem rightLarge_spec (sa sb : Bool) (xs ys den : List Bool)
    (horder : KS.W19.bitsValue xs ≤ KS.W19.bitsValue ys) :
    RunSpec rightLargeProgram (signedState sa xs sb ys den)
      (readyState sb (Computability.encodeNat (KS.W19.bitsValue ys - KS.W19.bitsValue xs)) den)
      (arithmeticBudget xs ys den) := by
  let num := Computability.encodeNat (KS.W19.bitsValue ys - KS.W19.bitsValue xs)
  have hs : RunSpec (KS.W19.FixedSubtraction.program rightSubtractPorts) (signedState sa xs sb ys den)
      (numeratorAt sa sb 7 num den) (2 * (max ys.length xs.length + 1)) := by
    convert KS.W19.FixedSubtraction.subtract_spec rightSubtractPorts (signedState sa xs sb ys den) ys xs horder using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  have hf := finishNumerator_spec sa sb 7 4 num den (Or.inl rfl) (Or.inr rfl)
  apply (hs.compose hf).mono
  have hl := subtractResult_length_le ys xs horder
  unfold arithmeticBudget
  dsimp [num] at *
  omega

theorem orderedBranch_spec (sa sb : Bool) (xs ys den : List Bool) :
    RunSpec orderedBranch (comparedState sa xs sb ys den)
      (if KS.W19.bitsValue xs ≤ KS.W19.bitsValue ys then
        readyState sb (Computability.encodeNat (KS.W19.bitsValue ys - KS.W19.bitsValue xs)) den
      else readyState sa (Computability.encodeNat (KS.W19.bitsValue xs - KS.W19.bitsValue ys)) den)
      (arithmeticBudget xs ys den + 3) := by
  have hc : RunSpec (KS.W04.BinaryStackMoves.clearProgram 12)
      (comparedState sa xs sb ys den) (signedState sa xs sb ys den) 2 := by
    convert clear_spec (12 : Fin 16) (comparedState sa xs sb ys den) using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  by_cases ho : KS.W19.bitsValue xs ≤ KS.W19.bitsValue ys
  · simp only [ite_eq_left ho]
    have h := branch_spec_right
      (compose (KS.W04.BinaryStackMoves.clearProgram 12) leftLargeProgram)
      (compose (KS.W04.BinaryStackMoves.clearProgram 12) rightLargeProgram)
      (10 : Fin 16) (KS.W06.RationalCompare.signSelect 12)
      _ _ _ (by intro coin; simp [KS.W06.RationalCompare.signSelect, observedHeads,
        comparedState, KS.W29.topCode, ho]) (hc.compose (rightLarge_spec sa sb xs ys den ho))
    convert h using 1 <;> first | rfl | omega
  · simp only [ite_eq_right ho]
    have h := branch_spec_left
      (compose (KS.W04.BinaryStackMoves.clearProgram 12) leftLargeProgram)
      (compose (KS.W04.BinaryStackMoves.clearProgram 12) rightLargeProgram)
      (10 : Fin 16) (KS.W06.RationalCompare.signSelect 12)
      _ _ _ (by intro coin; simp [KS.W06.RationalCompare.signSelect, observedHeads,
        comparedState, KS.W29.topCode, ho]) (hc.compose (leftLarge_spec sa sb xs ys den (by omega)))
    convert h using 1 <;> first | rfl | omega

theorem signed_spec (sa sb : Bool) (xs ys den : List Bool) :
    RunSpec signedProgram (signedState sa xs sb ys den)
      (readyState (signedNumerator sa xs sb ys).1 (signedNumerator sa xs sb ys).2 den)
      (signedBudget xs ys den) := by
  by_cases he : sa = sb
  · subst sb
    have h := branch_spec_left equalProgram differentProgram (10 : Fin 16) equalSignSelect
      _ _ _ (by intro coin; simp [equalSignSelect, observedHeads, signedState])
      (equal_spec sa sa xs ys den)
    have h' : RunSpec signedProgram (signedState sa xs sa ys den)
        (readyState (signedNumerator sa xs sa ys).1 (signedNumerator sa xs sa ys).2 den)
        (arithmeticBudget xs ys den + 1) := by simpa [signedProgram, signedNumerator] using h
    apply h'.mono
    unfold signedBudget arithmeticBudget
    omega
  · have h := (copyCompare_spec sa sb xs ys den).compose (orderedBranch_spec sa sb xs ys den)
    have hb := branch_spec_right equalProgram differentProgram (10 : Fin 16) equalSignSelect
      _ _ _ (by intro coin; cases sa <;> cases sb <;>
        simp_all [equalSignSelect, observedHeads, signedState, KS.W29.topCode]) h
    have h' : RunSpec signedProgram (signedState sa xs sb ys den)
        (readyState (signedNumerator sa xs sb ys).1 (signedNumerator sa xs sb ys).2 den)
        ((3 * xs.length + 3 * ys.length + 5) + (arithmeticBudget xs ys den + 3) + 1) := by
      convert hb using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
      unfold signedNumerator
      split_ifs <;> simp_all
    apply h'.mono
    unfold signedBudget arithmeticBudget
    omega

end KS.W13.RationalAdd

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_GCDMachinePolynomial
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem finish_spec (g : List Bool) :
    RunSpec finish (state g []) (outputState g) (g.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (3 : Fin 10) 5 (by decide)
    (state g []) bits (by
      change bits.length=g.reverse.length+1
      simpa only [List.length_reverse] using hlen)
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (3 : Fin 10) 5) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [state,outputState,DivisionMachine.«stacks»,
      KS.W04.BinaryStackMoves.twoConfig]

lemma gcd_encode_length_le (x y : List Bool) (L : ℕ)
    (hx : x.length ≤ L) (hy : y.length ≤ L) :
    (Computability.encodeNat (Nat.gcd (bitsValue x) (bitsValue y))).length ≤ L := by
  by_cases hz : bitsValue y = 0
  · rw [hz, Nat.gcd_zero_right, encodeNat_length_eq_size]
    exact (Nat.size_le.mpr (bitsValue_lt_two_pow_length x)).trans hx
  · have h := (KS.W30.BinaryGCD.gcdBits_length_le_right x y (Nat.pos_of_ne_zero hz)).trans hy
    simpa only [KS.W30.BinaryGCD.gcdBits_eq_encodeNat] using h

theorem program_spec (x y : List Bool) (L : ℕ)
    (hxc : CanonicalBits x) (hyc : CanonicalBits y)
    (hx : x.length ≤ L) (hy : y.length ≤ L) :
    RunSpec program (state x y)
      (outputState (Computability.encodeNat (Nat.gcd (bitsValue x) (bitsValue y))))
      (100 * (L + 1) ^ 3) := by
  let g := Computability.encodeNat (Nat.gcd (bitsValue x) (bitsValue y))
  have hloop : RunSpec loop (state x y) (state g [])
      ((2 * y.length + 1) * (40 * (L + 1) ^ 2 + 1)) := by
    intro bits hlen
    exact loop_run y.length x y bits L hxc hyc hx hy
      (bitsValue_lt_two_pow_length y) (by omega)
  have hf := finish_spec g
  have h := hloop.compose hf
  have hg : g.length ≤ L := gcd_encode_length_le x y L hx hy
  have hb : (2 * y.length + 1) * (40 * (L + 1) ^ 2 + 1) ≤
      (2 * L + 1) * (40 * (L + 1) ^ 2 + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (L + 1)
  have hquad : 1 ≤ (L + 1) ^ 2 := by
    have hp : 0 < (L + 1) ^ 2 := Nat.pow_pos (by omega)
    omega
  have hpoly : (2 * L + 1) * (40 * (L + 1) ^ 2 + 1) ≤ 82 * (L + 1) ^ 3 := by
    calc
      _ ≤ (2 * (L + 1)) * (41 * (L + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have ht : (2 * y.length + 1) * (40 * (L + 1) ^ 2 + 1) + (g.length + 1) ≤
      100 * (L + 1) ^ 3 := by omega
  exact h.mono ht

end KS.W30.GCDMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeSetup
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem copyNumerator_spec (n d : List Bool) (s : Bool) :
    RunSpec copyNumerator (state n d s)
      («stacks» (copiedNumeratorWork n) n d s) (2 * n.length + 2) := by
  intro bits hlen
  have h := KS.W01.FixedCopy.run_copy_restore numeratorCopyPorts (state n d s)
    n bits rfl rfl rfl hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W01.FixedCopy.machine numeratorCopyPorts) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem reverseNumeratorCopy_spec (n d : List Bool) (s : Bool) :
    RunSpec reverseNumeratorCopy («stacks» (copiedNumeratorWork n) n d s)
      («stacks» (GCDMachine.state n []) n d s) (n.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (1 : Fin 13) 3 (by decide)
    («stacks» (copiedNumeratorWork n) n d s) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (1 : Fin 13) 3) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,copiedNumeratorWork,GCDMachine.state,DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem copyDenominator_spec (n d : List Bool) (s : Bool) :
    RunSpec copyDenominator («stacks» (GCDMachine.state n []) n d s)
      («stacks» (GCDMachine.state n d) n d s) (2 * d.length + 2) := by
  intro bits hlen
  have h := KS.W01.FixedCopy.run_copy_restore denominatorCopyPorts
    («stacks» (GCDMachine.state n []) n d s) d bits rfl rfl rfl hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W01.FixedCopy.machine denominatorCopyPorts) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem prepare_spec (n d : List Bool) (s : Bool) :
    RunSpec prepare (state n d s) («stacks» (GCDMachine.state n d) n d s)
      (3 * n.length + 2 * d.length + 5) := by
  have h := (copyNumerator_spec n d s).compose
    ((reverseNumeratorCopy_spec n d s).compose (copyDenominator_spec n d s))
  convert h using 1 <;> first | rfl | omega

theorem gcd_spec (n d : List Bool) (s : Bool) (L : ℕ)
    (hnc : CanonicalBits n) (hdc : CanonicalBits d) (hn : n.length ≤ L) (hd : d.length ≤ L) :
    RunSpec gcd («stacks» (GCDMachine.state n d) n d s)
      («stacks» (GCDMachine.outputState
        (Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d)))) n d s)
      (100 * (L + 1) ^ 3) :=
  core_spec GCDMachine.program _ _ n d s _ (GCDMachine.program_spec n d L hnc hdc hn hd)

theorem reverseGCD_spec (g n d : List Bool) (s : Bool) :
    RunSpec reverseGCD («stacks» (GCDMachine.outputState g) n d s)
      («stacks» (reversedGCDWork g) n d s) (g.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (5 : Fin 13) 8 (by decide)
    («stacks» (GCDMachine.outputState g) n d s) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (5 : Fin 13) 8) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,GCDMachine.outputState,
      reversedGCDWork,DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem placeGCD_spec (g n d : List Bool) (s : Bool) :
    RunSpec placeGCD («stacks» (reversedGCDWork g) n d s)
      (divisorState g n d s) (g.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (8 : Fin 13) 2 (by decide)
    («stacks» (reversedGCDWork g) n d s) bits
    (by change bits.length=g.reverse.length+1; simpa only [List.length_reverse] using hlen)
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (8 : Fin 13) 2) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,divisorState,divisorWork,reversedGCDWork,
      DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem computeGCD_spec (n d : List Bool) (s : Bool) (L : ℕ)
    (hnc : CanonicalBits n) (hdc : CanonicalBits d) (hn : n.length ≤ L) (hd : d.length ≤ L) :
    let g := Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))
    RunSpec computeGCD (state n d s) (divisorState g n d s)
      (120 * (L + 1) ^ 3) := by
  dsimp only
  let g := Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))
  have h := (prepare_spec n d s).compose ((gcd_spec n d s L hnc hdc hn hd).compose
    ((reverseGCD_spec g n d s).compose (placeGCD_spec g n d s)))
  have hg : g.length ≤ L := GCDMachine.gcd_encode_length_le n d L hn hd
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (L + 1)
  have ht : (3 * n.length + 2 * d.length + 5) +
      (100 * (L + 1) ^ 3 + ((g.length + 1) + (g.length + 1))) ≤ 120 * (L + 1) ^ 3 := by
    omega
  exact h.mono ht

end KS.W30.RationalMagnitudeMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeDivision
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem divide_spec (g x n d : List Bool) (s : Bool) (L : ℕ)
    (hg : g.length ≤ L) (hx : x.length ≤ L) :
    let qr := DivisionLoop.process g x.reverse [] []
    RunSpec divide («stacks» (divisionWork g x) n d s)
      («stacks» (quotientWork g qr.1 qr.2) n d s) (40 * (L + 1) ^ 2) := by
  dsimp only
  have h : RunSpec DivisionMachine.loop (divisionWork g x)
      (quotientWork g (DivisionLoop.process g x.reverse [] []).1
        (DivisionLoop.process g x.reverse [] []).2)
      (x.length * (8 * (x.length + 2 * g.length + 2) + 1) + 1) := by
    intro bits hlen
    exact DivisionMachine.loop_payload g x bits (by omega)
  have hm : x.length * (8 * (x.length + 2 * g.length + 2) + 1) ≤
      L * (8 * (3 * L + 2) + 1) := Nat.mul_le_mul hx (by omega)
  have ht : x.length * (8 * (x.length + 2 * g.length + 2) + 1) + 1 ≤
      40 * (L + 1) ^ 2 := by nlinarith
  exact core_spec DivisionMachine.loop _ _ n d s _ (h.mono ht)

theorem reverseQuotient_spec (g q r n d : List Bool) (s : Bool) :
    RunSpec reverseQuotient («stacks» (quotientWork g q r) n d s)
      («stacks» (reversedQuotientWork g q r) n d s) (q.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (5 : Fin 13) 8 (by decide)
    («stacks» (quotientWork g q r) n d s) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (5 : Fin 13) 8) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,quotientWork,reversedQuotientWork,
      DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem clearRemainder_spec (g r n d : List Bool) (s : Bool) :
    RunSpec clearRemainder («stacks» (remainderWork g r) n d s)
      (divisorState g n d s) (r.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (4 : Fin 13)
    («stacks» (remainderWork g r) n d s) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.clearMachine (4 : Fin 13)) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

theorem takeNumerator_spec (g n d : List Bool) (sgn : Bool) :
    RunSpec takeNumerator (divisorState g n d sgn)
      («stacks» (divisionWork g n) [] d sgn) (n.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (10 : Fin 13) 3 (by decide)
    (divisorState g n d sgn) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (10 : Fin 13) 3) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,divisorState,divisorWork,
      divisionWork,DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem trimNumerator_input (g q r _numerator d : List Bool) (sgn : Bool) :
    UnsignedPairSerializer.registers numeratorTrimPorts («stacks» (remainderWork g r) [] d sgn) [] [] q.reverse=
      «stacks» (reversedQuotientWork g q r) [] d sgn :=by
  funext j
  fin_cases j <;> simp [UnsignedPairSerializer.registers,numeratorTrimPorts,«stacks»,
    remainderWork,reversedQuotientWork,DivisionMachine.«stacks»]

theorem trimNumerator_output (g q r _numerator d : List Bool) (sgn : Bool) :
    UnsignedPairSerializer.registers numeratorTrimPorts («stacks» (remainderWork g r) [] d sgn)
      [] (trimBits q) []=«stacks» (remainderWork g r) (trimBits q) d sgn :=by
  funext j
  fin_cases j <;> simp [UnsignedPairSerializer.registers,numeratorTrimPorts,«stacks»,
    remainderWork,DivisionMachine.«stacks»]

theorem trimNumerator_spec (g q r n d : List Bool) (sgn : Bool) :
    RunSpec trimNumerator («stacks» (reversedQuotientWork g q r) [] d sgn)
      («stacks» (remainderWork g r) (trimBits q) d sgn) (q.length+1) :=by
  have h :=FixedCanonicalize.trim_spec numeratorTrimPorts («stacks» (remainderWork g r) [] d sgn) [] q
  rw [←trimBits_eq_encodeNat,trimNumerator_input g q r n d sgn,
    trimNumerator_output g q r n d sgn] at h
  exact h

theorem reduceNumerator_spec (g n d : List Bool) (sgn : Bool) (L : ℕ)
    (hg : g.length ≤ L) (hx : n.length ≤ L) :
    let qr := DivisionLoop.process g n.reverse [] []
    RunSpec reduceNumerator (divisorState g n d sgn)
      (divisorState g (trimBits qr.1) (d) sgn) (50 * (L + 1) ^ 2) := by
  dsimp only
  let qr := DivisionLoop.process g n.reverse [] []
  have h := (takeNumerator_spec g n d sgn).compose
    ((divide_spec g n [] d sgn L hg hx).compose
      ((reverseQuotient_spec g qr.1 qr.2 [] d sgn).compose
        ((trimNumerator_spec g qr.1 qr.2 n d sgn).compose
          (clearRemainder_spec g qr.2 (trimBits qr.1) (d) sgn))))
  have hq : qr.1.length = n.length := by
    simpa only [qr, List.length_reverse, List.length_nil, Nat.add_zero] using
      GCDMachine.process_quotient_length g n.reverse [] []
  have hr : qr.2.length ≤ 2 * L := by
    have hh := GCDMachine.process_remainder_length g n.reverse [] [] (2 * L)
      (by simp only [List.length_nil, List.length_reverse]; omega)
      (by simp only [List.length_reverse]; omega)
    exact hh
  have ht : (n.length + 1) + (40 * (L + 1) ^ 2 +
      ((qr.1.length + 1) + ((qr.1.length + 1) + (qr.2.length + 1)))) ≤
      50 * (L + 1) ^ 2 := by rw [hq]; nlinarith
  exact h.mono ht

theorem takeDenominator_spec (g n d : List Bool) (sgn : Bool) :
    RunSpec takeDenominator (divisorState g n d sgn)
      («stacks» (divisionWork g d) n [] sgn) (d.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (11 : Fin 13) 3 (by decide)
    (divisorState g n d sgn) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (11 : Fin 13) 3) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [«stacks»,divisorState,divisorWork,
      divisionWork,DivisionMachine.«stacks»,KS.W04.BinaryStackMoves.twoConfig]

theorem trimDenominator_input (g q r n _denominator : List Bool) (sgn : Bool) :
    UnsignedPairSerializer.registers denominatorTrimPorts («stacks» (remainderWork g r) n [] sgn) [] [] q.reverse=
      «stacks» (reversedQuotientWork g q r) n [] sgn :=by
  funext j
  fin_cases j <;> simp [UnsignedPairSerializer.registers,denominatorTrimPorts,«stacks»,
    remainderWork,reversedQuotientWork,DivisionMachine.«stacks»]

theorem trimDenominator_output (g q r n _denominator : List Bool) (sgn : Bool) :
    UnsignedPairSerializer.registers denominatorTrimPorts («stacks» (remainderWork g r) n [] sgn)
      [] (trimBits q) []=«stacks» (remainderWork g r) n (trimBits q) sgn :=by
  funext j
  fin_cases j <;> simp [UnsignedPairSerializer.registers,denominatorTrimPorts,«stacks»,
    remainderWork,DivisionMachine.«stacks»]

theorem trimDenominator_spec (g q r n d : List Bool) (sgn : Bool) :
    RunSpec trimDenominator («stacks» (reversedQuotientWork g q r) n [] sgn)
      («stacks» (remainderWork g r) n (trimBits q) sgn) (q.length+1) :=by
  have h :=FixedCanonicalize.trim_spec denominatorTrimPorts («stacks» (remainderWork g r) n [] sgn) [] q
  rw [←trimBits_eq_encodeNat,trimDenominator_input g q r n d sgn,
    trimDenominator_output g q r n d sgn] at h
  exact h

theorem reduceDenominator_spec (g n d : List Bool) (sgn : Bool) (L : ℕ)
    (hg : g.length ≤ L) (hx : d.length ≤ L) :
    let qr := DivisionLoop.process g d.reverse [] []
    RunSpec reduceDenominator (divisorState g n d sgn)
      (divisorState g (n) (trimBits qr.1) sgn) (50 * (L + 1) ^ 2) := by
  dsimp only
  let qr := DivisionLoop.process g d.reverse [] []
  have h := (takeDenominator_spec g n d sgn).compose
    ((divide_spec g d n [] sgn L hg hx).compose
      ((reverseQuotient_spec g qr.1 qr.2 n [] sgn).compose
        ((trimDenominator_spec g qr.1 qr.2 n d sgn).compose
          (clearRemainder_spec g qr.2 (n) (trimBits qr.1) sgn))))
  have hq : qr.1.length = d.length := by
    simpa only [qr, List.length_reverse, List.length_nil, Nat.add_zero] using
      GCDMachine.process_quotient_length g d.reverse [] []
  have hr : qr.2.length ≤ 2 * L := by
    have hh := GCDMachine.process_remainder_length g d.reverse [] [] (2 * L)
      (by simp only [List.length_nil, List.length_reverse]; omega)
      (by simp only [List.length_reverse]; omega)
    exact hh
  have ht : (d.length + 1) + (40 * (L + 1) ^ 2 +
      ((qr.1.length + 1) + ((qr.1.length + 1) + (qr.2.length + 1)))) ≤
      50 * (L + 1) ^ 2 := by rw [hq]; nlinarith
  exact h.mono ht

end KS.W30.RationalMagnitudeMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeSign
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem sign_initial : normalizeSign.initial=(0 : Fin 2) :=rfl
theorem one_initial : insertOne.initial=(0 : Fin 1) :=rfl

lemma sign_zero_first (d : List Bool) (sgn coin : Bool) :
    (compile (0 : Fin 2) (10 : Fin 13) 10 signDispatch).step ⟨some (0 : Fin 2), state [] d sgn⟩ coin =
      ⟨some (1 : Fin 2), Function.update (state [] d sgn) (12 : Fin 13) []⟩ := by
  erw [step_compile]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

lemma sign_zero_second (d : List Bool) (sgn coin : Bool) :
    (compile (0 : Fin 2) (10 : Fin 13) 10 signDispatch).step ⟨some (1 : Fin 2), Function.update (state [] d sgn) (12 : Fin 13) []⟩ coin =
      ⟨none, state [] d false⟩ := by
  erw [step_compile]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

lemma sign_nonzero (n d : List Bool) (hn : n ≠ []) (sgn coin : Bool) :
    (compile (0 : Fin 2) (10 : Fin 13) 10 signDispatch).step ⟨some (0 : Fin 2), state n d sgn⟩ coin = ⟨none, state n d sgn⟩ := by
  cases n with
  | nil => exact (hn rfl).elim
  | cons b bs =>
    erw [step_compile]
    cases b <;> apply config_ext
    all_goals first | rfl | (intro j; fin_cases j <;> rfl)

theorem normalizeSign_spec (n d : List Bool) (sgn : Bool) :
    RunSpec normalizeSign (state n d sgn) (state n d (if n = [] then false else sgn)) 2 := by
  intro bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (compile (0 : Fin 2) (10 : Fin 13) 10 signDispatch) _ bits).trans ?_
  rw [sign_initial]
  cases bits with
  | nil => simp at hlen
  | cons c tail =>
    by_cases hn : n = []
    · subst n
      cases tail with
      | nil => simp at hlen
      | cons c' rest =>
        have hr : rest = [] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hlen; omega
        subst rest
        erw [Machine.run.eq_2]
        erw [sign_zero_first d sgn c]
        erw [Machine.run.eq_2]
        erw [sign_zero_second d sgn c']
        all_goals rfl
    · erw [Machine.run.eq_2]
      erw [sign_nonzero n d hn sgn c]
      rw [Machine.run_halted _ _ rfl]
      all_goals (simp only [ite_eq_right hn]; rfl)

theorem insertOne_spec (sgn : Bool) :
    RunSpec insertOne (state [] [] sgn) (state [] [true] sgn) 1 := by
  intro bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (compile (0 : Fin 1) (10 : Fin 13) 10 oneDispatch) _ bits).trans ?_
  rw [one_initial]
  cases bits with
  | nil => simp at hlen
  | cons coin tail =>
    have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hlen; omega
    subst tail
    erw [Machine.run.eq_2]
    erw [step_compile (0 : Fin 1) (10 : Fin 13) 10 oneDispatch
      (0 : Fin 1) (state [] [] sgn) coin]
    apply config_ext
    · rfl
    · intro j
      fin_cases j <;> rfl

theorem zeroBranch_spec (n : List Bool) (sgn : Bool) :
    RunSpec zeroBranch (state n [] sgn) (state [] [true] false) (n.length + 4) := by
  have h := (zeroNumerator_spec n sgn).compose
    ((insertOne_spec sgn).compose (normalizeSign_spec [] [true] sgn))
  convert h using 1 <;> rfl

theorem clearGCD_spec (g n d : List Bool) (sgn : Bool) :
    RunSpec clearGCD (divisorState g n d sgn) (state n d sgn) (g.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (2 : Fin 13) (divisorState g n d sgn) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.clearMachine (2 : Fin 13)) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

end KS.W30.RationalMagnitudeMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudePositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19 KS.W30.BinaryGCD

theorem positiveBranch_spec (n d : List Bool) (sgn : Bool) (L : ℕ)
    (hnc : CanonicalBits n) (hdc : CanonicalBits d)
    (hn : n.length ≤ L) (hd : d.length ≤ L) (hdp : 0 < bitsValue d) :
    let p := KS.W30.BinaryRational.normalizeMagnitude n d
    RunSpec positiveBranch (state n d sgn)
      (state p.1 p.2 (if p.1 = [] then false else sgn)) (250 * (L + 1) ^ 3) := by
  dsimp only
  let g := Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))
  let qn := DivisionLoop.process g n.reverse [] []
  let qd := DivisionLoop.process g d.reverse [] []
  have hg : g.length ≤ L := GCDMachine.gcd_encode_length_le n d L hn hd
  have hsetup := computeGCD_spec n d sgn L hnc hdc hn hd
  have hnrun := reduceNumerator_spec g n d sgn L hg hn
  have hdrun := reduceDenominator_spec g (trimBits qn.1) d sgn L hg hd
  have hfinish := (clearGCD_spec g (trimBits qn.1) (trimBits qd.1) sgn).compose
    (normalizeSign_spec (trimBits qn.1) (trimBits qd.1) sgn)
  have h := hsetup.compose (hnrun.compose (hdrun.compose hfinish))
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (L + 1)
  have hquad : (L + 1) ^ 2 ≤ (L + 1) ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have ht : 120 * (L + 1) ^ 3 + (50 * (L + 1) ^ 2 +
      (50 * (L + 1) ^ 2 + ((g.length + 1) + 2))) ≤ 250 * (L + 1) ^ 3 := by omega
  have hp : KS.W30.BinaryRational.normalizeMagnitude n d =
      (trimBits qn.1, trimBits qd.1) := positive_output_pair n d hdp
  simpa only [positiveBranch, hp] using h.mono ht

end KS.W30.RationalMagnitudeMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeCorrect
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

lemma selector_zero (n : List Bool) (sgn coin : Bool) :
    program.toMachine.step ⟨some program.initial, state n [] sgn⟩ coin =
      KS.W29.FixedBranch.liftLeft zeroBranch positiveBranch
        ⟨some zeroBranch.initial, state n [] sgn⟩ := by
  unfold program
  erw [KS.W29.FixedBranch.step_start]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

lemma selector_positive (n d : List Bool) (hd : d ≠ []) (sgn coin : Bool) :
    program.toMachine.step ⟨some program.initial, state n d sgn⟩ coin =
      KS.W29.FixedBranch.liftRight zeroBranch positiveBranch
        ⟨some positiveBranch.initial, state n d sgn⟩ := by
  cases d with
  | nil => exact (hd rfl).elim
  | cons b bs =>
    unfold program
    erw [KS.W29.FixedBranch.step_start]
    cases b <;> apply config_ext
    all_goals first | rfl | (intro j; fin_cases j <;> rfl)

theorem program_spec (n d : List Bool) (sgn : Bool) (L : ℕ)
    (hnc : CanonicalBits n) (hdc : CanonicalBits d)
    (hn : n.length ≤ L) (hd : d.length ≤ L) :
    let p := KS.W30.BinaryRational.normalizeMagnitude n d
    RunSpec program (state n d sgn)
      (state p.1 p.2 (if p.1 = [] then false else sgn)) (300 * (L + 1) ^ 3) := by
  dsimp only
  intro bits hlen
  cases bits with
  | nil => simp at hlen
  | cons coin tail =>
    simp only [List.length_cons] at hlen
    have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (L + 1)
    by_cases hd0 : d = []
    · subst d
      have ht : n.length + 4 ≤ tail.length := by omega
      rw [Machine.run, selector_zero]
      change (KS.W29.FixedBranch.branch zeroBranch positiveBranch 10 selector).toMachine.run
        (KS.W29.FixedBranch.liftLeft zeroBranch positiveBranch
          ⟨some zeroBranch.initial, state n [] sgn⟩) tail = _
      rw [KS.W29.FixedBranch.run_left]
      erw [(zeroBranch_spec n sgn).run_of_le tail ht]
      simp only [KS.W30.BinaryRational.normalizeMagnitude, trimBits, ↓reduceIte]
      rfl
    · have hdp := canonicalBits_value_pos d hdc hd0
      have ht : 250 * (L + 1) ^ 3 ≤ tail.length := by omega
      rw [Machine.run, selector_positive n d hd0 sgn coin]
      change (KS.W29.FixedBranch.branch zeroBranch positiveBranch 10 selector).toMachine.run
        (KS.W29.FixedBranch.liftRight zeroBranch positiveBranch
          ⟨some positiveBranch.initial, state n d sgn⟩) tail = _
      rw [KS.W29.FixedBranch.run_right]
      erw [(positiveBranch_spec n d sgn L hnc hdc hn hd hdp).run_of_le tail ht]
      rfl

theorem normalizes_ratBits (x : KS.W30.BinaryRational.RatBits) (L : ℕ)
    (hnc : CanonicalBits x.numerator) (hdc : CanonicalBits x.denominator)
    (hn : x.numerator.length ≤ L) (hd : x.denominator.length ≤ L) :
    RunSpec program (state x.numerator x.denominator x.negative)
      (state (KS.W30.BinaryRational.normalize x).numerator
        (KS.W30.BinaryRational.normalize x).denominator
        (KS.W30.BinaryRational.normalize x).negative) (300 * (L + 1) ^ 3) :=
  program_spec x.numerator x.denominator x.negative L hnc hdc hn hd

theorem normalizes_to_rational_encoding (x : KS.W30.BinaryRational.RatBits) (L : ℕ)
    (hnc : CanonicalBits x.numerator) (hdc : CanonicalBits x.denominator)
    (hn : x.numerator.length ≤ L) (hd : x.denominator.length ≤ L) :
    let q := x.value
    RunSpec program (state x.numerator x.denominator x.negative)
      (state (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        (decide (q.num < 0))) (300 * (L + 1) ^ 3) := by
  have h := normalizes_ratBits x L hnc hdc hn hd
  rw [KS.W30.BinaryRational.normalize_eq_encodeMagnitude] at h
  exact h

end KS.W30.RationalMagnitudeMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalAdd
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (magnitude product negativeBit constructorBits pairBits)

theorem preNormalize_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    let x := rawInputSum sa na da sb nb db
    RunSpec preNormalizeProgram (inputState (pairBits sa na da sb nb db))
      (readyState x.negative x.numerator x.denominator) (preNormalizeTicks sa na da sb nb db) := by
  exact (((prepare_spec sa na da sb nb db).compose
    (products_spec sa (magnitude sa na) da sb (magnitude sb nb) db)).compose
    (clearProducts_spec sa (magnitude sa na) da sb (magnitude sb nb) db)).compose
    (signed_spec sa sb (product (magnitude sa na) db) (product (magnitude sb nb) da) (product da db))

theorem rawInputSum_bounds (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    let x := rawInputSum sa na da sb nb db
    KS.W19.CanonicalBits x.numerator ∧ KS.W19.CanonicalBits x.denominator ∧
      x.numerator.length ≤ payloadBound na da nb db ∧ x.denominator.length ≤ payloadBound na da nb db := by
  dsimp only
  have ha := KS.W06.RationalCompare.magnitude_length_le sa na
  have hb := KS.W06.RationalCompare.magnitude_length_le sb nb
  have hl := KS.W06.RationalCompare.product_length_le (magnitude sa na) db
  have hr := KS.W06.RationalCompare.product_length_le (magnitude sb nb) da
  have hd := KS.W06.RationalCompare.product_length_le da db
  have hn := signedNumerator_length_le sa (product (magnitude sa na) db) sb (product (magnitude sb nb) da)
  refine ⟨signedNumerator_canonical _ _ _ _, KS.W19.canonicalBits_encodeNat _, ?_, ?_⟩
  · change (signedNumerator sa (product (magnitude sa na) db)
      sb (product (magnitude sb nb) da)).2.length ≤
        na.length + da.length + nb.length + db.length + 3
    omega
  · change (product da db).length ≤ na.length + da.length + nb.length + db.length + 3
    omega

def totalTicks (q r : ℚ) : ℕ :=
  preNormalizeTicks (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
    (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den) +
  300 * (payloadBound (constructorBits q.num) (Computability.encodeNat q.den)
    (constructorBits r.num) (Computability.encodeNat r.den) + 1) ^ 3 +
  16 * ((Computability.encodeNat (q+r).num.natAbs).length +
    (Computability.encodeNat (q+r).den).length + 1)

theorem full_spec (q r : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (outputState (KS.W01.encodeRat (q+r))) (totalTicks q r) := by
  let sa := negativeBit q.num
  let na := constructorBits q.num
  let da := Computability.encodeNat q.den
  let sb := negativeBit r.num
  let nb := constructorBits r.num
  let db := Computability.encodeNat r.den
  let x := rawInputSum sa na da sb nb db
  have hv : x.value = q+r := rawSum_encoded_value q r
  obtain ⟨hnc, hdc, hn, hd⟩ := rawInputSum_bounds sa na da sb nb db
  have hnorm := core_spec KS.W30.RationalMagnitudeMachine.program _ _ [] [] [] _
    (KS.W30.RationalMagnitudeMachine.normalizes_to_rational_encoding x
      (payloadBound na da nb db) hnc hdc hn hd)
  rw [hv] at hnorm
  have hserialize := core_spec KS.W01.SignedRationalSerializer.program _ _ [] [] [] _
    (KS.W01.SignedRationalSerializer.serializes_rational (q+r))
  have h := ((preNormalize_spec sa na da sb nb db).compose hnorm).compose hserialize
  simp only [sa, na, da, sb, nb, db, KS.W06.RationalCompare.pairBits_encodeRat] at h
  exact h

end KS.W13.RationalAdd

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalAddCorrect
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.RationalAdd
open scoped BigOperators
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (magnitude product negativeBit constructorBits pairBits)

theorem preNormalizeTicks_le (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    preNormalizeTicks sa na da sb nb db ≤ 128 * (payloadBound na da nb db) ^ 2 := by
  let S := na.length + da.length + nb.length + db.length
  have ha := KS.W06.RationalCompare.magnitude_length_le sa na
  have hb := KS.W06.RationalCompare.magnitude_length_le sb nb
  have hl := KS.W06.RationalCompare.product_length_le (magnitude sa na) db
  have hr := KS.W06.RationalCompare.product_length_le (magnitude sb nb) da
  have hd := KS.W06.RationalCompare.product_length_le da db
  have hpl := KS.W06.RationalCompare.productTicks_le (magnitude sa na) db
  have hpr := KS.W06.RationalCompare.productTicks_le (magnitude sb nb) da
  have hpd := KS.W06.RationalCompare.productTicks_le da db
  have hbl : (magnitude sa na).length + db.length + 2 ≤ S + 3 := by dsimp [S]; omega
  have hbr : (magnitude sb nb).length + da.length + 2 ≤ S + 3 := by dsimp [S]; omega
  have hbd : da.length + db.length + 2 ≤ S + 3 := by dsimp [S]; omega
  have hpl' := hpl.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hbl 2))
  have hpr' := hpr.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hbr 2))
  have hpd' := hpd.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hbd 2))
  unfold preNormalizeTicks productsTicks clearProductsTicks signedBudget payloadBound
  simp only [KS.W03.MultiplicationLoop.advance_length]
  unfold KS.W06.RationalCompare.parseTicks
  dsimp [S] at hpl' hpr' hpd'
  nlinarith [Nat.zero_le ((na.length + da.length + nb.length + db.length) ^ 2)]

theorem totalTicks_le_polynomial (q r : ℚ) :
    totalTicks q r ≤ KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  let na := constructorBits q.num
  let da := Computability.encodeNat q.den
  let nb := constructorBits r.num
  let db := Computability.encodeNat r.den
  let S := na.length + da.length + nb.length + db.length
  let L := (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length
  have hwire : L = 2 * S + 6 := by
    have h := KS.W06.RationalCompare.pairBits_length (negativeBit q.num) na da (negativeBit r.num) nb db
    rw [KS.W06.RationalCompare.pairBits_encodeRat] at h
    exact h
  have hp := preNormalizeTicks_le (negativeBit q.num) na da (negativeBit r.num) nb db
  have hsmall : payloadBound na da nb db ≤ L + 1 := by dsimp [payloadBound]; omega
  have hlarge : payloadBound na da nb db + 1 ≤ L + 1 := by dsimp [payloadBound]; omega
  have hpow2 : (L+1)^2 ≤ (L+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp' : preNormalizeTicks (negativeBit q.num) na da (negativeBit r.num) nb db ≤ 128 * (L+1)^3 :=
    hp.trans ((Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hsmall 2)).trans (Nat.mul_le_mul_left 128 hpow2))
  have hn : 300 * (payloadBound na da nb db + 1)^3 ≤ 300 * (L+1)^3 :=
    Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left hlarge 3)
  have hout := KS.W01.rational_parts_size_le_length (q+r)
  have hsize := KS.W01.ratLength_add_le q r
  have henc (n : ℕ) : (Computability.encodeNat n).length = Nat.size n := KS.W19.encodeNat_length_eq_size n
  have hser : 16 * ((Computability.encodeNat (q+r).num.natAbs).length +
      (Computability.encodeNat (q+r).den).length + 1) ≤ 304 * (L+1)^3 := by
    rw [henc, henc]
    have hlin : L+1 ≤ (L+1)^3 := Nat.le_self_pow (by decide) _
    have hlen : KS.W01.ratLength q + KS.W01.ratLength r = L := by
      simp [L, KS.W01.ratLength]
    omega
  change _ ≤ 1000 * (L+1)^3
  unfold totalTicks
  change preNormalizeTicks (negativeBit q.num) na da (negativeBit r.num) nb db +
    300 * (payloadBound na da nb db + 1)^3 + _ ≤ _
  omega

theorem polynomial_spec (q r : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (outputState (KS.W01.encodeRat (q+r)))
      (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) :=
  (full_spec q r).mono (totalTicks_le_polynomial q r)

end KS.W13.RationalAdd

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplyNormalize
attribute [-simp] _root_.OAI.KS.W08.denseMatrixBinaryCursor_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (magnitude product productTicks parseTicks prepareProgram

  negativeBit constructorBits pairBits fields signedFraction)

def rawCanonicalProduct (q r : ℚ) : KS.W30.BinaryRational.RatBits :=
  rawProduct (negativeBit q.num) (magnitude (negativeBit q.num) (constructorBits q.num))
    (Computability.encodeNat q.den) (negativeBit r.num)
    (magnitude (negativeBit r.num) (constructorBits r.num)) (Computability.encodeNat r.den)

theorem rawCanonicalProduct_value (q r : ℚ) : (rawCanonicalProduct q r).value = q * r := by
  unfold rawCanonicalProduct
  rw [rawProduct_value, KS.W06.RationalCompare.magnitude_constructor_value,
    KS.W06.RationalCompare.magnitude_constructor_value,
    KS.W19.bitsValue_encodeNat, KS.W19.bitsValue_encodeNat,
    KS.W06.RationalCompare.signedFraction_num_den,
    KS.W06.RationalCompare.signedFraction_num_den]

theorem normalized_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    let q := (rawProduct sa (magnitude sa na) da sb (magnitude sb nb) db).value
    RunSpec normalizeProgram (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (KS.W30.RationalMagnitudeMachine.state (Computability.encodeNat q.num.natAbs)
        (Computability.encodeNat q.den) (decide (q.num < 0)))
      (normalizeTicks sa na da sb nb db) := by
  dsimp only
  let a := magnitude sa na
  let b := magnitude sb nb
  let L := payloadSize na da nb db + 2
  have hla := KS.W06.RationalCompare.magnitude_length_le sa na
  have hlb := KS.W06.RationalCompare.magnitude_length_le sb nb
  have hn : (product a b).length ≤ L := by
    have h := KS.W06.RationalCompare.product_length_le a b
    dsimp [a,b,L,payloadSize] at *
    omega
  have hd : (product da db).length ≤ L := by
    have h := KS.W06.RationalCompare.product_length_le da db
    dsimp [L,payloadSize]
    omega
  have hnorm := KS.W30.RationalMagnitudeMachine.normalizes_to_rational_encoding
    (rawProduct sa a da sb b db) L
    (KS.W19.canonicalBits_encodeNat _) (KS.W19.canonicalBits_encodeNat _) hn hd
  have h := (((KS.W06.RationalCompare.prepare_spec sa na da sb nb db).compose
    (products_spec sa a da sb b db)).compose (cleanup_spec sa a da sb b db)).compose hnorm
  exact h

def canonicalNormalizeTicks (q r : ℚ) : Nat :=
  normalizeTicks (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
    (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den)

theorem canonical_normalized_spec (q r : ℚ) :
    RunSpec normalizeProgram
      (fields (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [] [] [] [] [] [])
      (KS.W30.RationalMagnitudeMachine.state (Computability.encodeNat (q * r).num.natAbs)
        (Computability.encodeNat (q * r).den) (decide ((q * r).num < 0)))
      (canonicalNormalizeTicks q r) := by
  have h := normalized_spec (negativeBit q.num) (constructorBits q.num)
    (Computability.encodeNat q.den) (negativeBit r.num) (constructorBits r.num)
    (Computability.encodeNat r.den)
  change RunSpec normalizeProgram _
    (KS.W30.RationalMagnitudeMachine.state
      (Computability.encodeNat (rawCanonicalProduct q r).value.num.natAbs)
      (Computability.encodeNat (rawCanonicalProduct q r).value.den)
      (decide ((rawCanonicalProduct q r).value.num < 0))) _ at h
  rw [rawCanonicalProduct_value, KS.W06.RationalCompare.pairBits_encodeRat] at h
  exact h

end KS.W15.RationalMultiply

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplicationMachine
attribute [-simp] _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def totalTicks (q r : ℚ) : Nat :=
  canonicalNormalizeTicks q r + 16 *
    ((Computability.encodeNat (q * r).num.natAbs).length +
      (Computability.encodeNat (q * r).den).length + 1)

theorem full_spec (q r : ℚ) :
    RunSpec program (KS.W06.RationalCompare.fields (inputBits q r) [] [] [] [] [] [])
      (KS.W01.SignedRationalSerializer.outputState (KS.W01.encodeRat (q * r)))
      (totalTicks q r) :=
  (canonical_normalized_spec q r).compose (KS.W01.SignedRationalSerializer.serializes_rational (q * r))

@[simp] theorem machine_inputStack : machine.inputStack = (0 : Fin 13) := rfl
@[simp] theorem machine_outputStack : machine.outputStack = (10 : Fin 13) := rfl

end KS.W15.RationalMultiply

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SingleRationalParser
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W06.SingleRationalParser

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare

theorem magnitude_constructor_eq (z : ℤ) :
    KS.W01.MagnitudeProgram.result (negativeBit z) (constructorBits z) =
      Computability.encodeNat z.natAbs := by
  apply KS.W19.canonicalBits_injective
    (magnitude_result_canonical _ _ (KS.W19.canonicalBits_encodeNat _))
    (KS.W19.canonicalBits_encodeNat _)
  rw [KS.W01.MagnitudeProgram.result_value, KS.W19.bitsValue_encodeNat]
  simp only [KS.W19.bitsValue_encodeNat]
  cases z <;> simp [negativeBit, KS.W01.intPayload, KS.W19.digit]

theorem base_spec (sign : Bool) (num den tail : List Bool) :
    RunSpec baseProgram
      (baseState (sign :: (KS.W01.frame num ++ KS.W01.frame den ++ tail)) [] [] [])
      (baseState tail (KS.W01.MagnitudeProgram.result sign num) den [sign])
      (baseTicks num den) := by
  let rest := KS.W01.frame num ++ KS.W01.frame den ++ tail
  have hs : RunSpec (signProgram (0 : Fin 6) 5)
      (baseState (sign :: rest) [] [] []) (baseState rest [] [] [sign]) 1 := by
    have h := sign_spec (0 : Fin 6) 5 (by decide) (baseState (sign :: rest) [] [] []) sign rest rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hn : RunSpec (decodeProgram numeratorPorts) (baseState rest [] [] [sign])
      (baseState (KS.W01.frame den ++ tail) num [] [sign]) (3 * num.length + 2) := by
    have h := decode_spec numeratorPorts (baseState rest [] [] [sign])
      num (KS.W01.frame den ++ tail) (by simp [baseState, numeratorPorts, rest, List.append_assoc]) rfl rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hd : RunSpec (decodeProgram denominatorPorts)
      (baseState (KS.W01.frame den ++ tail) num [] [sign])
      (baseState tail num den [sign]) (3 * den.length + 2) := by
    have h := decode_spec denominatorPorts (baseState (KS.W01.frame den ++ tail) num [] [sign])
      den tail rfl rfl rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hm : RunSpec (magnitudeProgram magnitudePorts 5) (baseState tail num den [sign])
      (baseState tail (KS.W01.MagnitudeProgram.result sign num) den [sign]) (2 * num.length + 4) := by
    have h := magnitude_spec magnitudePorts 5 (baseState tail num den [sign]) sign num rfl rfl rfl rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h := ((hs.compose hn).compose hd).compose hm
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  unfold baseTicks
  omega

theorem singleBits_encodeRat (q : ℚ) (tail : List Bool) :
    negativeBit q.num :: (KS.W01.frame (constructorBits q.num) ++
      KS.W01.frame (Computability.encodeNat q.den) ++ tail) = KS.W01.encodeRat q ++ tail := by
  have hi (z : ℤ) : KS.W01.encodeInt z = negativeBit z :: KS.W01.frame (constructorBits z) := by
    cases z <;> simp [KS.W01.encodeInt, KS.W01.encodeNat, KS.W01.intPayload,
      negativeBit, constructorBits]
  simp [KS.W01.encodeRat, hi, KS.W01.encodeNat, List.append_assoc]

theorem canonical_base_spec (q : ℚ) (tail : List Bool) :
    RunSpec baseProgram (baseState (KS.W01.encodeRat q ++ tail) [] [] [])
      (baseState tail (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        [decide (q.num < 0)])
      (baseTicks (constructorBits q.num) (Computability.encodeNat q.den)) := by
  have h := base_spec (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den) tail
  rw [singleBits_encodeRat, magnitude_constructor_eq] at h
  exact h

theorem canonical_ticks_le (q : ℚ) :
    baseTicks (constructorBits q.num) (Computability.encodeNat q.den) ≤
      8 * (KS.W01.ratLength q + 1) := by
  have hlen := congrArg List.length (singleBits_encodeRat q [])
  simp only [List.length_cons, List.length_append, KS.W01.length_frame,
    List.length_nil, Nat.add_zero] at hlen
  unfold baseTicks KS.W01.ratLength
  omega

theorem onPorts_spec {k : ℕ} (ports : Fin 6 ↪ Fin k)
    (before : Fin k → List Bool) (q : ℚ) (tail : List Bool)
    (hbefore : (fun i => before (ports i)) = baseState (KS.W01.encodeRat q ++ tail) [] [] []) :
    RunSpec (onPorts ports) before
      (replacePorts ports before
        (baseState tail (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
          [decide (q.num < 0)])) (8 * (KS.W01.ratLength q + 1)) := by
  apply (runSpec_liftPorts baseProgram ports before _ _ ?_).mono (canonical_ticks_le q)
  rw [hbefore]
  exact canonical_base_spec q tail

theorem canonical_spec (q : ℚ) (tail : List Bool) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ tail)) (canonicalState q tail)
      (8 * (KS.W01.ratLength q + 1)) := by
  have h := onPorts_spec normalizerPorts (inputState (KS.W01.encodeRat q ++ tail)) q tail
    (by funext i; fin_cases i <;> rfl)
  convert h using 1 <;> first | rfl | (funext i; fin_cases i <;> rfl)

end KS.W06.SingleRationalParser

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSignAction
attribute [-simp] _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W16.RationalSignAction
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem toggle_step_start (num den : List Bool) (sgn eps : Bool) (tail : List Bool) (coin : Bool) :
    toggleMachine.step ⟨some (0 : Fin 3), operandState num den sgn (eps :: tail)⟩ coin =
      ⟨some (if chooseSign num sgn eps then (2 : Fin 3) else (1 : Fin 3)), poppedState num den (eps :: tail)⟩ := by
  unfold toggleMachine
  rw [step_compile]
  cases num with
  | nil =>
    cases sgn <;> cases eps <;>
      apply congrArg₂ Config.mk
    all_goals first | (solve | rfl) |
      (funext j; fin_cases j <;> rfl)
  | cons b bs =>
    cases b <;> cases sgn <;> cases eps <;>
      apply congrArg₂ Config.mk
    all_goals first | (solve | rfl) |
      (funext j; fin_cases j <;> rfl)

theorem toggle_step_finish (num den tape : List Bool) (sgn : Bool) (coin : Bool) :
    toggleMachine.step ⟨some (if sgn then (2 : Fin 3) else (1 : Fin 3)), poppedState num den tape⟩ coin =
      ⟨none, operandState num den sgn tape⟩ := by
  unfold toggleMachine
  cases sgn <;> erw [step_compile]
  all_goals
    apply congrArg₂ Config.mk
    · rfl
    · funext j; fin_cases j <;> rfl

theorem toggle_spec (num den : List Bool) (sgn eps : Bool) (tail : List Bool) :
    RunSpec toggleProgram (operandState num den sgn (eps :: tail))
      (operandState num den (chooseSign num sgn eps) (eps :: tail)) 2 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine toggleMachine
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons b bs =>
    cases bs with
    | nil => simp at hbits
    | cons c cs =>
      have he : cs = [] := by apply List.length_eq_zero_iff.mp; simpa using hbits
      subst cs
      change toggleMachine.run ⟨some (0 : Fin 3), operandState num den sgn (eps :: tail)⟩ [b,c] = _
      rw [Machine.run, toggle_step_start, Machine.run, toggle_step_finish]
      rfl

theorem parse_spec (q : ℚ) (tape : List Bool) :
    RunSpec parseProgram (inputState (KS.W01.encodeRat q) tape)
      (operandState (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        (decide (q.num < 0)) tape) (8 * (KS.W01.ratLength q + 1)) := by
  have h := KS.W06.SingleRationalParser.canonical_spec q []
  simp only [List.append_nil] at h
  exact liftCore_spec KS.W06.SingleRationalParser.program _ _ tape _ h

theorem serialize_spec (q : ℚ) (tape : List Bool) :
    RunSpec serializeProgram
      (operandState (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        (decide (q.num < 0)) tape)
      (outputState (KS.W01.encodeRat q) tape)
      (16 * ((Computability.encodeNat q.num.natAbs).length +
        (Computability.encodeNat q.den).length + 1)) :=
  liftCore_spec KS.W01.SignedRationalSerializer.program _ _ tape _
    (KS.W01.SignedRationalSerializer.serializes_rational q)

def ticks (q : ℚ) : ℕ := 8 * (KS.W01.ratLength q + 1) + 2 +
  16 * ((Computability.encodeNat q.num.natAbs).length + (Computability.encodeNat q.den).length + 1)

theorem full_spec (q : ℚ) (eps : Bool) (tail : List Bool) :
    RunSpec program (inputState (KS.W01.encodeRat q) (eps :: tail))
      (outputState (KS.W01.encodeRat (signedRational eps q)) (eps :: tail)) (ticks q) := by
  have ht := toggle_spec (Computability.encodeNat q.num.natAbs)
    (Computability.encodeNat q.den) (decide (q.num < 0)) eps tail
  rw [chooseSign_rational] at ht
  have hs := serialize_spec (signedRational eps q) (eps :: tail)
  simp only [signedRational_num_abs, signedRational_den] at hs
  exact ((parse_spec q (eps :: tail)).compose ht).compose hs

theorem ticks_linear (q : ℚ) : ticks q ≤ 64 * (KS.W01.ratLength q + 1) := by
  have hp := KS.W01.rational_parts_size_le_length q
  have hn : (Computability.encodeNat q.num.natAbs).length ≤ KS.W01.ratLength q := by
    change KS.W01.natPayloadLength q.num.natAbs ≤ KS.W01.ratLength q
    rw [KS.W01.natPayloadLength_eq_size]
    exact hp.1
  have hd : (Computability.encodeNat q.den).length ≤ KS.W01.ratLength q := by
    change KS.W01.natPayloadLength q.den ≤ KS.W01.ratLength q
    rw [KS.W01.natPayloadLength_eq_size]
    exact hp.2
  unfold ticks
  omega

theorem linear_spec (q : ℚ) (eps : Bool) (tail : List Bool) :
    RunSpec program (inputState (KS.W01.encodeRat q) (eps :: tail))
      (outputState (KS.W01.encodeRat (signedRational eps q)) (eps :: tail))
      (64 * (KS.W01.ratLength q + 1)) :=
  (full_spec q eps tail).mono (ticks_linear q)

theorem negation_spec (q : ℚ) (tail : List Bool) :
    RunSpec program (inputState (KS.W01.encodeRat q) (false :: tail))
      (outputState (KS.W01.encodeRat (-q)) (false :: tail))
      (64 * (KS.W01.ratLength q + 1)) := linear_spec q false tail

end KS.W16.RationalSignAction

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem transfer_spec (source target : Fin 19) (hst : source ≠ target)
    (hs : source ≠ 18) (ht : target ≠ 18)
    (before : Fin 19 → List Bool) (htmp : before 18 = []) :
    RunSpec (transferProgram source target) before (transferAfter source target before)
      (2 * (before source).length + 2) := by
  exact KS.W12.StackTransfer.spec source target 18 hst hs ht before htmp

end KS.W12.FixedDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSubtractProgram
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalSubtract
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem parse_spec (q r : ℚ) :
    RunSpec parseProgram (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r)) (parsed q r)
      (8 * (KS.W01.ratLength q + 1)) := by
  have h := first_spec (by decide : 13 ≤ 19) KS.W06.SingleRationalParser.program _ _ (fun _ => []) _
    (KS.W06.SingleRationalParser.canonical_spec q (KS.W01.encodeRat r))
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem saveR_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 0 16) (parsed q r) (saved q r)
      (2 * KS.W01.ratLength r + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 0 16 (by decide) (by decide) (by decide) (parsed q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,parsed,saved,registers])

theorem serialize_spec (q r : ℚ) :
    RunSpec serializeProgram (saved q r) (emitted q r) (serializeTicks q) := by
  have h := first_spec (by decide : 13 ≤ 19) KS.W01.SignedRationalSerializer.program _ _
    (fun j => if j=16 then KS.W01.encodeRat r else []) _
    (KS.W01.SignedRationalSerializer.serializes_rational q)
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem saveQ_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 10 17) (emitted q r) (paired q r)
      (2 * KS.W01.ratLength q + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 10 17 (by decide) (by decide) (by decide) (emitted q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,emitted,paired,registers])

theorem takeR_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 16 0) (paired q r) (prepared q r)
      (2 * KS.W01.ratLength r + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 16 0 (by decide) (by decide) (by decide) (paired q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,paired,prepared,registers])

theorem mark_spec (q r : ℚ) : RunSpec markProgram (prepared q r) (marked q r) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine (compile (0 : Fin 1) (0 : Fin 19) 13 markDispatch)
  intro bits hb
  cases bits with
  | nil => simp at hb
  | cons coin tail =>
    have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hb)
    subst tail
    change (compile (0 : Fin 1) (0 : Fin 19) 13 markDispatch).step
      ⟨some (0 : Fin 1), prepared q r⟩ coin = _
    erw [step_compile]
    apply congrArg₂ Config.mk
    · rfl
    · funext j
      fin_cases j <;> rfl

theorem negate_spec (q r : ℚ) :
    RunSpec negateProgram (marked q r) (negated q r) (64 * (KS.W01.ratLength r + 1)) := by
  have h := first_spec (by decide : 14 ≤ 19) KS.W16.RationalSignAction.program _ _
    (fun j => if j=17 then KS.W01.encodeRat q else []) _
    (KS.W16.RationalSignAction.negation_spec r [])
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

theorem placeRight_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 10 0) (cleared q r) (withRight q r)
      (2 * KS.W01.ratLength (-r) + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 10 0 (by decide) (by decide) (by decide) (cleared q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,cleared,withRight,registers])

theorem prependLeft_spec (q r : ℚ) :
    RunSpec (KS.W12.FixedDot.transferProgram 17 0) (withRight q r)
      (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r))) (2 * KS.W01.ratLength q + 2) := by
  have h := KS.W12.FixedDot.transfer_spec 17 0 (by decide) (by decide) (by decide) (withRight q r) rfl
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> simp [KS.W12.FixedDot.transferAfter,withRight,inputState,registers])

theorem addition_spec (q r : ℚ) :
    RunSpec addProgram (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r)))
      (outputState (KS.W01.encodeRat (q-r)))
      (KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r)).length) := by
  have h := first_spec (by decide : 16 ≤ 19) KS.W13.RationalAdd.program _ _ (fun _ => []) _
    (KS.W13.RationalAdd.polynomial_spec q (-r))
  rw [← sub_eq_add_neg] at h
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

def prepareTicks (q r : ℚ) := (((8*(KS.W01.ratLength q+1)+(2*KS.W01.ratLength r+2))+
  serializeTicks q)+(2*KS.W01.ratLength q+2))+(2*KS.W01.ratLength r+2)
def changeSignTicks (q r : ℚ) := (((1+64*(KS.W01.ratLength r+1))+2)+
  (2*KS.W01.ratLength (-r)+2))+(2*KS.W01.ratLength q+2)
def totalTicks (q r : ℚ) := prepareTicks q r + changeSignTicks q r +
  KS.W29.polynomialFuel 1000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r)).length

theorem full_spec (q r : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (outputState (KS.W01.encodeRat (q-r))) (totalTicks q r) := by
  have hp := (((parse_spec q r).compose (saveR_spec q r)).compose (serialize_spec q r)).compose (saveQ_spec q r)
  have hp' := hp.compose (takeR_spec q r)
  have hn := (((mark_spec q r).compose (negate_spec q r)).compose (clearMark_spec q r)).compose (placeRight_spec q r)
  have hn' := hn.compose (prependLeft_spec q r)
  exact (hp'.compose hn').compose (addition_spec q r)

end KS.W13.RationalSubtract

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSubtractCorrect
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.RationalSubtract
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem serializeTicks_le (q : ℚ) : serializeTicks q ≤ 32 * KS.W01.ratLength q + 16 := by
  obtain ⟨hn,hd⟩ := KS.W01.rational_parts_size_le_length q
  unfold serializeTicks
  simp only [KS.W19.encodeNat_length_eq_size]
  omega

theorem preparation_linear (q r : ℚ) : prepareTicks q r + changeSignTicks q r ≤
    200 * ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + 1) := by
  have hs := serializeTicks_le q
  have hn := KS.W01.ratLength_neg_le r
  simp only [List.length_append]
  change _ ≤ 200 * (KS.W01.ratLength q + KS.W01.ratLength r + 1)
  unfold prepareTicks changeSignTicks
  omega

theorem totalTicks_le_polynomial (q r : ℚ) : totalTicks q r ≤
    KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  let L := (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length
  let N := (KS.W01.encodeRat q ++ KS.W01.encodeRat (-r)).length
  have hn := KS.W01.ratLength_neg_le r
  have hn' : N + 1 ≤ 8 * (L+1) := by
    dsimp [N,L]
    simp only [List.length_append]
    change KS.W01.ratLength q + KS.W01.ratLength (-r) + 1 ≤
      8 * (KS.W01.ratLength q + KS.W01.ratLength r + 1)
    omega
  have ha : 1000*(N+1)^3 ≤ 512000*(L+1)^3 := by
    calc
      _ ≤ 1000*(8*(L+1))^3 := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hn' 3)
      _ = _ := by ring
  have hp := preparation_linear q r
  have hlin : L+1 ≤ (L+1)^3 := Nat.le_self_pow (by decide) _
  change prepareTicks q r + changeSignTicks q r ≤ 200*(L+1) at hp
  unfold totalTicks
  change prepareTicks q r + changeSignTicks q r + 1000*(N+1)^3 ≤ 600000*(L+1)^3
  omega

theorem polynomial_spec (q r : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (outputState (KS.W01.encodeRat (q-r)))
      (KS.W29.polynomialFuel 600000 3 (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length) :=
  (full_spec q r).mono (totalTicks_le_polynomial q r)

end KS.W13.RationalSubtract

end

end OAI
end


