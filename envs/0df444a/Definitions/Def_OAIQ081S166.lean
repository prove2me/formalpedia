-- Prove2me | Definitions.Def_OAIQ081S166
-- name    : OAIQ081S166
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:08:15.460924+00:00
-- url     : https://prove2.me/theorems/fef49537-c419-4f7d-8c61-20c0444f772c
-- title:
--   Definitions bundle OAIQ081S166 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 16 definitions, 1 inductive type or structure and 9 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.completeCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.completeProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.buildCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.buildProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cacheBuildLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalBuild`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.nativeCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.setup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.Args`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Produced`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CostAssemblyRingBounds`, `SubexponentialSAT_SqrtLog_CostAssemblyRingSetup`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramFinish`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalar`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun`, `SubexponentialSAT_SqrtLog_IdempotentProgramComplete`, `SubexponentialSAT_SqrtLog_IdempotentProgramMachine`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgram`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode`, `SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S153`, `OAIQ081S154`, `OAIQ081S155` and `OAIQ081S157` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S173`, `OAIQ081S174`, `OAIQ081S175` and `OAIQ081S176`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cacheBuildLoop_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay.prepare_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cacheBuildLoop_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S154
import Definitions.Def_OAIQ081S155
import Definitions.Def_OAIQ081S157

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def setup : Cmd 9 77 := .seq numeric check

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitBudget -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def program := compiled setup (Bank.port 0) (Bank.port 42)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPublic -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem admissible (m : Model) : AdmissibleCode code m := by
  simp [code,AdmissibleCode,Admissible,next,output,lengthBound]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

attribute [local instance] OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.instFactPrimeOfNatNat_solutions_1
theorem arithmeticCommand_eval (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t)
    (v:Values 3 t) (d:Data) (h:Encoded 3 t M v d)
    (h29:d.stacks 29=List.replicate t true) (h40:d.stacks 40=[]) :
    ∃ n e, Eval arithmeticCommand n d e ∧ Output t M (finalValues t M v) e ∧
      Frame d e ∧
      n ≤ (3*t+10)*stepBudget 3 t+9*t+4*baseWidth 3 t+13 := by
  obtain ⟨n1,a,ha,hva,hfa,hn1⟩:=sequence_eval 3 t M constants v d h
  have ha29:a.stacks 29=List.replicate t true := by
    rw [hfa 29 (by intro i; fin_cases i <;> decide)]; exact h29
  have ha40:a.stacks 40=[] := by rw [hfa 40 port_ne40]; exact h40
  let b:=ArithmeticCalls.afterCopy 29 40 a
  have cp:=ArithmeticCalls.copyAt_eval (29:Fin 41) 40 38 a (by decide) (by decide)
    (by decide) ha40 hva.1.2
  have hbs:b.stacks=Function.update a.stacks 40 (List.replicate t true) := by
    simp [b,ArithmeticCalls.afterCopy,ha29]
  have hvb:Encoded 3 t M (run 3 t M constants v) b := by
    constructor
    · constructor
      · intro i
        have hi:low i≠40 := by intro hh; have hv:=congrArg Fin.val hh; dsimp [low] at hv; omega
        simpa [hbs,hi] using hva.1.1 i
      · simpa [hbs] using hva.1.2
    · intro i; simpa [hbs,port_ne40] using hva.2 i
  obtain ⟨n2,c,hc,hvc,hc40,hfc,hn2⟩:=halfLoop_eval 3 t M _ b hvb
  have hblen:(b.stacks 40).length=t := by simp [hbs]
  rw [hblen] at hvc hn2
  obtain ⟨n3,f,hf,hvf,hff,hn3⟩:=sequence_eval 3 t M finalCoefficients _ c hvc
  have f24:(f.stacks 24).length=baseWidth 3 t := by
    have hh:=hvf.2 6
    exact (congrArg List.length hh).trans ((run 3 t M finalCoefficients (iterateForward 3 t M (run 3 t M constants v) t) 6).property)
  have f25:(f.stacks 25).length=baseWidth 3 t := by
    have hh:=hvf.2 7
    exact (congrArg List.length hh).trans ((run 3 t M finalCoefficients (iterateForward 3 t M (run 3 t M constants v) t) 7).property)
  let g:=IdempotentProgram.cleared f 24
  let e:=IdempotentProgram.cleared g 25
  have cl1:=IdempotentProgram.registerClear_eval f 24
  have cl2:=IdempotentProgram.registerClear_eval g 25
  refine ⟨_,e,ha.seq (cp.seq (hc.seq (hf.seq (cl1.seq cl2)))),?_,?_,?_⟩
  · refine ⟨?_,by simp [e,g,IdempotentProgram.cleared],by simp [e,IdempotentProgram.cleared],?_⟩
    · constructor
      · intro i
        have h24:low i≠24 := by intro hh; have hv:=congrArg Fin.val hh; dsimp [low] at hv; omega
        have h25:low i≠25 := by intro hh; have hv:=congrArg Fin.val hh; dsimp [low] at hv; omega
        simpa [e,g,IdempotentProgram.cleared,h24,h25] using hvf.1.1 i
      · simpa [e,g,IdempotentProgram.cleared] using hvf.1.2
    · intro i hi6 hi7
      have hi24:port i≠24 := by intro hh; exact hi6 (port_injective hh)
      have hi25:port i≠25 := by intro hh; exact hi7 (port_injective hh)
      simpa [e,g,IdempotentProgram.cleared,hi24,hi25,finalValues] using hvf.2 i
  · intro j hj
    have hj24:j≠24 := (hj 6).symm
    have hj25:j≠25 := (hj 7).symm
    simp only [e,g,IdempotentProgram.cleared,Function.update_of_ne hj25,Function.update_of_ne hj24]
    rw [hff j hj]
    by_cases hj40:j=40
    · subst j; rw [hc40,h40]
    · rw [hfc j hj40 hj,hbs,Function.update_of_ne hj40,hfa j hj]
  · simp only [constants,List.length_cons,List.length_nil] at hn1
    simp only [finalCoefficients,List.length_cons,List.length_nil] at hn3
    simp only [g,IdempotentProgram.cleared,Function.update_of_ne (by decide : (25:Fin 41)≠24),
      f24,f25,ha29,List.length_replicate]
    nlinarith

theorem command_eval (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t)
    (shape:List Bool) (hs:shape.length=baseWidth 3 t) (d:Data) (W:ℕ)
    (h:Rest d M.bits) (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W)
    (h29:d.stacks 29=List.replicate t true) (h40:d.stacks 40=[]) :
    ∃ n e, Eval command n d e ∧
      Output t M (finalValues t M (baseValues t M shape hs)) e ∧ Frame d e ∧
      n ≤ 400*(baseWidth 3 t+W+1)+(3*t+10)*stepBudget 3 t+9*t+4*baseWidth 3 t+13 := by
  obtain ⟨n1,a,ha,hva,hfa,hn1⟩:=baseCommand_eval t M shape hs d W h h12 hW hslots
  have ha29:a.stacks 29=List.replicate t true := by
    rw [hfa 29 (by intro i; fin_cases i <;> decide)]; exact h29
  have ha40:a.stacks 40=[] := by rw [hfa 40 port_ne40]; exact h40
  obtain ⟨n2,e,he,hve,hfe,hn2⟩:=arithmeticCommand_eval t M _ a hva ha29 ha40
  exact ⟨n1+n2,e,ha.seq he,hve,fun j hj=>(hfe j hj).trans (hfa j hj),by omega⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar preparation contract for the 41-stack H-adic setup.
All generated constants are canonical; the selector and array builder receive
exact functional words. The only unbounded iteration uses cached unary t. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing BinaryArithmetic

theorem command_prepares (t:ℕ) (ht:0 < t) (M:SubexpPreparedQuartic.Modulus 3 t)
    (shape:List Bool) (hs:shape.length=baseWidth 3 t) (d:Data) (W:ℕ)
    (h:Rest d M.bits) (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W)
    (h29:d.stacks 29=List.replicate t true) (h40:d.stacks 40=[]) :
    ∃ n e cache u, Eval command n d e ∧ Prepared t M cache u e ∧ Frame d e ∧
      n ≤ 400*(baseWidth 3 t+W+1)+(3*t+10)*stepBudget 3 t+9*t+4*baseWidth 3 t+13 := by
  let v:=baseValues t M shape hs
  have hv:=baseValues_correct t ht M shape hs
  let cache:=generatedCache t M v hv.1 hv.2.1 hv.2.2.1
  let u:=finalValues t M v 8
  obtain ⟨n,e,he,ho,hf,hn⟩:=command_eval t M shape hs d W h h12 hW hslots h29 h40
  have hc:Canonical 3 t v:=hv.2.2.2
  have hcoeff:=final_coefficients t M v
  refine ⟨n,e,cache,u,he,?_,hf,hn⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,ho.1,ho.2.1,ho.2.2.1⟩
  · intro i
    rw [ho.2.2.2 (tableRegister i) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact congrArg Subtype.val (generated_table t M v hv.1 hv.2.1 hv.2.2.1 hc i).symm
  · exact ho.2.2.2 0 (by decide) (by decide)
  · exact ho.2.2.2 1 (by decide) (by decide)
  · exact ho.2.2.2 8 (by decide) (by decide)
  · exact ho.2.2.2 9 (by decide) (by decide)
  · rw [show e.stacks 30=(finalValues t M v 10).val from ho.2.2.2 10 (by decide) (by decide)]
    exact congrArg Subtype.val hcoeff.1
  · rw [show e.stacks 31=(finalValues t M v 11).val from ho.2.2.2 11 (by decide) (by decide)]
    simpa [cache,u,generatedCache,hcoeff.1] using congrArg Subtype.val hcoeff.2
  · exact (final_half t M v hv.1 hv.2.1 hv.2.2.1).1
  · exact final_canonical t M v hc 9
  · exact final_canonical t M v hc 0
  · exact final_canonical t M v hc 1

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing

theorem finishCommand_eval (t : ℕ) (ht : 0 < t) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) (W : ℕ)
    (h37 : d.stacks 37=List.replicate (3*t) true)
    (h26 : d.stacks 26=[]) (h22 : d.stacks 22=[])
    (h32 : d.stacks 32=[]) (h33 : d.stacks 33=[])
    (h34 : d.stacks 34=[]) (h35 : d.stacks 35=[]) (h36 : d.stacks 36=[])
    (hW : ∀ p ∈ preparationDiscard, (d.stacks p).length ≤ W) :
    ∃ cost e, cost ≤ finishBudget t (SubexpLiftRing.baseWidth 3 t) W ∧
      Eval finishCommand cost d e ∧
      e.stacks = finishedStacks d.stacks t
        (IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache))) := by
  let table := IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache))
  obtain ⟨nt,rt,hnt,het⟩ := prepared_nativeTable_eval t M cache u d hp h37 h26 h22
  let a : Data := ⟨rt,Function.update d.stacks 22 table⟩
  have hzero : (d.stacks 17).length = SubexpLiftRing.baseWidth 3 t := by
    rw [prepared_zero t M cache u d hp]
    exact cache.zero.property
  have hp1 : d.stacks (1 : Fin 41) = [] := by
    change d.stacks (Fin.castAdd 33 (1 : Fin 8)) = []
    simpa only [Scalar.low, ite_eq_right (show (1 : Fin 8) ≠ 5 by decide)] using hp.rest.1 (1 : Fin 8)
  have hp2 : d.stacks (2 : Fin 41) = [] := by
    change d.stacks (Fin.castAdd 33 (2 : Fin 8)) = []
    simpa only [Scalar.low, ite_eq_right (show (2 : Fin 8) ≠ 5 by decide)] using hp.rest.1 (2 : Fin 8)
  obtain ⟨na,ra,hna,hea⟩ := arrayStage_eval a t (SubexpLiftRing.baseWidth 3 t) ht
    (by simpa [a] using h37) (by simpa [a] using hp1)
    (by simpa [a] using hp2) (by simpa [a] using h32)
    (by simpa [a] using h33) (by simpa [a] using h34)
    (by simpa [a] using h35) (by simpa [a] using h36)
    (by simpa [a] using hzero) (by simp [a,hp.half,u.property])
    (by simp [a,hp.minusOne,cache.minusOne.property])
    (by simp only [a,Function.update_of_ne (by decide : (30:Fin 41)≠22),hp.twice]
        exact (SubexpPreparedQuartic.wordAdd 3 t M u u).1.property)
    (by simp only [a,Function.update_of_ne (by decide : (31:Fin 41)≠22),hp.minusThree]
        exact (SubexpPreparedQuartic.wordMul 3 t M
          (SubexpPreparedQuartic.wordAdd 3 t M (SubexpPreparedQuartic.wordAdd 3 t M u u).1 u).1
          cache.minusOne).1.property)
  let b : Data := ⟨ra,arrayStacks a.stacks t⟩
  have hb : ∀ p ∈ preparationDiscard, b.stacks p=d.stacks p := by
    intro p hmem
    have hp22 : p ≠ (22 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
      all_goals first | omega | (revert hmem; decide)
    have hp32 : p ≠ (32 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
      all_goals first | omega | (revert hmem; decide)
    have hp33 : p ≠ (33 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
      all_goals first | omega | (revert hmem; decide)
    have hp34 : p ≠ (34 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
      all_goals first | omega | (revert hmem; decide)
    have hp35 : p ≠ (35 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
      all_goals first | omega | (revert hmem; decide)
    have hp36 : p ≠ (36 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
      all_goals first | omega | (revert hmem; decide)
    simp [b, a, arrayStacks, hp22, hp32, hp33, hp34, hp35, hp36]
  obtain ⟨nc,e,hnc,hec,hs⟩ := preparationCleanup_eval b W (by
    intro p hmem
    rw [hb p hmem]
    exact hW p hmem)
  refine ⟨nt+(na+nc),e,?_,het.seq (hea.seq hec),?_⟩
  · dsimp [finishBudget]; omega
  · funext i
    rw [hs]
    rfl

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed four-array Newton machine. Its native services perform full dynamic
vector arithmetic, operand copying, and target replacement. -/

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem arithmeticService_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {dim : ℕ} (table : Fin dim → Fin dim → Fin dim → Word (baseWidth p t))
    (zero one minusOne : RingProgram.Code (Word (baseWidth p t)) dim)
    (degree width : List Bool) (hd : degree.length = dim) (hw : width.length = baseWidth p t) :
    NativeInstructionSpec
      (binaryProgram (RingProgram.program (RingProgram.scalarProgram p t M cache) table zero one) minusOne)
      newtonPorts arithmeticService
      (RegistersEncoded M.bits width cache.zero.val (RingTriple.tableEncoding table) degree minusOne)
      (arithmeticBudget (baseWidth p t) dim) := by
  intro instruction regs state encoded hscratch
  have port_low (i : Fin 4) : 32 ≤ (arrayRegister i).val := by dsimp [arrayRegister]; omega
  have port_tmp (i : Fin 4) : arrayRegister i ≠ 38 := by
    intro h; have hv := congrArg Fin.val h; have := i.isLt
    dsimp [arrayRegister] at hv; omega
  cases instruction with
  | add dst x y =>
      obtain ⟨n,next,hn,he,henc,hcounter,hs⟩ := registerArrayStep
        RingScan.serviceAdd M.bits width cache.zero.val (RingTriple.tableEncoding table)
        degree hd minusOne regs state encoded dst (arrayRegister x) (arrayRegister y)
        (regs x) (regs y) (RingProgram.addRun (RingProgram.scalarProgram p t M cache) (regs x) (regs y)).1
        (port_low x) (port_low y) (port_tmp x) (port_tmp y) (encoded.values x) (encoded.values y)
        (RingScan.serviceAddBudget (baseWidth p t) dim) (le_max_left _ _)
        (fun flags => RingScan.serviceAdd_eval p t M cache (regs x) (regs y) flags degree width
          (RingTriple.tableEncoding table) hd hw)
      exact ⟨n,next,hn,he,henc,hcounter,hs.trans hscratch⟩
  | mul dst x y =>
      obtain ⟨n,next,hn,he,henc,hcounter,hs⟩ := registerArrayStep
        RingScan.serviceMul M.bits width cache.zero.val (RingTriple.tableEncoding table)
        degree hd minusOne regs state encoded dst (arrayRegister x) (arrayRegister y)
        (regs x) (regs y) (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table (regs x) (regs y)).1
        (port_low x) (port_low y) (port_tmp x) (port_tmp y) (encoded.values x) (encoded.values y)
        (RingScan.serviceMulBudget (baseWidth p t) dim) (le_max_right _ _)
        (fun flags => RingScan.serviceMul_eval p t M cache hz table (regs x) (regs y) flags degree width hd hw)
      exact ⟨n,next,hn,he,henc,hcounter,hs.trans hscratch⟩
  | neg dst x =>
      obtain ⟨n,next,hn,he,henc,hcounter,hs⟩ := registerArrayStep
        RingScan.serviceMul M.bits width cache.zero.val (RingTriple.tableEncoding table)
        degree hd minusOne regs state encoded dst 36 (arrayRegister x)
        minusOne (regs x) (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table minusOne (regs x)).1
        (by decide) (port_low x) (by decide) (port_tmp x) encoded.negativeUnit (encoded.values x)
        (RingScan.serviceMulBudget (baseWidth p t) dim) (le_max_right _ _)
        (fun flags => RingScan.serviceMul_eval p t M cache hz table minusOne (regs x) flags degree width hd hw)
      exact ⟨n,next,hn,he,henc,hcounter,hs.trans hscratch⟩

/-- No native arithmetic hypothesis remains in this theorem. The input carries
its cached table, constants, dimension/width data, and starting arrays. -/
theorem newtonMachine_exact (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {dim : ℕ} (table : Fin dim → Fin dim → Fin dim → Word (baseWidth p t))
    (zero one minusOne : RingProgram.Code (Word (baseWidth p t)) dim)
    (degree width : List Bool) (hd : degree.length = dim) (hw : width.length = baseWidth p t)
    (regs : Registers (RingProgram.Code (Word (baseWidth p t)) dim)) (state : RegisterData)
    (encoded : RegistersEncoded M.bits width cache.zero.val (RingTriple.tableEncoding table) degree minusOne regs state)
    (hs : state.stacks 40 = []) :
    ∃ n next, Eval newtonMachine n state next ∧
      RegistersEncoded M.bits width cache.zero.val (RingTriple.tableEncoding table) degree minusOne
        (codeRun
          (binaryProgram (RingProgram.program (RingProgram.scalarProgram p t M cache) table zero one) minusOne)
          (liftCode (CounterPrograms.value (state.stacks 39))) regs).1 next ∧
      n ≤ 7*CounterPrograms.value (state.stacks 39)*arithmeticBudget (baseWidth p t) dim +
        (CounterPrograms.value (state.stacks 39)+1)*(16*(state.stacks 39).length+16) := by
  exact nativeNewtonLoop_exact _ newtonPorts arithmeticService _ _
    (arithmeticService_spec p t M cache hz table zero one minusOne degree width hd hw)
    (fun _ _ _ hf hh => RegistersEncoded.frame hf hh) regs state encoded hs

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite bit program constructs the ternary H-adic lift from its
binary precision alone. Preparation, array arithmetic, iteration and output
serialization are all covered by actual bit-instruction traces. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing

abbrev completeCommand : Cmd 8 41 :=
  .seq IdempotentPreparationProgram.preparation (.call newtonProgram)

def completeProgram := compiled completeCommand 31 32

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls LeafParametersProgram SubexpQuarticRing SubexpLiftRing

structure Produced (m : Circuit.Model) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33)) (a : Data) : Prop where
  caches : RingCaches (m.val 33) (m.val 34) (IrreducibleSearch.data hd) M cache u a
  native : NativeBytes (m.val 33) (m.val 34) (IrreducibleSearch.data hd) M cache a
  ambient : a.stacks 191=List.replicate (m.val 0) true
  exponent : a.stacks 209=List.replicate ((Circuit.result Serialization.code m).val 44) true
  jetOrder : a.stacks 243=List.replicate (m.val 42) true
  flatNodes : a.stacks 256=((nodeWords (m.val 33) (m.val 34) (m.val 21)).map RingProgram.flat).flatten
  framedNodes : a.stacks 300=Encoding.encodeList id
    ((nodeWords (m.val 33) (m.val 34) (m.val 21)).map RingProgram.flat)
  idempotent : ∃ (M' : SubexpPreparedQuartic.Modulus 3 (m.val 33))
      (cache' : RingProgram.ScalarCache 3 (m.val 33))
      (u' : RingProgram.ScalarCode 3 (m.val 33)),
    a.stacks 281=RingProgram.flat (IdempotentProgram.binaryLiftWords (m.val 33) M' cache' u') ∧
      (2 : ZMod (3^(m.val 33)))*wordValue 3 (m.val 33) u'=1
  privateClean : ∀ i∈privatePorts,a.stacks i=[]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyRingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed polynomial bound for the actual ring producer's numerical cost.
The size cap includes the unary numeric bank bound V, so large stored values
are not silently replaced by their binary lengths. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

open LeafRingSetupProgram LeafParametersProgram CostAssembly.Polynomial

theorem producerBudget_le (m : Circuit.Model) (initialWidth V bankWidth S : ℕ)
    (hi : initialWidth ≤ S) (hv : V ≤ S) (hw : bankWidth ≤ S)
    (hl : ∀ i, m.len i ≤ S)
    (ht : m.val 33 ≤ S) (hd : m.val 34 ≤ S) (hq : m.val 21 ≤ S)
    (hfield : 3^(m.val 34) ≤ 16*(m.val 21+1)^2) :
    producerBudget m initialWidth V bankWidth ≤ polynomialEnvelope S := by
  have hser := serialization_budget_le m S hl
  have hsearch := IrreducibleSearchBootstrap.totalCost_sizeDegreeBound hfield
  have h0 : numberBudget m initialWidth V bankWidth ≤ numberEnvelope S := by
    unfold numberBudget numberEnvelope
    gcongr
  have h1 : coreBudget (m.val 33) (m.val 34) bankWidth ≤ coreEnvelope S := by
    unfold coreBudget coreEnvelope scalarBudget
    simp only [RingProgram.ternary_baseWidth]
    change IrreducibleSearchBootstrap.totalCost (m.val 34) ≤
      searchCoefficient*(m.val 21+1)^10 at hsearch
    calc
      _ ≤ 2001*(m.val 33+bankWidth+2)^2+500000*(3*m.val 33+bankWidth+1)^3+1+
          (7*(2*m.val 33)+8)+32+
          (3*(searchCoefficient*(m.val 21+1)^10)+7*(2*m.val 33)+
            m.val 34*(28*m.val 33+14)+15)+
          (7*(2*m.val 33)+8)+208000*(m.val 34+1)^5*(m.val 33+1)^2 := by gcongr
      _ ≤ _ := by gcongr
  have h2 : constantsBudget
      (initialWidth+numberBudget m initialWidth V bankWidth+coreBudget (m.val 33) (m.val 34) bankWidth+1)
      (SubexpLiftRing.baseWidth 3 (m.val 33)) (m.val 34) ≤
      constantsBudget (S+numberEnvelope S+coreEnvelope S+1) (2*S) S := by
    unfold constantsBudget LeafProgram.Constants.budget
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  unfold producerBudget polynomialEnvelope
  dsimp only
  have hn : ∀ W W', W ≤ W' → nodesBudget W (m.val 33) (m.val 34) (m.val 21) ≤ nodesBudget W' S S S := by
    intro W W' hW
    unfold nodesBudget RingNodeProgram.budget RingNodeProgram.stepBudget
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  have he : ∀ W W', W ≤ W' → idempotentBudget (m.val 33) W ≤ idempotentEnvelope S W' := by
    intro W W' hW
    unfold idempotentBudget idempotentEnvelope
    have hp := IdempotentProgram.completeBudget_polynomial (m.val 33) W
    calc
      _ ≤ idempotentStartPorts.length*(2*W+3)+(7*W+8)+32+
          IdempotentProgram.polynomialBudget (m.val 33) W+(7*(6*(m.val 33)^2)+8) := by omega
      _ ≤ _ := by unfold IdempotentProgram.polynomialBudget; gcongr
  let W := initialWidth+numberBudget m initialWidth V bankWidth+
    coreBudget (m.val 33) (m.val 34) bankWidth+1+
    constantsBudget (initialWidth+numberBudget m initialWidth V bankWidth+
      coreBudget (m.val 33) (m.val 34) bankWidth+1)
      (SubexpLiftRing.baseWidth 3 (m.val 33)) (m.val 34)+1
  let W' := S+numberEnvelope S+coreEnvelope S+1+
    constantsBudget (S+numberEnvelope S+coreEnvelope S+1) (2*S) S+1
  have hW : W ≤ W' := by dsimp [W,W']; omega
  have h3 := hn W W' hW
  have h4 := he (W+nodesBudget W (m.val 33) (m.val 34) (m.val 21)+1)
    (W'+nodesBudget W' S S S+1) (by omega)
  dsimp [W,W'] at h3 h4
  gcongr

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyRingSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup
open LeafRingSetupProgram LeafParametersProgram CostAssembly.Polynomial

theorem producerBudget_ordinary : ∃ C d : ℕ,
    ∀ (m : Circuit.Model) (initialWidth V bankWidth S : ℕ),
      initialWidth ≤ S → V ≤ S → bankWidth ≤ S → (∀ i, m.len i ≤ S) →
      m.val 33 ≤ S → m.val 34 ≤ S → m.val 21 ≤ S →
      3^(m.val 34) ≤ 16*(m.val 21+1)^2 →
      producerBudget m initialWidth V bankWidth ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := polynomialEnvelope_ordinary
  exact ⟨C,d,fun m i V W S hi hv hw hl ht hd hq hf =>
    (producerBudget_le m i V W S hi hv hw hl ht hd hq hf).trans (h S)⟩

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single fixed native interpolation-cache producer. The only data
inputs are the actual node stream and already prepared ring constants.
No inverse, negative, or pairwise table is supplied to this program. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing
local infixr:55 " ;; " => seq_p0

def command : Code := inverseTable ;; negativeTable ;; differenceTable ;;
  countCopy 256 262 ;; countCopy 104 263

def program := compiled command 256 261

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev cacheBuildLoop : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram program id cacheBuildPorts)

abbrev buildCommand : Cmd 8 19 := .seq initialBuild cacheBuildLoop
def buildProgram := compiled buildCommand 17 15

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/

/-! Value and shape contracts for the generic adapter and binomial row. -/

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev finalBuild : Cmd 8 20 := .call (ProgramLinking.liftProgram buildProgram id buildFinalPorts)

abbrev finalCommand : Cmd 8 20 := .seq finalBuild finalFlatten
def finalProgram := compiled finalCommand 17 0

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete extension-ring denominator program. It first lifts the actual
scalar-half word, then runs the paid native multiplication loop. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing
open IntegerRingLiftProgram

def command : Code :=
  .seq modelSignedCommand (powerCommand HornerProgram.Services.multiply)

def program := compiled command 239 252

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The per-query denominator is computed in a disjoint 256-stack bank. The
only persistent output is stack 728; the runtime exponent is read from 740. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev nativeCall : Cmd 16 768 := .call
  (ProgramLinking.liftProgram LayoutDenominatorProgram.program id port)

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-only closure of the physical parameter/cache/export costs, including
the exact binary word lengths used by the subsequent offset producer. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BinaryArithmetic Bank Circuit Asymptotic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Args := Input × (Fin 8 → ℕ)

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end


