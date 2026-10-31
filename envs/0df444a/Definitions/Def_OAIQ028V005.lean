-- Prove2me | Definitions.Def_OAIQ028V005
-- name    : OAIQ028V005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:09:15.930299+00:00
-- url     : https://prove2.me/theorems/35ede4d1-4968-4442-9ff1-61b755aa9d08
-- title:
--   Definitions bundle OAIQ028V005 of the split of OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VertexCover.explicit_cover_gap` and `OAI.VertexCover.every_fixed_factor_below_two`, carved from OpenAI's openai/math development (OpenAI, *The Factor-Two Hardness Threshold for Vertex Cover (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 61 declarations of OpenAI's Lean: 31 definitions and 30 theorems. The definitions and types are `OAI.VertexCover.Machine.CloudMachine.pairCode`, `OAI.VertexCover.Machine.ExpandMachine.stepData`, `OAI.VertexCover.Machine.ExpandMachine.stepRow`, `OAI.VertexCover.Machine.FinalCNFMachine.eraseLiteral`, `OAI.VertexCover.Machine.FormulaParser.Acc`, `OAI.VertexCover.Machine.FormulaParser.State`, `OAI.VertexCover.Machine.FormulaParser.accCode`, `OAI.VertexCover.Machine.FormulaParser.budget`, `OAI.VertexCover.Machine.FormulaParser.clauseCode`, `OAI.VertexCover.Machine.FormulaParser.clauseDefault`, `OAI.VertexCover.Machine.FormulaParser.compactDataClause`, `OAI.VertexCover.Machine.FormulaParser.compactDataLiteral`, `OAI.VertexCover.Machine.FormulaParser.dataCode`, `OAI.VertexCover.Machine.FormulaParser.denseData`, `OAI.VertexCover.Machine.FormulaParser.formulaCode`, `OAI.VertexCover.Machine.FormulaParser.literalCode`, `OAI.VertexCover.Machine.FormulaParser.literalData`, `OAI.VertexCover.Machine.FormulaParser.literalDefault`, `OAI.VertexCover.Machine.FormulaParser.literalNamePoly`, `OAI.VertexCover.Machine.FormulaParser.literalSignPoly`, `OAI.VertexCover.Machine.FormulaParser.observe`, `OAI.VertexCover.Machine.FormulaParser.oneStep`, `OAI.VertexCover.Machine.FormulaParser.stateCode`, `OAI.VertexCover.Machine.FormulaParser.step`, `OAI.VertexCover.Machine.FormulaParser.targetLiteralData`, `OAI.VertexCover.Machine.FormulaParser.tripleCode`, `OAI.VertexCover.Machine.FormulaParser.unaryClauseCode`, `OAI.VertexCover.Machine.FormulaParser.unaryLiteralCode`, `OAI.VertexCover.Machine.InitialTable.signsCode`, `OAI.VertexCover.Machine.Logarithm.enc`, `OAI.VertexCover.Machine.Poly.binaryFrame`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `VertexCover_Machines_BinaryOutput`, `VertexCover_Machines_Cloud`, `VertexCover_Machines_Codec`, `VertexCover_Machines_DenseParse`, `VertexCover_Machines_ExpanderBound`, `VertexCover_Machines_ExpanderCorrect`, `VertexCover_Machines_ExpanderFamily`, `VertexCover_Machines_ExpanderStep`, `VertexCover_Machines_FinalCNFBase`, `VertexCover_Machines_InitialTable`, `VertexCover_Machines_Iteration`, `VertexCover_Machines_ListMore`, `VertexCover_Machines_ListNat`, `VertexCover_Machines_ListParam`, `VertexCover_Machines_NatLog`, `VertexCover_Machines_ParseClause`, `VertexCover_Machines_ParseFormula`, `VertexCover_Machines_ParseSize`, `VertexCover_Machines_Power`, `VertexCover_Machines_TableCodeBound`.
--
--   **Imports.** It imports the published bundle `Def_VertexCover`; the bundles `OAIQ028V000`, `OAIQ028V001` and `OAIQ028V002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ028V007`.
-- source:
--   OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_VertexCover
import Definitions.Def_OAIQ028V000
import Definitions.Def_OAIQ028V001
import Definitions.Def_OAIQ028V002

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                         
section

namespace VertexCover.Machine
open UniqueGames.Foundations.Complexity

theorem listBits_member_length {α : Type} (e : α → List Bool) {a : α} {xs : List α} (h : a ∈ xs) :
    (e a).length ≤ (listBits e xs).length := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rw [listBits_cons_length]
    rcases h with rfl | h
    · omega
    · have hh := ih h; omega

theorem listBits_map_bound {α β : Type} (eb : β → List Bool)
    (f : α → β) (xs : List α) (B : ℕ) (h : ∀ a ∈ xs, (eb (f a)).length ≤ B) :
    (listBits eb (xs.map f)).length ≤ (2*B+2)*xs.length+1 := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have h₁ := h a (by simp)
    have h₂ := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, listBits_cons_length, List.length_cons]
    nlinarith

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListParam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                          
section

namespace VertexCover.Machine

namespace WithParam
variable {α β : Type}

theorem mapped_length (ea : α → List Bool) (eb : β → List Bool) (a : α) (xs : List β) :
    (listBits (prodBits ea eb) (xs.map (a,·))).length =
      (4*(ea a).length+2)*xs.length + (listBits eb xs).length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.map_cons,listBits_cons_length,prodBits,pairBits_length,ih,List.length_cons]
    ring

end WithParam

theorem listBits_flatten_bound {α : Type} (e : α → List Bool) (xss : List (List α)) :
    (listBits e xss.flatten).length ≤ (listBits (listBits e) xss).length := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    have hh := listBits_append_length e xs xss.flatten
    simp only [List.flatten_cons,listBits_cons_length]
    omega

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ListNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                        
section

namespace VertexCover.Machine

theorem listBits_tail_length_le {α : Type} (e : α → List Bool) (xs : List α) :
    (listBits e xs.tail).length ≤ (listBits e xs).length := by
  cases xs with
  | nil => exact le_rfl
  | cons a xs => simp only [List.tail_cons,listBits_cons_length]; omega

namespace Range

theorem run (k a : ℕ) (xs : List ℕ) :
    Iterate.run step k (a,xs) = (a+k,(List.range' a k).reverse++xs) := by
  induction k generalizing a xs with
  | zero => simp [Iterate.run]
  | succ k ih =>
    simp only [Iterate.run,step,ih,List.range'_succ,List.reverse_cons,List.append_assoc,
      List.singleton_append]
    congr 1; omega

theorem bits_bound (k a : ℕ) :
    (listBits natBits (List.range' a k)).length ≤ (2*(a+k)+2)*k+1 := by
  have h := listBits_map_bound natBits id (List.range' a k) (a+k) (by
    intro b hb
    simp only [id_eq,natBits_length]
    exact (List.mem_range'_1.mp hb).2.le)
  simpa using h

end Range

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseClause
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                
section

namespace VertexCover.Machine

namespace FormulaParser
open UniqueGames.BinaryFormula UniqueGames.BinaryEncoding

def literalCode (l : Literal) : List Bool := prodBits boolBits Nat.bits (l.positive,l.name)
def clauseCode (clause : Clause) : List Bool :=
  prodBits (prodBits literalCode literalCode) literalCode ((clause[0],clause[1]),clause[2])
def formulaCode (F : Formula) : List Bool := listBits clauseCode F.clauses

def literalDefault : Literal := ⟨0,false⟩
def clauseDefault : Clause := #v[literalDefault,literalDefault,literalDefault]

end FormulaParser
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_DenseParse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                               
section

namespace VertexCover.Machine
namespace FormulaParser
open UniqueGames.BinaryFormula
open UniqueGames.Foundations

abbrev tripleCode {α : Type} (e : α → List Bool) : Triple α → List Bool := prodBits (prodBits e e) e

def literalData (l : Literal) : Bool × ℕ := (l.positive,l.name)
def unaryLiteralCode : Bool × ℕ → List Bool := prodBits boolBits natBits
def unaryClauseCode : Triple (Bool × ℕ) → List Bool := tripleCode unaryLiteralCode
def dataCode : FormulaData → List Bool := prodBits natBits (listBits unaryClauseCode)

def targetLiteralData {n : ℕ} (l : Target.Literal n) : Bool × ℕ :=
  (l.positive,l.variableIndex.val)

noncomputable def literalNamePoly : Poly literalCode Nat.bits (fun l => l.name) :=
  (Poly.snd boolBits Nat.bits).encodeCongr literalData (fun _ => rfl) (fun _ => rfl)

noncomputable def literalSignPoly : Poly literalCode boolBits (fun l => l.positive) :=
  (Poly.fst boolBits Nat.bits).encodeCongr literalData (fun _ => rfl) (fun _ => rfl)

def compactDataLiteral (p : List ℕ × Literal) : Bool × ℕ :=
  (p.2.positive,p.1.idxOf p.2.name)

def compactDataClause (p : List ℕ × Clause) : Triple (Bool × ℕ) :=
  ((compactDataLiteral (p.1,p.2[0]),compactDataLiteral (p.1,p.2[1])),compactDataLiteral (p.1,p.2[2]))

def denseData (F : Formula) : FormulaData :=
  ((activeNames F).length,F.clauses.map fun clause => compactDataClause (activeNames F,clause))

end FormulaParser
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseSize
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.compactLiteral_positive _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.BinaryFormula.eval_compact_extend _root_.OAI.UniqueGames.BinaryFormula.eval_compact_restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                              
section

namespace VertexCover.Machine.FormulaParser
open UniqueGames.BinaryFormula UniqueGames.BinaryEncoding

theorem frame_sound (input digits rest : List Bool) (h : parseFrame input=some (digits,rest)) :
    input=UniqueGames.BinaryEncoding.frame digits++rest := by
  induction input using List.twoStepInduction generalizing digits rest with
  | nil => simp [parseFrame] at h
  | singleton b =>
    cases b with
    | true => simp [parseFrame] at h
    | false =>
      simp only [parseFrame,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
  | cons_cons a b bs ih _ =>
    cases a with
    | false =>
      simp only [parseFrame,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
    | true =>
      cases hp : parseFrame bs with
      | none => simp [parseFrame,hp] at h
      | some p =>
        rcases p with ⟨ds,rs⟩
        simp only [parseFrame,hp,Option.bind_eq_bind,Option.pure_def,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        rw [ih ds rs hp]
        rfl

theorem name_sound (input : List Bool) (n : ℕ) (rest : List Bool)
    (h : parseName input=some (n,rest)) : input=nameBits n++rest := by
  cases hp : parseFrame input with
  | none => simp [parseName,hp] at h
  | some p =>
    rcases p with ⟨digits,rs⟩
    simp only [parseName,hp,Option.bind_eq_bind,Option.bind_some] at h
    split at h
    · rename_i hc
      have he := Option.some.inj h
      cases he
      have hf := frame_sound input digits rest hp
      simpa only [nameBits,← hc] using hf
    · contradiction

theorem literal_sound (input : List Bool) (l : Literal) (rest : List Bool)
    (h : parseLiteral input=some (l,rest)) : input=literalBits l++rest := by
  cases input with
  | nil => simp [parseLiteral] at h
  | cons b bs =>
    cases hp : parseName bs with
    | none => simp [parseLiteral,hp] at h
    | some p =>
      rcases p with ⟨n,rs⟩
      simp only [parseLiteral,hp,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at h
      have he := Option.some.inj h
      cases he
      have hn := name_sound bs n rest hp
      simpa only [literalBits,List.cons_append] using congrArg (List.cons b) hn

theorem clause_sound (input : List Bool) (clause : Clause) (rest : List Bool)
    (h : parseClause input=some (clause,rest)) : input=clauseBits clause++rest := by
  cases h₁ : parseLiteral input with
  | none => simp [parseClause,h₁] at h
  | some a =>
    rcases a with ⟨a,rs₁⟩
    cases h₂ : parseLiteral rs₁ with
    | none => simp [parseClause,h₁,h₂] at h
    | some b =>
      rcases b with ⟨b,rs₂⟩
      cases h₃ : parseLiteral rs₂ with
      | none => simp [parseClause,h₁,h₂,h₃] at h
      | some c =>
        rcases c with ⟨c,rs₃⟩
        simp only [parseClause,h₁,h₂,h₃,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at h
        cases Option.some.inj h
        rw [literal_sound input a rs₁ h₁,literal_sound rs₁ b rs₂ h₂,literal_sound rs₂ c rest h₃]
        simp only [clauseBits,List.append_assoc]
        rfl

theorem clause_code_bound (clause : Clause) :
    2*(clauseCode clause).length+2 ≤ 16*(clauseBits clause).length := by
  simp only [clauseCode,literalCode,prodBits,pairBits_length,boolBits,List.length_nil,
    clauseBits,List.length_append,literalBits,List.length_cons,nameBits,UniqueGames.BinaryEncoding.frame_length]
  omega

end VertexCover.Machine.FormulaParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ParseFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine.FormulaParser
open UniqueGames.BinaryFormula UniqueGames.BinaryEncoding

abbrev Acc := List Clause × List Bool
abbrev accCode : Acc → List Bool := prodBits (listBits clauseCode) id
abbrev State := Bool × Option Acc
abbrev stateCode : State → List Bool := prodBits boolBits (optionBits accCode)

def oneStep (p : Acc) : State :=
  if p.2.isEmpty then (false,none)
  else if p.2.headD false then
    let parsed := parseClause p.2.tail
    (parsed.isSome,parsed.map (fun q => (q.1::p.1,q.2)))
  else (false,some (p.1,p.2.tail))

def step (s : State) : State := if s.1 then oneStep (s.2.getD ([],[])) else s

def budget (s : State) : ℕ := match s.2 with
  | none => 10
  | some (out,bs) => 2*(listBits clauseCode out).length+32*bs.length+10

theorem size_le_budget (s : State) : (stateCode s).length ≤ budget s := by
  rcases s with ⟨b,v⟩
  cases v with
  | none => simp [stateCode,prodBits,pairBits_length,boolBits,optionBits,budget]
  | some p =>
    simp only [stateCode,prodBits,pairBits_length,boolBits,List.length_nil,
      optionBits,List.length_cons,accCode,id_eq,budget]
    omega

theorem budget_le_size (s : State) : budget s ≤ 32*((stateCode s).length+1) := by
  rcases s with ⟨b,v⟩
  cases v with
  | none => simp [stateCode,prodBits,pairBits_length,boolBits,optionBits,budget]
  | some p =>
    simp only [stateCode,prodBits,pairBits_length,boolBits,List.length_nil,
      optionBits,List.length_cons,accCode,id_eq,budget]
    omega

theorem step_budget (s : State) : budget (step s) ≤ budget s := by
  rcases s with ⟨b,v⟩
  cases b with
  | false => rfl
  | true =>
    cases v with
    | none => rfl
    | some p =>
      rcases p with ⟨out,bs⟩
      cases bs with
      | nil => simp [step,oneStep,budget]
      | cons b bs =>
        cases b with
        | false => simp [step,oneStep,budget,List.length_cons]
        | true =>
          cases h : parseClause bs with
          | none => simp [step,oneStep,budget,h]
          | some p =>
            rcases p with ⟨c,rest⟩
            have he := congrArg List.length (clause_sound bs c rest h)
            simp only [List.length_append] at he
            have hc := clause_code_bound c
            simp only [step,oneStep,ite_eq_left,Option.getD_some,List.isEmpty_cons,
              Bool.false_eq_true,ite_false,List.headD_cons,List.tail_cons,h,Option.isSome_some,
              Option.map_some,budget,listBits_cons_length,List.length_cons]
            omega

theorem run_budget (n : ℕ) (s : State) : budget (Iterate.run step n s) ≤ budget s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih (step s)).trans (step_budget s)

def observe (s : State) : Option Acc := if s.1 then none else s.2

theorem run_done (n : ℕ) (v : Option Acc) : Iterate.run step n (false,v)=(false,v) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem observe_run (fuel : ℕ) (out : List Clause) (input : List Bool) :
    observe (Iterate.run step fuel (true,some (out,input))) =
      (parseClauses fuel input).map (fun p => (p.1.reverse++out,p.2)) := by
  induction fuel generalizing out input with
  | zero => rfl
  | succ fuel ih =>
    cases input with
    | nil => simp only [Iterate.run,step,oneStep,Option.getD_some,List.isEmpty_nil,
        ite_eq_left,run_done,observe,Bool.false_eq_true,ite_false,parseClauses,Option.map_none]
    | cons b bs =>
      cases b with
      | false =>
        simp only [Iterate.run,step,oneStep,Option.getD_some,List.isEmpty_cons,
          Bool.false_eq_true,ite_eq_left,ite_false,List.headD_cons,List.tail_cons,run_done,observe,
          parseClauses,Option.map_some,List.reverse_nil,List.nil_append]
      | true =>
        cases h : parseClause bs with
        | none =>
          simp only [Iterate.run,step,oneStep,Option.getD_some,List.isEmpty_cons,
            Bool.false_eq_true,ite_eq_left,ite_false,List.headD_cons,List.tail_cons,h,Option.isSome_none,
            Option.map_none,run_done,observe,parseClauses,Option.bind_eq_bind,Option.bind_none]
        | some p =>
          rcases p with ⟨c,rest⟩
          have hstep : step (true,some (out,true::bs)) = (true,some (c::out,rest)) := by
            simp [step,oneStep,h]
          rw [Iterate.run,hstep,ih]
          simp only [parseClauses,h,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
          cases hp : parseClauses fuel rest <;>
            simp [List.reverse_cons,List.append_assoc]

end VertexCover.Machine.FormulaParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_BinaryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
noncomputable def Poly.binaryFrame : Poly id id UniqueGames.BinaryEncoding.frame := by
  let δ : Unit → Bool → Unit × List Bool := fun _ b => ((),[true,b])
  have h (q : Unit) (bs : List Bool) : Stream.output δ (fun _ => [false]) q bs = UniqueGames.BinaryEncoding.frame bs := by
    induction bs generalizing q with
    | nil => rfl
    | cons b bs ih => simp only [Stream.output,δ,List.cons_append,List.nil_append,ih,UniqueGames.BinaryEncoding.frame]
  exact (Stream.poly () δ (fun _ => [false]) 2 (by simp [δ]) (by simp)).congr (fun bs => h () bs)
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace ExpandMachine

def stepRow (d : ℕ) (H : List ℕ) (p : Data × ℕ) : ℕ :=
  let D := d*d
  let g := D*D
  let x := p.2/D
  let port := p.2%D
  let first := lookup d (H,(x%g,port/d))
  let outerFirst := lookup D (p.1.2,(x/g,first.1/D))
  let outerSecond := lookup D (p.1.2,(outerFirst.1,first.1%D))
  let last := lookup d (H,(outerFirst.2+D*outerSecond.2,port%d))
  (first.2+d*last.2)+D*(last.1+g*outerSecond.1)

def stepData (d : ℕ) (H : List ℕ) (T : Data) : Data :=
  let v := T.1*((d*d)*(d*d))
  (v,(List.range (v*(d*d))).map (fun i => stepRow d H (T,i)))

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.ExpandMachine
open UniqueGames.Foundations.PCP

@[simp] theorem index_val {v q : ℕ} (x : Fin v × Fin q) :
    (ExpanderTables.rowIndex v q x).val=x.2.val+q*x.1.val := rfl
@[simp] theorem index_inv_fst {v q : ℕ} (i : Fin (v*q)) :
    ((ExpanderTables.rowIndex v q).symm i).1.val=i.val/q := rfl
@[simp] theorem index_inv_snd {v q : ℕ} (i : Fin (v*q)) :
    ((ExpanderTables.rowIndex v q).symm i).2.val=i.val%q := rfl

end VertexCover.Machine.ExpandMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

theorem listBits_length_bound {α : Type} (e : α → List Bool) (xs : List α) (B : ℕ)
    (h : ∀ x ∈ xs, (e x).length ≤ B) :
    (listBits e xs).length ≤ xs.length*(2*B+2)+1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.length_cons,listBits_cons_length]
    nlinarith

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

theorem iterate_fixed {α : Type} (f : α → α) (a : α) (h : f a = a) (n : ℕ) :
    Iterate.run f n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Iterate.run,h] using ih

namespace ExpandMachine

 theorem growth_eq : ExpanderFamily.growth =
    (Expanders.baseDegree*Expanders.baseDegree)*(Expanders.baseDegree*Expanders.baseDegree) := by
  unfold ExpanderFamily.growth
  ring

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Cloud
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace CloudMachine
open TableMachine

abbrev pairCode := prodBits natBits natBits

end CloudMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                          
section

namespace VertexCover.Machine

theorem prodBits_injective {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Function.Injective ea) (hb : Function.Injective eb) :
    Function.Injective (prodBits ea eb) := by
  intro a b h
  apply Prod.ext
  · apply ha
    have hh := congrArg (Stream.output (Project.trans true false) (fun _ => []) 0) h
    simpa only [prodBits,Project.framed,Bool.false_eq_true,↓reduceIte,List.append_nil] using hh
  · apply hb
    have hh := congrArg (Stream.output (Project.trans false true) (fun _ => []) 0) h
    simpa only [prodBits,Project.framed,Bool.false_eq_true,↓reduceIte,List.nil_append] using hh

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_FinalCNFBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine.FinalCNFMachine
open UniqueGames.Foundations
open PCP PCP.VerifierToCNF PCP.GraphTables Target FormulaParser TableMachine

def eraseLiteral {n : ℕ} (f : Fin n → ℕ) (l : Literal n) : Bool × ℕ := (l.positive,f l.variableIndex)

theorem oldIndex_value {q : ℕ} (V : FiniteVerifier q) (i : Fin V.variables) :
    (oldIndex V i).val = i.val := rfl

end VertexCover.Machine.FinalCNFMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_InitialTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
open UniqueGames.Foundations
open PCP PCP.GraphTables
open FormulaParser TableMachine

namespace InitialTable

def signsCode : Signs → List Bool := tripleCode boolBits

end InitialTable
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_NatLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                           
section

namespace VertexCover.Machine
namespace Logarithm
abbrev enc : State → List Bool := prodBits natBits natBits

 theorem run (n c B : ℕ) (hsize : (enc (n,c)).length ≤ B) :
    ∃ k, k ≤ n+1 ∧ BoundedRun enc body B (n,c) (result (n,c)) k := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases h : 2 ≤ n
    · have hlt := Nat.div_lt_self (by omega : 0<n) (by decide : 1<2)
      have hs : (enc (n/2,c+1)).length ≤ B := by
        simp only [enc,prodBits,pairBits_length,natBits_length] at hsize ⊢
        omega
      obtain ⟨k,hk,hr⟩ := ih (n/2) hlt (c+1) hs
      have he : result (n/2,c+1) = result (n,c) := by
        simp only [result]
        rw [Nat.log2_def n,ite_eq_left h]
        apply Prod.ext <;> simp only
        · omega
        · omega
      rw [he] at hr
      refine ⟨k+1,by omega,.next _ _ k hsize (by simp [body,h]) ?_⟩
      simpa only [body,h,ite_true] using hr
    · have he : result (n,c) = (n,c) := by
        simp only [result,Nat.log2_def n,ite_eq_right h,Nat.add_zero]
        congr 1
        omega
      rw [he]
      refine ⟨1,by omega,?_⟩
      simpa only [body,h,ite_false] using (BoundedRun.stop (e := enc) (body := body) (n,c) hsize (by simp [body,h]))
end Logarithm
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Power
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine.PowerMachine
open UniqueGames.Foundations.PCP
open PoweringLabels PoweringEnumeration PoweringTables PowerRowMachine

 theorem relation_ext {q : ℕ} {r s : GenericGraphTables.RelationTable q}
    (h : ∀ a b, GenericGraphTables.relationAt r a b = GenericGraphTables.relationAt s a b) : r=s := by
  apply Vector.ext
  intro i hi
  let ab := (GenericGraphTables.relationIndex q).symm (⟨i,hi⟩ : Fin (q*q))
  have he : GenericGraphTables.relationIndex q ab = (⟨i,hi⟩ : Fin (q*q)) :=
    (GenericGraphTables.relationIndex q).apply_symm_apply _
  have hp := h ab.1 ab.2
  simpa only [GenericGraphTables.relationAt,he,Fin.getElem_fin] using hp

end VertexCover.Machine.PowerMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_TableCodeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP
 theorem listBits_length_le {α : Type} (e : α → List Bool) (xs : List α) (B : ℕ)
    (h : ∀ a ∈ xs, (e a).length ≤ B) : (listBits e xs).length ≤ xs.length*(2*B+2)+1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hh := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [listBits_cons_length,List.length_cons]
    nlinarith
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Iteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                     
section

namespace VertexCover.Machine
open UniqueGames.Foundations
open PCP
 theorem Iterate.run_source {α : Type} (f : α → α) (n : ℕ) (a : α) :
    Iterate.run f n a = AmplificationIteration.run f n a := by
  have commute (k : ℕ) (a : α) :
      AmplificationIteration.run f k (f a) = f (AmplificationIteration.run f k a) := by
    induction k with
    | zero => rfl
    | succ k ih => exact congrArg f ih
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact (ih (f a)).trans (commute n a)
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end


