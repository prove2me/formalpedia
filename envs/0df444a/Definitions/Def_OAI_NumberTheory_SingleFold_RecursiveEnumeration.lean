-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_RecursiveEnumeration
-- name    : OAI_NumberTheory_SingleFold_RecursiveEnumeration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:48:13.711189+00:00
-- url     : https://prove2.me/theorems/e2d62f33-60cc-4843-8780-f71c8cb2658a
-- title:
--   Finite counter machines for partial recursive programs
-- statement:
--   Fix a stack-machine program $M$ with a finite set $S$ of reachable labels and $n$ inputs.
--
--   1. The statements of $S$ are all sub-statements of $M(l)$ for $l\in S$, a finite set $A$. A macro label is good if every statement in it lies in $A$; the good labels form a finite type, being the image of a finite type of bounded labels.
--   2. The finite program is the macro program restricted to good labels, starting from the first input-loading label.
--   3. The counter program is its compilation into a counter machine
--   $$
--   \mathrm{counterProgram}(M,S):\ \text{states }\mathrm{State}(\text{good labels}),\ \text{registers }(\text{stacks}\sqcup\mathrm{Fin}\,n)\sqcup\{\text{scratch},\text{zero}\},
--   $$
--      and the counter input places $a_i$ in the $i$-th input register and $0$ elsewhere.
--
--   Every partial recursive function therefore halts exactly when a finite counter machine does. This is the step from recursive enumerability to counter machines.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/RecursiveEnumeration.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/RecursiveEnumeration.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterCompilation
import Definitions.Def_OAI_NumberTheory_SingleFold_MacroMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_TuringSimulation

namespace OAI

noncomputable section

namespace SingleFold.TM2Macro
open Turing Turing.PartrecToTM2 StateTransition Relation
open scoped Classical
variable {n : ℕ} {Λ : Type}
def Good (A : Finset (Stmt Λ)) : Label n Λ → Prop
  | .code q _=>q∈A | .restore _ _ q _=>q∈A
  | .start _=>True | .divide _=>True | .bit _=>True | .pushBit _ _=>True
  | .reverse _=>True | .pushRev _ _=>True
inductive BLabel (n : ℕ) (C : Type)
  | code (q : C) (v : Store)
  | restore (k : Stack) (d : Fin 5) (q : C) (v : Store)
  | start (i : Fin (n+1))
  | divide (i : Fin n)
  | bit (i : Fin n)
  | pushBit (i : Fin n) (d : Fin 5)
  | reverse (i : Fin n)
  | pushRev (i : Fin n) (d : Fin 5)
  deriving Fintype
def forget (A : Finset (Stmt Λ)) : BLabel n {q // q∈A} → Label n Λ
  | .code q v=>.code q.val v | .restore k d q v=>.restore k d q.val v
  | .start i=>.start i | .divide i=>.divide i | .bit i=>.bit i | .pushBit i d=>.pushBit i d
  | .reverse i=>.reverse i | .pushRev i d=>.pushRev i d
lemma forget_good (A : Finset (Stmt Λ)) (q : BLabel n {q // q∈A}) : Good A (forget A q) := by
  cases q <;> simp only [forget,Good]
  all_goals exact Subtype.property _
lemma forget_surj (A : Finset (Stmt Λ)) (q : {q : Label n Λ // Good A q}) :
    ∃ b : BLabel n {q // q∈A}, forget A b=q.val := by
  rcases q with ⟨q,hq⟩
  cases q with
  | code q v => exact ⟨.code ⟨q,hq⟩ v,rfl⟩
  | restore k d q v => exact ⟨.restore k d ⟨q,hq⟩ v,rfl⟩
  | start i => exact ⟨.start i,rfl⟩
  | divide i => exact ⟨.divide i,rfl⟩
  | bit i => exact ⟨.bit i,rfl⟩
  | pushBit i d => exact ⟨.pushBit i d,rfl⟩
  | reverse i => exact ⟨.reverse i,rfl⟩
  | pushRev i d => exact ⟨.pushRev i d,rfl⟩
instance finite_good (A : Finset (Stmt Λ)) : Finite {q : Label n Λ // Good A q} :=
  Finite.of_surjective (fun b=>⟨forget A b,forget_good A b⟩) (fun q=>by
    obtain ⟨b,hb⟩:=forget_surj A q
    exact ⟨b,Subtype.ext hb⟩)
def statements (M : Λ → Stmt Λ) (S : Finset Λ) : Finset (Stmt Λ) := S.biUnion (fun l=>TM2.stmts₁ (M l))
instance fintype_good (A : Finset (Stmt Λ)) : Fintype {q : Label n Λ // Good A q} := Fintype.ofFinite _
abbrev FiniteState (n : ℕ) (M : Λ → Stmt Λ) (S : Finset Λ) := {q : Label n Λ // Good (statements M S) q}
def finStart (M : Λ → Stmt Λ) (S : Finset Λ) : FiniteState n M S := ⟨.start (Fin.last n),trivial⟩
def finProgram (M : Λ → Stmt Λ) (initial : Λ) (S : Finset Λ) : FiniteState n M S → Macro.Instr (FiniteState n M S) (Reg n) :=
  Macro.restrict (program M initial) (Good (statements M S)) (finStart M S)
def counterProgram (M : Λ → Stmt Λ) (initial : Λ) (S : Finset Λ) : Counter.Machine (Macro.State (FiniteState n M S)) (Macro.Reg (Reg n)) :=
  Macro.compile (finProgram M initial S) (finStart M S)
def inputSlot : Macro.Reg (Reg n) → Option (Fin n)
  | .inl (.inr i)=>some i | _=>none
def counterInput (a : Fin n → ℕ) : Macro.Reg (Reg n) → ℕ := fun j=>(inputSlot j).elim 0 a
end SingleFold.TM2Macro

end

end OAI


