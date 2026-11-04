-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
-- name    : Submission_ThreeSumApsp_Lang_ToMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:23:18.44648+00:00
-- url     : https://prove2.me/theorems/a6163e7f-1f03-4780-9a73-27ce408540d4
-- title:
--   To Machine
-- statement:
--   Definitions and structural lemmas for To Machine, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
namespace Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
structure Small (s k : ℕ) (params : List ℕ) (lim : Limits) : Prop where
  nonneg : 0 ≤ lim.word
  word : lim.word ≤ (polyBound s k params : ℤ)
  space : lim.space ≤ polyBound s k params
  depth : lim.depth ≤ polyBound s k params
structure ProgramSolvesAt (prob : Problem) (P : Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (x : prob.Inst) (T : ℝ) (lim : Limits) (σ' : State) (c : ℕ) : Prop where
  /-- The run starts on the memory that holds the input of the problem. -/
  run : Exec lim P 0 (mainStmt p0) ⟨frame [0, 0, 0], memOf (prob.input x)⟩ σ' c
  /-- It ends within the time bound. -/
  time : (c : ℝ) ≤ T
  /-- The numbers of the input fit in a word. -/
  input_fits : ∀ v ∈ prob.input x, |v| ≤ lim.word
  /-- The limits are polynomial in the parameters of the instance. -/
  small : Small s k (prob.params x) lim
  /-- The result gives the verdict, and the cells after the input hold the output. -/
  answer : prob.IsAnswer x (verdictOf dec (σ'.loc 0)) fun i => σ'.mem ((prob.input x).length + i)
def ProgramSolves (prob : Problem) (P : Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) : Prop :=
  ∀ x, dom x → ∃ (lim : Limits) (σ' : State) (c : ℕ),
    ProgramSolvesAt prob P p0 dec s k x (T x) lim σ' c
def textBound (P : Program) (dec : Bool) : ℕ := 32 + 8 * (frameSize P + 1) + 2 * dispPos P dec
def textBoundBits (P : Program) (dec : Bool) : ℕ := Nat.size (textBound P dec)
def slopeOf (P : Program) (dec : Bool) (s k r : ℕ) : ℕ := textBoundBits P dec + s + k * r + k
def timeConst (P : Program) (dec : Bool) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec) + lowCell P dec ⟨0, 0, 0⟩
section run
variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}
end run
def AnswersQueries (lim : Limits) (P : Program) (pQ : ℕ) (x : ThinPair) (T : ℝ)
    (DS : (ℕ → ℤ) → Prop) : Prop :=
  ∀ μ, DS μ → ∀ I J : Fin x.N, ∃ (σ' : State) (c : ℕ),
    Exec lim P 0 (mainStmt pQ) ⟨frame [0, (I : ℕ), (J : ℕ)], μ⟩ σ' c ∧ (c : ℝ) ≤ T ∧
    σ'.loc 0 = (x.X * x.Y) I J ∧ DS σ'.mem
structure ProgramIsDataStructureAt (P : Program) (pPre pQ : ℕ) (s k : ℕ) (extra : List ℤ)
    (x : ThinPair) (Tp Sp Tq : ℝ) (lim : Limits) (DS : (ℕ → ℤ) → Prop) : Prop where
  /-- The limits are polynomial in N and D. -/
  small : Small s k [x.N, x.D] lim
  /-- The indices of rows and columns fit in a word. -/
  index_fits : (x.N : ℤ) ≤ lim.word
  /-- The numbers of the input fit in a word. -/
  input_fits : ∀ v ∈ x.input extra, |v| ≤ lim.word
  time_nonneg : 0 ≤ Tq
  /-- The space bounds the addresses after the input. -/
  space : (lim.space : ℝ) ≤ (x.input extra).length + Sp
  /-- The space bounds the nesting of calls. -/
  depth : (lim.depth : ℝ) ≤ Sp
  /-- The preprocessing, on the memory that holds the input, establishes DS. -/
  pre : ∃ (σ' : State) (c : ℕ),
    Exec lim P 0 (mainStmt pPre) ⟨frame [0, 0, 0], memOf (x.input extra)⟩ σ' c ∧
    (c : ℝ) ≤ Tp ∧ DS σ'.mem
  /-- Every query needs and keeps DS. -/
  query : AnswersQueries lim P pQ x Tq DS
def ProgramIsDataStructure (P : Program) (pPre pQ : ℕ) (s k : ℕ) (extra : List ℤ)
    (dom : ThinPair → Prop) (Tp Sp Tq : ThinPair → ℝ) : Prop :=
  ∀ x, dom x → ∃ (lim : Limits) (DS : (ℕ → ℤ) → Prop),
    ProgramIsDataStructureAt P pPre pQ s k extra x (Tp x) (Sp x) (Tq x) lim DS
end Light


