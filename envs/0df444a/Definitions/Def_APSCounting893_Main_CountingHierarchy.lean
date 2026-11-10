-- Prove2me | Definitions.Def_APSCounting893_Main_CountingHierarchy
-- name    : APSCounting893_Main_CountingHierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:00:10.447966+00:00
-- url     : https://prove2.me/theorems/d40bec59-1f68-42dc-bb58-c0de73994c22
-- title:
--   Finite oracle machines, strict majority and the Counting Hierarchy
-- statement:
--   A language is a set of finite binary words. A finite multitape machine has a finite transition table, a finite alphabet, and separate input, random, query and output tapes. An ordinary step writes one cell per tape and moves each head by at most one cell. A query step branches on the language oracle's answer to the finite string physically written from the query tape's origin. Writing that string takes ordinary steps.
--
--   For one machine and natural constants $c,d,a,b$, every computation on $a(|x|+1)^b$ fair bits must halt within $c(|x|+1)^d$ steps. Strict majority defines $\mathrm{PP}^A$. The hierarchy is
--
--   $$C_0P=P,\qquad C_{j+1}P=\mathrm{PP}^{C_jP},\qquad \mathrm{CH}=\bigcup_jC_jP.$$
--
--   Machine descriptions, bounds and hierarchy levels are uniform over all inputs. Function computation reads the actual output tape. This interface supplies computational semantics rather than an assumed complexity-class oracle.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), §3.4, p. 15, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Mathlib

set_option autoImplicit false

namespace APSCounting893.Main

abbrev Word := List Bool
abbrev Language := Word → Prop

/-- A tape cell is blank, a bit, or an auxiliary symbol from a fixed finite alphabet. -/
inductive TapeSymbol (a : ℕ) where
  | blank
  | bit (b : Bool)
  | extra (s : Fin a)
  deriving DecidableEq

/-- A physical two-way tape, represented by a finite log of writes and an integer head position.
The newest write at a position takes precedence; absent cells are blank. -/
structure Tape (a : ℕ) where
  cells : List (ℤ × TapeSymbol a) := []
  head : ℤ := 0

inductive Move where
  | left | stay | right

def Tape.read {a : ℕ} (t : Tape a) (i : ℤ) : TapeSymbol a :=
  ((t.cells.find? (fun p => p.1 == i)).map Prod.snd).getD .blank

/-- One physical step writes one cell and moves by at most one cell. -/
def Tape.step {a : ℕ} (t : Tape a) (s : TapeSymbol a) (m : Move) : Tape a :=
  ⟨(t.head, s) :: t.cells,
    t.head + (match m with | .left => -1 | .stay => 0 | .right => 1)⟩

def Tape.input {a : ℕ} (w : Word) : Tape a :=
  ⟨w.zipIdx.map (fun p => ((p.2 + 1 : ℕ), TapeSymbol.bit p.1)), 0⟩

/-- The initial bit string on a tape ends at its first non-bit cell. -/
def TapeSymbol.bits {a : ℕ} : List (TapeSymbol a) → Word
  | .bit b :: ss => b :: TapeSymbol.bits ss
  | _ => []

def Tape.word {a : ℕ} (t : Tape a) : Word :=
  TapeSymbol.bits ((List.range (t.cells.foldl (fun m p => max m (p.1.natAbs + 2)) 1)).map
    (fun i => t.read (i + 1)))

/-- Finite actions. A query step answers the bits physically written on the query tape. -/
inductive Action (q a k : ℕ) where
  | step (next : Fin q) (write : Fin k → TapeSymbol a) (move : Fin k → Move)
  | query (yes no : Fin q)
  | halt (answer : Bool)

/-- A finite multitape transition table with four distinguished tapes.
The input and random tapes are ordinary writable tapes after initialization. -/
structure OracleMachine where
  states : ℕ
  alphabet : ℕ
  tapes : ℕ
  inputTape : Fin tapes
  randomTape : Fin tapes
  queryTape : Fin tapes
  outputTape : Fin tapes
  distinctTapes : Function.Injective
    (fun i : Fin 4 => ![inputTape, randomTape, queryTape, outputTape] i)
  initial : Fin states
  transition : Fin states → (Fin tapes → TapeSymbol alphabet) → Action states alphabet tapes

structure MachineConfig (M : OracleMachine) where
  state : Fin M.states
  tapes : Fin M.tapes → Tape M.alphabet
  answer : Option Bool

noncomputable def machineStep (M : OracleMachine) (A : Language)
    (cfg : MachineConfig M) : MachineConfig M := by
  classical
  exact if cfg.answer.isSome then cfg else
    match M.transition cfg.state (fun j => (cfg.tapes j).read (cfg.tapes j).head) with
    | .halt b => { cfg with answer := some b }
    | .query yes no =>
        { cfg with state := if A (cfg.tapes M.queryTape).word then yes else no }
    | .step next write move =>
        { cfg with state := next, tapes := fun j => (cfg.tapes j).step (write j) (move j) }

/-- The first nonblank cell has position 1. The query is read from that fixed origin. -/
def initialConfig (M : OracleMachine) (x w : Word) : MachineConfig M :=
  { state := M.initial
    tapes := fun j => if j = M.inputTape then Tape.input x
      else if j = M.randomTape then Tape.input w else ⟨[], 0⟩
    answer := none }

noncomputable def machineRun (M : OracleMachine) (A : Language) (x w : Word)
    (time : ℕ) : MachineConfig M :=
  (machineStep M A)^[time] (initialConfig M x w)

def polyBound (c d n : ℕ) : ℕ := c * (n + 1) ^ d

/-- Every input, and every seed of the chosen length, halts within the same polynomial. -/
def RunsInTime (M : OracleMachine) (A : Language) (c d a b : ℕ) : Prop :=
  ∀ x w : Word, w.length = polyBound a b x.length →
    (machineRun M A x w (polyBound c d x.length)).answer.isSome

/-- Strict majority, including the single computation when the seed length is zero. -/
def InOraclePP (A L : Language) : Prop :=
  ∃ (M : OracleMachine) (c d a b : ℕ), RunsInTime M A c d a b ∧
    ∀ x : Word, L x ↔ 2 ^ polyBound a b x.length <
      2 * Set.ncard {w : Word | w.length = polyBound a b x.length ∧
        (machineRun M A x w (polyBound c d x.length)).answer = some true}

/-- A total deterministic polynomial-time decider. -/
def InOracleP (A L : Language) : Prop :=
  ∃ (M : OracleMachine) (c d : ℕ), ∀ x : Word,
    ∃ answer : Bool,
      (machineRun M A x [] (polyBound c d x.length)).answer = some answer ∧
      (answer = true ↔ L x)

/-- The machine and hierarchy level precede every input and every input length. -/
def AtCHLevel : ℕ → Language → Prop
  | 0, L => InOracleP (fun _ => False) L
  | j + 1, L => ∃ A : Language, AtCHLevel j A ∧ InOraclePP A L

def InCountingHierarchy (L : Language) : Prop := ∃ j : ℕ, AtCHLevel j L

/-- Function output is read from the actual charged output tape. -/
def FunctionInPWithOracle (A : Language) (f : Word → Word) : Prop :=
  ∃ (M : OracleMachine) (c d : ℕ), ∀ x : Word,
    let cfg := machineRun M A x [] (polyBound c d x.length)
    cfg.answer.isSome ∧ (cfg.tapes M.outputTape).word = f x

end APSCounting893.Main


