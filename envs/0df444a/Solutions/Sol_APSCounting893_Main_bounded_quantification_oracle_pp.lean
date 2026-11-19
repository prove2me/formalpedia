-- Prove2me | solution 1 for APSCounting893.Main.bounded_quantification_oracle_pp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:17:55.085669+00:00
-- url     : https://prove2.me/submissions/b522c130-e6eb-453b-b044-f8aa9dae51af

import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
namespace APSCounting893.Main

noncomputable def haltMachine (b : Bool) : OracleMachine where
  states := 1
  alphabet := 0
  tapes := 4
  inputTape := 0
  randomTape := 1
  queryTape := 2
  outputTape := 3
  distinctTapes := by decide
  initial := 0
  transition := fun _ _ => .halt b

lemma haltMachine_answer_one (b : Bool) (A : Language) (x w : Word) :
    (machineRun (haltMachine b) A x w 1).answer = some b := rfl

lemma constant_inOracleP (A : Language) (b : Bool) : InOracleP A (fun _ => b = true) := by
  refine ⟨haltMachine b, 1, 0, ?_⟩
  intro x
  exact ⟨b, haltMachine_answer_one b A x [], Iff.rfl⟩

lemma constant_inOraclePP (A : Language) (b : Bool) : InOraclePP A (fun _ => b = true) := by
  refine ⟨haltMachine b, 1, 0, 0, 0, ?_, ?_⟩
  · intro x w hw
    rw [show polyBound 1 0 x.length = 1 by simp [polyBound], haltMachine_answer_one]
    rfl
  · intro x
    simp only [polyBound, pow_zero, mul_one, zero_mul, pow_zero, haltMachine_answer_one]
    cases b <;> simp

lemma constant_inCountingHierarchy (b : Bool) : InCountingHierarchy (fun _ => b = true) := by
  exact ⟨0, constant_inOracleP (fun _ => False) b⟩

lemma constant_atCHLevel (j : ℕ) (b : Bool) : AtCHLevel j (fun _ => b = true) := by
  induction j with
  | zero => exact constant_inOracleP _ b
  | succ j ih => exact ⟨fun _ => b = true, ih, constant_inOraclePP _ b⟩

lemma machineStep_halted (M : OracleMachine) (A : Language) (cfg : MachineConfig M)
    (h : cfg.answer.isSome) : machineStep M A cfg = cfg := by
  simp only [machineStep, if_pos h]

lemma machineRun_succ (M : OracleMachine) (A : Language) (x w : Word) (t : ℕ) :
    machineRun M A x w (t + 1) = machineStep M A (machineRun M A x w t) := by
  exact Function.iterate_succ_apply' _ _ _

lemma machineRun_halted_persistent (M : OracleMachine) (A : Language) (x w : Word)
    (t s : ℕ) (h : (machineRun M A x w t).answer.isSome) :
    machineRun M A x w (t + s) = machineRun M A x w t := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.add_succ]
      rw [machineRun_succ]
      rw [ih, machineStep_halted M A _ h]

end APSCounting893.Main
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

inductive ProgramAction (Q : Type) (a k : ℕ) where
  | step (next : Q) (write : Fin k → TapeSymbol a) (move : Fin k → Move)
  | query (yes no : Q)
  | halt (answer : Bool)

structure FiniteProgram (Q : Type) (a k : ℕ) where
  inputTape : Fin k
  randomTape : Fin k
  queryTape : Fin k
  outputTape : Fin k
  distinctTapes : Function.Injective
    (fun i : Fin 4 => ![inputTape, randomTape, queryTape, outputTape] i)
  initial : Q
  transition : Q → (Fin k → TapeSymbol a) → ProgramAction Q a k

structure ProgramConfig (Q : Type) (a k : ℕ) where
  state : Q
  tapes : Fin k → Tape a
  answer : Option Bool

noncomputable def FiniteProgram.compile {Q : Type} [Fintype Q] {a k : ℕ}
    (P : FiniteProgram Q a k) : OracleMachine where
  states := Fintype.card Q
  alphabet := a
  tapes := k
  inputTape := P.inputTape
  randomTape := P.randomTape
  queryTape := P.queryTape
  outputTape := P.outputTape
  distinctTapes := P.distinctTapes
  initial := Fintype.equivFin Q P.initial
  transition := fun q s => match P.transition ((Fintype.equivFin Q).symm q) s with
    | .step next write move => .step (Fintype.equivFin Q next) write move
    | .query yes no => .query (Fintype.equivFin Q yes) (Fintype.equivFin Q no)
    | .halt b => .halt b

noncomputable def FiniteProgram.compileConfig {Q : Type} [Fintype Q] {a k : ℕ}
    (P : FiniteProgram Q a k) (cfg : ProgramConfig Q a k) : MachineConfig P.compile where
  state := Fintype.equivFin Q cfg.state
  tapes := cfg.tapes
  answer := cfg.answer

noncomputable def FiniteProgram.step {Q : Type} {a k : ℕ}
    (P : FiniteProgram Q a k) (A : Language) (cfg : ProgramConfig Q a k) : ProgramConfig Q a k := by
  classical
  exact if cfg.answer.isSome then cfg else
    match P.transition cfg.state (fun j => (cfg.tapes j).read (cfg.tapes j).head) with
    | .halt b => { cfg with answer := some b }
    | .query yes no =>
        { cfg with state := if A (cfg.tapes P.queryTape).word then yes else no }
    | .step next write move =>
        { cfg with state := next, tapes := fun j => (cfg.tapes j).step (write j) (move j) }

def FiniteProgram.initialConfig {Q : Type} {a k : ℕ}
    (P : FiniteProgram Q a k) (x w : Word) : ProgramConfig Q a k :=
  { state := P.initial
    tapes := fun j => if j = P.inputTape then Tape.input x
      else if j = P.randomTape then Tape.input w else ⟨[], 0⟩
    answer := none }

noncomputable def FiniteProgram.run {Q : Type} {a k : ℕ}
    (P : FiniteProgram Q a k) (A : Language) (x w : Word) (time : ℕ) : ProgramConfig Q a k :=
  (P.step A)^[time] (P.initialConfig x w)

lemma FiniteProgram.compile_step {Q : Type} [Fintype Q] {a k : ℕ}
    (P : FiniteProgram Q a k) (A : Language) (cfg : ProgramConfig Q a k) :
    machineStep P.compile A (P.compileConfig cfg) = P.compileConfig (P.step A cfg) := by
  classical
  rcases cfg with ⟨q, tapes, answer⟩
  cases answer with
  | some b => rfl
  | none =>
      cases h : P.transition q (fun j => (tapes j).read (tapes j).head) with
      | step next write move => simp [machineStep, compile, compileConfig, step, h]
      | query yes no =>
          by_cases hA : A (tapes P.queryTape).word <;>
            simp [machineStep, compile, compileConfig, step, h, hA]
      | halt b => simp [machineStep, compile, compileConfig, step, h]

lemma FiniteProgram.compile_initial {Q : Type} [Fintype Q] {a k : ℕ}
    (P : FiniteProgram Q a k) (x w : Word) :
    APSCounting893.Main.initialConfig P.compile x w = P.compileConfig (P.initialConfig x w) := rfl

lemma FiniteProgram.run_succ {Q : Type} {a k : ℕ}
    (P : FiniteProgram Q a k) (A : Language) (x w : Word) (time : ℕ) :
    P.run A x w (time + 1) = P.step A (P.run A x w time) :=
  Function.iterate_succ_apply' _ _ _

lemma FiniteProgram.compile_run {Q : Type} [Fintype Q] {a k : ℕ}
    (P : FiniteProgram Q a k) (A : Language) (x w : Word) (time : ℕ) :
    machineRun P.compile A x w time = P.compileConfig (P.run A x w time) := by
  induction time with
  | zero => exact P.compile_initial x w
  | succ t ih => rw [machineRun_succ, P.run_succ, ih, P.compile_step]

lemma FiniteProgram.step_step {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (A : Language) (cfg : ProgramConfig Q a k) (next : Q)
    (write : Fin k → TapeSymbol a) (move : Fin k → Move) (ha : cfg.answer = none)
    (ht : P.transition cfg.state (fun j => (cfg.tapes j).read (cfg.tapes j).head) =
      .step next write move) :
    P.step A cfg = { cfg with state := next, tapes := fun j => (cfg.tapes j).step (write j) (move j) } := by
  simp [step, ha, ht]

lemma FiniteProgram.step_halt {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (A : Language) (cfg : ProgramConfig Q a k) (b : Bool) (ha : cfg.answer = none)
    (ht : P.transition cfg.state (fun j => (cfg.tapes j).read (cfg.tapes j).head) = .halt b) :
    P.step A cfg = { cfg with answer := some b } := by
  simp [step, ha, ht]

noncomputable def FiniteProgram.exec {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (A : Language) (cfg : ProgramConfig Q a k) (t : ℕ) : ProgramConfig Q a k := (P.step A)^[t] cfg

lemma FiniteProgram.exec_succ {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (A : Language) (cfg : ProgramConfig Q a k) (t : ℕ) :
    P.exec A cfg (t + 1) = P.step A (P.exec A cfg t) := Function.iterate_succ_apply' _ _ _

lemma FiniteProgram.exec_add {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (A : Language) (cfg : ProgramConfig Q a k) (t s : ℕ) :
    P.exec A cfg (t + s) = P.exec A (P.exec A cfg t) s := by
  unfold exec
  rw [Nat.add_comm, Function.iterate_add_apply]

lemma FiniteProgram.exec_one {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (A : Language) (cfg : ProgramConfig Q a k) : P.exec A cfg 1 = P.step A cfg := rfl

lemma FiniteProgram.exec_eq_of_step_eq {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (A : Language) (cfg cfg' : ProgramConfig Q a k) (t : ℕ) (ht : 0 < t)
    (h : P.step A cfg = P.step A cfg') : P.exec A cfg t = P.exec A cfg' t := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  unfold exec
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h]

end APSCounting893.Main
end Component_1

section Component_2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma tape_read_nil {a : ℕ} (h i : ℤ) : (Tape.mk [] h : Tape a).read i = .blank := rfl

lemma tape_step_read_self {a : ℕ} (t : Tape a) (s : TapeSymbol a) (m : Move) :
    (t.step s m).read t.head = s := by
  simp [Tape.step, Tape.read]

lemma tape_step_read_ne {a : ℕ} (t : Tape a) (s : TapeSymbol a) (m : Move) (i : ℤ)
    (hi : i ≠ t.head) : (t.step s m).read i = t.read i := by
  simp [Tape.step, Tape.read, Ne.symm hi]

lemma tape_step_head_stay {a : ℕ} (t : Tape a) (s : TapeSymbol a) :
    (t.step s .stay).head = t.head := by simp [Tape.step]

lemma tape_step_head_left {a : ℕ} (t : Tape a) (s : TapeSymbol a) :
    (t.step s .left).head = t.head - 1 := by simp [Tape.step, sub_eq_add_neg]

lemma tape_step_head_right {a : ℕ} (t : Tape a) (s : TapeSymbol a) :
    (t.step s .right).head = t.head + 1 := rfl

lemma tape_read_eq_of_cells_eq {a : ℕ} (t u : Tape a) (h : t.cells = u.cells) (i : ℤ) :
    t.read i = u.read i := by simp only [Tape.read, h]

lemma tape_input_nil {a : ℕ} (i : ℤ) : (Tape.input (a := a) []).read i = .blank := rfl

lemma tape_read_of_uniform {a : ℕ} (t : Tape a) (i : ℤ) (s : TapeSymbol a)
    (hin : (i, s) ∈ t.cells)
    (hc : ∀ p ∈ t.cells, p.1 = i → p.2 = s) : t.read i = s := by
  unfold Tape.read
  cases h : t.cells.find? (fun p => p.1 == i) with
  | none =>
      have hn := List.find?_eq_none.mp h (i, s) hin
      simp at hn
  | some p =>
      have hp := List.mem_of_find?_eq_some h
      have hi : p.1 = i := by simpa using List.find?_some h
      simpa using hc p hp hi

lemma tape_read_blank_of_absent {a : ℕ} (t : Tape a) (i : ℤ)
    (h : ∀ p ∈ t.cells, p.1 ≠ i) : t.read i = .blank := by
  have hf : t.cells.find? (fun p => p.1 == i) = none := by
    apply List.find?_eq_none.mpr
    intro p hp
    simpa using h p hp
  simp [Tape.read, hf]

lemma tape_input_read {a : ℕ} (w : Word) (i : ℕ) :
    (Tape.input (a := a) w).read (i + 1) =
      if h : i < w.length then .bit w[i] else .blank := by
  classical
  by_cases hi : i < w.length
  · rw [dif_pos hi]
    apply tape_read_of_uniform
    · apply List.mem_map.mpr
      exact ⟨(w[i], i), List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi), by simp⟩
    · intro p hp hpi
      obtain ⟨⟨b, j⟩, hj, rfl⟩ := List.mem_map.mp hp
      have hji : j = i := by simpa using hpi
      subst j
      have hb : w[i]? = some b := List.mk_mem_zipIdx_iff_getElem?.mp hj
      rw [List.getElem?_eq_getElem hi] at hb
      exact congrArg (TapeSymbol.bit (a := a)) (Option.some.inj hb).symm
  · rw [dif_neg hi]
    apply tape_read_blank_of_absent
    intro p hp hpi
    obtain ⟨⟨b, j⟩, hj, rfl⟩ := List.mem_map.mp hp
    have hji : j = i := by simpa using hpi
    subst j
    have hb : w[i]? = some b := List.mk_mem_zipIdx_iff_getElem?.mp hj
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hi)] at hb
    cases hb

lemma tapeSymbol_bits_prefix {a : ℕ} (w : Word) (ss : List (TapeSymbol a)) :
    TapeSymbol.bits (w.map TapeSymbol.bit ++ .blank :: ss) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [TapeSymbol.bits] using congrArg (List.cons b) ih

lemma bits_map_range {a : ℕ} (f : ℕ → TapeSymbol a) (w : Word) (N : ℕ)
    (hN : w.length < N) (hf : ∀ i (hi : i < w.length), f i = .bit w[i])
    (hblank : f w.length = .blank) :
    TapeSymbol.bits ((List.range N).map f) = w := by
  have hp : (List.range w.length).map f = w.map TapeSymbol.bit := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simpa using hf i (by simpa using hi)
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_lt hN
  rw [show N = w.length + (r + 1) by omega, List.range_add, List.map_append, hp, List.range_succ_eq_map]
  simp only [List.map_cons, Nat.add_zero, hblank]
  apply tapeSymbol_bits_prefix

lemma tape_extent_init_le {a : ℕ} (cells : List (ℤ × TapeSymbol a)) (m : ℕ) :
    m ≤ cells.foldl (fun r p => max r (p.1.natAbs + 2)) m := by
  induction cells generalizing m with
  | nil => rfl
  | cons p cells ih =>
      exact (Nat.le_max_left _ _).trans (ih _)

lemma tape_extent_cell_le {a : ℕ} (cells : List (ℤ × TapeSymbol a)) (m : ℕ)
    (p : ℤ × TapeSymbol a) (hp : p ∈ cells) :
    p.1.natAbs + 2 ≤ cells.foldl (fun r p => max r (p.1.natAbs + 2)) m := by
  induction cells generalizing m with
  | nil => simp at hp
  | cons q cells ih =>
      obtain rfl | hp := List.mem_cons.mp hp
      · exact (Nat.le_max_right _ _).trans (tape_extent_init_le cells _)
      · exact ih _ hp

lemma tape_extent_of_read_ne_blank {a : ℕ} (t : Tape a) (i : ℤ)
    (h : t.read i ≠ .blank) :
    i.natAbs + 2 ≤ t.cells.foldl (fun r p => max r (p.1.natAbs + 2)) 1 := by
  cases hf : t.cells.find? (fun p => p.1 == i) with
  | none => simp [Tape.read, hf] at h
  | some p =>
      have hi : p.1 = i := by simpa using List.find?_some hf
      simpa [hi] using tape_extent_cell_le t.cells 1 p (List.mem_of_find?_eq_some hf)

lemma tape_word_of_reads {a : ℕ} (t : Tape a) (w : Word)
    (h : ∀ i : ℕ, t.read (i + 1) = if hi : i < w.length then .bit w[i] else .blank) :
    t.word = w := by
  unfold Tape.word
  simp only [bind_pure_comp]
  change TapeSymbol.bits (List.map (fun i : ℤ => t.read (i + 1))
    (List.map (fun i : ℕ => (i : ℤ)) (List.range _))) = w
  rw [List.map_map]
  apply bits_map_range
  · cases w with
    | nil => exact tape_extent_init_le t.cells 1
    | cons b w =>
        have hr : t.read ((w.length : ℤ) + 1) ≠ .blank := by
          rw [h w.length, dif_pos (by simp)]
          intro hbad; cases hbad
        have he := tape_extent_of_read_ne_blank t ((w.length : ℤ) + 1) hr
        have habs : ((w.length : ℤ) + 1).natAbs = w.length + 1 := by omega
        rw [habs] at he
        simp only [List.length_cons]
        omega
  · intro i hi
    dsimp only [Function.comp_apply]
    rw [h, dif_pos hi]
  · dsimp only [Function.comp_apply]
    rw [h, dif_neg (by omega)]

lemma tape_input_word {a : ℕ} (w : Word) : (Tape.input (a := a) w).word = w :=
  tape_word_of_reads _ w (tape_input_read w)

lemma tape_step_same_reads {a : ℕ} (t : Tape a) (m : Move) (i : ℤ) :
    (t.step (t.read t.head) m).read i = t.read i := by
  by_cases h : i = t.head
  · subst i; exact tape_step_read_self ..
  · exact tape_step_read_ne t _ m i h


lemma tape_input_read_of_getElem {a : ℕ} (w : Word) (i : ℕ) (b : Bool)
    (hb : w[i]? = some b) : (Tape.input (a := a) w).read (i + 1) = .bit b := by
  have hi : i < w.length := List.getElem?_eq_some_iff.mp hb |>.1
  rw [tape_input_read, dif_pos hi]
  rw [List.getElem?_eq_getElem hi] at hb
  exact congrArg (TapeSymbol.bit (a := a)) (Option.some.inj hb)

end APSCounting893.Main
end Component_2

section Component_3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

/-- A prefix code whose first argument can be copied in linear time without a counter. -/

structure FlagStats where
  seen : Bool := false
  first : Bool := true
  allZero : Bool := true
  allOne : Bool := true
  payloadZero : Bool := true
  deriving DecidableEq, Fintype

def FlagStats.update (s : FlagStats) (payload flag : Bool) : FlagStats where
  seen := true
  first := if s.seen then s.first else flag
  allZero := s.allZero && !flag
  allOne := s.allOne && flag
  payloadZero := s.payloadZero && !payload

def quantifierBaseline (universal : Bool) (s : FlagStats) : Bool :=
  if universal then (!s.first && !s.allZero) || (s.allZero && s.payloadZero) else !s.first

def quantifierDecision (universal : Bool) (s : FlagStats) (oracleAnswer : Bool) : Bool :=
  if quantifierBaseline universal s then true else if s.allOne then oracleAnswer else false

inductive QuantifierState where
  | initial
  | input
  | inputBit (b : Bool)
  | payload (s : FlagStats)
  | flag (s : FlagStats) (b : Bool)
  | answer (b : Bool)
  deriving DecidableEq, Fintype

open QuantifierState in
noncomputable def quantifierProgram (universal : Bool) : FiniteProgram QuantifierState 0 4 where
  inputTape := 0
  randomTape := 1
  queryTape := 2
  outputTape := 3
  distinctTapes := by decide
  initial := .initial
  transition := fun q symbols =>
    let writeQuery := fun b j => if j = 2 then TapeSymbol.bit b else symbols j
    let moveQuery := fun j : Fin 4 => if j = 2 then Move.right else Move.stay
    let moveRandom := fun j : Fin 4 => if j = 1 then Move.right else Move.stay
    match q with
    | .initial => .step .input symbols
        (fun j => if j = 0 ∨ j = 1 ∨ j = 2 then .right else .stay)
    | .input => match symbols 0 with
      | .bit b => .step (.inputBit b) (writeQuery true) moveQuery
      | _ => .step (.payload {}) (writeQuery false) moveQuery
    | .inputBit b => .step .input (writeQuery b)
        (fun j => if j = 0 ∨ j = 2 then .right else .stay)
    | .payload s => match symbols 1 with
      | .bit b => .step (.flag s b) (writeQuery b)
          (fun j => if j = 1 ∨ j = 2 then .right else .stay)
      | _ =>
          let baseline := quantifierBaseline universal s
          if baseline then .halt true
          else if s.allOne then .query (.answer true) (.answer false)
          else .halt false
    | .flag s b => match symbols 1 with
      | .bit f => .step (.payload (s.update b f)) symbols moveRandom
      | _ => .halt false
    | .answer b => .halt b

/-- Odd-positioned seed bits are flags; even-positioned bits form the queried witness. -/
def interleave (payload flags : Word) : Word :=
  (payload.zip flags).flatMap (fun p => [p.1, p.2])

def flagStats (payload flags : Word) : FlagStats :=
  (payload.zip flags).foldl (fun s p => s.update p.1 p.2) {}

lemma pairWord_length (x y : Word) : (pairWord x y).length = 2 * x.length + 1 + y.length := by
  simp [pairWord, List.length_flatMap, List.sum_replicate, Nat.mul_comm, Nat.add_assoc, Nat.add_comm]

lemma interleave_length (payload flags : Word) (h : payload.length = flags.length) :
    (interleave payload flags).length = 2 * payload.length := by
  simp [interleave, List.length_flatMap, List.length_zip, h, List.sum_replicate, Nat.mul_comm]

end APSCounting893.Main
end Component_3

section Component_4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

structure TapePrefix {a : ℕ} (t : Tape a) (w : Word) : Prop where
  head : t.head = (w.length + 1 : ℕ)
  read : ∀ j : ℕ, t.read (j + 1) =
    if h : j < w.length then .bit w[j] else .blank

lemma TapePrefix.word {a : ℕ} {t : Tape a} {w : Word} (h : TapePrefix t w) :
    t.word = w := tape_word_of_reads t w h.read

lemma TapePrefix.append {a : ℕ} {t : Tape a} {w : Word} (h : TapePrefix t w) (b : Bool) :
    TapePrefix (t.step (.bit b) .right) (w ++ [b]) := by
  constructor
  · simp [Tape.step, h.head]
  · intro j
    by_cases hj : j = w.length
    · subst j
      rw [show (w.length : ℤ) + 1 = t.head by simpa using h.head.symm,
        tape_step_read_self]
      simp
    · have hjhead : (j : ℤ) + 1 ≠ t.head := by rw [h.head]; exact_mod_cast (by omega : j + 1 ≠ w.length + 1)
      rw [tape_step_read_ne t _ _ _ hjhead, h.read]
      by_cases hlt : j < w.length
      · have hlt' : j < (w ++ [b]).length := by simp; omega
        rw [dif_pos hlt, dif_pos hlt', List.getElem_append_left hlt]
      · have hlt' : ¬ j < (w ++ [b]).length := by simp; omega
        rw [dif_neg hlt, dif_neg hlt']

lemma TapePrefix.stay {a : ℕ} {t : Tape a} {w : Word} (h : TapePrefix t w) :
    TapePrefix (t.step (t.read t.head) .stay) w := by
  constructor
  · simpa [Tape.step] using h.head
  · intro j
    rw [tape_step_same_reads, h.read]

lemma tapePrefix_initial : TapePrefix ((Tape.mk [] 0 : Tape 0).step .blank .right) [] := by
  constructor
  · rfl
  · intro j
    rw [tape_step_read_ne]
    · rfl
    · change (j : ℤ) + 1 ≠ 0
      omega

end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def escapedWord (x : Word) : Word := x.flatMap (fun b => [true, b])

structure InputPrefixInvariant (x seed : Word) (i : ℕ)
    (cfg : ProgramConfig QuantifierState 0 4) : Prop where
  state : cfg.state = .input
  answer : cfg.answer = none
  inputHead : (cfg.tapes 0).head = (i + 1 : ℕ)
  inputRead : ∀ j : ℤ, (cfg.tapes 0).read j = (Tape.input x).read j
  randomHead : (cfg.tapes 1).head = 1
  randomRead : ∀ j : ℤ, (cfg.tapes 1).read j = (Tape.input seed).read j
  query : TapePrefix (cfg.tapes 2) (escapedWord (x.take i))

lemma quantifier_initial (u : Bool) (A : Language) (x seed : Word) :
    InputPrefixInvariant x seed 0 ((quantifierProgram u).run A x seed 1) := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro j
    change ((Tape.input x).step ((Tape.input x).read 0) .right).read j = _
    exact tape_step_same_reads ..
  · rfl
  · intro j
    change ((Tape.input seed).step ((Tape.input seed).read 0) .right).read j = _
    exact tape_step_same_reads ..
  · exact tapePrefix_initial

lemma quantifier_copy_input (u : Bool) (A : Language) (x seed : Word) (i : ℕ)
    (hi : i < x.length) (cfg : ProgramConfig QuantifierState 0 4)
    (hc : InputPrefixInvariant x seed i cfg) :
    InputPrefixInvariant x seed (i + 1)
      ((quantifierProgram u).step A ((quantifierProgram u).step A cfg)) := by
  have hin : (cfg.tapes 0).read (cfg.tapes 0).head = .bit x[i] := by
    rw [hc.inputHead, hc.inputRead]
    simpa only [Nat.cast_add, Nat.cast_one, tape_input_read, dif_pos hi]
  let cfg1 : ProgramConfig QuantifierState 0 4 :=
    { cfg with state := .inputBit x[i], tapes := fun j =>
        ((cfg.tapes j).step (if j = 2 then .bit true else (cfg.tapes j).read (cfg.tapes j).head)
          (if j = 2 then .right else .stay)) }
  have hstep1 : (quantifierProgram u).step A cfg = cfg1 := by
    simp [FiniteProgram.step, quantifierProgram, hc.state, hc.answer, hin, cfg1]
  have hstep2 : (quantifierProgram u).step A cfg1 =
      { cfg1 with state := .input, tapes := fun j =>
        ((cfg1.tapes j).step (if j = 2 then .bit x[i] else (cfg1.tapes j).read (cfg1.tapes j).head)
          (if j = 0 ∨ j = 2 then .right else .stay)) } := by
    simp [FiniteProgram.step, quantifierProgram, cfg1, hc.answer]
  rw [hstep1, hstep2]
  constructor
  · rfl
  · exact hc.answer
  · simp [cfg1, Tape.step, hc.inputHead]
  · intro j
    change (((cfg1.tapes 0).step ((cfg1.tapes 0).read (cfg1.tapes 0).head) .right).read j) = _
    rw [tape_step_same_reads]
    change (((cfg.tapes 0).step ((cfg.tapes 0).read (cfg.tapes 0).head) .stay).read j) = _
    rw [tape_step_same_reads, hc.inputRead]
  · simpa [cfg1, Tape.step] using hc.randomHead
  · intro j
    change (((cfg1.tapes 1).step ((cfg1.tapes 1).read (cfg1.tapes 1).head) .stay).read j) = _
    rw [tape_step_same_reads]
    change (((cfg.tapes 1).step ((cfg.tapes 1).read (cfg.tapes 1).head) .stay).read j) = _
    rw [tape_step_same_reads, hc.randomRead]
  · have hq := (hc.query.append true).append x[i]
    change TapePrefix (((cfg.tapes 2).step (.bit true) .right).step (.bit x[i]) .right) _
    have hp : escapedWord (x.take (i + 1)) = (escapedWord (x.take i) ++ [true]) ++ [x[i]] := by
      simp only [escapedWord]
      rw [List.take_succ_eq_append_getElem hi, List.flatMap_append]
      simp [List.append_assoc]
    rw [hp]
    exact hq

lemma quantifier_input_run (u : Bool) (A : Language) (x seed : Word) (i : ℕ)
    (hi : i ≤ x.length) : InputPrefixInvariant x seed i
      ((quantifierProgram u).run A x seed (2 * i + 1)) := by
  induction i with
  | zero => exact quantifier_initial u A x seed
  | succ i ih =>
      rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 1 + 1 by omega,
        FiniteProgram.run_succ, FiniteProgram.run_succ]
      exact quantifier_copy_input u A x seed i (by omega) _ (ih (by omega))

end APSCounting893.Main
end Component_5

section Component_6

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def splitSeed : Word → Word × Word
  | b :: f :: w => let p := splitSeed w; (b :: p.1, f :: p.2)
  | [b] => ([b], [])
  | [] => ([], [])

lemma splitSeed_interleave (y f : Word) (h : y.length = f.length) :
    splitSeed (interleave y f) = (y, f) := by
  induction y generalizing f with
  | nil =>
      have hf : f = [] := List.length_eq_zero_iff.mp h.symm
      subst f
      rfl
  | cons b y ih =>
      cases f with
      | nil => simp at h
      | cons a f =>
          simp only [interleave, List.zip_cons_cons, List.flatMap_cons, List.cons_append,
            List.nil_append]
          change (b :: (splitSeed (interleave y f)).1, a :: (splitSeed (interleave y f)).2) = _
          rw [ih f (by simpa using h)]

lemma splitSeed_length (p : ℕ) (w : Word) (h : w.length = 2 * p) :
    (splitSeed w).1.length = p ∧ (splitSeed w).2.length = p ∧
      interleave (splitSeed w).1 (splitSeed w).2 = w := by
  induction p generalizing w with
  | zero =>
      have hw : w = [] := List.length_eq_zero_iff.mp (by simpa using h)
      subst w
      exact ⟨rfl, rfl, rfl⟩
  | succ p ih =>
      cases w with
      | nil => simp at h
      | cons b w =>
          cases w with
          | nil => simp at h; omega
          | cons f w =>
              have hw : w.length = 2 * p := by simp only [List.length_cons] at h; omega
              obtain ⟨hy, hf, hi⟩ := ih w hw
              refine ⟨by simpa [splitSeed] using congrArg Nat.succ hy,
                by simpa [splitSeed] using congrArg Nat.succ hf, ?_⟩
              simpa [splitSeed, interleave] using congrArg (fun l => b :: f :: l) hi

lemma words_length_eq_range (p : ℕ) :
    {w : Word | w.length = p} = Set.range (fun f : Fin p → Bool => List.ofFn f) := by
  ext w
  constructor
  · intro hw
    have hlen : w.length = p := hw
    let f : Fin p → Bool := fun i => w[i.val]'(by omega)
    refine ⟨f, ?_⟩
    apply List.ext_getElem
    · simpa using hw.symm
    · intro i hi hi'
      simp [f]
  · rintro ⟨f, rfl⟩
    simp

lemma words_length_ncard (p : ℕ) : Set.ncard {w : Word | w.length = p} = 2 ^ p := by
  rw [words_length_eq_range]
  rw [← Set.image_univ, List.ofFn_injective.injOn.ncard_image, Set.ncard_univ]
  simp [Nat.card_eq_fintype_card]

lemma interleave_functions_injective (p : ℕ) : Function.Injective
    (fun z : (Fin p → Bool) × (Fin p → Bool) => interleave (List.ofFn z.1) (List.ofFn z.2)) := by
  intro z z' h
  have hsplit := congrArg splitSeed h
  rw [splitSeed_interleave _ _ (by simp), splitSeed_interleave _ _ (by simp)] at hsplit
  exact Prod.ext (List.ofFn_injective (congrArg Prod.fst hsplit))
    (List.ofFn_injective (congrArg Prod.snd hsplit))

lemma interleave_getElem_payload (y f : Word) (h : y.length = f.length)
    (i : ℕ) (hi : i < y.length) : (interleave y f)[2 * i]? = some y[i] := by
  induction y generalizing f i with
  | nil => simp at hi
  | cons b y ih =>
      cases f with
      | nil => simp at h
      | cons a f =>
          cases i with
          | zero => rfl
          | succ i =>
              have hi' : i < y.length := by simp only [List.length_cons] at hi; omega
              have h' : y.length = f.length := by simpa using h
              simpa only [interleave, List.zip_cons_cons, List.flatMap_cons, List.cons_append,
                List.nil_append, show 2 * (i + 1) = 2 * i + 2 by omega,
                List.getElem?_cons_succ, List.getElem_cons_succ] using ih f h' i hi'

lemma interleave_getElem_flag (y f : Word) (h : y.length = f.length)
    (i : ℕ) (hi : i < f.length) : (interleave y f)[2 * i + 1]? = some f[i] := by
  induction y generalizing f i with
  | nil => simp only [List.length_nil] at h; omega
  | cons b y ih =>
      cases f with
      | nil => simp at hi
      | cons a f =>
          cases i with
          | zero => rfl
          | succ i =>
              have hi' : i < f.length := by simp only [List.length_cons] at hi; omega
              have h' : y.length = f.length := by simpa using h
              simpa only [interleave, List.zip_cons_cons, List.flatMap_cons, List.cons_append,
                List.nil_append, show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega,
                List.getElem?_cons_succ, List.getElem_cons_succ] using ih f h' i hi'

end APSCounting893.Main
end Component_6

section Component_7

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma foldStats_allZero (s : FlagStats) (pairs : List (Bool × Bool)) :
    (pairs.foldl (fun s p => s.update p.1 p.2) s).allZero =
      (s.allZero && pairs.all (fun p => !p.2)) := by
  induction pairs generalizing s with
  | nil => simp
  | cons p pairs ih =>
      rw [List.foldl_cons, ih]
      simp only [FlagStats.update, List.all_cons, Bool.and_assoc]

lemma foldStats_allOne (s : FlagStats) (pairs : List (Bool × Bool)) :
    (pairs.foldl (fun s p => s.update p.1 p.2) s).allOne =
      (s.allOne && pairs.all Prod.snd) := by
  induction pairs generalizing s with
  | nil => simp
  | cons p pairs ih =>
      rw [List.foldl_cons, ih]
      simp only [FlagStats.update, List.all_cons, Bool.and_assoc]

lemma foldStats_payloadZero (s : FlagStats) (pairs : List (Bool × Bool)) :
    (pairs.foldl (fun s p => s.update p.1 p.2) s).payloadZero =
      (s.payloadZero && pairs.all (fun p => !p.1)) := by
  induction pairs generalizing s with
  | nil => simp
  | cons p pairs ih =>
      rw [List.foldl_cons, ih]
      simp only [FlagStats.update, List.all_cons, Bool.and_assoc]

lemma foldStats_first_of_seen (s : FlagStats) (pairs : List (Bool × Bool)) (h : s.seen = true) :
    (pairs.foldl (fun s p => s.update p.1 p.2) s).first = s.first := by
  induction pairs generalizing s with
  | nil => rfl
  | cons p pairs ih => simpa [FlagStats.update, h] using ih (s.update p.1 p.2) rfl

lemma flagStats_first (b f : Bool) (y flags : Word) :
    (flagStats (b :: y) (f :: flags)).first = f := by
  unfold flagStats
  rw [List.zip_cons_cons, List.foldl_cons, foldStats_first_of_seen _ _ rfl]
  rfl

lemma flagStats_allOne (y flags : Word) (h : y.length = flags.length) :
    (flagStats y flags).allOne = flags.all id := by
  rw [flagStats, foldStats_allOne]
  simp only [Bool.true_and]
  induction y generalizing flags with
  | nil => have hf : flags = [] := List.length_eq_zero_iff.mp h.symm; subst flags; rfl
  | cons b y ih =>
      cases flags with
      | nil => simp at h
      | cons f flags => simp [ih flags (by simpa using h)]

lemma flagStats_allZero (y flags : Word) (h : y.length = flags.length) :
    (flagStats y flags).allZero = flags.all Bool.not := by
  rw [flagStats, foldStats_allZero]
  simp only [Bool.true_and]
  induction y generalizing flags with
  | nil => have hf : flags = [] := List.length_eq_zero_iff.mp h.symm; subst flags; rfl
  | cons b y ih =>
      cases flags with
      | nil => simp at h
      | cons f flags => simp [ih flags (by simpa using h)]

lemma flagStats_payloadZero (y flags : Word) (h : y.length = flags.length) :
    (flagStats y flags).payloadZero = y.all Bool.not := by
  rw [flagStats, foldStats_payloadZero]
  simp only [Bool.true_and]
  induction y generalizing flags with
  | nil => rfl
  | cons b y ih =>
      cases flags with
      | nil => simp at h
      | cons f flags => simp [ih flags (by simpa using h)]

lemma flagStats_take_succ (y flags : Word) (h : y.length = flags.length) (i : ℕ)
    (hi : i < y.length) : flagStats (y.take (i + 1)) (flags.take (i + 1)) =
      (flagStats (y.take i) (flags.take i)).update y[i] (flags[i]'(by omega)) := by
  unfold flagStats
  rw [List.take_succ_eq_append_getElem hi,
    List.take_succ_eq_append_getElem (by omega : i < flags.length),
    List.zip_append (by simp [h]), List.foldl_append]
  rfl

end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

structure PayloadInvariant (x y flags : Word) (i : ℕ) (s : FlagStats)
    (cfg : ProgramConfig QuantifierState 0 4) : Prop where
  state : cfg.state = .payload s
  answer : cfg.answer = none
  randomHead : (cfg.tapes 1).head = (2 * i + 1 : ℕ)
  randomRead : ∀ j : ℤ, (cfg.tapes 1).read j = (Tape.input (interleave y flags)).read j
  query : TapePrefix (cfg.tapes 2) (pairWord x (y.take i))

lemma quantifier_finish_input (u : Bool) (A : Language) (x y flags : Word)
    (cfg : ProgramConfig QuantifierState 0 4)
    (hc : InputPrefixInvariant x (interleave y flags) x.length cfg) :
    PayloadInvariant x y flags 0 {} ((quantifierProgram u).step A cfg) := by
  have hin : (cfg.tapes 0).read (cfg.tapes 0).head = .blank := by
    rw [hc.inputHead, hc.inputRead]
    simpa only [Nat.cast_add, Nat.cast_one, tape_input_read,
      dif_neg (by omega : ¬ x.length < x.length)]
  have hs : (quantifierProgram u).step A cfg =
      { cfg with state := .payload {}, tapes := fun j =>
        ((cfg.tapes j).step (if j = 2 then .bit false else (cfg.tapes j).read (cfg.tapes j).head)
          (if j = 2 then .right else .stay)) } := by
    simp [FiniteProgram.step, quantifierProgram, hc.state, hc.answer, hin]
  rw [hs]
  constructor
  · rfl
  · exact hc.answer
  · simpa [Tape.step] using hc.randomHead
  · intro j
    change (((cfg.tapes 1).step ((cfg.tapes 1).read (cfg.tapes 1).head) .stay).read j) = _
    rw [tape_step_same_reads, hc.randomRead]
  · have hq := hc.query.append false
    simpa [escapedWord, pairWord] using hq

lemma quantifier_payload_step (u : Bool) (A : Language) (x y flags : Word)
    (hlen : y.length = flags.length) (i : ℕ) (hi : i < y.length) (s : FlagStats)
    (cfg : ProgramConfig QuantifierState 0 4) (hc : PayloadInvariant x y flags i s cfg) :
    PayloadInvariant x y flags (i + 1) (s.update y[i] (flags[i]'(by omega)))
      ((quantifierProgram u).step A ((quantifierProgram u).step A cfg)) := by
  have hy : (cfg.tapes 1).read (cfg.tapes 1).head = .bit y[i] := by
    rw [hc.randomHead, hc.randomRead]
    simpa only [Nat.cast_add, Nat.cast_one] using
      tape_input_read_of_getElem (interleave y flags) (2 * i) y[i]
        (interleave_getElem_payload y flags hlen i hi)
  let cfg1 : ProgramConfig QuantifierState 0 4 :=
    { cfg with state := .flag s y[i], tapes := fun j =>
        ((cfg.tapes j).step (if j = 2 then .bit y[i] else (cfg.tapes j).read (cfg.tapes j).head)
          (if j = 1 ∨ j = 2 then .right else .stay)) }
  have hs1 : (quantifierProgram u).step A cfg = cfg1 := by
    simp [FiniteProgram.step, quantifierProgram, hc.state, hc.answer, hy, cfg1]
  have hf : (cfg1.tapes 1).read (cfg1.tapes 1).head = .bit (flags[i]'(by omega)) := by
    change (((cfg.tapes 1).step ((cfg.tapes 1).read (cfg.tapes 1).head) .right).read
      ((cfg.tapes 1).head + 1)) = _
    rw [tape_step_same_reads, hc.randomHead, hc.randomRead]
    exact tape_input_read_of_getElem (interleave y flags) (2 * i + 1) flags[i]
      (interleave_getElem_flag y flags hlen i (by omega))
  have hs2 : (quantifierProgram u).step A cfg1 =
      { cfg1 with state := .payload (s.update y[i] (flags[i]'(by omega))), tapes := fun j =>
        ((cfg1.tapes j).step ((cfg1.tapes j).read (cfg1.tapes j).head)
          (if j = 1 then .right else .stay)) } := by
    apply FiniteProgram.step_step
    · exact hc.answer
    · have hstate : cfg1.state = .flag s y[i] := rfl
      simp only [quantifierProgram, hstate, hf]
  rw [hs1, hs2]
  constructor
  · rfl
  · exact hc.answer
  · simp [cfg1, Tape.step, hc.randomHead]
    omega
  · intro j
    change (((cfg1.tapes 1).step ((cfg1.tapes 1).read (cfg1.tapes 1).head) .right).read j) = _
    rw [tape_step_same_reads]
    change (((cfg.tapes 1).step ((cfg.tapes 1).read (cfg.tapes 1).head) .right).read j) = _
    rw [tape_step_same_reads, hc.randomRead]
  · have hq := (hc.query.append y[i]).stay
    have hp : pairWord x (y.take (i + 1)) = pairWord x (y.take i) ++ [y[i]] := by
      simp only [pairWord]
      rw [List.take_succ_eq_append_getElem hi]
      simp only [List.append_assoc]
    rw [hp]
    exact hq

lemma quantifier_payload_run (u : Bool) (A : Language) (x y flags : Word)
    (hlen : y.length = flags.length) (i : ℕ) (hi : i ≤ y.length) :
    PayloadInvariant x y flags i (flagStats (y.take i) (flags.take i))
      ((quantifierProgram u).run A x (interleave y flags) (2 * x.length + 2 + 2 * i)) := by
  induction i with
  | zero =>
      have h := quantifier_finish_input u A x y flags _
        (quantifier_input_run u A x (interleave y flags) x.length le_rfl)
      rw [show 2 * x.length + 2 + 2 * 0 = (2 * x.length + 1) + 1 by omega,
        FiniteProgram.run_succ]
      exact h
  | succ i ih =>
      rw [show 2 * x.length + 2 + 2 * (i + 1) =
          (2 * x.length + 2 + 2 * i) + 1 + 1 by omega,
        FiniteProgram.run_succ, FiniteProgram.run_succ,
        flagStats_take_succ y flags hlen i (by omega)]
      exact quantifier_payload_step u A x y flags hlen i (by omega) _ _ (ih (by omega))

lemma quantifier_full_payload (u : Bool) (A : Language) (x y flags : Word)
    (hlen : y.length = flags.length) :
    PayloadInvariant x y flags y.length (flagStats y flags)
      ((quantifierProgram u).run A x (interleave y flags) (2 * x.length + 2 + 2 * y.length)) := by
  have hf : flags.take y.length = flags := List.take_of_length_le (by omega)
  simpa only [List.take_length, hf] using quantifier_payload_run u A x y flags hlen y.length le_rfl

end APSCounting893.Main
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma quantifier_finish_payload (u : Bool) (A : Language) (x y flags : Word)
    (hlen : y.length = flags.length) (s : FlagStats)
    (cfg : ProgramConfig QuantifierState 0 4) (hc : PayloadInvariant x y flags y.length s cfg) :
    ((quantifierProgram u).step A ((quantifierProgram u).step A cfg)).answer =
      some (quantifierDecision u s (@decide (A (pairWord x y)) (Classical.propDecidable _))) := by
  classical
  have hr : (cfg.tapes 1).read (cfg.tapes 1).head = .blank := by
    rw [hc.randomHead, hc.randomRead]
    have hlength := interleave_length y flags hlen
    simpa only [Nat.cast_add, Nat.cast_one, tape_input_read,
      dif_neg (by omega : ¬ 2 * y.length < (interleave y flags).length)]
  have hq : (cfg.tapes 2).word = pairWord x y := by
    simpa only [List.take_length] using hc.query.word
  cases hb : quantifierBaseline u s <;> cases ho : s.allOne <;>
    by_cases hA : A (pairWord x y) <;>
      simp [FiniteProgram.step, quantifierProgram, hc.state, hc.answer, hr, hq,
        quantifierDecision, hb, ho, hA]

lemma quantifier_run_answer (u : Bool) (A : Language) (x y flags : Word)
    (hlen : y.length = flags.length) :
    ((quantifierProgram u).run A x (interleave y flags) (2 * x.length + 2 * y.length + 4)).answer =
      some (quantifierDecision u (flagStats y flags)
        (@decide (A (pairWord x y)) (Classical.propDecidable _))) := by
  rw [show 2 * x.length + 2 * y.length + 4 =
      (2 * x.length + 2 + 2 * y.length) + 1 + 1 by omega,
    FiniteProgram.run_succ, FiniteProgram.run_succ]
  exact quantifier_finish_payload u A x y flags hlen _ _ (quantifier_full_payload u A x y flags hlen)

end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma quantifier_time_bound (a b n : ℕ) :
    2 * n + 2 * polyBound a b n + 4 ≤ polyBound (2 * a + 6) (b + 1) n := by
  have hP : 1 ≤ (n + 1) ^ b := Nat.one_le_pow _ _ (by omega)
  have hscale : a * (n + 1) ^ b ≤ a * (n + 1) ^ b * (n + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hn : n + 1 ≤ (n + 1) ^ b * (n + 1) := Nat.le_mul_of_pos_left _ hP
  simp only [polyBound, pow_succ]
  nlinarith

lemma quantifier_compiled_answer (u : Bool) (A : Language) (x y flags : Word)
    (hlen : y.length = flags.length) (a b : ℕ) (hy : y.length = polyBound a b x.length) :
    (machineRun (quantifierProgram u).compile A x (interleave y flags)
      (polyBound (2 * a + 6) (b + 1) x.length)).answer =
      some (quantifierDecision u (flagStats y flags)
        (@decide (A (pairWord x y)) (Classical.propDecidable _))) := by
  have hanswer : (machineRun (quantifierProgram u).compile A x (interleave y flags)
      (2 * x.length + 2 * y.length + 4)).answer =
      some (quantifierDecision u (flagStats y flags)
        (@decide (A (pairWord x y)) (Classical.propDecidable _))) := by
    rw [FiniteProgram.compile_run]
    exact quantifier_run_answer u A x y flags hlen
  have hle : 2 * x.length + 2 * y.length + 4 ≤
      polyBound (2 * a + 6) (b + 1) x.length := by rw [hy]; exact quantifier_time_bound a b x.length
  have hhalt : (machineRun (quantifierProgram u).compile A x (interleave y flags)
      (2 * x.length + 2 * y.length + 4)).answer.isSome := by rw [hanswer]; rfl
  have heq := machineRun_halted_persistent (quantifierProgram u).compile A x (interleave y flags)
    (2 * x.length + 2 * y.length + 4)
    (polyBound (2 * a + 6) (b + 1) x.length - (2 * x.length + 2 * y.length + 4)) hhalt
  rw [Nat.add_sub_of_le hle] at heq
  rw [heq, hanswer]

lemma quantifier_runs_in_time (u : Bool) (A : Language) (a b : ℕ) :
    RunsInTime (quantifierProgram u).compile A (2 * a + 6) (b + 1) (2 * a) b := by
  intro x w hw
  have hw' : w.length = 2 * polyBound a b x.length := by simpa only [polyBound, Nat.mul_assoc] using hw
  obtain ⟨hy, hf, hinter⟩ := splitSeed_length (polyBound a b x.length) w hw'
  rw [← hinter, quantifier_compiled_answer u A x _ _ (hy.trans hf.symm) a b hy]
  rfl

end APSCounting893.Main
end Component_10

section Component_11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

abbrev BitTuple (p : ℕ) := Fin p → Bool

def firstFalseFlags (p : ℕ) : Set (BitTuple (p + 1)) := {f | f 0 = false}

lemma firstFalseFlags_ncard (p : ℕ) : (firstFalseFlags p).ncard = 2 ^ p := by
  have hr : firstFalseFlags p = Set.range (fun f : BitTuple p => Fin.cons false f) := by
    ext f
    constructor
    · intro hf
      refine ⟨Fin.tail f, ?_⟩
      have hf' : f 0 = false := hf
      rw [← hf']
      exact Fin.cons_self_tail f
    · rintro ⟨g, rfl⟩
      rfl
  rw [hr, ← Set.image_univ, Set.ncard_image_of_injective]
  · simp [Nat.card_eq_fintype_card]
  · intro f g h
    simpa only [Fin.tail_cons] using congrArg Fin.tail h

noncomputable def existentialSeedSet (p : ℕ) (good : Set (BitTuple (p + 1))) :
    Set (BitTuple (p + 1) × BitTuple (p + 1)) :=
  ((Set.univ : Set (BitTuple (p + 1))) ×ˢ firstFalseFlags p) ∪ (good ×ˢ {fun _ => true})

lemma existentialSeedSet_ncard (p : ℕ) (good : Set (BitTuple (p + 1))) :
    (existentialSeedSet p good).ncard = 2 ^ (p + 1) * 2 ^ p + good.ncard := by
  have hd : Disjoint ((Set.univ : Set (BitTuple (p + 1))) ×ˢ firstFalseFlags p) (good ×ˢ {fun _ => true}) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hf : z.2 0 = false := hz.2
    have hone : z.2 = fun _ => true := hz'.2
    simp [hone] at hf
  rw [existentialSeedSet, Set.ncard_union_eq hd, Set.ncard_prod, Set.ncard_prod,
    firstFalseFlags_ncard]
  simp [Nat.card_eq_fintype_card]

lemma existentialSeedSet_majority (p : ℕ) (good : Set (BitTuple (p + 1))) :
    2 ^ (2 * (p + 1)) < 2 * (existentialSeedSet p good).ncard ↔ good.Nonempty := by
  rw [existentialSeedSet_ncard]
  have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by simp [pow_succ, Nat.mul_comm]
  have hsquare : 2 ^ (2 * (p + 1)) = 2 ^ (p + 1) * 2 ^ (p + 1) := by rw [two_mul, pow_add]
  rw [← Set.ncard_pos]
  rw [hsquare, hpow]
  constructor <;> intro h <;> nlinarith

noncomputable def universalSeedSet (p : ℕ) (good : Set (BitTuple (p + 1))) :
    Set (BitTuple (p + 1) × BitTuple (p + 1)) :=
  (((Set.univ : Set (BitTuple (p + 1))) ×ˢ (firstFalseFlags p \ {fun _ => false})) ∪
    {(fun _ => false, fun _ => false)}) ∪ (good ×ˢ {fun _ => true})

lemma universalSeedSet_ncard (p : ℕ) (good : Set (BitTuple (p + 1))) :
    (universalSeedSet p good).ncard = 2 ^ (p + 1) * (2 ^ p - 1) + 1 + good.ncard := by
  have hd1 : Disjoint ((Set.univ : Set (BitTuple (p + 1))) ×ˢ (firstFalseFlags p \ {fun _ => false}))
      {(fun _ => false, fun _ => false)} := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have heq : z = (fun _ => false, fun _ => false) := hz'
    subst z
    exact hz.2.2 rfl
  have hd2 : Disjoint (((Set.univ : Set (BitTuple (p + 1))) ×ˢ (firstFalseFlags p \ {fun _ => false})) ∪
      {(fun _ => false, fun _ => false)}) (good ×ˢ {fun _ => true}) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hone : z.2 = fun _ => true := hz'.2
    rcases hz with hz | hz
    · have hf : z.2 0 = false := hz.2.1
      simp [hone] at hf
    · have heq : z = (fun _ => false, fun _ => false) := hz
      subst z
      have hbad := congrFun hone 0
      cases hbad
  have hzero : {fun _ : Fin (p + 1) => false} ⊆ firstFalseFlags p := by
    intro f hf
    have heq : f = fun _ => false := hf
    simp [firstFalseFlags, heq]
  rw [universalSeedSet, Set.ncard_union_eq hd2, Set.ncard_union_eq hd1,
    Set.ncard_prod, Set.ncard_prod, Set.ncard_sdiff hzero, firstFalseFlags_ncard]
  simp [Nat.card_eq_fintype_card]

lemma universalSeedSet_majority (p : ℕ) (good : Set (BitTuple (p + 1))) :
    2 ^ (2 * (p + 1)) < 2 * (universalSeedSet p good).ncard ↔
      ∀ y, y ∈ good := by
  have hgood : good.ncard ≤ 2 ^ (p + 1) := by
    simpa [Nat.card_eq_fintype_card] using Set.ncard_le_ncard (Set.subset_univ good)
  have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by simp [pow_succ, Nat.mul_comm]
  have hsquare : 2 ^ (2 * (p + 1)) = 2 ^ (p + 1) * 2 ^ (p + 1) := by rw [two_mul, pow_add]
  have hpos : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by decide)
  rw [universalSeedSet_ncard, hsquare]
  constructor
  · intro h
    have heq : good.ncard = 2 ^ (p + 1) := by
      have hsub : 2 ^ p - 1 + 1 = 2 ^ p := Nat.sub_add_cancel hpos
      nlinarith
    have hfull : good = Set.univ := Set.eq_of_subset_of_ncard_le (Set.subset_univ good)
      (by simpa [Nat.card_eq_fintype_card, heq])
    simp [hfull]
  · intro h
    have hfull : good = Set.univ := Set.eq_univ_of_forall h
    have hc : good.ncard = 2 ^ (p + 1) := by simp [hfull, Nat.card_eq_fintype_card]
    have hsub : 2 ^ p - 1 + 1 = 2 ^ p := Nat.sub_add_cancel hpos
    nlinarith

end APSCounting893.Main
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma flagStats_tuple_first (p : ℕ) (y f : BitTuple (p + 1)) :
    (flagStats (List.ofFn y) (List.ofFn f)).first = f 0 := by
  rw [List.ofFn_succ, List.ofFn_succ, flagStats_first]

lemma flagStats_tuple_allOne (p : ℕ) (y f : BitTuple (p + 1)) :
    (flagStats (List.ofFn y) (List.ofFn f)).allOne = true ↔ f = fun _ => true := by
  rw [flagStats_allOne _ _ (by simp), List.all_eq_true]
  constructor
  · intro h
    funext i
    exact h (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h
    subst f
    simp

lemma flagStats_tuple_allZero (p : ℕ) (y f : BitTuple (p + 1)) :
    (flagStats (List.ofFn y) (List.ofFn f)).allZero = true ↔ f = fun _ => false := by
  rw [flagStats_allZero _ _ (by simp), List.all_eq_true]
  constructor
  · intro h
    funext i
    simpa using h (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h
    subst f
    simp

lemma flagStats_tuple_payloadZero (p : ℕ) (y f : BitTuple (p + 1)) :
    (flagStats (List.ofFn y) (List.ofFn f)).payloadZero = true ↔ y = fun _ => false := by
  rw [flagStats_payloadZero _ _ (by simp), List.all_eq_true]
  constructor
  · intro h
    funext i
    simpa using h (y i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h
    subst y
    simp


lemma quantifierDecision_eq_true (u : Bool) (s : FlagStats) (b : Bool) :
    quantifierDecision u s b = true ↔
      quantifierBaseline u s = true ∨ (s.allOne = true ∧ b = true) := by
  cases hb : quantifierBaseline u s <;> cases ho : s.allOne <;> cases b <;>
    simp [quantifierDecision, hb, ho]

lemma existential_decision_iff (p : ℕ) (A : Language) (x : Word)
    (y f : BitTuple (p + 1)) :
    quantifierDecision false (flagStats (List.ofFn y) (List.ofFn f))
      (@decide (A (pairWord x (List.ofFn y))) (Classical.propDecidable _)) = true ↔
      (y, f) ∈ existentialSeedSet p {y | A (pairWord x (List.ofFn y))} := by
  classical
  rw [quantifierDecision_eq_true]
  simp only [quantifierBaseline, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true_eq_eq_false,
    flagStats_tuple_first, flagStats_tuple_allOne, decide_eq_true_eq,
    existentialSeedSet, firstFalseFlags, Set.mem_union, Set.mem_prod, Set.mem_univ,
    Set.mem_singleton_iff, Set.mem_setOf_eq, true_and]
  tauto

lemma universal_decision_iff (p : ℕ) (A : Language) (x : Word)
    (y f : BitTuple (p + 1)) :
    quantifierDecision true (flagStats (List.ofFn y) (List.ofFn f))
      (@decide (A (pairWord x (List.ofFn y))) (Classical.propDecidable _)) = true ↔
      (y, f) ∈ universalSeedSet p {y | A (pairWord x (List.ofFn y))} := by
  classical
  rw [quantifierDecision_eq_true]
  simp only [quantifierBaseline, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false,
    flagStats_tuple_first, flagStats_tuple_allOne, flagStats_tuple_allZero,
    flagStats_tuple_payloadZero, decide_eq_true_eq,
    universalSeedSet, firstFalseFlags, Set.mem_union, Set.mem_prod, Set.mem_univ,
    Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_diff, true_and, Prod.mk.injEq]
  have hz : (flagStats (List.ofFn y) (List.ofFn f)).allZero = false ↔
      f ≠ fun _ => false := by
    have hb : (flagStats (List.ofFn y) (List.ofFn f)).allZero = false ↔
        ¬ (flagStats (List.ofFn y) (List.ofFn f)).allZero = true := by
      cases (flagStats (List.ofFn y) (List.ofFn f)).allZero <;> simp
    exact hb.trans (not_congr (flagStats_tuple_allZero p y f))
  rw [hz]
  tauto

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def quantifierSeedSet (u : Bool) (p : ℕ) (good : Set (BitTuple (p + 1))) :=
  if u then universalSeedSet p good else existentialSeedSet p good

lemma decision_seedSet_iff (u : Bool) (p : ℕ) (A : Language) (x : Word)
    (y f : BitTuple (p + 1)) :
    quantifierDecision u (flagStats (List.ofFn y) (List.ofFn f))
      (@decide (A (pairWord x (List.ofFn y))) (Classical.propDecidable _)) = true ↔
      (y, f) ∈ quantifierSeedSet u p {y | A (pairWord x (List.ofFn y))} := by
  cases u
  · exact existential_decision_iff p A x y f
  · exact universal_decision_iff p A x y f

lemma quantifier_accepting_set (u : Bool) (A : Language) (x : Word) (a b p : ℕ)
    (hp : polyBound a b x.length = p + 1) :
    {w : Word | w.length = polyBound (2 * a) b x.length ∧
      (machineRun (quantifierProgram u).compile A x w
        (polyBound (2 * a + 6) (b + 1) x.length)).answer = some true} =
      (fun z : BitTuple (p + 1) × BitTuple (p + 1) =>
        interleave (List.ofFn z.1) (List.ofFn z.2)) ''
          quantifierSeedSet u p {y | A (pairWord x (List.ofFn y))} := by
  classical
  have hlenpoly : polyBound (2 * a) b x.length = 2 * (p + 1) := by
    rw [show polyBound (2 * a) b x.length = 2 * polyBound a b x.length by
      simp only [polyBound, Nat.mul_assoc], hp]
  ext w
  constructor
  · rintro ⟨hw, ha⟩
    have hw' : w.length = 2 * (p + 1) := hw.trans hlenpoly
    obtain ⟨hy, hf, hinter⟩ := splitSeed_length (p + 1) w hw'
    have hys : (splitSeed w).1 ∈ Set.range (fun y : BitTuple (p + 1) => List.ofFn y) := by
      rw [← words_length_eq_range]
      exact hy
    have hfs : (splitSeed w).2 ∈ Set.range (fun f : BitTuple (p + 1) => List.ofFn f) := by
      rw [← words_length_eq_range]
      exact hf
    obtain ⟨y, hyof⟩ := hys
    obtain ⟨f, hfof⟩ := hfs
    have hwrepr : interleave (List.ofFn y) (List.ofFn f) = w := by
      change List.ofFn y = (splitSeed w).1 at hyof
      change List.ofFn f = (splitSeed w).2 at hfof
      rw [hyof, hfof]
      exact hinter
    refine ⟨(y, f), ?_, hwrepr⟩
    apply (decision_seedSet_iff u p A x y f).mp
    rw [← hwrepr, quantifier_compiled_answer u A x _ _ (by simp) a b (by simp [hp])] at ha
    exact Option.some.inj ha
  · rintro ⟨⟨y, f⟩, hz, rfl⟩
    constructor
    · rw [interleave_length _ _ (by simp)]
      simpa only [List.length_ofFn] using hlenpoly.symm
    · rw [quantifier_compiled_answer u A x _ _ (by simp) a b (by simp [hp])]
      exact congrArg some ((decision_seedSet_iff u p A x y f).mpr hz)

lemma bounded_exists_inOraclePP (A : Language) (a b : ℕ) (ha : 0 < a) :
    InOraclePP A (fun x => ∃ y : Word, y.length = polyBound a b x.length ∧ A (pairWord x y)) := by
  refine ⟨(quantifierProgram false).compile, 2 * a + 6, b + 1, 2 * a, b,
    quantifier_runs_in_time false A a b, ?_⟩
  intro x
  have hpos : 0 < polyBound a b x.length := by
    unfold polyBound
    exact Nat.mul_pos ha (Nat.pow_pos (by omega))
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  change polyBound a b x.length = p + 1 at hp
  rw [quantifier_accepting_set false A x a b p hp,
    Set.ncard_image_of_injective _ (interleave_functions_injective (p + 1))]
  have hlen : polyBound (2 * a) b x.length = 2 * (p + 1) := by
    rw [show polyBound (2 * a) b x.length = 2 * polyBound a b x.length by
      simp only [polyBound, Nat.mul_assoc], hp]
  rw [hlen]
  change _ ↔ 2 ^ (2 * (p + 1)) < 2 *
    (existentialSeedSet p {y | A (pairWord x (List.ofFn y))}).ncard
  rw [existentialSeedSet_majority]
  constructor
  · rintro ⟨y, hy, hA⟩
    have hy' : y ∈ Set.range (fun f : BitTuple (p + 1) => List.ofFn f) := by
      rw [← words_length_eq_range]
      exact hy.trans hp
    obtain ⟨f, rfl⟩ := hy'
    exact ⟨f, hA⟩
  · rintro ⟨f, hf⟩
    exact ⟨List.ofFn f, by simp only [List.length_ofFn, hp], hf⟩

lemma bounded_forall_inOraclePP (A : Language) (a b : ℕ) (ha : 0 < a) :
    InOraclePP A (fun x => ∀ y : Word, y.length = polyBound a b x.length → A (pairWord x y)) := by
  refine ⟨(quantifierProgram true).compile, 2 * a + 6, b + 1, 2 * a, b,
    quantifier_runs_in_time true A a b, ?_⟩
  intro x
  have hpos : 0 < polyBound a b x.length := by
    unfold polyBound
    exact Nat.mul_pos ha (Nat.pow_pos (by omega))
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  change polyBound a b x.length = p + 1 at hp
  rw [quantifier_accepting_set true A x a b p hp,
    Set.ncard_image_of_injective _ (interleave_functions_injective (p + 1))]
  have hlen : polyBound (2 * a) b x.length = 2 * (p + 1) := by
    rw [show polyBound (2 * a) b x.length = 2 * polyBound a b x.length by
      simp only [polyBound, Nat.mul_assoc], hp]
  rw [hlen]
  change _ ↔ 2 ^ (2 * (p + 1)) < 2 *
    (universalSeedSet p {y | A (pairWord x (List.ofFn y))}).ncard
  rw [universalSeedSet_majority]
  constructor
  · intro h f
    exact h (List.ofFn f) (by simp only [List.length_ofFn, hp])
  · intro h y hy
    have hy' : y ∈ Set.range (fun f : BitTuple (p + 1) => List.ofFn f) := by
      rw [← words_length_eq_range]
      exact hy.trans hp
    obtain ⟨f, rfl⟩ := hy'
    exact h f

lemma AtCHLevel.bounded_exists {A : Language} {j : ℕ} (hA : AtCHLevel j A)
    (a b : ℕ) (ha : 0 < a) : AtCHLevel (j + 1)
      (fun x => ∃ y : Word, y.length = polyBound a b x.length ∧ A (pairWord x y)) :=
  ⟨A, hA, bounded_exists_inOraclePP A a b ha⟩

lemma AtCHLevel.bounded_forall {A : Language} {j : ℕ} (hA : AtCHLevel j A)
    (a b : ℕ) (ha : 0 < a) : AtCHLevel (j + 1)
      (fun x => ∀ y : Word, y.length = polyBound a b x.length → A (pairWord x y)) :=
  ⟨A, hA, bounded_forall_inOraclePP A a b ha⟩

end APSCounting893.Main
end Component_13

theorem solution
    (A : APSCounting893.Main.Language) (a b : ℕ) (ha : 0 < a) :
    APSCounting893.Main.InOraclePP A (fun x => ∃ y : APSCounting893.Main.Word,
      y.length = APSCounting893.Main.polyBound a b x.length ∧ A (APSCounting893.Main.pairWord x y)) ∧
    APSCounting893.Main.InOraclePP A (fun x => ∀ y : APSCounting893.Main.Word,
      y.length = APSCounting893.Main.polyBound a b x.length → A (APSCounting893.Main.pairWord x y)) := by
  exact ⟨APSCounting893.Main.bounded_exists_inOraclePP A a b ha, APSCounting893.Main.bounded_forall_inOraclePP A a b ha⟩
