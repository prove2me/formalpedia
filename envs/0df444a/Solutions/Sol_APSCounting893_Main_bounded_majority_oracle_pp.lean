-- Prove2me | solution 1 for APSCounting893.Main.bounded_majority_oracle_pp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T19:46:20.427192+00:00
-- url     : https://prove2.me/submissions/0f73e97f-afb6-4ec0-beca-84eebdfee454

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

/-- A stack occupies the cells before a fixed blank boundary, with its top under the head. -/
structure StackTape {a : ℕ} (t : Tape a) (boundary : ℤ) (w : Word) : Prop where
  head : t.head = boundary - w.length
  read : ∀ (j : ℕ) (hj : j < w.length), t.read (t.head + j) = .bit w[j]
  bottom : t.read boundary = .blank

lemma StackTape.top {a : ℕ} {t : Tape a} {boundary : ℤ} {b : Bool} {w : Word}
    (h : StackTape t boundary (b :: w)) : t.read t.head = .bit b := by
  have ht := h.read 0 (by simp)
  change t.read (t.head + 0) = .bit b at ht
  simpa only [add_zero] using ht

lemma StackTape.empty {a : ℕ} {t : Tape a} {boundary : ℤ}
    (h : StackTape t boundary []) : t.read t.head = .blank := by
  simpa [h.head] using h.bottom

lemma StackTape.pop {a : ℕ} {t : Tape a} {boundary : ℤ} {b : Bool} {w : Word}
    (h : StackTape t boundary (b :: w)) : StackTape (t.step .blank .right) boundary w := by
  constructor
  · have hh := h.head
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hh
    change t.head + 1 = boundary - w.length
    omega
  · intro j hj
    have hne : t.head + 1 + (j : ℤ) ≠ t.head := by omega
    change (t.step .blank .right).read (t.head + 1 + j) = _
    rw [tape_step_read_ne _ _ _ _ hne]
    have hj' : j + 1 < (b :: w).length := by simp; omega
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm,
      List.getElem_cons_succ] using h.read (j + 1) hj'
  · apply (tape_step_read_ne t _ _ boundary (by have := h.head; simp at this; omega)).trans
    exact h.bottom

lemma StackTape.push {a : ℕ} {t : Tape a} {boundary : ℤ} {w : Word}
    (h : StackTape t boundary w) (b : Bool) :
    StackTape ((t.step (t.read t.head) .left).step (.bit b) .stay) boundary (b :: w) := by
  constructor
  · simp only [Tape.step, List.length_cons]
    have hh := h.head
    push_cast at hh ⊢
    omega
  · intro j hj
    rw [tape_step_head_stay, tape_step_head_left]
    cases j with
    | zero =>
        simpa only [Nat.cast_zero, add_zero, tape_step_head_left, List.getElem_cons_zero] using
          tape_step_read_self (t.step (t.read t.head) .left) (.bit b) .stay
    | succ j =>
        have hj' : j < w.length := by simpa using hj
        change ((t.step (t.read t.head) .left).step (.bit b) .stay).read
          (t.head - 1 + (j + 1 : ℕ)) = _
        rw [tape_step_read_ne]
        · rw [tape_step_same_reads]
          have heq : t.head - 1 + ((j + 1 : ℕ) : ℤ) = t.head + j := by push_cast; omega
          rw [heq]
          exact h.read j hj'
        · simp only [Tape.step]
          push_cast
          omega
  · rw [tape_step_read_ne]
    · rw [tape_step_same_reads]
      exact h.bottom
    · simp only [Tape.step]
      have hh := h.head
      omega

lemma stackTape_input {a : ℕ} (w : Word) :
    StackTape ((Tape.input (a := a) w).step ((Tape.input w).read 0) .right)
      (w.length + 1) w := by
  constructor
  · simp [Tape.step, Tape.input]
  · intro j hj
    have hr := tape_step_same_reads (Tape.input (a := a) w) .right (1 + (j : ℤ))
    change ((Tape.input w).step ((Tape.input w).read 0) .right).read _ = _ at hr
    change ((Tape.input w).step ((Tape.input w).read 0) .right).read (1 + (j : ℤ)) = _
    rw [hr]
    simpa only [add_comm, tape_input_read, dif_pos hj]
  · have hr := tape_step_same_reads (Tape.input (a := a) w) .right ((w.length : ℤ) + 1)
    change ((Tape.input w).step ((Tape.input w).read 0) .right).read _ = _ at hr
    rw [hr]
    simpa only [tape_input_read, dif_neg (by omega : ¬ w.length < w.length)]

lemma StackTape.stay {a : ℕ} {t : Tape a} {boundary : ℤ} {w : Word}
    (h : StackTape t boundary w) : StackTape (t.step (t.read t.head) .stay) boundary w := by
  constructor
  · simpa only [tape_step_head_stay] using h.head
  · intro j hj
    rw [tape_step_head_stay, tape_step_same_reads]
    exact h.read j hj
  · rw [tape_step_same_reads]
    exact h.bottom

lemma stackTape_empty {a : ℕ} : StackTape ((Tape.mk [] 0 : Tape a).step .blank .right) 1 [] := by
  constructor
  · rfl
  · intro j hj; simp at hj
  · rw [tape_step_read_ne]
    · rfl
    · change (1 : ℤ) ≠ 0
      omega

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
namespace APSCounting893.Main
def stackRegisterTape {r : ℕ} (j : Fin (r + 2)) : Fin (r + 4) :=
  ⟨if j.val < 2 then j.val else j.val + 2, by split_ifs <;> omega⟩

lemma stackRegisterTape_injective (r : ℕ) : Function.Injective (@stackRegisterTape r) := by
  intro j k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [stackRegisterTape] at hv
  split_ifs at hv <;> omega

lemma stackRegisterTape_ne_query {r : ℕ} (j : Fin (r + 2)) : stackRegisterTape j ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  change (if j.val < 2 then j.val else j.val + 2) = 2 % (r + 4) at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  split_ifs at hv <;> omega

inductive StackControl (Q : Type) (r : ℕ) where
  | initial
  | execute (q : Q)
  | pushFinish (reg : Fin (r + 2)) (bit : Bool) (next : Q)
  | copyQuery (reg : Fin (r + 2)) (yes no : Q)
  | clearStart (next : Q)
  | clearQuery (next : Q)
  deriving DecidableEq, Fintype

def stackCopyAction {Q : Type} {r : ℕ} (reg : Fin (r + 2)) (yes no : Q)
    (s : Fin (r + 4) → TapeSymbol 0) : ProgramAction (StackControl Q r) 0 (r + 4) :=
  match s (stackRegisterTape reg) with
  | .bit b => .step (.copyQuery reg yes no)
      (fun j => if j = stackRegisterTape reg then .blank else if j = 2 then .bit b else s j)
      (fun j => if j = stackRegisterTape reg ∨ j = 2 then .right else .stay)
  | _ => .query (.clearStart yes) (.clearStart no)

noncomputable def StackProgram.compile {Q : Type} {r : ℕ} (P : StackProgram Q r) :
    FiniteProgram (StackControl Q r) 0 (r + 4) where
  inputTape := 0
  randomTape := 1
  queryTape := 2
  outputTape := 3
  distinctTapes := by
    intro i j h
    have hv := congrArg Fin.val h
    have h2 : 2 % (r + 4) = 2 := Nat.mod_eq_of_lt (by omega)
    have h3 : 3 % (r + 4) = 3 := Nat.mod_eq_of_lt (by omega)
    fin_cases i <;> fin_cases j
    all_goals first | rfl | (exfalso; norm_num [h2, h3] at hv)
  initial := .initial
  transition := fun q s => match q with
    | .initial => .step (.execute P.initial) s (fun _ => .right)
    | .execute q => match P.transition q with
      | .jump next => .step (.execute next) s (fun _ => .stay)
      | .peek reg zero one empty =>
          let next := match s (stackRegisterTape reg) with
            | .bit false => zero | .bit true => one | _ => empty
          .step (.execute next) s (fun _ => .stay)
      | .pop reg zero one empty =>
          match s (stackRegisterTape reg) with
          | .bit b => .step (.execute (if b then one else zero))
              (fun j => if j = stackRegisterTape reg then .blank else s j)
              (fun j => if j = stackRegisterTape reg then .right else .stay)
          | _ => .step (.execute empty) s (fun _ => .stay)
      | .push reg b next => .step (.pushFinish reg b next) s
          (fun j => if j = stackRegisterTape reg then .left else .stay)
      | .query reg yes no => stackCopyAction reg yes no s
      | .halt b => .halt b
    | .pushFinish reg b next => .step (.execute next)
        (fun j => if j = stackRegisterTape reg then .bit b else s j) (fun _ => .stay)
    | .copyQuery reg yes no => stackCopyAction reg yes no s
    | .clearStart next => .step (.clearQuery next) s (fun j => if j = 2 then .left else .stay)
    | .clearQuery next => match s 2 with
        | .bit _ => .step (.clearQuery next) (fun j => if j = 2 then .blank else s j)
            (fun j => if j = 2 then .left else .stay)
        | _ => .step (.execute next) s (fun j => if j = 2 then .right else .stay)


end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_reverse_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src dst : Fin (r + 2)) (hne : src ≠ dst) (loop zero one finish : Q)
    (hloop : P.transition loop = .pop src zero one finish)
    (hzero : P.transition zero = .push dst false loop)
    (hone : P.transition one = .push dst true loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) :
    P.exec A cfg (2 * w.length + 1) =
      { state := finish,
        regs := Function.update (Function.update cfg.regs src []) dst (w.reverse ++ cfg.regs dst),
        answer := none } := by
  classical
  induction w generalizing cfg with
  | nil =>
      change P.step A cfg = _
      have hup : Function.update cfg.regs src [] = cfg.regs := by
        rw [← hw]
        exact Function.update_eq_self src cfg.regs
      simp [StackProgram.step, hs, ha, hloop, hw, hup]
  | cons b w ih =>
      let next := if b then one else zero
      let cfg1 : StackConfig Q r :=
        { state := next, regs := Function.update cfg.regs src w, answer := none }
      let cfg2 : StackConfig Q r :=
        { state := loop, regs := Function.update (Function.update cfg.regs src w) dst (b :: cfg.regs dst), answer := none }
      have hstep1 : P.step A cfg = cfg1 := by
        cases b <;> simp [StackProgram.step, hs, ha, hloop, hw, cfg1, next]
      have hstep2 : P.step A cfg1 = cfg2 := by
        cases b <;> simp [StackProgram.step, cfg1, cfg2, next, hzero, hone, Ne.symm hne]
      have hsrc : cfg2.regs src = w := by simp [cfg2, hne]
      have hrec := ih cfg2 rfl rfl hsrc
      have htime : 2 * (b :: w).length + 1 = 1 + (1 + (2 * w.length + 1)) := by simp; omega
      rw [htime, StackProgram.exec_add, StackProgram.exec_one, hstep1,
        StackProgram.exec_add, StackProgram.exec_one, hstep2, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j
        simp [cfg2, Function.update, hne, Ne.symm hne]
      · by_cases hjd : j = dst
        · subst j
          simp [cfg2, Function.update, hne, Ne.symm hne, List.reverse_cons, List.append_assoc]
        · simp [cfg2, Function.update, hjs, hjd]

lemma stack_map_reverse_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (f : Bool → Bool) (src dst : Fin (r + 2)) (hne : src ≠ dst) (loop zero one finish : Q)
    (hloop : P.transition loop = .pop src zero one finish)
    (hzero : P.transition zero = .push dst (f false) loop)
    (hone : P.transition one = .push dst (f true) loop)
    (cfg : StackConfig Q r) (hs : cfg.state = loop) (ha : cfg.answer = none)
    (w : Word) (hw : cfg.regs src = w) :
    P.exec A cfg (2 * w.length + 1) =
      { state := finish,
        regs := Function.update (Function.update cfg.regs src []) dst ((w.map f).reverse ++ cfg.regs dst),
        answer := none } := by
  classical
  induction w generalizing cfg with
  | nil =>
      change P.step A cfg = _
      have hup : Function.update cfg.regs src [] = cfg.regs := by
        rw [← hw]
        exact Function.update_eq_self src cfg.regs
      simp [StackProgram.step, hs, ha, hloop, hw, hup]
  | cons b w ih =>
      let next := if b then one else zero
      let cfg1 : StackConfig Q r :=
        { state := next, regs := Function.update cfg.regs src w, answer := none }
      let cfg2 : StackConfig Q r :=
        { state := loop, regs := Function.update (Function.update cfg.regs src w) dst (f b :: cfg.regs dst), answer := none }
      have hstep1 : P.step A cfg = cfg1 := by
        cases b <;> simp [StackProgram.step, hs, ha, hloop, hw, cfg1, next]
      have hstep2 : P.step A cfg1 = cfg2 := by
        cases b <;> simp [StackProgram.step, cfg1, cfg2, next, hzero, hone, Ne.symm hne]
      have hsrc : cfg2.regs src = w := by simp [cfg2, hne]
      have hrec := ih cfg2 rfl rfl hsrc
      have htime : 2 * (b :: w).length + 1 = 1 + (1 + (2 * w.length + 1)) := by simp; omega
      rw [htime, StackProgram.exec_add, StackProgram.exec_one, hstep1,
        StackProgram.exec_add, StackProgram.exec_one, hstep2, hrec]
      congr 1
      funext j
      by_cases hjs : j = src
      · subst j
        simp [cfg2, Function.update, hne, Ne.symm hne]
      · by_cases hjd : j = dst
        · subst j
          simp [cfg2, Function.update, hne, Ne.symm hne, List.map_cons, List.reverse_cons, List.append_assoc]
        · simp [cfg2, Function.update, hjs, hjd]

end APSCounting893.Main
end Component_5

section Component_6
namespace APSCounting893.Main
lemma pairWord_length (x y : Word) : (pairWord x y).length=2*x.length+1+y.length := by
  simp [pairWord,List.length_flatMap,List.sum_replicate,Nat.mul_comm,Nat.add_assoc,Nat.add_comm]
end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_escaped_prefix_routine {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (src dst : Fin (r+2)) (hne : src ≠ dst) (loop zero one flag finish : Q)
    (hloop : P.transition loop=.pop src zero one finish)
    (hzero : P.transition zero=.push dst false flag)
    (hone : P.transition one=.push dst true flag)
    (hflag : P.transition flag=.push dst true loop)
    (cfg : StackConfig Q r) (hs : cfg.state=loop) (ha : cfg.answer=none)
    (w : Word) (hw : cfg.regs src=w) :
    P.exec A cfg (3*w.length+1) =
      {state := finish,regs := Function.update (Function.update cfg.regs src []) dst
        (w.reverse.flatMap (fun b => [true,b]) ++ cfg.regs dst),answer := none} := by
  classical
  induction w generalizing cfg with
  | nil =>
    change P.step A cfg=_
    have hup : Function.update cfg.regs src []=cfg.regs := by
      rw [←hw]
      exact Function.update_eq_self src cfg.regs
    simp [StackProgram.step,hs,ha,hloop,hw,hup]
  | cons b w ih =>
    let next := if b then one else zero
    let cfg1 : StackConfig Q r := {state:=next,regs:=Function.update cfg.regs src w,answer:=none}
    let cfg2 : StackConfig Q r := {state:=flag,regs:=Function.update (Function.update cfg.regs src w) dst (b::cfg.regs dst),answer:=none}
    let cfg3 : StackConfig Q r := {state:=loop,regs:=Function.update (Function.update cfg.regs src w) dst (true::b::cfg.regs dst),answer:=none}
    have h1 : P.step A cfg=cfg1 := by
      cases b <;> simp [StackProgram.step,hs,ha,hloop,hw,cfg1,next]
    have h2 : P.step A cfg1=cfg2 := by
      cases b <;> simp [StackProgram.step,cfg1,cfg2,next,hzero,hone,Ne.symm hne]
    have h3 : P.step A cfg2=cfg3 := by
      simp [StackProgram.step,cfg2,cfg3,hflag]
    have hsrc : cfg3.regs src=w := by simp [cfg3,hne]
    have hrec:=ih cfg3 rfl rfl hsrc
    have ht : 3*(b::w).length+1=1+(1+(1+(3*w.length+1))) := by simp;omega
    rw [ht,StackProgram.exec_add,StackProgram.exec_one,h1,
      StackProgram.exec_add,StackProgram.exec_one,h2,
      StackProgram.exec_add,StackProgram.exec_one,h3,hrec]
    congr 1
    funext j
    by_cases hjs : j=src
    · subst j
      simp [cfg3,Function.update,hne,Ne.symm hne]
    · by_cases hjd : j=dst
      · subst j
        simp [cfg3,Function.update,hne,Ne.symm hne,List.reverse_cons,List.flatMap_append,List.append_assoc]
      · simp [cfg3,Function.update,hjs,hjd]

end APSCounting893.Main
end Component_7

section Component_8

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
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

structure StackRepresentation {Q : Type} {r : ℕ} (boundary : Fin (r + 2) → ℤ)
    (cfg : ProgramConfig (StackControl Q r) 0 (r + 4)) (sc : StackConfig Q r) : Prop where
  state : cfg.state = .execute sc.state
  answer : cfg.answer = sc.answer
  regs : ∀ j, StackTape (cfg.tapes (stackRegisterTape j)) (boundary j) (sc.regs j)
  query : TapePrefix (cfg.tapes 2) []
  queryZero : (cfg.tapes 2).read 0 = .blank

def stackBoundaries {r : ℕ} (x w : Word) (j : Fin (r + 2)) : ℤ :=
  if j = 0 then x.length + 1 else if j = 1 then w.length + 1 else 1

lemma stackRegisterTape_zero (r : ℕ) : stackRegisterTape (0 : Fin (r + 2)) = 0 := by
  apply Fin.ext
  change (if 0 % (r + 2) < 2 then 0 % (r + 2) else 0 % (r + 2) + 2) = 0 % (r + 4)
  simp

lemma stackRegisterTape_one (r : ℕ) : stackRegisterTape (1 : Fin (r + 2)) = 1 := by
  apply Fin.ext
  change (if 1 % (r + 2) < 2 then 1 % (r + 2) else 1 % (r + 2) + 2) = 1 % (r + 4)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rfl

lemma stackRegisterTape_ne_zero {r : ℕ} (j : Fin (r + 2)) (h : j ≠ 0) : stackRegisterTape j ≠ 0 := by
  intro hz
  exact h (stackRegisterTape_injective r (hz.trans (stackRegisterTape_zero r).symm))

lemma stackRegisterTape_ne_one {r : ℕ} (j : Fin (r + 2)) (h : j ≠ 1) : stackRegisterTape j ≠ 1 := by
  intro hz
  exact h (stackRegisterTape_injective r (hz.trans (stackRegisterTape_one r).symm))

lemma StackProgram.compile_initial_representation {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (x w : Word) :
    StackRepresentation (stackBoundaries x w) (P.compile.run A x w 1) (P.initialConfig x w) := by
  constructor
  · rfl
  · rfl
  · intro j
    by_cases hj0 : j = 0
    · subst j
      simpa [FiniteProgram.run, FiniteProgram.step, compile, FiniteProgram.initialConfig,
        initialConfig, stackBoundaries, stackRegisterTape_zero, Tape.read, Tape.input] using stackTape_input (a := 0) x
    · by_cases hj1 : j = 1
      · subst j
        have h10 : (1 : Fin (r + 2)) ≠ 0 := by intro h; have := congrArg Fin.val h; norm_num at this
        simpa [FiniteProgram.run, FiniteProgram.step, compile, FiniteProgram.initialConfig,
          initialConfig, stackBoundaries, stackRegisterTape_one, Tape.read, Tape.input] using stackTape_input (a := 0) w
      · have hreg0 := stackRegisterTape_ne_zero j hj0
        have hreg1 := stackRegisterTape_ne_one j hj1
        simpa [FiniteProgram.run, FiniteProgram.step, compile, FiniteProgram.initialConfig,
          initialConfig, stackBoundaries, hj0, hj1, hreg0, hreg1, Tape.read] using stackTape_empty (a := 0)
  · exact tapePrefix_initial
  · rfl

end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma StackRepresentation.stay {Q : Type} {r : ℕ} {boundary : Fin (r + 2) → ℤ}
    {cfg : ProgramConfig (StackControl Q r) 0 (r + 4)} {sc : StackConfig Q r}
    (h : StackRepresentation boundary cfg sc) (next : Q) :
    StackRepresentation boundary
      { cfg with state := .execute next, tapes := fun j =>
        (cfg.tapes j).step ((cfg.tapes j).read (cfg.tapes j).head) .stay }
      { sc with state := next } := by
  constructor
  · rfl
  · exact h.answer
  · intro j; exact (h.regs j).stay
  · exact h.query.stay
  · rw [tape_step_same_reads]
    exact h.queryZero

lemma StackRepresentation.pop {Q : Type} {r : ℕ} {boundary : Fin (r + 2) → ℤ}
    {cfg : ProgramConfig (StackControl Q r) 0 (r + 4)} {sc : StackConfig Q r}
    (h : StackRepresentation boundary cfg sc) (reg : Fin (r + 2)) (b : Bool) (w : Word)
    (hw : sc.regs reg = b :: w) (next : Q) :
    StackRepresentation boundary
      { cfg with state := .execute next, tapes := fun j =>
        ((cfg.tapes j).step (if j = stackRegisterTape reg then .blank else (cfg.tapes j).read (cfg.tapes j).head)
          (if j = stackRegisterTape reg then .right else .stay)) }
      { sc with state := next, regs := Function.update sc.regs reg w } := by
  constructor
  · rfl
  · exact h.answer
  · intro j
    by_cases hj : j = reg
    · subst j
      have hr := h.regs reg
      rw [hw] at hr
      simpa only [if_pos rfl, ite_true, Function.update_self] using hr.pop
    · have ht : stackRegisterTape j ≠ stackRegisterTape reg :=
        (stackRegisterTape_injective r).ne hj
      simpa only [if_neg ht, Function.update_of_ne hj] using (h.regs j).stay
  · have ht := stackRegisterTape_ne_query reg
    simpa only [if_neg (Ne.symm ht)] using h.query.stay
  · have ht := stackRegisterTape_ne_query reg
    simpa only [if_neg (Ne.symm ht), tape_step_same_reads] using h.queryZero

def stackPushMovedTapes {Q : Type} {r : ℕ}
    (cfg : ProgramConfig (StackControl Q r) 0 (r + 4)) (reg : Fin (r + 2)) : Fin (r + 4) → Tape 0 :=
  fun j => (cfg.tapes j).step ((cfg.tapes j).read (cfg.tapes j).head)
    (if j = stackRegisterTape reg then .left else .stay)

lemma StackRepresentation.push {Q : Type} {r : ℕ} {boundary : Fin (r + 2) → ℤ}
    {cfg : ProgramConfig (StackControl Q r) 0 (r + 4)} {sc : StackConfig Q r}
    (h : StackRepresentation boundary cfg sc) (reg : Fin (r + 2)) (b : Bool) (next : Q) :
    StackRepresentation boundary
      { cfg with state := .execute next, tapes := fun j =>
        ((stackPushMovedTapes cfg reg j).step
          (if j = stackRegisterTape reg then .bit b else
            (stackPushMovedTapes cfg reg j).read (stackPushMovedTapes cfg reg j).head) .stay) }
      { sc with state := next, regs := Function.update sc.regs reg (b :: sc.regs reg) } := by
  constructor
  · rfl
  · exact h.answer
  · intro j
    by_cases hj : j = reg
    · subst j
      simpa only [stackPushMovedTapes, if_pos rfl, ite_true, Function.update_self] using (h.regs reg).push b
    · have ht : stackRegisterTape j ≠ stackRegisterTape reg := (stackRegisterTape_injective r).ne hj
      simpa only [stackPushMovedTapes, if_neg ht, Function.update_of_ne hj] using (h.regs j).stay.stay
  · have ht := stackRegisterTape_ne_query reg
    simpa only [stackPushMovedTapes, if_neg (Ne.symm ht)] using h.query.stay.stay
  · have ht := stackRegisterTape_ne_query reg
    simp only [stackPushMovedTapes, if_neg (Ne.symm ht)]
    rw [tape_step_same_reads, tape_step_same_reads]
    exact h.queryZero

end APSCounting893.Main
end Component_10

section Component_11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_compile_jump {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (hc : StackRepresentation boundary cfg sc) (ha : sc.answer = none)
    (next : Q) (ht : P.transition sc.state = .jump next) :
    StackRepresentation boundary (P.compile.exec A cfg 1) { sc with state := next } := by
  have hha : cfg.answer = none := hc.answer.trans ha
  have hs : P.compile.step A cfg =
      { cfg with state := .execute next, tapes := fun j =>
        (cfg.tapes j).step ((cfg.tapes j).read (cfg.tapes j).head) .stay } := by
    apply FiniteProgram.step_step
    · exact hha
    · simp only [StackProgram.compile, hc.state, ht]
  rw [FiniteProgram.exec_one, hs]
  exact hc.stay next

lemma stack_compile_push {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (hc : StackRepresentation boundary cfg sc) (ha : sc.answer = none)
    (reg : Fin (r + 2)) (b : Bool) (next : Q) (ht : P.transition sc.state = .push reg b next) :
    StackRepresentation boundary (P.compile.exec A cfg 2)
      { sc with state := next, regs := Function.update sc.regs reg (b :: sc.regs reg) } := by
  have hha : cfg.answer = none := hc.answer.trans ha
  let cfg1 : ProgramConfig (StackControl Q r) 0 (r + 4) :=
    { cfg with state := .pushFinish reg b next, tapes := stackPushMovedTapes cfg reg }
  have hs1 : P.compile.step A cfg = cfg1 := by
    simp [FiniteProgram.step, StackProgram.compile, hc.state, hha, ht, cfg1]
    rfl
  have hs2 : P.compile.step A cfg1 =
      { cfg with state := .execute next, tapes := fun j =>
        ((stackPushMovedTapes cfg reg j).step
          (if j = stackRegisterTape reg then .bit b else
            (stackPushMovedTapes cfg reg j).read (stackPushMovedTapes cfg reg j).head) .stay) } := by
    apply FiniteProgram.step_step
    · exact hha
    · have hstate : cfg1.state = .pushFinish reg b next := rfl
      simp only [StackProgram.compile, hstate]
      rfl
  change StackRepresentation boundary (P.compile.step A (P.compile.step A cfg)) _
  rw [hs1, hs2]
  exact hc.push reg b next

lemma stack_compile_pop_cons {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (hc : StackRepresentation boundary cfg sc) (ha : sc.answer = none)
    (reg : Fin (r + 2)) (b : Bool) (w : Word) (zero one empty : Q)
    (hw : sc.regs reg = b :: w) (ht : P.transition sc.state = .pop reg zero one empty) :
    StackRepresentation boundary (P.compile.exec A cfg 1)
      { sc with state := if b then one else zero, regs := Function.update sc.regs reg w } := by
  have hha : cfg.answer = none := hc.answer.trans ha
  have hr := hc.regs reg
  rw [hw] at hr
  have htop := hr.top
  have hs : P.compile.step A cfg =
      { cfg with state := .execute (if b then one else zero), tapes := fun j =>
        ((cfg.tapes j).step (if j = stackRegisterTape reg then .blank else (cfg.tapes j).read (cfg.tapes j).head)
          (if j = stackRegisterTape reg then .right else .stay)) } := by
    apply FiniteProgram.step_step
    · exact hha
    · simp only [StackProgram.compile, hc.state, ht, htop]
  rw [FiniteProgram.exec_one, hs]
  exact hc.pop reg b w hw _

lemma stack_compile_peek_cons {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (hc : StackRepresentation boundary cfg sc) (ha : sc.answer = none)
    (reg : Fin (r + 2)) (b : Bool) (w : Word) (zero one empty : Q)
    (hw : sc.regs reg = b :: w) (ht : P.transition sc.state = .peek reg zero one empty) :
    StackRepresentation boundary (P.compile.exec A cfg 1)
      { sc with state := if b then one else zero } := by
  have hha : cfg.answer = none := hc.answer.trans ha
  have hr := hc.regs reg
  rw [hw] at hr
  have htop := hr.top
  have hs : P.compile.step A cfg =
      { cfg with state := .execute (if b then one else zero), tapes := fun j =>
        (cfg.tapes j).step ((cfg.tapes j).read (cfg.tapes j).head) .stay } := by
    apply FiniteProgram.step_step
    · exact hha
    · cases b <;> simp only [StackProgram.compile, hc.state, ht, htop, ↓reduceIte] <;> rfl
  rw [FiniteProgram.exec_one, hs]
  exact hc.stay _

lemma stack_compile_peek_empty {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (hc : StackRepresentation boundary cfg sc) (ha : sc.answer = none)
    (reg : Fin (r + 2)) (zero one empty : Q)
    (hw : sc.regs reg = []) (ht : P.transition sc.state = .peek reg zero one empty ∨
      P.transition sc.state = .pop reg zero one empty) :
    StackRepresentation boundary (P.compile.exec A cfg 1) { sc with state := empty } := by
  have hha : cfg.answer = none := hc.answer.trans ha
  have hr := hc.regs reg
  rw [hw] at hr
  have htop := hr.empty
  have hs : P.compile.step A cfg =
      { cfg with state := .execute empty, tapes := fun j =>
        (cfg.tapes j).step ((cfg.tapes j).read (cfg.tapes j).head) .stay } := by
    apply FiniteProgram.step_step
    · exact hha
    · rcases ht with ht | ht <;> simp only [StackProgram.compile, hc.state, ht, htop]
  rw [FiniteProgram.exec_one, hs]
  exact hc.stay _

lemma stack_compile_halt {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (hc : StackRepresentation boundary cfg sc) (ha : sc.answer = none)
    (b : Bool) (ht : P.transition sc.state = .halt b) :
    StackRepresentation boundary (P.compile.exec A cfg 1) { sc with answer := some b } := by
  have hha : cfg.answer = none := hc.answer.trans ha
  have hs : P.compile.step A cfg = { cfg with answer := some b } := by
    apply FiniteProgram.step_halt
    · exact hha
    · simp only [StackProgram.compile, hc.state, ht]
  rw [FiniteProgram.exec_one, hs]
  exact ⟨hc.state, rfl, hc.regs, hc.query, hc.queryZero⟩

end APSCounting893.Main
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

structure ClearTape {a : ℕ} (t : Tape a) (w : Word) : Prop where
  head : t.head = w.length
  read : ∀ j : ℕ, t.read (j + 1) = if h : j < w.length then .bit w[j] else .blank
  zero : t.read 0 = .blank

lemma ClearTape.top {a : ℕ} {t : Tape a} {w : Word} {b : Bool}
    (h : ClearTape t (w ++ [b])) : t.read t.head = .bit b := by
  rw [h.head]
  have hr := h.read w.length
  simpa using hr

lemma ClearTape.erase {a : ℕ} {t : Tape a} {w : Word} {b : Bool}
    (h : ClearTape t (w ++ [b])) : ClearTape (t.step .blank .left) w := by
  have hh : t.head = (w.length : ℤ) + 1 := by simpa using h.head
  constructor
  · simp [Tape.step, hh]
  · intro j
    by_cases hj : j = w.length
    · subst j
      rw [← hh, tape_step_read_self, dif_neg (by omega)]
    · rw [tape_step_read_ne]
      · rw [h.read]
        by_cases hj' : j < w.length
        · have hj'' : j < (w ++ [b]).length := by simp; omega
          rw [dif_pos hj'', dif_pos hj', List.getElem_append_left hj']
        · have hj'' : ¬ j < (w ++ [b]).length := by simp; omega
          rw [dif_neg hj'', dif_neg hj']
      · rw [hh]
        exact_mod_cast (show j + 1 ≠ w.length + 1 by omega)
  · rw [tape_step_read_ne]
    · exact h.zero
    · rw [hh]
      omega

lemma ClearTape.finish {a : ℕ} {t : Tape a} (h : ClearTape t []) :
    TapePrefix (t.step (t.read t.head) .right) [] ∧
      (t.step (t.read t.head) .right).read 0 = .blank := by
  constructor
  · constructor
    · simp [Tape.step, h.head]
    · intro j
      rw [tape_step_same_reads, h.read]
  · rw [tape_step_same_reads]
    exact h.zero

lemma TapePrefix.start_clear {a : ℕ} {t : Tape a} {w : Word} (h : TapePrefix t w)
    (hzero : t.read 0 = .blank) : ClearTape (t.step (t.read t.head) .left) w := by
  constructor
  · simp only [Tape.step, h.head]
    push_cast
    omega
  · intro j
    rw [tape_step_same_reads, h.read]
  · rw [tape_step_same_reads]
    exact hzero

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

structure ClearRepresentation {Q : Type} {r : ℕ} (boundary : Fin (r + 2) → ℤ)
    (cfg : ProgramConfig (StackControl Q r) 0 (r + 4)) (sc : StackConfig Q r) (w : Word) : Prop where
  state : cfg.state = .clearQuery sc.state
  answer : cfg.answer = sc.answer
  regs : ∀ j, StackTape (cfg.tapes (stackRegisterTape j)) (boundary j) (sc.regs j)
  query : ClearTape (cfg.tapes 2) w

lemma stack_clear_query {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (ha : sc.answer = none) (w : Word)
    (hc : ClearRepresentation boundary cfg sc w) :
    StackRepresentation boundary (P.compile.exec A cfg (w.length + 1)) sc := by
  induction w using List.reverseRecOn generalizing cfg with
  | nil =>
      have hha : cfg.answer = none := hc.answer.trans ha
      have htop : (cfg.tapes 2).read (cfg.tapes 2).head = .blank := by
        rw [hc.query.head]
        exact hc.query.zero
      have hs : P.compile.step A cfg =
          { cfg with state := .execute sc.state, tapes := fun j =>
            ((cfg.tapes j).step ((cfg.tapes j).read (cfg.tapes j).head)
              (if j = 2 then .right else .stay)) } := by
        apply FiniteProgram.step_step
        · exact hha
        · simp only [StackProgram.compile, hc.state, htop]
      change StackRepresentation boundary (P.compile.step A cfg) sc
      rw [hs]
      constructor
      · rfl
      · exact hc.answer
      · intro j
        simpa only [if_neg (stackRegisterTape_ne_query j)] using (hc.regs j).stay
      · simpa only [if_pos rfl, ite_true] using hc.query.finish.1
      · simpa only [if_pos rfl, ite_true] using hc.query.finish.2
  | append_singleton w b ih =>
      have hha : cfg.answer = none := hc.answer.trans ha
      have htop := hc.query.top
      let cfg1 : ProgramConfig (StackControl Q r) 0 (r + 4) :=
        { cfg with state := .clearQuery sc.state, tapes := fun j =>
          ((cfg.tapes j).step (if j = 2 then .blank else (cfg.tapes j).read (cfg.tapes j).head)
            (if j = 2 then .left else .stay)) }
      have hs : P.compile.step A cfg = cfg1 := by
        simp [FiniteProgram.step, StackProgram.compile, hc.state, hha, htop, cfg1]
      have hc1 : ClearRepresentation boundary cfg1 sc w := by
        constructor
        · rfl
        · exact hc.answer
        · intro j
          simpa only [cfg1, if_neg (stackRegisterTape_ne_query j)] using (hc.regs j).stay
        · simpa only [cfg1, if_pos rfl, ite_true] using hc.query.erase
      rw [show (w ++ [b]).length + 1 = 1 + (w.length + 1) by simp; omega,
        FiniteProgram.exec_add, FiniteProgram.exec_one, hs]
      exact ih cfg1 hc1

end APSCounting893.Main
end Component_13

section Component_14

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

structure CopyQueryRepresentation {Q : Type} {r : ℕ} (boundary : Fin (r + 2) → ℤ)
    (cfg : ProgramConfig (StackControl Q r) 0 (r + 4)) (sc : StackConfig Q r)
    (reg : Fin (r + 2)) (yes no : Q) (front rest : Word) : Prop where
  state : cfg.state = .copyQuery reg yes no
  answer : cfg.answer = none
  regs : ∀ j, StackTape (cfg.tapes (stackRegisterTape j)) (boundary j)
    (if j = reg then rest else sc.regs j)
  query : TapePrefix (cfg.tapes 2) front
  queryZero : (cfg.tapes 2).read 0 = .blank

lemma stack_copy_query_step {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (reg : Fin (r + 2)) (yes no : Q) (front rest : Word) (b : Bool)
    (hc : CopyQueryRepresentation boundary cfg sc reg yes no front (b :: rest)) :
    CopyQueryRepresentation boundary (P.compile.step A cfg) sc reg yes no (front ++ [b]) rest := by
  have hr : StackTape (cfg.tapes (stackRegisterTape reg)) (boundary reg) (b :: rest) := by
    simpa using hc.regs reg
  have htop := hr.top
  have hneq := stackRegisterTape_ne_query reg
  have hs : P.compile.step A cfg =
      { cfg with state := .copyQuery reg yes no, tapes := fun j =>
        ((cfg.tapes j).step
          (if j = stackRegisterTape reg then .blank else if j = 2 then .bit b else (cfg.tapes j).read (cfg.tapes j).head)
          (if j = stackRegisterTape reg ∨ j = 2 then .right else .stay)) } := by
    apply FiniteProgram.step_step
    · exact hc.answer
    · simp only [StackProgram.compile, hc.state, stackCopyAction, htop]
  rw [hs]
  constructor
  · rfl
  · exact hc.answer
  · intro j
    by_cases hj : j = reg
    · subst j
      simpa only [if_pos rfl, eq_self_iff_true, ite_true, true_or] using hr.pop
    · have hjt : stackRegisterTape j ≠ stackRegisterTape reg := (stackRegisterTape_injective r).ne hj
      have hjq := stackRegisterTape_ne_query j
      simpa only [if_neg hjt, if_neg hjq, if_neg (not_or.mpr ⟨hjt, hjq⟩), if_neg hj] using (hc.regs j).stay
  · simpa only [if_neg (Ne.symm hneq), if_pos rfl, ite_true, or_true] using hc.query.append b
  · have hhead : (cfg.tapes 2).head ≠ 0 := by have hh := hc.query.head; omega
    simp only [if_neg (Ne.symm hneq), eq_self_iff_true, ite_true, or_true]
    rw [tape_step_read_ne _ _ _ _ (Ne.symm hhead)]
    exact hc.queryZero

lemma stack_copy_query_all {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (reg : Fin (r + 2)) (yes no : Q) (front rest : Word)
    (hc : CopyQueryRepresentation boundary cfg sc reg yes no front rest) :
    CopyQueryRepresentation boundary (P.compile.exec A cfg rest.length) sc reg yes no (front ++ rest) [] := by
  induction rest generalizing cfg front with
  | nil =>
      change CopyQueryRepresentation boundary cfg sc reg yes no (front ++ []) []
      simpa only [List.append_nil] using hc
  | cons b rest ih =>
      have hc1 := stack_copy_query_step P A boundary cfg sc reg yes no front rest b hc
      have hrec := ih (P.compile.step A cfg) (front ++ [b]) hc1
      have heq : P.compile.exec A cfg (b :: rest).length =
          P.compile.exec A (P.compile.step A cfg) rest.length := by
        change (P.compile.step A)^[rest.length + 1] cfg = _
        exact Function.iterate_succ_apply _ _ _
      rw [heq]
      simpa only [List.append_assoc, List.singleton_append] using hrec

end APSCounting893.Main
end Component_14

section Component_15

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_query_finish {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (reg : Fin (r + 2)) (yes no : Q) (w : Word)
    (hc : CopyQueryRepresentation boundary cfg sc reg yes no w []) :
    StackRepresentation boundary (P.compile.exec A cfg (w.length + 3))
      { state := (@ite Q (A w) (Classical.propDecidable _) yes no),
        regs := Function.update sc.regs reg [], answer := none } := by
  classical
  have hr : StackTape (cfg.tapes (stackRegisterTape reg)) (boundary reg) [] := by simpa using hc.regs reg
  have htop := hr.empty
  have hword := hc.query.word
  let next : Q := if A w then yes else no
  let sc' : StackConfig Q r := { state := next, regs := Function.update sc.regs reg [], answer := none }
  let cfg1 : ProgramConfig (StackControl Q r) 0 (r + 4) := { cfg with state := .clearStart next }
  have hs1 : P.compile.step A cfg = cfg1 := by
    by_cases hA : A w <;>
      simp [FiniteProgram.step, StackProgram.compile, hc.state, hc.answer, stackCopyAction,
        htop, hword, next, cfg1, hA]
  let cfg2 : ProgramConfig (StackControl Q r) 0 (r + 4) :=
    { cfg1 with state := .clearQuery next, tapes := fun j =>
        ((cfg.tapes j).step ((cfg.tapes j).read (cfg.tapes j).head)
          (if j = 2 then .left else .stay)) }
  have hs2 : P.compile.step A cfg1 = cfg2 := by
    apply FiniteProgram.step_step
    · exact hc.answer
    · have hstate : cfg1.state = .clearStart next := rfl
      simp only [StackProgram.compile, hstate]
      rfl
  have hc2 : ClearRepresentation boundary cfg2 sc' w := by
    constructor
    · rfl
    · exact hc.answer
    · intro j
      have ht := stackRegisterTape_ne_query j
      have hj := hc.regs j
      by_cases hreg : j = reg
      · subst j
        simpa only [cfg2, sc', if_neg ht, Function.update_self, if_pos rfl, ite_true] using hj.stay
      · simpa only [cfg2, sc', if_neg ht, Function.update_of_ne hreg, if_neg hreg] using hj.stay
    · simpa only [cfg2, if_pos rfl, ite_true] using hc.query.start_clear hc.queryZero
  have hfinish := stack_clear_query P A boundary cfg2 sc' rfl w hc2
  rw [show w.length + 3 = 1 + (1 + (w.length + 1)) by omega,
    FiniteProgram.exec_add, FiniteProgram.exec_one, hs1,
    FiniteProgram.exec_add, FiniteProgram.exec_one, hs2]
  exact hfinish

end APSCounting893.Main
end Component_15

section Component_16

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_compile_query {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (hc : StackRepresentation boundary cfg sc) (ha : sc.answer = none)
    (reg : Fin (r + 2)) (yes no : Q) (ht : P.transition sc.state = .query reg yes no) :
    StackRepresentation boundary (P.compile.exec A cfg (2 * (sc.regs reg).length + 3)) (P.step A sc) := by
  classical
  let cfg0 : ProgramConfig (StackControl Q r) 0 (r + 4) := { cfg with state := .copyQuery reg yes no }
  have hc0 : CopyQueryRepresentation boundary cfg0 sc reg yes no [] (sc.regs reg) := by
    constructor
    · rfl
    · exact hc.answer.trans ha
    · intro j
      by_cases hj : j = reg
      · subst j; simpa only [if_pos rfl, ite_true] using hc.regs reg
      · simpa only [if_neg hj] using hc.regs j
    · exact hc.query
    · exact hc.queryZero
  have hcopy := stack_copy_query_all P A boundary cfg0 sc reg yes no [] (sc.regs reg) hc0
  simp only [List.nil_append] at hcopy
  have hfinish := stack_query_finish P A boundary
    (P.compile.exec A cfg0 (sc.regs reg).length) sc reg yes no (sc.regs reg) hcopy
  have hha : cfg.answer = none := hc.answer.trans ha
  have hstep : P.compile.step A cfg = P.compile.step A cfg0 := by
    cases htop : (cfg.tapes (stackRegisterTape reg)).read (cfg.tapes (stackRegisterTape reg)).head with
    | blank =>
        by_cases hA : A (cfg.tapes 2).word <;>
          simp [FiniteProgram.step, StackProgram.compile, hc.state, hha, ht, cfg0, stackCopyAction, htop, hA]
    | bit b => simp [FiniteProgram.step, StackProgram.compile, hc.state, hha, ht, cfg0, stackCopyAction, htop]
    | extra e => exact Fin.elim0 e
  have heq := P.compile.exec_eq_of_step_eq A cfg cfg0 (2 * (sc.regs reg).length + 3) (by omega) hstep
  rw [heq, show 2 * (sc.regs reg).length + 3 = (sc.regs reg).length + ((sc.regs reg).length + 3) by omega,
    FiniteProgram.exec_add]
  have hhigh : P.step A sc =
      { state := (@ite Q (A (sc.regs reg)) (Classical.propDecidable _) yes no),
        regs := Function.update sc.regs reg [], answer := none } := by
    simp [StackProgram.step, ha, ht]
  rw [hhigh]
  exact hfinish

end APSCounting893.Main
end Component_16

section Component_17

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def stackSize {r : ℕ} (regs : Fin (r + 2) → Word) : ℕ := ∑ j, (regs j).length

lemma stackSize_update_le {r : ℕ} (regs : Fin (r + 2) → Word) (j : Fin (r + 2))
    (w : Word) (c : ℕ) (h : w.length ≤ (regs j).length + c) :
    stackSize (Function.update regs j w) ≤ stackSize regs + c := by
  classical
  calc
    _ ≤ ∑ i : Fin (r + 2), ((regs i).length + if i = j then c else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hij : i = j
      · subst i; simpa using h
      · simp [Function.update, hij]
    _ = _ := by simp [stackSize, Finset.sum_add_distrib]

lemma StackProgram.size_step_le {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (cfg : StackConfig Q r) :
    stackSize (P.step A cfg).regs ≤ stackSize cfg.regs + 1 := by
  classical
  by_cases ha : cfg.answer.isSome
  · simp only [step, if_pos ha]
    omega
  · rw [step, if_neg ha]
    cases ht : P.transition cfg.state with
    | jump next => simp
    | peek j zero one empty => simp
    | pop j zero one empty =>
        exact (stackSize_update_le cfg.regs j (cfg.regs j).tail 0 (by simp)).trans (by omega)
    | push j bit next =>
        exact stackSize_update_le cfg.regs j (bit :: cfg.regs j) 1 (by simp)
    | query j yes no =>
        exact (stackSize_update_le cfg.regs j [] 0 (by simp)).trans (by omega)
    | halt bit => simp

lemma StackProgram.run_succ {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (x w : Word) (t : ℕ) :
    P.run A x w (t + 1) = P.step A (P.run A x w t) :=
  Function.iterate_succ_apply' _ _ _

lemma StackProgram.size_run_le {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (x w : Word) (t : ℕ) :
    stackSize (P.run A x w t).regs ≤ stackSize (P.initialConfig x w).regs + t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ]
      exact (P.size_step_le A _).trans (by omega)

end APSCounting893.Main
end Component_17

section Component_18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma stack_compile_step {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (boundary : Fin (r + 2) → ℤ) (cfg : ProgramConfig (StackControl Q r) 0 (r + 4))
    (sc : StackConfig Q r) (hc : StackRepresentation boundary cfg sc) :
    ∃ t ≤ 2 * stackSize sc.regs + 3,
      StackRepresentation boundary (P.compile.exec A cfg t) (P.step A sc) := by
  classical
  cases hans : sc.answer with
  | some b =>
      refine ⟨0, by omega, ?_⟩
      change StackRepresentation boundary cfg (P.step A sc)
      simpa only [StackProgram.step, hans, Option.isSome_some, Bool.true_eq, ↓reduceIte] using hc
  | none =>
      cases ht : P.transition sc.state with
      | jump next =>
          refine ⟨1, by omega, ?_⟩
          have hp := stack_compile_jump P A boundary cfg sc hc hans next ht
          simpa [StackProgram.step, hans, ht] using hp
      | peek reg zero one empty =>
          refine ⟨1, by omega, ?_⟩
          cases hw : sc.regs reg with
          | nil =>
              have hp := stack_compile_peek_empty P A boundary cfg sc hc hans reg zero one empty hw (Or.inl ht)
              simpa [StackProgram.step, hans, ht, hw] using hp
          | cons b w =>
              have hp := stack_compile_peek_cons P A boundary cfg sc hc hans reg b w zero one empty hw ht
              cases b <;> simpa [StackProgram.step, hans, ht, hw] using hp
      | pop reg zero one empty =>
          refine ⟨1, by omega, ?_⟩
          cases hw : sc.regs reg with
          | nil =>
              have hp := stack_compile_peek_empty P A boundary cfg sc hc hans reg zero one empty hw (Or.inr ht)
              have hup : Function.update sc.regs reg [] = sc.regs := by
                ext j
                by_cases hj : j = reg
                · subst j; simp [hw]
                · simp [Function.update, hj]
              simpa [StackProgram.step, hans, ht, hw, hup] using hp
          | cons b w =>
              have hp := stack_compile_pop_cons P A boundary cfg sc hc hans reg b w zero one empty hw ht
              cases b <;> simpa [StackProgram.step, hans, ht, hw] using hp
      | push reg b next =>
          refine ⟨2, by omega, ?_⟩
          simpa [StackProgram.step, hans, ht] using stack_compile_push P A boundary cfg sc hc hans reg b next ht
      | query reg yes no =>
          have hlen : (sc.regs reg).length ≤ stackSize sc.regs := by
            change (sc.regs reg).length ≤ ∑ j : Fin (r + 2), (sc.regs j).length
            exact Finset.single_le_sum (fun j hj => Nat.zero_le (sc.regs j).length) (Finset.mem_univ reg)
          exact ⟨2 * (sc.regs reg).length + 3, by omega,
            stack_compile_query P A boundary cfg sc hc hans reg yes no ht⟩
      | halt b =>
          refine ⟨1, by omega, ?_⟩
          simpa [StackProgram.step, hans, ht] using stack_compile_halt P A boundary cfg sc hc hans b ht

lemma FiniteProgram.run_add {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (A : Language) (x w : Word) (t s : ℕ) :
    P.run A x w (t + s) = P.exec A (P.run A x w t) s := by
  exact P.exec_add A (P.initialConfig x w) t s

lemma stack_compile_run {Q : Type} {r : ℕ} (P : StackProgram Q r) (A : Language)
    (x w : Word) (T : ℕ) :
    ∃ t ≤ 1 + T * (2 * (stackSize (P.initialConfig x w).regs + T) + 3),
      StackRepresentation (stackBoundaries x w) (P.compile.run A x w t) (P.run A x w T) := by
  induction T with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      exact P.compile_initial_representation A x w
  | succ T ih =>
      obtain ⟨t, ht, hc⟩ := ih
      obtain ⟨s, hs, hc'⟩ := stack_compile_step P A (stackBoundaries x w)
        (P.compile.run A x w t) (P.run A x w T) hc
      refine ⟨t + s, ?_, ?_⟩
      · have hsize := P.size_run_le A x w T
        nlinarith
      · rw [FiniteProgram.run_add, StackProgram.run_succ]
        exact hc'

end APSCounting893.Main
end Component_18

section Component_19

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma StackProgram.initial_size {Q : Type} {r : ℕ} (P : StackProgram Q r) (x w : Word) :
    stackSize (P.initialConfig x w).regs = x.length + w.length := by
  classical
  have h01 : (0 : Fin (r + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  have hf : ∀ j : Fin (r + 2), ((P.initialConfig x w).regs j).length =
      (if j = 0 then x.length else 0) + (if j = 1 then w.length else 0) := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp only [initialConfig, if_pos rfl, ite_true, if_neg h01, Nat.add_zero]
    · by_cases hj1 : j = 1
      · simp only [initialConfig, if_neg hj0, if_pos hj1, zero_add]
      · simp only [initialConfig, if_neg hj0, if_neg hj1, List.length_nil, Nat.add_zero]
  unfold stackSize
  simp_rw [hf]
  rw [Finset.sum_add_distrib]
  simp


lemma stack_simulation_polynomial_bound (a b c d n : ℕ) :
    1 + polyBound c d n * (2 * (n + polyBound a b n + polyBound c d n) + 3) ≤
      polyBound (1 + c * (2 * (1 + a + c) + 3)) (2 * (d + b + 1)) n := by
  let K := d + b + 1
  let V := (n + 1) ^ K
  have hV : 1 ≤ V := Nat.one_le_pow _ _ (by omega)
  have hn : n ≤ V := by
    have hp : n + 1 ≤ (n + 1) ^ K := by
      calc
        n + 1 = (n + 1) ^ 1 := by simp
        _ ≤ (n + 1) ^ K := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hm : polyBound a b n ≤ a * V :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by dsimp [K]; omega))
  have hT : polyBound c d n ≤ c * V :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by dsimp [K]; omega))
  have hS : n + polyBound a b n + polyBound c d n ≤ (1 + a + c) * V := by nlinarith
  have hVV : V ≤ V * V := Nat.le_mul_of_pos_left _ hV
  have hVV1 : 1 ≤ V * V := hV.trans hVV
  have hcVV : c * V ≤ c * (V * V) := Nat.mul_le_mul_left c hVV
  calc
    _ ≤ 1 + (c * V) * (2 * ((1 + a + c) * V) + 3) := by gcongr
    _ ≤ (1 + c * (2 * (1 + a + c) + 3)) * (V * V) := by nlinarith
    _ = _ := by simp only [polyBound, V, K, ← pow_add, two_mul]

lemma StackProgram.compiled_answer {Q : Type} [Fintype Q] {r : ℕ} (P : StackProgram Q r)
    (A : Language) (a b c d : ℕ) (x w : Word) (hw : w.length = polyBound a b x.length)
    (answer : Bool) (hanswer : (P.run A x w (polyBound c d x.length)).answer = some answer) :
    (machineRun P.compile.compile A x w
      (polyBound (1 + c * (2 * (1 + a + c) + 3)) (2 * (d + b + 1)) x.length)).answer = some answer := by
  obtain ⟨t, ht, hc⟩ := stack_compile_run P A x w (polyBound c d x.length)
  have hphysical : (machineRun P.compile.compile A x w t).answer = some answer := by
    rw [FiniteProgram.compile_run]
    exact hc.answer.trans hanswer
  have hle : t ≤ polyBound (1 + c * (2 * (1 + a + c) + 3)) (2 * (d + b + 1)) x.length := by
    rw [P.initial_size, hw] at ht
    exact ht.trans (stack_simulation_polynomial_bound a b c d x.length)
  have hh : (machineRun P.compile.compile A x w t).answer.isSome := by rw [hphysical]; rfl
  have heq := machineRun_halted_persistent P.compile.compile A x w t
    (polyBound (1 + c * (2 * (1 + a + c) + 3)) (2 * (d + b + 1)) x.length - t) hh
  rw [Nat.add_sub_of_le hle] at heq
  rw [heq, hphysical]

lemma StackProgram.inOracleP {Q : Type} [Fintype Q] {r : ℕ} (P : StackProgram Q r)
    (A L : Language) (c d : ℕ)
    (h : ∀ x : Word, ∃ answer : Bool,
      (P.run A x [] (polyBound c d x.length)).answer = some answer ∧ (answer = true ↔ L x)) :
    InOracleP A L := by
  refine ⟨P.compile.compile, 1 + c * (2 * (1 + 0 + c) + 3), 2 * (d + 0 + 1), ?_⟩
  intro x
  obtain ⟨answer, ha, hL⟩ := h x
  exact ⟨answer, P.compiled_answer A 0 0 c d x [] (by simp [polyBound]) answer ha, hL⟩

lemma StackProgram.inOraclePP {Q : Type} [Fintype Q] {r : ℕ} (P : StackProgram Q r)
    (A L : Language) (a b c d : ℕ)
    (hhalt : ∀ x w : Word, w.length = polyBound a b x.length →
      (P.run A x w (polyBound c d x.length)).answer.isSome)
    (hmajority : ∀ x : Word, L x ↔ 2 ^ polyBound a b x.length <
      2 * Set.ncard {w : Word | w.length = polyBound a b x.length ∧
        (P.run A x w (polyBound c d x.length)).answer = some true}) : InOraclePP A L := by
  classical
  refine ⟨P.compile.compile, 1 + c * (2 * (1 + a + c) + 3), 2 * (d + b + 1), a, b, ?_, ?_⟩
  · intro x w hw
    obtain ⟨answer, ha⟩ := Option.isSome_iff_exists.mp (hhalt x w hw)
    rw [P.compiled_answer A a b c d x w hw answer ha]
    rfl
  · intro x
    have hsets : {w : Word | w.length = polyBound a b x.length ∧
        (machineRun P.compile.compile A x w
          (polyBound (1 + c * (2 * (1 + a + c) + 3)) (2 * (d + b + 1)) x.length)).answer = some true} =
        {w : Word | w.length = polyBound a b x.length ∧
          (P.run A x w (polyBound c d x.length)).answer = some true} := by
      ext w
      by_cases hw : w.length = polyBound a b x.length
      · obtain ⟨answer, ha⟩ := Option.isSome_iff_exists.mp (hhalt x w hw)
        simp only [Set.mem_setOf_eq, hw, true_and]
        rw [P.compiled_answer A a b c d x w hw answer ha, ha]
      · simp only [Set.mem_setOf_eq, hw, false_and]
    rw [hsets]
    exact hmajority x

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

inductive MajorityQueryState where
  | seedLoop | seedZero | seedOne
  | backLoop | backZero | backOne
  | delimiter
  | inputLoop | inputZero | inputOne
  | escapeLoop | escapeZero | escapeOne | escapeFlag
  | query | answer (b : Bool)
  deriving DecidableEq,Fintype

open MajorityQueryState in
noncomputable def majorityQueryProgram : StackProgram MajorityQueryState 2 where
  initial:=.seedLoop
  transition:=fun q => match q with
    | .seedLoop => .pop 1 .seedZero .seedOne .backLoop
    | .seedZero => .push 3 false .seedLoop
    | .seedOne => .push 3 true .seedLoop
    | .backLoop => .pop 3 .backZero .backOne .delimiter
    | .backZero => .push 2 false .backLoop
    | .backOne => .push 2 true .backLoop
    | .delimiter => .push 2 false .inputLoop
    | .inputLoop => .pop 0 .inputZero .inputOne .escapeLoop
    | .inputZero => .push 3 false .inputLoop
    | .inputOne => .push 3 true .inputLoop
    | .escapeLoop => .pop 3 .escapeZero .escapeOne .query
    | .escapeZero => .push 2 false .escapeFlag
    | .escapeOne => .push 2 true .escapeFlag
    | .escapeFlag => .push 2 true .escapeLoop
    | .query => .query 2 (.answer true) (.answer false)
    | .answer b => .halt b

open MajorityQueryState in
lemma majorityQueryProgram_answer (A : Language) (x w : Word) :
    (majorityQueryProgram.run A x w (5*x.length+4*w.length+7)).answer =
      some (@decide (A (pairWord x w)) (Classical.propDecidable _)) := by
  classical
  let P:=majorityQueryProgram
  let C0:=P.initialConfig x w
  let C1 : StackConfig MajorityQueryState 2 := {state:=.backLoop,regs:=![x,[],[],w.reverse],answer:=none}
  let C2 : StackConfig MajorityQueryState 2 := {state:=.delimiter,regs:=![x,[],w,[]],answer:=none}
  let C3 : StackConfig MajorityQueryState 2 := {state:=.inputLoop,regs:=![x,[],false::w,[]],answer:=none}
  let C4 : StackConfig MajorityQueryState 2 := {state:=.escapeLoop,regs:=![[],[],false::w,x.reverse],answer:=none}
  let C5 : StackConfig MajorityQueryState 2 := {state:=.query,regs:=![[],[],pairWord x w,[]],answer:=none}
  have h1 : P.exec A C0 (2*w.length+1)=C1 := by
    rw [stack_reverse_routine P A 1 3 (by decide) .seedLoop .seedZero .seedOne .backLoop
      rfl rfl rfl C0 rfl rfl w (by simp [C0,StackProgram.initialConfig])]
    congr 1
    funext j
    fin_cases j <;> simp [C0,C1,StackProgram.initialConfig]
  have h2 : P.exec A C1 (2*w.length+1)=C2 := by
    have hh:=stack_reverse_routine P A 3 2 (by decide) .backLoop .backZero .backOne .delimiter
      rfl rfl rfl C1 rfl rfl w.reverse rfl
    rw [List.length_reverse] at hh
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [C1,C2]
  have h3 : P.step A C2=C3 := by
    simp [P,StackProgram.step,majorityQueryProgram,C2,C3]
    funext j
    fin_cases j <;> rfl
  have h4 : P.exec A C3 (2*x.length+1)=C4 := by
    rw [stack_reverse_routine P A 0 3 (by decide) .inputLoop .inputZero .inputOne .escapeLoop
      rfl rfl rfl C3 rfl rfl x rfl]
    congr 1
    funext j
    fin_cases j <;> simp [C3,C4]
  have h5 : P.exec A C4 (3*x.length+1)=C5 := by
    have hh:=stack_escaped_prefix_routine P A 3 2 (by decide) .escapeLoop .escapeZero .escapeOne .escapeFlag .query
      rfl rfl rfl rfl C4 rfl rfl x.reverse rfl
    rw [List.length_reverse] at hh
    rw [hh]
    congr 1
    funext j
    fin_cases j <;> simp [C4,C5,pairWord,List.append_assoc]
  have h6 : (P.step A (P.step A C5)).answer=some (decide (A (pairWord x w))) := by
    by_cases ha : A (pairWord x w) <;> simp [P,StackProgram.step,majorityQueryProgram,C5,ha]
  have ht : 5*x.length+4*w.length+7=(2*w.length+1)+((2*w.length+1)+(1+((2*x.length+1)+((3*x.length+1)+(1+1))))) := by omega
  change (P.exec A C0 _).answer=_
  rw [ht,StackProgram.exec_add,h1,StackProgram.exec_add,h2,StackProgram.exec_add,StackProgram.exec_one,h3,
    StackProgram.exec_add,h4,StackProgram.exec_add,h5,StackProgram.exec_add,StackProgram.exec_one,StackProgram.exec_one]
  exact h6

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma StackProgram.exec_eq_self_of_halted {Q : Type} {r : ℕ} (P : StackProgram Q r)
    (A : Language) (cfg : StackConfig Q r) (h : cfg.answer.isSome) (t : ℕ) : P.exec A cfg t=cfg := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [StackProgram.exec_succ,ih]
    simp only [StackProgram.step,h,ite_true]

lemma majorityQueryProgram_time_bound (a b n : ℕ) :
    5*n+4*polyBound a b n+7 ≤ polyBound (12+4*a) (b+1) n := by
  let V := (n+1)^(b+1)
  have hV : 1≤V := Nat.one_le_pow _ _ (by omega)
  have hn : n≤V := by
    have hh : n+1≤V := by
      calc
        n+1=(n+1)^1 := by simp
        _ ≤ (n+1)^(b+1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hp : polyBound a b n ≤ a*V := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  change _ ≤ (12+4*a)*V
  nlinarith

lemma majorityQueryProgram_answer_poly (A : Language) (a b : ℕ) (x w : Word)
    (hw : w.length=polyBound a b x.length) :
    (majorityQueryProgram.run A x w (polyBound (12+4*a) (b+1) x.length)).answer =
      some (@decide (A (pairWord x w)) (Classical.propDecidable _)) := by
  have hle : 5*x.length+4*w.length+7≤polyBound (12+4*a) (b+1) x.length := by
    rw [hw]
    exact majorityQueryProgram_time_bound a b x.length
  let t:=5*x.length+4*w.length+7
  have ha:=majorityQueryProgram_answer A x w
  have hh : (majorityQueryProgram.run A x w t).answer.isSome := by rw [ha];rfl
  have heq := majorityQueryProgram.exec_eq_self_of_halted A (majorityQueryProgram.run A x w t) hh
    (polyBound (12+4*a) (b+1) x.length-t)
  have ht : polyBound (12+4*a) (b+1) x.length=t+(polyBound (12+4*a) (b+1) x.length-t) := by omega
  change (majorityQueryProgram.exec A (majorityQueryProgram.initialConfig x w) _).answer=_
  rw [ht,StackProgram.exec_add]
  change (majorityQueryProgram.exec A (majorityQueryProgram.run A x w t) _).answer=_
  rw [heq]
  exact ha

noncomputable def boundedMajorityLanguage (A : Language) (a b : ℕ) : Language := fun x =>
  2^polyBound a b x.length < 2*Set.ncard {w : Word | w.length=polyBound a b x.length ∧ A (pairWord x w)}

lemma bounded_majority_inOraclePP (A : Language) (a b : ℕ) :
    InOraclePP A (boundedMajorityLanguage A a b) := by
  classical
  apply majorityQueryProgram.inOraclePP A _ a b (12+4*a) (b+1)
  · intro x w hw
    rw [majorityQueryProgram_answer_poly A a b x w hw]
    rfl
  · intro x
    have hs : {w : Word | w.length=polyBound a b x.length ∧
        (majorityQueryProgram.run A x w (polyBound (12+4*a) (b+1) x.length)).answer=some true} =
        {w : Word | w.length=polyBound a b x.length ∧ A (pairWord x w)} := by
      ext w
      by_cases hw : w.length=polyBound a b x.length
      · simp only [Set.mem_setOf_eq,hw,true_and]
        rw [majorityQueryProgram_answer_poly A a b x w hw]
        simp
      · simp only [Set.mem_setOf_eq,hw,false_and]
    rw [hs]
    rfl

lemma AtCHLevel.bounded_majority {A : Language} {j : ℕ} (hA : AtCHLevel j A) (a b : ℕ) :
    AtCHLevel (j+1) (boundedMajorityLanguage A a b) :=
  ⟨A,hA,bounded_majority_inOraclePP A a b⟩

end APSCounting893.Main
end Component_21

open APSCounting893.Main
theorem solution (A : Language) (a b : ℕ) :
    InOraclePP A (fun x =>
      2^polyBound a b x.length < 2*Set.ncard
        {w : Word | w.length=polyBound a b x.length ∧ A (pairWord x w)}) := by
  exact bounded_majority_inOraclePP A a b
