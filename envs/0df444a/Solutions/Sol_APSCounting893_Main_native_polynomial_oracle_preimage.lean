-- Prove2me | solution 1 for APSCounting893.Main.native_polynomial_oracle_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T19:43:18.820203+00:00
-- url     : https://prove2.me/submissions/bfa2b956-f598-4f7a-b07a-3a6a03e09c2b

import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Bool
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
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
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

inductive OutputOracleControl (Q : Type) where
  | running (q : Q)
  | answer (b : Bool)
  deriving DecidableEq,Fintype

def ProgramQueryUnused {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k) : Prop :=
  ∀ q read,match P.transition q read with
    | .step _ write move => write P.queryTape=read P.queryTape ∧ move P.queryTape=.stay
    | .query _ _ => False
    | .halt _ => True

def blankQueryRead {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (read : Fin k → TapeSymbol a) (j : Fin k) : TapeSymbol a :=
  if j=P.queryTape then .blank else read j

noncomputable def outputOracleProgram {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k) :
    FiniteProgram (OutputOracleControl Q) a k where
  inputTape:=P.inputTape
  randomTape:=P.randomTape
  queryTape:=P.queryTape
  outputTape:=P.outputTape
  distinctTapes:=P.distinctTapes
  initial:=.running P.initial
  transition:=fun q read => match q with
    | .answer b => .halt b
    | .running q => match P.transition q (blankQueryRead P read) with
      | .halt _ => .query (.answer true) (.answer false)
      | .query yes no => .query (.running yes) (.running no)
      | .step next write move =>
        .step (.running next)
          (fun j => if j=P.queryTape then write P.outputTape else write j)
          (fun j => if j=P.queryTape then move P.outputTape else move j)

structure OutputOracleRelated {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (s : ProgramConfig (OutputOracleControl Q) a k) (t : ProgramConfig Q a k) : Prop where
  state : s.state=.running t.state
  sourceAnswer : t.answer=none
  targetAnswer : s.answer=none
  otherTape : ∀ j,j≠P.queryTape → s.tapes j=t.tapes j
  sourceQuery : ∀ z,(t.tapes P.queryTape).read z=.blank
  mirror : s.tapes P.queryTape=s.tapes P.outputTape

lemma outputOracle_distinct {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k) :
    P.queryTape≠P.outputTape ∧ P.queryTape≠P.inputTape ∧ P.queryTape≠P.randomTape ∧
      P.outputTape≠P.inputTape ∧ P.outputTape≠P.randomTape := by
  have h := P.distinctTapes
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals intro heq
  · have := h (a₁:=2) (a₂:=3) heq
    have hv := congrArg Fin.val this
    norm_num at hv
  · have := h (a₁:=2) (a₂:=0) heq
    have hv := congrArg Fin.val this
    norm_num at hv
  · have := h (a₁:=2) (a₂:=1) heq
    have hv := congrArg Fin.val this
    norm_num at hv
  · have := h (a₁:=3) (a₂:=0) heq
    have hv := congrArg Fin.val this
    norm_num at hv
  · have := h (a₁:=3) (a₂:=1) heq
    have hv := congrArg Fin.val this
    norm_num at hv

lemma OutputOracleRelated.read {Q : Type} {a k : ℕ} {P : FiniteProgram Q a k}
    {s : ProgramConfig (OutputOracleControl Q) a k} {t : ProgramConfig Q a k}
    (h : OutputOracleRelated P s t) :
    blankQueryRead P (fun j => (s.tapes j).read (s.tapes j).head)=
      (fun j => (t.tapes j).read (t.tapes j).head) := by
  funext j
  by_cases hj : j=P.queryTape
  · subst j
    simp [blankQueryRead,h.sourceQuery]
  · simp [blankQueryRead,hj,h.otherTape j hj]

lemma outputOracle_initial_related {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k) (x : Word) :
    OutputOracleRelated P ((outputOracleProgram P).initialConfig x []) (P.initialConfig x []) := by
  rcases outputOracle_distinct P with ⟨hqo,hqi,hqr,hoi,hor⟩
  refine ⟨rfl,rfl,rfl,fun _ _ => rfl,?_,?_⟩
  · intro z
    simp [FiniteProgram.initialConfig,hqi,hqr,Tape.read]
  · simp [FiniteProgram.initialConfig,outputOracleProgram,hqi,hqr,hoi,hor]

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma outputOracle_step_related {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (hu : ProgramQueryUnused P) (A : Language)
    (s : ProgramConfig (OutputOracleControl Q) a k) (t : ProgramConfig Q a k)
    (h : OutputOracleRelated P s t) (hnext : (P.step (fun _ => False) t).answer=none) :
    OutputOracleRelated P ((outputOracleProgram P).step A s) (P.step (fun _ => False) t) := by
  let read := fun j => (t.tapes j).read (t.tapes j).head
  cases ht : P.transition t.state read with
  | halt b =>
    rw [P.step_halt _ _ b h.sourceAnswer ht] at hnext
    contradiction
  | query yes no =>
    have hb := hu t.state read
    rw [ht] at hb
    exact hb.elim
  | step next write move =>
    have hb := hu t.state read
    rw [ht] at hb
    have hwblank : write P.queryTape=.blank := hb.1.trans (h.sourceQuery _)
    let sw := fun j => if j=P.queryTape then write P.outputTape else write j
    let sm := fun j => if j=P.queryTape then move P.outputTape else move j
    have htr : (outputOracleProgram P).transition s.state
        (fun j => (s.tapes j).read (s.tapes j).head)=.step (.running next) sw sm := by
      simp only [outputOracleProgram,h.state]
      rw [h.read,ht]
    rw [(outputOracleProgram P).step_step A s (.running next) sw sm h.targetAnswer htr,
      P.step_step (fun _ => False) t next write move h.sourceAnswer ht]
    refine ⟨rfl,h.sourceAnswer,h.targetAnswer,?_,?_,?_⟩
    · intro j hj
      simp only [sw,sm,if_neg hj,h.otherTape j hj]
    · intro z
      by_cases hz : z=(t.tapes P.queryTape).head
      · subst z
        rw [tape_step_read_self,hwblank]
      · rw [tape_step_read_ne _ _ _ _ hz,h.sourceQuery]
    · have hoq := (outputOracle_distinct P).1.symm
      change (s.tapes P.queryTape).step (sw P.queryTape) (sm P.queryTape)=
        (s.tapes P.outputTape).step (sw P.outputTape) (sm P.outputTape)
      simp only [sw,sm,if_pos rfl,if_neg hoq,h.mirror]

lemma outputOracle_run_related {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (hu : ProgramQueryUnused P) (A : Language) (x : Word) (T : ℕ)
    (hT : ∀ t ≤ T,(P.run (fun _ => False) x [] t).answer=none) :
    OutputOracleRelated P ((outputOracleProgram P).run A x [] T) (P.run (fun _ => False) x [] T) := by
  induction T with
  | zero => exact outputOracle_initial_related P x
  | succ T ih =>
    rw [FiniteProgram.run_succ,FiniteProgram.run_succ]
    apply outputOracle_step_related P hu A _ _
      (ih (fun t ht => hT t (by omega)))
    simpa only [FiniteProgram.run_succ] using hT (T+1) le_rfl

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma finiteProgram_run_halted {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k) (A : Language)
    (x w : Word) (t s : ℕ) (h : (P.run A x w t).answer.isSome) :
    P.run A x w (t+s)=P.run A x w t := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.add_succ,FiniteProgram.run_succ,ih]
    simp only [FiniteProgram.step,h,ite_true]

lemma outputOracle_halt_answer {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k) (A : Language)
    (s : ProgramConfig (OutputOracleControl Q) a k) (t : ProgramConfig Q a k)
    (h : OutputOracleRelated P s t) (b : Bool)
    (ht : P.transition t.state (fun j => (t.tapes j).read (t.tapes j).head)=.halt b) :
    (((outputOracleProgram P).step A)^[2] s).answer=
      some (@decide (A (t.tapes P.outputTape).word) (Classical.propDecidable _)) := by
  classical
  have hquery : (s.tapes P.queryTape).word=(t.tapes P.outputTape).word := by
    rw [h.mirror,h.otherTape _ (outputOracle_distinct P).1.symm]
  have htr : (outputOracleProgram P).transition s.state
      (fun j => (s.tapes j).read (s.tapes j).head)=.query (.answer true) (.answer false) := by
    simp only [outputOracleProgram,h.state]
    rw [h.read,ht]
  change ((outputOracleProgram P).step A ((outputOracleProgram P).step A s)).answer=_
  simp only [FiniteProgram.step,h.targetAnswer,Option.isSome_none,Bool.false_eq_true,ite_false,htr]
  by_cases ha : A (t.tapes P.outputTape).word
  · simp [outputOracleProgram,hquery,ha]
  · simp [outputOracleProgram,hquery,ha]

lemma finiteProgram_first_halt {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k) (x : Word)
    (T : ℕ) (hT : (P.run (fun _ => False) x [] T).answer.isSome) :
    ∃ t b,t+1 ≤ T ∧
      (∀ u ≤ t,(P.run (fun _ => False) x [] u).answer=none) ∧
      P.transition (P.run (fun _ => False) x [] t).state
        (fun j => ((P.run (fun _ => False) x [] t).tapes j).read
          ((P.run (fun _ => False) x [] t).tapes j).head)=.halt b ∧
      (P.run (fun _ => False) x [] t).tapes=(P.run (fun _ => False) x [] T).tapes := by
  have hex : ∃ t,(P.run (fun _ => False) x [] t).answer.isSome := ⟨T,hT⟩
  let tau:=Nat.find hex
  have htau : (P.run (fun _ => False) x [] tau).answer.isSome := Nat.find_spec hex
  have hle : tau ≤ T := Nat.find_min' hex hT
  have hbefore : ∀ u < tau,(P.run (fun _ => False) x [] u).answer=none := by
    intro u hu
    have hn := Nat.find_min hex hu
    cases ha : (P.run (fun _ => False) x [] u).answer <;> simp_all
  have hpos : 0 < tau := by
    by_contra hn
    have heq : tau=0 := by omega
    simp [heq,FiniteProgram.run,FiniteProgram.initialConfig] at htau
  obtain ⟨t,heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hnone := hbefore t (by omega)
  have hpersist := finiteProgram_run_halted P (fun _ => False) x [] tau (T-tau) htau
  rw [Nat.add_sub_of_le hle] at hpersist
  rw [heq,FiniteProgram.run_succ] at htau hpersist
  cases htr : P.transition (P.run (fun _ => False) x [] t).state
      (fun j => ((P.run (fun _ => False) x [] t).tapes j).read
        ((P.run (fun _ => False) x [] t).tapes j).head) with
  | step next write move => simp [FiniteProgram.step,hnone,htr] at htau
  | query yes no => simp [FiniteProgram.step,hnone,htr] at htau
  | halt b =>
    refine ⟨t,b,by omega,fun u hu => hbefore u (by omega),htr,?_⟩
    rw [P.step_halt _ _ b hnone htr] at hpersist
    exact (congrArg ProgramConfig.tapes hpersist).symm

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma finiteProgram_run_add {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k) (A : Language)
    (x w : Word) (t s : ℕ) :
    P.run A x w (t+s)=(P.step A)^[s] (P.run A x w t) := by
  unfold FiniteProgram.run
  rw [Nat.add_comm,Function.iterate_add_apply]

lemma outputOracleProgram_computation {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k)
    (hu : ProgramQueryUnused P) (A : Language) (x : Word) (T : ℕ)
    (hT : (P.run (fun _ => False) x [] T).answer.isSome) :
    ((outputOracleProgram P).run A x [] (T+1)).answer=
      some (@decide (A ((P.run (fun _ => False) x [] T).tapes P.outputTape).word)
        (Classical.propDecidable _)) := by
  classical
  obtain ⟨t,b,ht,hbefore,hhalt,htapes⟩ := finiteProgram_first_halt P x T hT
  have hrel := outputOracle_run_related P hu A x t hbefore
  have ha := outputOracle_halt_answer P A _ _ hrel b hhalt
  rw [htapes] at ha
  have hrun : ((outputOracleProgram P).run A x [] (t+2)).answer=
      some (@decide (A ((P.run (fun _ => False) x [] T).tapes P.outputTape).word)
        (Classical.propDecidable _)) := by
    rw [finiteProgram_run_add]
    exact ha
  have his : ((outputOracleProgram P).run A x [] (t+2)).answer.isSome := by rw [hrun];rfl
  have htime : t+2 ≤ T+1 := by omega
  have hpersist := finiteProgram_run_halted (outputOracleProgram P) A x [] (t+2)
    (T+1-(t+2)) his
  rw [Nat.add_sub_of_le htime] at hpersist
  rw [hpersist]
  exact hrun

end APSCounting893.Main
end Component_6

section Component_7

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
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def nativeSymbol (b : Option Bool) : TapeSymbol 2:=match b with | none=>.blank | some b=>.bit b
def readNativeSymbol : TapeSymbol 2 → Option Bool | .bit b=>some b | _=>none
@[simp] lemma read_nativeSymbol (b : Option Bool) : readNativeSymbol (nativeSymbol b)=b := by cases b <;> rfl

def nativeMove : SignType → Move | .neg=>.left | .zero=>.stay | .pos=>.right

def moveOffset : Move → ℤ | .left=>-1 | .stay=>0 | .right=>1
@[simp] lemma nativeMove_offset (m : SignType) : moveOffset (nativeMove m)=(m.cast:ℤ) := by cases m <;> rfl

def nativeInputMove (s : TapeSymbol 2) : SignType → Move
  | .neg=>if s=.extra 0 then .stay else .left
  | .zero=>.stay
  | .pos=>if s=.extra 1 then .stay else .right

def nativeWorkTape {k : ℕ} (j : Fin k) : Fin (k+4):=⟨j.val+4,by omega⟩

lemma nativeWorkTape_injective (k : ℕ) : Function.Injective (@nativeWorkTape k) := by
  intro i j h
  apply Fin.ext
  have hh:=congrArg Fin.val h
  dsimp [nativeWorkTape] at hh
  omega

lemma nativeWorkTape_ne_small {k : ℕ} (j : Fin k) (i : ℕ) (hi : i<4) : nativeWorkTape j≠Fin.ofNat (k+4) i := by
  intro h
  have hv:=congrArg Fin.val h
  change j.val+4=i%(k+4) at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  omega

inductive NativeControl (Q : Type) where
  | markLeft | scanRight | scanLeft | simulate (state : Option Q) (last : Bool)
  deriving DecidableEq,Fintype

def nativeWrites {Q : Type} {k : ℕ} (act : Turing.Action k Bool Q)
    (s : Fin (k+4) → TapeSymbol 2) (j : Fin (k+4)) : TapeSymbol 2 :=
  if hj : 4≤j.val then
    match (act.workTapes ⟨j.val-4,by have hh:=j.isLt;omega⟩).1 with
    | none=>s j
    | some b=>nativeSymbol b
  else if j=3 then match act.output with | none=>s j | some b=>.bit b
  else s j

def nativeMoves {Q : Type} {k : ℕ} (act : Turing.Action k Bool Q)
    (s : Fin (k+4) → TapeSymbol 2) (j : Fin (k+4)) : Move :=
  if hj : 4≤j.val then nativeMove (act.workTapes ⟨j.val-4,by have hh:=j.isLt;omega⟩).2
  else if j=0 then nativeInputMove (s 0) act.inputTape
  else if j=3 then if act.output.isSome then .right else .stay
  else .stay

noncomputable def nativeProgram {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q)
    (answerFromOutput : Bool) : FiniteProgram (NativeControl Q) 2 (k+4) where
  inputTape:=0
  randomTape:=1
  queryTape:=2
  outputTape:=3
  distinctTapes:=by
    intro i j h
    have hv:=congrArg Fin.val h
    fin_cases i <;> fin_cases j
    all_goals first | rfl | (norm_num [Nat.mod_eq_of_lt (show 0<k+4 by omega),Nat.mod_eq_of_lt (show 1<k+4 by omega),Nat.mod_eq_of_lt (show 2<k+4 by omega),Nat.mod_eq_of_lt (show 3<k+4 by omega)] at hv)
  initial:=.markLeft
  transition:=fun q s=>match q with
    | .markLeft=>.step .scanRight (fun j=>if j=0 then .extra 0 else s j) (fun j=>if j=0 then .right else .stay)
    | .scanRight=>match s 0 with
      | .bit _=>.step .scanRight s (fun j=>if j=0 then .right else .stay)
      | _=>.step .scanLeft (fun j=>if j=0 then .extra 1 else s j) (fun j=>if j=0 then .left else .stay)
    | .scanLeft=>if s 0=.extra 0 then
        .step (.simulate (some tm.q₀) false) s (fun j=>if j=0 ∨ j=3 then .right else .stay)
      else .step .scanLeft s (fun j=>if j=0 then .left else .stay)
    | .simulate none last=>.halt (if answerFromOutput then last else true)
    | .simulate (some q) last=>
      let act:=tm.tr q (readNativeSymbol (s 0)) (fun j=>readNativeSymbol (s (nativeWorkTape j)))
      .step (.simulate act.state (act.output.getD last))
        (nativeWrites act s) (nativeMoves act s)

structure NativeInputTape {k : ℕ} {Q : Type} {x : Word} (t : Tape 2) (cfg : Turing.Cfg k Bool Q x) : Prop where
  head : t.head=cfg.inputPos.val
  left : t.read 0=.extra 0
  right : t.read (x.length+1)=.extra 1
  bits : ∀ (i : ℕ) (hi : i<x.length),t.read (i+1)=.bit x[i]

structure NativeRepresentation {k : ℕ} {Q : Type} {x : Word}
    (pc : ProgramConfig (NativeControl Q) 2 (k+4)) (cfg : Turing.Cfg k Bool Q x) : Prop where
  state : pc.state=.simulate cfg.state (cfg.output.getLastD false)
  answer : pc.answer=none
  input : NativeInputTape (pc.tapes 0) cfg
  workHead : ∀ j,(pc.tapes (nativeWorkTape j)).head=cfg.workTapePos j
  workRead : ∀ j p,(pc.tapes (nativeWorkTape j)).read p=nativeSymbol (cfg.workTapes j p)
  output : TapePrefix (pc.tapes 3) cfg.output

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma nativeProgram_query_unused {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool) :
    ProgramQueryUnused (nativeProgram tm mode) := by
  have h20 : (2 : Fin (k+4))≠0 := by
    intro h
    have hv:=congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (show 2<k+4 by omega),Nat.mod_eq_of_lt (show 0<k+4 by omega)] at hv
  have h23 : (2 : Fin (k+4))≠3 := by
    intro h
    have hv:=congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (show 2<k+4 by omega),Nat.mod_eq_of_lt (show 3<k+4 by omega)] at hv
  have hval : (2 : Fin (k+4)).val=2 := by
    change 2%(k+4)=2
    exact Nat.mod_eq_of_lt (by omega)
  have hmod : 2%(k+4)=2 := Nat.mod_eq_of_lt (by omega)
  intro q read
  cases q with
  | markLeft => simp [nativeProgram,h20]
  | scanRight => cases hr : read 0 <;> simp [nativeProgram,hr,h20]
  | scanLeft => by_cases hr : read 0=.extra 0 <;> simp [nativeProgram,hr,h20,h23]
  | simulate state last =>
    cases state with
    | none => trivial
    | some q => simp [nativeProgram,nativeWrites,nativeMoves,h20,h23,hval,hmod]

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

structure NativeSetup {Q : Type} {k : ℕ} (pc : ProgramConfig (NativeControl Q) 2 (k+4)) (x : Word)
    (rightMarked : Bool) : Prop where
  left : (pc.tapes 0).read 0=.extra 0
  right : (pc.tapes 0).read (x.length+1)=if rightMarked then .extra 1 else .blank
  bits : ∀ (i : ℕ) (hi : i<x.length),(pc.tapes 0).read (i+1)=.bit x[i]
  otherHead : ∀ j,j≠0 → (pc.tapes j).head=0
  otherRead : ∀ j,j≠0 → ∀ p,(pc.tapes j).read p=.blank

lemma NativeSetup.transport {Q : Type} {k : ℕ} {pc out : ProgramConfig (NativeControl Q) 2 (k+4)}
    {x : Word} {mark : Bool} (h : NativeSetup pc x mark)
    (hhead : ∀ j,j≠0 → (out.tapes j).head=(pc.tapes j).head)
    (hread : ∀ j p,(out.tapes j).read p=(pc.tapes j).read p) : NativeSetup out x mark := by
  constructor
  · rw [hread];exact h.left
  · rw [hread];exact h.right
  · intro i hi;rw [hread];exact h.bits i hi
  · intro j hj;rw [hhead j hj];exact h.otherHead j hj
  · intro j hj p;rw [hread];exact h.otherRead j hj p

lemma native_blank_tape_start (t : Tape 2) (hhead : t.head=0) (hread : ∀ p,t.read p=.blank) :
    TapePrefix (t.step (t.read t.head) .right) [] := by
  constructor
  · simp [Tape.step,hhead]
  · intro j
    rw [tape_step_same_reads,hread]
    simp

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma native_initial_input {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool) (x : Word) :
    ((nativeProgram tm mode).initialConfig x []).tapes 0=Tape.input x := by
  simp [FiniteProgram.initialConfig,nativeProgram]

lemma native_initial_other {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool) (x : Word)
    (j : Fin (k+4)) (hj : j≠0) :
    (((nativeProgram tm mode).initialConfig x []).tapes j).head=0 ∧
      ∀ p,(((nativeProgram tm mode).initialConfig x []).tapes j).read p=.blank := by
  simp [FiniteProgram.initialConfig,nativeProgram,hj,Tape.input,Tape.read]

lemma native_mark_left {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) (x : Word) :
    let out:=(nativeProgram tm mode).run A x [] 1
    out.state=.scanRight ∧ out.answer=none ∧ (out.tapes 0).head=1 ∧ NativeSetup out x false := by
  classical
  let cfg:=(nativeProgram tm mode).initialConfig x []
  let out : ProgramConfig (NativeControl Q) 2 (k+4):=
    {state:=.scanRight,tapes:=fun j=>(cfg.tapes j).step
      (if j=0 then .extra 0 else (cfg.tapes j).read (cfg.tapes j).head)
      (if j=0 then .right else .stay),answer:=none}
  have hstep : (nativeProgram tm mode).run A x [] 1=out := by
    rfl
  rw [hstep]
  refine ⟨rfl,rfl,?_,?_⟩
  · simp [out,cfg,native_initial_input,Tape.step,Tape.input]
  · constructor
    · change ((cfg.tapes 0).step (.extra 0) .right).read 0=.extra 0
      have hh : (cfg.tapes 0).head=0 := by simp [cfg,native_initial_input,Tape.input]
      rw [←hh,tape_step_read_self]
    · change ((cfg.tapes 0).step (.extra 0) .right).read ((x.length:ℤ)+1)=.blank
      rw [tape_step_read_ne]
      · rw [show cfg.tapes 0=Tape.input x from native_initial_input tm mode x]
        simpa only [tape_input_read,dif_neg (show ¬x.length<x.length by omega)] using
          (show (Tape.input x : Tape 2).read ((x.length:ℤ)+1)=.blank from by simp [tape_input_read])
      · simp [cfg,native_initial_input,Tape.input]
        omega
    · intro i hi
      change ((cfg.tapes 0).step (.extra 0) .right).read ((i:ℤ)+1)=.bit x[i]
      rw [tape_step_read_ne]
      · rw [show cfg.tapes 0=Tape.input x from native_initial_input tm mode x]
        simpa only [tape_input_read,dif_pos hi] using (tape_input_read (a:=2) x i)
      · simp [cfg,native_initial_input,Tape.input]
        omega
    · intro j hj
      change ((cfg.tapes j).step _ _).head=0
      simp only [if_neg hj,Tape.step,add_zero]
      exact (native_initial_other tm mode x j hj).1
    · intro j hj p
      change ((cfg.tapes j).step _ _).read p=.blank
      simp only [if_neg hj,tape_step_same_reads]
      exact (native_initial_other tm mode x j hj).2 p

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma finiteProgram_scan_bits {Q : Type} {a k : ℕ} (P : FiniteProgram Q a k) (A : Language)
    (src : Fin k) (loop : Q) (direction : Move)
    (hloop : ∀ (s : Fin k → TapeSymbol a) (b : Bool),s src=.bit b →
      P.transition loop s=.step loop s (fun j=>if j=src then direction else .stay))
    (cfg : ProgramConfig Q a k) (hs : cfg.state=loop) (ha : cfg.answer=none) (n : ℕ)
    (hbits : ∀ i : ℕ,i<n → ∃ b : Bool,(cfg.tapes src).read ((cfg.tapes src).head+(i:ℤ)*moveOffset direction)=.bit b) :
    let out:=P.exec A cfg n
    out.state=loop ∧ out.answer=none ∧
      (out.tapes src).head=(cfg.tapes src).head+(n:ℤ)*moveOffset direction ∧
      (∀ j,j≠src → (out.tapes j).head=(cfg.tapes j).head) ∧
      (∀ j p,(out.tapes j).read p=(cfg.tapes j).read p) := by
  classical
  induction n generalizing cfg with
  | zero => exact ⟨hs,ha,by simp [FiniteProgram.exec],by intro j hj;rfl,by intro j p;rfl⟩
  | succ n ih =>
    obtain ⟨b,hb⟩:=hbits 0 (by omega)
    simp only [Nat.cast_zero,zero_mul,add_zero] at hb
    let cfg1 : ProgramConfig Q a k:=
      {state:=loop,tapes:=fun j=>(cfg.tapes j).step ((cfg.tapes j).read (cfg.tapes j).head)
        (if j=src then direction else .stay),answer:=none}
    have hstep : P.step A cfg=cfg1 := by
      have htr:=hloop (fun j=>(cfg.tapes j).read (cfg.tapes j).head) b hb
      simp [FiniteProgram.step,hs,ha,htr,cfg1]
    have hread1 : ∀ j p,(cfg1.tapes j).read p=(cfg.tapes j).read p := by
      intro j p
      exact tape_step_same_reads _ _ _
    have hhead1 : (cfg1.tapes src).head=(cfg.tapes src).head+moveOffset direction := by
      dsimp only [cfg1]
      simp only [ite_true]
      rfl
    have hbits1 : ∀ i : ℕ,i<n → ∃ b : Bool,(cfg1.tapes src).read
        ((cfg1.tapes src).head+(i:ℤ)*moveOffset direction)=.bit b := by
      intro i hi
      obtain ⟨b,hb⟩:=hbits (i+1) (by omega)
      refine ⟨b,?_⟩
      rw [hread1,hhead1]
      have he : (cfg.tapes src).head+moveOffset direction+(i:ℤ)*moveOffset direction=
          (cfg.tapes src).head+((i+1:ℕ):ℤ)*moveOffset direction := by push_cast;ring
      rw [he]
      exact hb
    have hrec:=ih cfg1 rfl rfl hbits1
    rw [show n+1=1+n by omega,FiniteProgram.exec_add,FiniteProgram.exec_one,hstep]
    refine ⟨hrec.1,hrec.2.1,?_,?_,?_⟩
    · rw [hrec.2.2.1,hhead1]
      push_cast
      ring
    · intro j hj
      rw [hrec.2.2.2.1 j hj]
      simp [cfg1,hj,Tape.step]
    · intro j p
      rw [hrec.2.2.2.2 j p,hread1]

end APSCounting893.Main
end Component_12

section Component_13
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma native_scan_input_right {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) (x : Word) (cfg : ProgramConfig (NativeControl Q) 2 (k+4))
    (hs : cfg.state=.scanRight) (ha : cfg.answer=none) (hhead : (cfg.tapes 0).head=1)
    (setup : NativeSetup cfg x false) :
    let out:=(nativeProgram tm mode).exec A cfg x.length
    out.state=.scanRight ∧ out.answer=none ∧ (out.tapes 0).head=(x.length:ℤ)+1 ∧ NativeSetup out x false := by
  have hb : ∀ i : ℕ,i<x.length → ∃ b : Bool,(cfg.tapes 0).read
      ((cfg.tapes 0).head+(i:ℤ)*moveOffset .right)=.bit b := by
    intro i hi
    refine ⟨x[i],?_⟩
    simpa only [hhead,moveOffset,mul_one,add_comm] using setup.bits i hi
  have hscan:=finiteProgram_scan_bits (nativeProgram tm mode) A 0 .scanRight .right
    (by intro s b h;simp [nativeProgram,h]) cfg hs ha x.length hb
  refine ⟨hscan.1,hscan.2.1,?_,setup.transport hscan.2.2.2.1 hscan.2.2.2.2⟩
  rw [hscan.2.2.1,hhead]
  simp [moveOffset,add_comm]

lemma native_mark_right {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) (x : Word) (cfg : ProgramConfig (NativeControl Q) 2 (k+4))
    (hs : cfg.state=.scanRight) (ha : cfg.answer=none) (hhead : (cfg.tapes 0).head=(x.length:ℤ)+1)
    (setup : NativeSetup cfg x false) :
    let out:=(nativeProgram tm mode).step A cfg
    out.state=.scanLeft ∧ out.answer=none ∧ (out.tapes 0).head=x.length ∧ NativeSetup out x true := by
  classical
  have hblank : (cfg.tapes 0).read (cfg.tapes 0).head=.blank := by simpa only [hhead,Bool.false_eq_true,if_false] using setup.right
  let out : ProgramConfig (NativeControl Q) 2 (k+4):=
    {state:=.scanLeft,tapes:=fun j=>(cfg.tapes j).step
      (if j=0 then .extra 1 else (cfg.tapes j).read (cfg.tapes j).head)
      (if j=0 then .left else .stay),answer:=none}
  have hstep : (nativeProgram tm mode).step A cfg=out := by simp [FiniteProgram.step,hs,ha,nativeProgram,hblank,out]
  rw [hstep]
  refine ⟨rfl,rfl,?_,?_⟩
  · simp [out,Tape.step,hhead]
  · constructor
    · change ((cfg.tapes 0).step (.extra 1) .left).read 0=.extra 0
      rw [tape_step_read_ne _ _ _ _ (by rw [hhead];omega)]
      exact setup.left
    · change ((cfg.tapes 0).step (.extra 1) .left).read ((x.length:ℤ)+1)=.extra 1
      rw [←hhead,tape_step_read_self]
    · intro i hi
      change ((cfg.tapes 0).step (.extra 1) .left).read ((i:ℤ)+1)=.bit x[i]
      rw [tape_step_read_ne _ _ _ _ (by rw [hhead];omega)]
      exact setup.bits i hi
    · intro j hj
      change ((cfg.tapes j).step _ _).head=0
      simpa only [if_neg hj,tape_step_head_stay] using setup.otherHead j hj
    · intro j hj p
      change ((cfg.tapes j).step _ _).read p=.blank
      simp only [if_neg hj,tape_step_same_reads]
      exact setup.otherRead j hj p

end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def nativeWorkWrite (old : TapeSymbol 2) : Option (Option Bool) → TapeSymbol 2
  | none=>old
  | some b=>nativeSymbol b

lemma nativeWorkTape_step (t : Tape 2) (contents : ℤ → Option Bool) (pos : ℤ)
    (hhead : t.head=pos) (hread : ∀ i,t.read i=nativeSymbol (contents i))
    (write : Option (Option Bool)) (move : SignType) :
    let t':=t.step (nativeWorkWrite (t.read t.head) write) (nativeMove move)
    t'.head=pos+(move.cast:ℤ) ∧
      ∀ i,t'.read i=nativeSymbol ((match write with | none=>contents | some b=>Function.update contents pos b) i) := by
  constructor
  · change t.head+moveOffset (nativeMove move)=_
    rw [nativeMove_offset,hhead]
  · intro i
    cases write with
    | none => simpa only [nativeWorkWrite,tape_step_same_reads] using hread i
    | some b =>
      change (t.step (nativeSymbol b) (nativeMove move)).read i=nativeSymbol (Function.update contents pos b i)
      by_cases hi : i=pos
      · subst i
        rw [←hhead,tape_step_read_self]
        simp
      · rw [tape_step_read_ne t _ _ i (by rwa [hhead]),Function.update_of_ne hi]
        exact hread i

lemma native_output_last (word : Word) (output : Option Bool) :
    (word++output.toList).getLastD false=output.getD (word.getLastD false) := by
  cases output <;> simp

end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma native_tape_value {k : ℕ} (i : ℕ) (hi : i<4) : (Fin.ofNat (k+4) i).val=i := by
  exact Nat.mod_eq_of_lt (by omega)

lemma nativeWrites_work {Q : Type} {k : ℕ} (act : Turing.Action k Bool Q)
    (s : Fin (k+4) → TapeSymbol 2) (j : Fin k) :
    nativeWrites act s (nativeWorkTape j)=nativeWorkWrite (s (nativeWorkTape j)) (act.workTapes j).1 := by
  unfold nativeWrites
  have hv : 4≤(nativeWorkTape j).val := by dsimp [nativeWorkTape];omega
  rw [dif_pos hv]
  have he : (⟨(nativeWorkTape j).val-4,by have hh:=(nativeWorkTape j).isLt;omega⟩:Fin k)=j := by
    apply Fin.ext
    simp [nativeWorkTape]
  rw [he]
  rfl

lemma nativeMoves_work {Q : Type} {k : ℕ} (act : Turing.Action k Bool Q)
    (s : Fin (k+4) → TapeSymbol 2) (j : Fin k) :
    nativeMoves act s (nativeWorkTape j)=nativeMove (act.workTapes j).2 := by
  unfold nativeMoves
  have hv : 4≤(nativeWorkTape j).val := by dsimp [nativeWorkTape];omega
  rw [dif_pos hv]
  congr 2

lemma nativeWrites_input {Q : Type} {k : ℕ} (act : Turing.Action k Bool Q)
    (s : Fin (k+4) → TapeSymbol 2) : nativeWrites act s 0=s 0 := by
  have h03 : (0:Fin (k+4))≠3 := by
    intro h
    have hh:=congrArg Fin.val h
    change 0%(k+4)=3%(k+4) at hh
    rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hh
    omega
  simp [nativeWrites,h03]

lemma nativeMoves_input {Q : Type} {k : ℕ} (act : Turing.Action k Bool Q)
    (s : Fin (k+4) → TapeSymbol 2) : nativeMoves act s 0=nativeInputMove (s 0) act.inputTape := by
  simp [nativeMoves]

lemma nativeWrites_output {Q : Type} {k : ℕ} (act : Turing.Action k Bool Q)
    (s : Fin (k+4) → TapeSymbol 2) : nativeWrites act s 3=act.output.elim (s 3) TapeSymbol.bit := by
  have hv : (3:Fin (k+4)).val=3 := native_tape_value 3 (by decide)
  simp only [nativeWrites,hv,show ¬4≤3 by omega,dite_false,ite_true]
  cases act.output <;> rfl

lemma nativeMoves_output {Q : Type} {k : ℕ} (act : Turing.Action k Bool Q)
    (s : Fin (k+4) → TapeSymbol 2) : nativeMoves act s 3=if act.output.isSome then .right else .stay := by
  have hv : (3:Fin (k+4)).val=3 := native_tape_value 3 (by decide)
  have h30 : (3:Fin (k+4))≠0 := by
    intro h
    have hh:=congrArg Fin.val h
    change 3%(k+4)=0%(k+4) at hh
    rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hh
    omega
  simp [nativeMoves,Nat.mod_eq_of_lt (show 3<k+4 by omega),h30]

end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma native_scan_input_left {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) (x : Word) (cfg : ProgramConfig (NativeControl Q) 2 (k+4))
    (hs : cfg.state=.scanLeft) (ha : cfg.answer=none) (hhead : (cfg.tapes 0).head=x.length)
    (setup : NativeSetup cfg x true) :
    let out:=(nativeProgram tm mode).exec A cfg x.length
    out.state=.scanLeft ∧ out.answer=none ∧ (out.tapes 0).head=0 ∧ NativeSetup out x true := by
  have hb : ∀ i : ℕ,i<x.length → ∃ b : Bool,(cfg.tapes 0).read
      ((cfg.tapes 0).head+(i:ℤ)*moveOffset .left)=.bit b := by
    intro i hi
    let j:=x.length-(i+1)
    have hj : j<x.length := by dsimp [j];omega
    refine ⟨x[j],?_⟩
    rw [hhead]
    have he : (x.length:ℤ)+(i:ℤ)*moveOffset .left=(j:ℤ)+1 := by dsimp [j,moveOffset];omega
    rw [he]
    exact setup.bits j hj
  have hscan:=finiteProgram_scan_bits (nativeProgram tm mode) A 0 .scanLeft .left
    (by intro s b h;simp [nativeProgram,h]) cfg hs ha x.length hb
  refine ⟨hscan.1,hscan.2.1,?_,setup.transport hscan.2.2.2.1 hscan.2.2.2.2⟩
  rw [hscan.2.2.1,hhead]
  simp [moveOffset]

lemma native_finish_setup {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) (x : Word) (cfg : ProgramConfig (NativeControl Q) 2 (k+4))
    (hs : cfg.state=.scanLeft) (ha : cfg.answer=none) (hhead : (cfg.tapes 0).head=0)
    (setup : NativeSetup cfg x true) :
    NativeRepresentation ((nativeProgram tm mode).step A cfg) (Turing.Cfg.init tm.q₀ x) := by
  classical
  have hmark : (cfg.tapes 0).read (cfg.tapes 0).head=.extra 0 := by rw [hhead];exact setup.left
  let out : ProgramConfig (NativeControl Q) 2 (k+4):=
    {state:=.simulate (some tm.q₀) false,tapes:=fun j=>(cfg.tapes j).step ((cfg.tapes j).read (cfg.tapes j).head)
      (if j=0 ∨ j=3 then .right else .stay),answer:=none}
  have hstep : (nativeProgram tm mode).step A cfg=out := by simp [FiniteProgram.step,hs,ha,nativeProgram,hmark,out]
  rw [hstep]
  constructor
  · rfl
  · rfl
  · constructor
    · simp [out,Tape.step,hhead,Turing.Cfg.init,Nat.mod_eq_of_lt (show 1<x.length+2 by omega)]
    · change ((cfg.tapes 0).step _ _).read 0=.extra 0
      rw [tape_step_same_reads]
      exact setup.left
    · change ((cfg.tapes 0).step _ _).read ((x.length:ℤ)+1)=.extra 1
      rw [tape_step_same_reads]
      exact setup.right
    · intro i hi
      change ((cfg.tapes 0).step _ _).read ((i:ℤ)+1)=.bit x[i]
      rw [tape_step_same_reads]
      exact setup.bits i hi
  · intro j
    have h0:=nativeWorkTape_ne_small j 0 (by decide)
    have h3:=nativeWorkTape_ne_small j 3 (by decide)
    change ((cfg.tapes (nativeWorkTape j)).step _ _).head=0
    have hn : ¬(nativeWorkTape j=0 ∨ nativeWorkTape j=3) := by
      rintro (h|h)
      · exact h0 h
      · exact h3 h
    rw [if_neg hn,tape_step_head_stay]
    exact setup.otherHead _ h0
  · intro j p
    have h0:=nativeWorkTape_ne_small j 0 (by decide)
    change ((cfg.tapes (nativeWorkTape j)).step _ _).read p=.blank
    rw [tape_step_same_reads]
    exact setup.otherRead _ h0 p
  · have h30 : (3:Fin (k+4))≠0 := by
      intro h
      have hh:=congrArg Fin.val h
      change 3%(k+4)=0%(k+4) at hh
      rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hh
      omega
    simpa [out,Turing.Cfg.init] using
      native_blank_tape_start _ (setup.otherHead 3 h30) (setup.otherRead 3 h30)

end APSCounting893.Main
end Component_16

section Component_17
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma nativeProgram_preprocessing {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) (x : Word) :
    NativeRepresentation ((nativeProgram tm mode).run A x [] (2*x.length+3)) (Turing.Cfg.init tm.q₀ x) := by
  let P:=nativeProgram tm mode
  let p1:=P.run A x [] 1
  let p2:=P.exec A p1 x.length
  let p3:=P.step A p2
  let p4:=P.exec A p3 x.length
  let p5:=P.step A p4
  have h1:=native_mark_left tm mode A x
  have h2:=native_scan_input_right tm mode A x p1 h1.1 h1.2.1 h1.2.2.1 h1.2.2.2
  have h3:=native_mark_right tm mode A x p2 h2.1 h2.2.1 h2.2.2.1 h2.2.2.2
  have h4:=native_scan_input_left tm mode A x p3 h3.1 h3.2.1 h3.2.2.1 h3.2.2.2
  have h5 : NativeRepresentation p5 (Turing.Cfg.init tm.q₀ x):=
    native_finish_setup tm mode A x p4 h4.1 h4.2.1 h4.2.2.1 h4.2.2.2
  have hrun : P.run A x [] (2*x.length+3)=p5 := by
    rw [show 2*x.length+3=1+(x.length+(1+(x.length+1))) by omega]
    change P.exec A (P.initialConfig x []) (1+(x.length+(1+(x.length+1))))=p5
    rw [FiniteProgram.exec_add]
    change P.exec A p1 (x.length+(1+(x.length+1)))=p5
    rw [FiniteProgram.exec_add]
    change P.exec A p2 (1+(x.length+1))=p5
    rw [FiniteProgram.exec_add,FiniteProgram.exec_one]
    change P.exec A p3 (x.length+1)=p5
    rw [FiniteProgram.exec_add,FiniteProgram.exec_one]
  rw [hrun]
  exact h5

end APSCounting893.Main
end Component_17

section Component_18
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma NativeInputTape.read_head {k : ℕ} {Q : Type} {x : Word} {t : Tape 2}
    {cfg : Turing.Cfg k Bool Q x} (h : NativeInputTape t cfg) :
    readNativeSymbol (t.read t.head)=cfg.inputSymbol := by
  by_cases hp0 : cfg.inputPos.val=0
  · rw [h.head,hp0]
    simp only [Nat.cast_zero,h.left]
    rw [Turing.inputSymbol_eq_none_of_boundary (Or.inl hp0)]
    rfl
  · by_cases hpend : cfg.inputPos.val=x.length+1
    · rw [h.head,hpend]
      simp only [Nat.cast_add,Nat.cast_one,h.right]
      rw [Turing.inputSymbol_eq_none_of_boundary (Or.inr hpend)]
      rfl
    · have hi : cfg.inputPos.val-1<x.length := by have hh:=cfg.inputPos.isLt;omega
      have hpos : cfg.inputPos.val=1+(cfg.inputPos.val-1) := by omega
      have hh:=h.bits (cfg.inputPos.val-1) hi
      rw [h.head]
      have ht : (cfg.inputPos.val:ℤ)=((cfg.inputPos.val-1:ℕ):ℤ)+1 := by omega
      rw [ht,hh,Turing.inputSymbolInner (cfg.inputPos.val-1) hpos hi]
      rfl

lemma NativeInputTape.move_head {k : ℕ} {Q : Type} {x : Word} {t : Tape 2}
    {cfg : Turing.Cfg k Bool Q x} (h : NativeInputTape t cfg) (m : SignType) :
    t.head+moveOffset (nativeInputMove (t.read t.head) m)=
      ((Turing.moveInputPos cfg.inputPos m).val:ℤ) := by
  have hv:=Turing.val_moveInputPos_eq cfg.inputPos m
  by_cases hp0 : cfg.inputPos.val=0
  · rw [h.head,hp0]
    simp only [Nat.cast_zero,h.left]
    cases m <;> simp [nativeInputMove,moveOffset,Turing.moveInputPos,SignType.cast] at hv ⊢ <;> omega
  · by_cases hpend : cfg.inputPos.val=x.length+1
    · rw [h.head,hpend]
      simp only [Nat.cast_add,Nat.cast_one,h.right]
      cases m <;> simp [nativeInputMove,moveOffset,SignType.cast] at hv ⊢ <;> omega
    · have hi : cfg.inputPos.val-1<x.length := by have hh:=cfg.inputPos.isLt;omega
      have hh:=h.bits (cfg.inputPos.val-1) hi
      have ht : (cfg.inputPos.val:ℤ)=((cfg.inputPos.val-1:ℕ):ℤ)+1 := by omega
      rw [h.head,ht,hh]
      cases m <;> simp [nativeInputMove,moveOffset,SignType.cast] at hv ⊢ <;> omega

lemma NativeInputTape.step {k : ℕ} {Q : Type} {x : Word} {t : Tape 2}
    {cfg : Turing.Cfg k Bool Q x} (h : NativeInputTape t cfg) (act : Turing.Action k Bool Q) :
    NativeInputTape (t.step (t.read t.head) (nativeInputMove (t.read t.head) act.inputTape)) (act.apply cfg) := by
  constructor
  · change t.head+moveOffset (nativeInputMove (t.read t.head) act.inputTape)=_
    exact h.move_head act.inputTape
  · rw [tape_step_same_reads];exact h.left
  · rw [tape_step_same_reads];exact h.right
  · intro i hi
    rw [tape_step_same_reads]
    exact h.bits i hi

end APSCounting893.Main
end Component_18

section Component_19
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def nativeStepConfig {Q : Type} {k : ℕ} (pc : ProgramConfig (NativeControl Q) 2 (k+4))
    (act : Turing.Action k Bool Q) (last : Bool) : ProgramConfig (NativeControl Q) 2 (k+4):=
  let s:=fun j=>(pc.tapes j).read (pc.tapes j).head
  {state:=.simulate act.state (act.output.getD last),
    tapes:=fun j=>(pc.tapes j).step (nativeWrites act s j) (nativeMoves act s j),answer:=none}

lemma nativeProgram_live_step {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) {x : Word} (pc : ProgramConfig (NativeControl Q) 2 (k+4))
    (cfg : Turing.Cfg k Bool Q x) (rep : NativeRepresentation pc cfg) (q : Q) (hq : cfg.state=some q) :
    (nativeProgram tm mode).step A pc=
      nativeStepConfig pc (tm.tr q cfg.inputSymbol cfg.workTapeSymbols) (cfg.output.getLastD false) := by
  classical
  have hinput:=rep.input.read_head
  have hwork : (fun j=>readNativeSymbol ((pc.tapes (nativeWorkTape j)).read (pc.tapes (nativeWorkTape j)).head))=
      cfg.workTapeSymbols := by
    funext j
    rw [rep.workHead j,rep.workRead j]
    simp only [read_nativeSymbol,Turing.Cfg.workTapeSymbols]
  simp only [FiniteProgram.step,rep.answer,Option.isSome_none,Bool.false_eq_true,if_false,nativeProgram,
    rep.state,hq]
  rw [hinput,hwork]
  rfl

lemma nativeRepresentation_live_step {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) {x : Word} (pc : ProgramConfig (NativeControl Q) 2 (k+4))
    (cfg : Turing.Cfg k Bool Q x) (rep : NativeRepresentation pc cfg) (q : Q) (hq : cfg.state=some q) :
    NativeRepresentation ((nativeProgram tm mode).step A pc) (tm.step cfg) := by
  rw [nativeProgram_live_step tm mode A pc cfg rep q hq,tm.step_of_state hq]
  let act:=tm.tr q cfg.inputSymbol cfg.workTapeSymbols
  change NativeRepresentation (nativeStepConfig pc act (cfg.output.getLastD false)) (act.apply cfg)
  constructor
  · simp only [nativeStepConfig,Turing.Action.apply,native_output_last]
  · rfl
  · change NativeInputTape ((pc.tapes 0).step _ _) (act.apply cfg)
    simp only [nativeWrites_input,nativeMoves_input]
    exact rep.input.step act
  · intro j
    change ((pc.tapes (nativeWorkTape j)).step _ _).head=_
    simp only [nativeWrites_work,nativeMoves_work]
    exact (nativeWorkTape_step _ _ _ (rep.workHead j) (rep.workRead j) (act.workTapes j).1 (act.workTapes j).2).1
  · intro j p
    change ((pc.tapes (nativeWorkTape j)).step _ _).read p=_
    simp only [nativeWrites_work,nativeMoves_work]
    have hh:=(nativeWorkTape_step _ _ _ (rep.workHead j) (rep.workRead j) (act.workTapes j).1 (act.workTapes j).2).2 p
    cases hw : (act.workTapes j).1 with
    | none => simpa [Turing.Action.apply,hw,nativeWorkWrite] using hh
    | some b =>
      by_cases hp : p=cfg.workTapePos j <;>
        simpa [Turing.Action.apply,hw,nativeWorkWrite,Function.update,hp] using hh
  · change TapePrefix ((pc.tapes 3).step _ _) (cfg.output++act.output.toList)
    simp only [nativeWrites_output,nativeMoves_output]
    cases ho : act.output with
    | none => simpa [ho] using rep.output.stay
    | some b => simpa [ho] using rep.output.append b

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma nativeProgram_simulate_to_halt {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) (x : Word) (tau : ℕ) (hhalt : tm.HaltsAt (tm.initCfg x) tau) :
    ∀ u : ℕ,u≤tau → NativeRepresentation
      ((nativeProgram tm mode).run A x [] (2*x.length+3+u)) (tm.runFrom (tm.initCfg x) u) := by
  intro u
  induction u with
  | zero =>
    intro hu
    simpa [Turing.MultiTapeTM.runFrom,Turing.MultiTapeNTM.initCfg] using nativeProgram_preprocessing tm mode A x
  | succ u ih =>
    intro hu
    have rep:=ih (by omega)
    have hnot:=hhalt.not_halted (show u<tau by omega)
    cases hq : (tm.runFrom (tm.initCfg x) u).state with
    | none => exact False.elim (hnot hq)
    | some q =>
      rw [show 2*x.length+3+(u+1)=(2*x.length+3+u)+1 by omega,FiniteProgram.run_succ,Turing.MultiTapeTM.runFrom_succ]
      exact nativeRepresentation_live_step tm mode A _ _ rep q hq

lemma nativeProgram_finish {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) {x : Word} (pc : ProgramConfig (NativeControl Q) 2 (k+4))
    (cfg : Turing.Cfg k Bool Q x) (rep : NativeRepresentation pc cfg) (hn : cfg.state=none) :
    ((nativeProgram tm mode).step A pc).answer=some (if mode then cfg.output.getLastD false else true) ∧
      (((nativeProgram tm mode).step A pc).tapes 3).word=cfg.output := by
  have hstep : (nativeProgram tm mode).step A pc=
      {pc with answer:=some (if mode then cfg.output.getLastD false else true)} := by
    simp [FiniteProgram.step,rep.answer,rep.state,hn,nativeProgram]
  rw [hstep]
  exact ⟨rfl,rep.output.word⟩

lemma native_first_halt_output {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q)
    (x output : Word) (T S : ℕ) (h : tm.ComputesInTimeAndSpace x output T S) :
    ∃ tau≤T,tm.HaltsAt (tm.initCfg x) tau ∧ (tm.runFrom (tm.initCfg x) tau).output=output := by
  obtain ⟨tau,htau,hhalt⟩:=Turing.MultiTapeTM.exists_haltsAt (Turing.MultiTapeTM.runsInTime_iff_halted.mp h.2.1)
  obtain ⟨u,hu,houtput⟩:=h.1
  have heq : tm.runFrom (tm.initCfg x) tau=tm.runFrom (tm.initCfg x) u := by
    rcases le_total tau u with htu|hut
    · exact (hhalt.runFrom_eq htu).symm
    · exact tm.runFrom_eq_of_halt _ hut hu
  refine ⟨tau,htau,hhalt,?_⟩
  rw [heq]
  exact houtput

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma nativeProgram_computation {Q : Type} {k : ℕ} (tm : Turing.MultiTapeTM k Bool Q) (mode : Bool)
    (A : Language) (x output : Word) (T S : ℕ) (h : tm.ComputesInTimeAndSpace x output T S) :
    ∃ tau≤T,
      ((nativeProgram tm mode).run A x [] (2*x.length+3+tau+1)).answer=
        some (if mode then output.getLastD false else true) ∧
      (((nativeProgram tm mode).run A x [] (2*x.length+3+tau+1)).tapes 3).word=output := by
  obtain ⟨tau,htau,hhalt,houtput⟩:=native_first_halt_output tm x output T S h
  have rep:=nativeProgram_simulate_to_halt tm mode A x tau hhalt tau (le_refl tau)
  have hfinish:=nativeProgram_finish tm mode A _ _ rep hhalt.halted
  rw [houtput] at hfinish
  refine ⟨tau,htau,?_⟩
  rw [FiniteProgram.run_succ]
  exact hfinish

end APSCounting893.Main
end Component_21

section Component_22
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma native_simulation_clock (c d n tau : ℕ) (h : tau≤c*(n+1)^d) :
    2*n+3+tau+1≤polyBound (c+4) (d+1) n := by
  have hp : (n+1)^d≤(n+1)^(d+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hn : n+1≤(n+1)^(d+1) := by
    calc
      n+1=(n+1)^1 := by simp
      _≤(n+1)^(d+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have ht : tau≤c*(n+1)^(d+1) := h.trans (Nat.mul_le_mul_left c hp)
  unfold polyBound
  nlinarith


end APSCounting893.Main
end Component_22

section Component_23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def negateMachine (M : OracleMachine) : OracleMachine :=
  { M with transition := fun q symbols => match M.transition q symbols with
    | .step q write move => .step q write move
    | .query yes no => .query yes no
    | .halt b => .halt (!b) }

def negateConfig (M : OracleMachine) (cfg : MachineConfig M) : MachineConfig (negateMachine M) where
  state := cfg.state
  tapes := cfg.tapes
  answer := cfg.answer.map Bool.not

lemma negateMachine_step (M : OracleMachine) (A : Language) (cfg : MachineConfig M) :
    machineStep (negateMachine M) A (negateConfig M cfg) = negateConfig M (machineStep M A cfg) := by
  classical
  rcases cfg with ⟨q, tapes, answer⟩
  cases answer with
  | some b => rfl
  | none =>
      cases h : M.transition q (fun j => (tapes j).read (tapes j).head) with
      | step q' write move => simp [machineStep, negateMachine, negateConfig, h]
      | query yes no => simp [machineStep, negateMachine, negateConfig, h]
      | halt b => simp [machineStep, negateMachine, negateConfig, h]

lemma negateMachine_initial (M : OracleMachine) (x w : Word) :
    initialConfig (negateMachine M) x w = negateConfig M (initialConfig M x w) := rfl

lemma negateMachine_run (M : OracleMachine) (A : Language) (x w : Word) (t : ℕ) :
    machineRun (negateMachine M) A x w t = negateConfig M (machineRun M A x w t) := by
  induction t with
  | zero => exact negateMachine_initial M x w
  | succ t ih =>
      rw [machineRun_succ, machineRun_succ, ih, negateMachine_step]

lemma InOracleP.compl {A L : Language} (hL : InOracleP A L) : InOracleP A (fun x => ¬ L x) := by
  obtain ⟨M, c, d, hM⟩ := hL
  refine ⟨negateMachine M, c, d, ?_⟩
  intro x
  obtain ⟨b, hb, hbx⟩ := hM x
  refine ⟨!b, ?_, ?_⟩
  · rw [negateMachine_run]
    change (machineRun M A x [] (polyBound c d x.length)).answer.map Bool.not = some (!b)
    rw [hb]
    rfl
  · cases b <;> simp_all

lemma InOracleP.inOraclePP {A L : Language} (hL : InOracleP A L) : InOraclePP A L := by
  obtain ⟨M, c, d, hM⟩ := hL
  refine ⟨M, c, d, 0, 0, ?_, ?_⟩
  · intro x w hw
    have hw0 : w = [] := List.length_eq_zero_iff.mp (by simpa [polyBound] using hw)
    subst w
    obtain ⟨b, hb, _⟩ := hM x
    rw [hb]
    rfl
  · intro x
    obtain ⟨b, hb, hbx⟩ := hM x
    have hset : {w : Word | w.length = polyBound 0 0 x.length ∧
        (machineRun M A x w (polyBound c d x.length)).answer = some true} =
        if b then {[]} else ∅ := by
      ext w
      simp only [polyBound, zero_mul, List.length_eq_zero_iff, Set.mem_setOf_eq]
      by_cases hw : w = []
      · subst w
        dsimp [polyBound] at hb
        cases b <;> simp [hb]
      · simp [hw]
    rw [hset]
    cases b <;> simp_all [polyBound]

end APSCounting893.Main
end Component_23

section Component_24
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma native_oracle_preimage (f : Word → Word)
    (h : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (A : Language) : InOracleP A (fun x => A (f x)) := by
  classical
  obtain ⟨time,space,htime,hspace,k,Q,hQ,tm,hm⟩ := h
  letI : Finite Q := hQ
  letI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨c,d,hbound⟩ := Cslib.polynomiallyBounded_iff_le.mp htime
  let P := nativeProgram tm false
  let W := outputOracleProgram P
  refine ⟨W.compile,c+5,d+1,?_⟩
  intro x
  have hx : tm.ComputesInTimeAndSpace x (f x) (time x.length) (space x.length) := by
    simpa only [Turing.MultiTapeTM.encBits,Function.Embedding.refl_apply] using hm x
  obtain ⟨tau,htau,hanswer,hword⟩ :=
    nativeProgram_computation tm false (fun _ => False) x (f x) (time x.length) (space x.length) hx
  let start := 2*x.length+3+tau+1
  let T := polyBound (c+4) (d+1) x.length
  have hstart : start ≤ T := native_simulation_clock c d x.length tau (htau.trans (hbound x.length))
  have hanswer' : (P.run (fun _ => False) x [] start).answer=some true := hanswer
  have his : (P.run (fun _ => False) x [] start).answer.isSome := by rw [hanswer'];rfl
  have hpersist := finiteProgram_run_halted P (fun _ => False) x [] start (T-start) his
  rw [Nat.add_sub_of_le hstart] at hpersist
  have hT : (P.run (fun _ => False) x [] T).answer.isSome := by rw [hpersist];exact his
  have hw : ((P.run (fun _ => False) x [] T).tapes P.outputTape).word=f x := by
    rw [hpersist]
    exact hword
  have hquery := outputOracleProgram_computation P (nativeProgram_query_unused tm false) A x T hT
  rw [hw] at hquery
  have hclock : T+1 ≤ polyBound (c+5) (d+1) x.length := by
    have hv : 1 ≤ (x.length+1)^(d+1) := Nat.one_le_pow _ _ (by omega)
    dsimp [T,polyBound]
    nlinarith
  have hhalt : (W.run A x [] (T+1)).answer.isSome := by rw [hquery];rfl
  have hwp := finiteProgram_run_halted W A x [] (T+1)
    (polyBound (c+5) (d+1) x.length-(T+1)) hhalt
  rw [Nat.add_sub_of_le hclock] at hwp
  refine ⟨decide (A (f x)),?_,by simp⟩
  rw [FiniteProgram.compile_run,hwp]
  exact hquery

lemma AtCHLevel.native_preimage {A : Language} {j : ℕ} (hA : AtCHLevel j A)
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits) :
    AtCHLevel (j+1) (fun x => A (f x)) :=
  ⟨A,hA,(native_oracle_preimage f hf A).inOraclePP⟩

end APSCounting893.Main
end Component_24

open APSCounting893.Main
theorem solution
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (A : Language) : InOracleP A (fun x => A (f x)) := by
  exact native_oracle_preimage f hf A
