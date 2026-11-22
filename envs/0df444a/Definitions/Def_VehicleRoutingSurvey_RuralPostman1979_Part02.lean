-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part02
-- name    : VehicleRoutingSurvey_RuralPostman1979_Part02
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T13:55:26.376284+00:00
-- url     : https://prove2.me/theorems/bf14465b-e48c-44d6-b429-fb3ba62c1853
-- title:
--   Rural postman algorithm — Arithmetic instruction semantics and initialization of shortest-path queues
-- statement:
--   This module supplies the Lean definitions and checked auxiliary results for arithmetic instruction semantics and initialization of shortest-path queues in the Table 3 proof. It uses the mission’s rural-run and arithmetic-RAM model.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_Routing_RuralRuntime
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VehicleRoutingSurvey_Routing_RuralAlgorithm
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Induction
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01

/-! runtime/ArithmeticRuntime.lean -/
section RppSource_ArithmeticRuntime
namespace VehicleRoutingSurvey.Routing

theorem arithmeticRun_after (p : List ArithmeticInstruction) (ns : List ℕ) (rs : List ℝ)
    (before extra : ℕ) :
    arithmeticRun p (before + extra) ns rs =
      (arithmeticStep p)^[extra] (arithmeticRun p before ns rs) := by
  rw [arithmeticRun, Nat.add_comm before, Function.iterate_add_apply, ← arithmeticRun]

/-- Move branch targets along with a block inserted after a prefix. -/
def relocateInstruction (offset : ℕ) : ArithmeticInstruction → ArithmeticInstruction
  | .natBranch x y yes no => .natBranch x y (offset + yes) (offset + no)
  | .realBranch x y yes no => .realBranch x y (offset + yes) (offset + no)
  | .jump target => .jump (offset + target)
  | instruction => instruction

def relocateState (offset : ℕ) (s : ArithmeticState) : ArithmeticState :=
  {s with pc := offset + s.pc}

/-- While the program counter is in the relocated block, appending it to surrounding
code gives the same machine step, with only the program counter offset. -/
theorem arithmeticStep_relocate (front block back : List ArithmeticInstruction)
    (s : ArithmeticState) (inside : s.pc < block.length) :
    arithmeticStep (front ++ block.map (relocateInstruction front.length) ++ back)
        (relocateState front.length s) =
      relocateState front.length (arithmeticStep block s) := by
  by_cases halted : s.halted = true
  · simp [arithmeticStep, relocateState, halted]
  · have lookup :
        (front ++ block.map (relocateInstruction front.length) ++ back)[front.length + s.pc]? =
          block[s.pc]?.map (relocateInstruction front.length) := by
      simp [List.getElem?_append_right (Nat.le_add_right front.length s.pc),
        List.getElem?_append_left (by simpa using inside : s.pc < (block.map (relocateInstruction front.length)).length)]
    simp only [arithmeticStep, relocateState, halted, lookup]
    cases selected : block[s.pc]? with
    | none => rfl
    | some ins =>
      cases ins <;> simp [relocateInstruction, Nat.add_assoc] <;> split <;> rfl

/-- Compose bytecode blocks up to and including their exit transition. -/
theorem arithmeticIterate_relocate (front block back : List ArithmeticInstruction)
    (s : ArithmeticState) (t : ℕ)
    (inside : ∀ j < t, ((arithmeticStep block)^[j] s).pc < block.length) :
    (arithmeticStep (front ++ block.map (relocateInstruction front.length) ++ back))^[t]
        (relocateState front.length s) =
      relocateState front.length ((arithmeticStep block)^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun j hj => inside j (hj.trans (Nat.lt_succ_self t)))]
    exact arithmeticStep_relocate front block back _ (inside t (Nat.lt_succ_self t))

/-- Compute a finite upper sentinel, one plus the sum of the input edge weights.
Register 1 holds the number of edges and register 2 holds the next input index. -/
def weightSumProgram : List ArithmeticInstruction :=
  [.natConst 0 1, .natLoad 1 0, .natConst 2 0, .realConst 0 1,
    .natBranch 1 2 9 5, .realLoad 1 2, .realAdd 0 0 1, .natAdd 2 2 0, .jump 4, .halt]

private structure WeightSumState (ns : List ℕ) (rs : List ℝ) (i : ℕ)
    (s : ArithmeticState) : Prop where
  pc : s.pc = 4
  running : s.halted = false
  one : s.nr 0 = 1
  length : s.nr 1 = rs.length
  index : s.nr 2 = i
  sum : s.rr 0 = 1 + (rs.take i).sum
  natMemory : s.nm = (arithmeticInput ns rs).nm
  realMemory : s.rm = (arithmeticInput ns rs).rm

private theorem weightSum_init (ns : List ℕ) (rs : List ℝ)
    (encoded : ns[1]? = some rs.length) :
    WeightSumState ns rs 0 (arithmeticRun weightSumProgram 4 ns rs) := by
  constructor <;> simp [arithmeticRun, arithmeticStep, arithmeticInput, weightSumProgram,
    Function.iterate_succ_apply', encoded]

private theorem weightSum_loop (ns : List ℕ) (rs : List ℝ) (i : ℕ) (s : ArithmeticState)
    (before : WeightSumState ns rs i s) (hi : i < rs.length) :
    WeightSumState ns rs (i + 1) ((arithmeticStep weightSumProgram)^[5] s) := by
  have enter : arithmeticStep weightSumProgram s = {s with pc := 5} := by
    simp [arithmeticStep, before.running, before.pc, weightSumProgram, before.length,
      before.index, not_le.mpr hi]
  change WeightSumState ns rs (i + 1)
    (arithmeticStep weightSumProgram (arithmeticStep weightSumProgram
      (arithmeticStep weightSumProgram (arithmeticStep weightSumProgram (arithmeticStep weightSumProgram s)))))
  rw [enter]
  let loaded := {s with pc := 6, rr := Function.update s.rr 1 (s.rm i)}
  have load : arithmeticStep weightSumProgram {s with pc := 5} = loaded := by
    simp [loaded, arithmeticStep, weightSumProgram, before.running, before.index]
  rw [load]
  let added := {loaded with pc := 7, rr := Function.update loaded.rr 0 (s.rr 0 + s.rm i)}
  have addWeight : arithmeticStep weightSumProgram loaded = added := by
    simp [added, loaded, arithmeticStep, weightSumProgram, before.running]
  rw [addWeight]
  let advanced := {added with pc := 8, nr := Function.update s.nr 2 (i + 1)}
  have advance : arithmeticStep weightSumProgram added = advanced := by
    simp [advanced, added, loaded, arithmeticStep, weightSumProgram, before.running, before.index,
      before.one]
  rw [advance]
  have restart : arithmeticStep weightSumProgram advanced = {advanced with pc := 4} := by
    simp [advanced, added, loaded, arithmeticStep, weightSumProgram, before.running]
  rw [restart]
  refine ⟨rfl, before.running, ?_, ?_, ?_, ?_, before.natMemory, before.realMemory⟩
  · simpa [advanced] using before.one
  · simpa [advanced] using before.length
  · simp [advanced]
  · change Function.update loaded.rr 0 (s.rr 0 + s.rm i) 0 = _
    simp only [Function.update_self, before.sum, before.realMemory, arithmeticInput,
      List.take_succ_eq_append_getElem hi, List.getElem?_eq_getElem hi, Option.getD_some,
      List.sum_append, List.sum_singleton, add_assoc]

private theorem weightSum_progress (ns : List ℕ) (rs : List ℝ)
    (encoded : ns[1]? = some rs.length) (i : ℕ) (hi : i ≤ rs.length) :
    WeightSumState ns rs i (arithmeticRun weightSumProgram (4 + 5 * i) ns rs) := by
  induction i with
  | zero => exact weightSum_init ns rs encoded
  | succ i ih =>
    simpa only [Nat.mul_succ, ← Nat.add_assoc, arithmeticRun_after] using
      weightSum_loop ns rs i _ (ih (Nat.le_of_succ_le hi)) hi

/-- The scan halts after five instructions per link and six fixed instructions.
Both input memories remain intact. -/
theorem weightSumProgram_correct (ns : List ℕ) (rs : List ℝ)
    (encoded : ns[1]? = some rs.length) :
    let s := arithmeticRun weightSumProgram (4 + 5 * rs.length + 2) ns rs
    s.halted = true ∧ s.rr 0 = 1 + rs.sum ∧
      s.nm = (arithmeticInput ns rs).nm ∧ s.rm = (arithmeticInput ns rs).rm := by
  rw [arithmeticRun_after]
  let s := arithmeticRun weightSumProgram (4 + 5 * rs.length) ns rs
  have before : WeightSumState ns rs rs.length s :=
    weightSum_progress ns rs encoded rs.length le_rfl
  change let t := arithmeticStep weightSumProgram (arithmeticStep weightSumProgram s)
         t.halted = true ∧ t.rr 0 = 1 + rs.sum ∧
           t.nm = (arithmeticInput ns rs).nm ∧ t.rm = (arithmeticInput ns rs).rm
  have exitStep : arithmeticStep weightSumProgram s = {s with pc := 9} := by
    simp [arithmeticStep, weightSumProgram, before.pc, before.running, before.length, before.index]
  rw [exitStep]
  simp [arithmeticStep, weightSumProgram, before.running, before.sum, before.natMemory,
    before.realMemory]

/-- The exact rural-postman input layout supplies the header and weight array. -/
theorem ruralWeightSumProgram_correct (I : Service) :
    let ns := ruralNatInput I
    let rs := ruralRealInput I
    let s := arithmeticRun weightSumProgram (4 + 5 * I.graph.q + 2) ns rs
    s.halted = true ∧ s.rr 0 = 1 + rs.sum ∧
      s.nm = (arithmeticInput ns rs).nm ∧ s.rm = (arithmeticInput ns rs).rm := by
  simpa [ruralRealInput] using weightSumProgram_correct (ruralNatInput I) (ruralRealInput I)
    (by simp [ruralNatInput, ruralRealInput])

/-- A verified linear preprocessing pass produces a finite upper distance
sentinel and preserves the exact input. -/
theorem ruralWeightSumProgram_sentinel (I : Service) (rural : Rural I) :
    let t := 4 + 5 * I.graph.q + 2
    let s := arithmeticRun weightSumProgram t (ruralNatInput I) (ruralRealInput I)
    s.halted = true ∧ (∀ u v, distance I.graph u v < s.rr 0) ∧
      t ≤ 6 * (I.graph.n ^ 3 + I.graph.q) := by
  obtain ⟨halted, value, _, _⟩ := ruralWeightSumProgram_correct I
  refine ⟨halted, ?_, ?_⟩
  · intro u v
    rw [value]
    simpa [ruralRealInput, ← List.ofFn_eq_map, List.sum_ofFn] using
      distance_lt_weight_sentinel rural.1 rural.2.1 u v
  · have positive : 0 < I.graph.n ^ 3 := pow_pos rural.1.1 _
    omega

end VehicleRoutingSurvey.Routing
end RppSource_ArithmeticRuntime

/-! runtime/CountedLoop.lean -/
section RppSource_CountedLoop
namespace VehicleRoutingSurvey.Routing

/-- A block may exit to the instruction immediately following its final
instruction. The strict trace bound is what makes relocation sound. -/
structure BlockRuns (code : List ArithmeticInstruction) (steps : ℕ)
    (initial final : ArithmeticState) : Prop where
  inside : ∀ i < steps, ((arithmeticStep code)^[i] initial).pc < code.length
  run : (arithmeticStep code)^[steps] initial = final
  exit : final.pc = code.length

/-- Fetching an instruction outside the block halts the machine. A run that
still executes at the exit therefore stayed within the block on every step. -/
theorem BlockRuns.of_running_exit {code : List ArithmeticInstruction} {steps : ℕ}
    {initial final : ArithmeticState}
    (result : (arithmeticStep code)^[steps] initial = final)
    (running : final.halted = false) (exit : final.pc = code.length) :
    BlockRuns code steps initial final := by
  refine ⟨?_, result, exit⟩
  intro i earlier
  by_contra! outside
  let state := (arithmeticStep code)^[i] initial
  have badFetch : code[state.pc]? = none := List.getElem?_eq_none outside
  let stopped := arithmeticStep code state
  have halted : stopped.halted = true := by
    cases wasHalted : state.halted <;> simp [stopped, arithmeticStep, wasHalted, badFetch]
  have stays (k : ℕ) : (arithmeticStep code)^[k] stopped = stopped := by
    induction k with
    | zero => rfl
    | succ k ih => simp [Function.iterate_succ_apply', ih, arithmeticStep, halted]
  obtain ⟨k, count⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt earlier)
  have after : (arithmeticStep code)^[i + 1] initial = stopped := by
    simp [Function.iterate_succ_apply', stopped, state]
  have eq : final = stopped := by
    rw [← result, count, Nat.add_comm (i + 1) k, Function.iterate_add_apply, after, stays]
  simp [eq, halted] at running

def appendBlock (left right : List ArithmeticInstruction) : List ArithmeticInstruction :=
  left ++ right.map (relocateInstruction left.length)

@[simp] theorem appendBlock_length (left right : List ArithmeticInstruction) :
    (appendBlock left right).length = left.length + right.length := by
  simp [appendBlock]

theorem arithmeticStep_prefix (left right : List ArithmeticInstruction) (s : ArithmeticState)
    (inside : s.pc < left.length) : arithmeticStep (left ++ right) s = arithmeticStep left s := by
  simp only [arithmeticStep, List.getElem?_append_left inside]

theorem arithmeticIterate_prefix (left right : List ArithmeticInstruction) (s : ArithmeticState)
    (steps : ℕ) (inside : ∀ i < steps, ((arithmeticStep left)^[i] s).pc < left.length) :
    (arithmeticStep (left ++ right))^[steps] s = (arithmeticStep left)^[steps] s := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun i hi => inside _ (hi.trans (Nat.lt_succ_self _)))]
    exact arithmeticStep_prefix _ _ _ (inside _ (Nat.lt_succ_self _))

theorem BlockRuns.append {left right : List ArithmeticInstruction} {a b : ℕ}
    {start middle finish : ArithmeticState}
    (hLeft : BlockRuns left a start middle)
    (hRight : BlockRuns right b {middle with pc := 0} finish) :
    BlockRuns (appendBlock left right) (a + b) start (relocateState left.length finish) := by
  have leftAt (i : ℕ) (hi : i ≤ a) :
      (arithmeticStep (appendBlock left right))^[i] start = (arithmeticStep left)^[i] start :=
    arithmeticIterate_prefix _ _ _ _ (fun j hj => hLeft.inside j (hj.trans_le hi))
  have reset : middle = relocateState left.length {middle with pc := 0} := by
    change middle = {middle with pc := left.length + 0}
    rw [Nat.add_zero, ← hLeft.exit]
  have rightAt (i : ℕ) (hi : i ≤ b) :
      (arithmeticStep (appendBlock left right))^[a + i] start =
        relocateState left.length ((arithmeticStep right)^[i] {middle with pc := 0}) := by
    calc
      _ = (arithmeticStep (appendBlock left right))^[i] middle := by
        rw [Nat.add_comm a, Function.iterate_add_apply, leftAt a le_rfl, hLeft.run]
      _ = _ := by
        conv_lhs => rw [reset]
        simpa [appendBlock] using arithmeticIterate_relocate left right []
          {middle with pc := 0} i (fun j hj => hRight.inside j (hj.trans_le hi))
  refine ⟨?_, ?_, by simp [relocateState, hRight.exit]⟩
  · intro i hi
    by_cases earlier : i < a
    · rw [leftAt i earlier.le, appendBlock_length]
      exact (hLeft.inside i earlier).trans_le (Nat.le_add_right _ _)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt earlier)
      have later : j < b := by omega
      rw [rightAt j later.le, appendBlock_length]
      exact Nat.add_lt_add_left (hRight.inside j later) _
  · rw [rightAt b le_rfl, hRight.run]

private structure TraceRuns (code : List ArithmeticInstruction) (steps : ℕ)
    (initial final : ArithmeticState) : Prop where
  inside : ∀ i < steps, ((arithmeticStep code)^[i] initial).pc < code.length
  run : (arithmeticStep code)^[steps] initial = final

private theorem TraceRuns.single {code : List ArithmeticInstruction} {s t : ArithmeticState}
    (inside : s.pc < code.length) (result : arithmeticStep code s = t) :
    TraceRuns code 1 s t := by
  refine ⟨fun i hi => ?_, result⟩
  have eq : i = 0 := by omega
  exact eq.symm ▸ inside

private theorem TraceRuns.then {code : List ArithmeticInstruction} {a b : ℕ}
    {s m t : ArithmeticState} (first : TraceRuns code a s m) (second : TraceRuns code b m t) :
    TraceRuns code (a + b) s t := by
  refine ⟨?_, by rw [Nat.add_comm a, Function.iterate_add_apply, first.run, second.run]⟩
  intro i hi
  by_cases earlier : i < a
  · exact first.inside _ earlier
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt earlier)
    rw [Nat.add_comm a, Function.iterate_add_apply, first.run]
    exact second.inside _ (by omega)

private theorem BlockRuns.relocate {code : List ArithmeticInstruction} {steps : ℕ}
    {initial final : ArithmeticState} (h : BlockRuns code steps initial final)
    (front back : List ArithmeticInstruction) :
    TraceRuns (front ++ code.map (relocateInstruction front.length) ++ back) steps
      (relocateState front.length initial) (relocateState front.length final) := by
  refine ⟨?_, (arithmeticIterate_relocate front code back initial steps h.inside).trans
    (congrArg (relocateState front.length) h.run)⟩
  intro i hi
  rw [arithmeticIterate_relocate front code back initial i (fun j hj => h.inside j (hj.trans hi))]
  simpa [relocateState, Nat.add_assoc] using
    (Nat.add_lt_add_left (h.inside i hi) front.length).trans_le
      (Nat.le_add_right (front.length + code.length) back.length)

/-- Repeat the block while the current index is below the limit. The
caller chooses a register containing one. Each iteration has a test,
the body, an increment, and a backward jump. -/
def countedLoop (one index limit : ℕ) (body : List ArithmeticInstruction) :
    List ArithmeticInstruction :=
  [.natBranch limit index (body.length + 3) 1] ++
    body.map (relocateInstruction 1) ++ [.natAdd index index one, .jump 0]

@[simp] theorem countedLoop_length (one index limit : ℕ) (body : List ArithmeticInstruction) :
    (countedLoop one index limit body).length = body.length + 3 := by
  simp [countedLoop, Nat.add_comm, Nat.add_left_comm]

private theorem countedLoop_tail (one index limit : ℕ) (body : List ArithmeticInstruction) :
    (countedLoop one index limit body)[1 + body.length]? = some (.natAdd index index one) ∧
      (countedLoop one index limit body)[1 + body.length + 1]? = some (.jump 0) := by
  rw [Nat.add_comm 1 body.length]
  constructor
  · change (body.map (relocateInstruction 1) ++
      [.natAdd index index one, .jump 0])[body.length]? = _
    rw [List.getElem?_append_right (by simp)]
    simp
  · change (body.map (relocateInstruction 1) ++
      [.natAdd index index one, .jump 0])[body.length + 1]? = _
    rw [List.getElem?_append_right (by simp)]
    simp

private theorem countedLoop_cycle (one index limit : ℕ) (body : List ArithmeticInstruction)
    {steps : ℕ} {s t : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (more : s.nr index < s.nr limit) (bodyRun : BlockRuns body steps s t)
    (ready : t.halted = false) :
    TraceRuns (countedLoop one index limit body) (steps + 3) s
      {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr one)} := by
  have enter : TraceRuns (countedLoop one index limit body) 1 s (relocateState 1 s) := by
    apply TraceRuns.single
    · simp [entry]
    · simp [arithmeticStep, countedLoop, relocateState, entry, running, not_le.mpr more]
  have during : TraceRuns (countedLoop one index limit body) steps
      (relocateState 1 s) (relocateState 1 t) :=
    bodyRun.relocate [.natBranch limit index (body.length + 3) 1] [.natAdd index index one, .jump 0]
  let registers := Function.update t.nr index (t.nr index + t.nr one)
  let bumped := {t with pc := 1 + body.length + 1, nr := registers}
  have bump : TraceRuns (countedLoop one index limit body) 1 (relocateState 1 t) bumped := by
    apply TraceRuns.single
    · simp [relocateState, bodyRun.exit] <;> omega
    · simp [arithmeticStep, relocateState, bodyRun.exit, ready,
        (countedLoop_tail one index limit body).1, bumped, registers]
  have back : TraceRuns (countedLoop one index limit body) 1 bumped
      {t with pc := 0, nr := registers} := by
    apply TraceRuns.single
    · simp [bumped] <;> omega
    · simp [arithmeticStep, bumped, ready, (countedLoop_tail one index limit body).2]
  rw [show steps + 3 = 1 + steps + 1 + 1 by omega]
  exact ((enter.then during).then bump).then back

/-- Lift a fixed-cost verified body to a counted loop. The indexed invariant
specifies both the loop registers and the semantic effect of each iteration. -/
theorem countedLoop_correct (one index limit n steps : ℕ) (body : List ArithmeticInstruction)
    (inv : ℕ → ArithmeticState → Prop) {s : ArithmeticState}
    (initial : inv 0 s)
    (control : ∀ i m, inv i m →
      m.pc = 0 ∧ m.halted = false ∧ m.nr index = i ∧ m.nr limit = n)
    (iterate : ∀ i < n, ∀ m, inv i m → ∃ t,
      BlockRuns body steps m t ∧ t.halted = false ∧
      inv (i + 1) {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr one)}) :
    ∃ last, inv n last ∧
      BlockRuns (countedLoop one index limit body) (n * (steps + 3) + 1) s
        {last with pc := (countedLoop one index limit body).length} := by
  let code := countedLoop one index limit body
  have progress (k : ℕ) (hk : k ≤ n) :
      ∃ m, inv k m ∧ TraceRuns code (k * (steps + 3)) s m := by
    induction k with
    | zero => exact ⟨s, initial, ⟨fun _ h => by omega, by simp⟩⟩
    | succ k ih =>
      obtain ⟨m, hm, hTrace⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨t, bodyRun, ready, next⟩ := iterate k hk m hm
      obtain ⟨entry, running, indexAt, limitAt⟩ := control k m hm
      have more : m.nr index < m.nr limit := by simpa [indexAt, limitAt] using hk
      have cycle := countedLoop_cycle one index limit body entry running more bodyRun ready
      exact ⟨_, next, by simpa only [Nat.succ_mul] using hTrace.then cycle⟩
  obtain ⟨m, hm, trace⟩ := progress n le_rfl
  obtain ⟨entry, running, indexAt, limitAt⟩ := control n m hm
  have leave : TraceRuns code 1 m {m with pc := code.length} := by
    apply TraceRuns.single
    · simp [code, entry]
    · simp [code, arithmeticStep, countedLoop, entry, running, indexAt, limitAt,
        Nat.add_comm, Nat.add_left_comm]
  have total := trace.then leave
  exact ⟨m, hm, ⟨total.inside, total.run, rfl⟩⟩

theorem zeroRegister_runs (index : ℕ) (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns [.natConst index 0] 1 s {s with pc := 1, nr := Function.update s.nr index 0} := by
  refine ⟨fun i hi => ?_, ?_, rfl⟩
  · have eq : i = 0 := by omega
    simp [eq, entry]
  · simp [arithmeticStep, entry, running]

def countedLoopFromZero (one index limit : ℕ) (body : List ArithmeticInstruction) :
    List ArithmeticInstruction :=
  appendBlock [.natConst index 0] (countedLoop one index limit body)

theorem countedLoopFromZero_correct (one index limit n steps : ℕ)
    (body : List ArithmeticInstruction) (inv : ℕ → ArithmeticState → Prop)
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (initial : inv 0 {s with pc := 0, nr := Function.update s.nr index 0})
    (control : ∀ i m, inv i m →
      m.pc = 0 ∧ m.halted = false ∧ m.nr index = i ∧ m.nr limit = n)
    (iterate : ∀ i < n, ∀ m, inv i m → ∃ t,
      BlockRuns body steps m t ∧ t.halted = false ∧
      inv (i + 1) {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr one)}) :
    ∃ last, inv n last ∧
      BlockRuns (countedLoopFromZero one index limit body) (1 + (n * (steps + 3) + 1)) s
        (relocateState 1 {last with pc := (countedLoop one index limit body).length}) := by
  obtain ⟨last, final, loop⟩ := countedLoop_correct one index limit n steps body inv
    initial control iterate
  exact ⟨last, final, (zeroRegister_runs index s entry running).append loop⟩

/-- Lift a variable-cost body to a counted loop using a common upper
bound for each taken iteration. -/
theorem countedLoop_bounded (one index limit n budget : ℕ) (body : List ArithmeticInstruction)
    (inv : ℕ → ArithmeticState → Prop) {s : ArithmeticState} (initial : inv 0 s)
    (control : ∀ i m, inv i m →
      m.pc = 0 ∧ m.halted = false ∧ m.nr index = i ∧ m.nr limit = n)
    (iterate : ∀ i < n, ∀ m, inv i m → ∃ t steps,
      steps ≤ budget ∧ BlockRuns body steps m t ∧ t.halted = false ∧
      inv (i + 1) {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr one)}) :
    ∃ last actual, inv n last ∧ actual ≤ n * (budget + 3) + 1 ∧
      BlockRuns (countedLoop one index limit body) actual s
        {last with pc := (countedLoop one index limit body).length} := by
  let code := countedLoop one index limit body
  have progress (k : ℕ) (hk : k ≤ n) :
      ∃ m actual, inv k m ∧ actual ≤ k * (budget + 3) ∧ TraceRuns code actual s m := by
    induction k with
    | zero => exact ⟨s, 0, initial, Nat.zero_le _, ⟨fun _ h => by omega, by simp⟩⟩
    | succ k ih =>
      obtain ⟨m, actual, hm, bound, trace⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨t, steps, cost, bodyRun, ready, next⟩ := iterate k hk m hm
      obtain ⟨entry, running, indexAt, limitAt⟩ := control k m hm
      have more : m.nr index < m.nr limit := by simpa [indexAt, limitAt] using hk
      have cycle := countedLoop_cycle one index limit body entry running more bodyRun ready
      refine ⟨_, actual + (steps + 3), next, ?_, trace.then cycle⟩
      simpa only [Nat.succ_mul] using (Nat.add_le_add bound (Nat.add_le_add_right cost 3))
  obtain ⟨m, actual, hm, bound, trace⟩ := progress n le_rfl
  obtain ⟨entry, running, indexAt, limitAt⟩ := control n m hm
  have leave : TraceRuns code 1 m {m with pc := code.length} := by
    apply TraceRuns.single
    · simp [code, entry]
    · simp [code, arithmeticStep, countedLoop, entry, running, indexAt, limitAt,
        Nat.add_comm, Nat.add_left_comm]
  have total := trace.then leave
  exact ⟨m, actual + 1, hm, Nat.add_le_add_right bound 1, ⟨total.inside, total.run, rfl⟩⟩

theorem countedLoopFromZero_bounded (one index limit n budget : ℕ)
    (body : List ArithmeticInstruction) (inv : ℕ → ArithmeticState → Prop)
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (initial : inv 0 {s with pc := 0, nr := Function.update s.nr index 0})
    (control : ∀ i m, inv i m →
      m.pc = 0 ∧ m.halted = false ∧ m.nr index = i ∧ m.nr limit = n)
    (iterate : ∀ i < n, ∀ m, inv i m → ∃ t steps,
      steps ≤ budget ∧ BlockRuns body steps m t ∧ t.halted = false ∧
      inv (i + 1) {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr one)}) :
    ∃ last actual, inv n last ∧ actual ≤ 1 + (n * (budget + 3) + 1) ∧
      BlockRuns (countedLoopFromZero one index limit body) actual s
        (relocateState 1 {last with pc := (countedLoop one index limit body).length}) := by
  obtain ⟨last, actual, final, bound, loop⟩ :=
    countedLoop_bounded one index limit n budget body inv initial control iterate
  exact ⟨last, 1 + actual, final, Nat.add_le_add_left bound 1,
    (zeroRegister_runs index s entry running).append loop⟩

/-- Lift a variable-cost body with a nonnegative state potential. The
output inequality retains the final potential for subsequent blocks. -/
theorem countedLoop_amortized (one index limit n base : ℕ) (body : List ArithmeticInstruction)
    (inv : ℕ → ArithmeticState → Prop) (potential : ArithmeticState → ℕ)
    {s : ArithmeticState} (initial : inv 0 s)
    (control : ∀ i m, inv i m →
      m.pc = 0 ∧ m.halted = false ∧ m.nr index = i ∧ m.nr limit = n)
    (iterate : ∀ i < n, ∀ m, inv i m → ∃ t steps,
      let next := {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr one)}
      BlockRuns body steps m t ∧ t.halted = false ∧ inv (i + 1) next ∧
        steps + potential next ≤ base + potential m) :
    ∃ last actual, inv n last ∧ actual + potential last ≤ n * (base + 3) + potential s + 1 ∧
      BlockRuns (countedLoop one index limit body) actual s
        {last with pc := (countedLoop one index limit body).length} := by
  let code := countedLoop one index limit body
  have progress (k : ℕ) (hk : k ≤ n) :
      ∃ m spent, inv k m ∧ spent + potential m ≤ k * (base + 3) + potential s ∧
        TraceRuns code spent s m := by
    induction k with
    | zero => exact ⟨s, 0, initial, by simp, ⟨fun _ h => by omega, by simp⟩⟩
    | succ k ih =>
      obtain ⟨m, spent, pm, before, trace⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨t, steps, runs, ready, next, charge⟩ := iterate k hk m pm
      obtain ⟨entry, running, indexAt, limitAt⟩ := control k m pm
      have more : m.nr index < m.nr limit := by simpa [indexAt, limitAt] using hk
      have cycle := countedLoop_cycle one index limit body entry running more runs ready
      refine ⟨_, spent + (steps + 3), next, ?_, trace.then cycle⟩
      rw [Nat.succ_mul]
      omega
  obtain ⟨m, spent, pm, bound, trace⟩ := progress n le_rfl
  obtain ⟨entry, running, indexAt, limitAt⟩ := control n m pm
  have leave : TraceRuns code 1 m {m with pc := code.length} := by
    apply TraceRuns.single
    · simp [code, entry]
    · simp [code, arithmeticStep, countedLoop, entry, running, indexAt, limitAt,
        Nat.add_comm, Nat.add_left_comm]
  have complete := trace.then leave
  exact ⟨m, spent + 1, pm, by omega, ⟨complete.inside, complete.run, rfl⟩⟩

/-- Amortized counted loop with the same zero-initialization convention as
the exact and fixed-budget variants. -/
theorem countedLoopFromZero_amortized (one index limit n base : ℕ)
    (body : List ArithmeticInstruction) (inv : ℕ → ArithmeticState → Prop)
    (potential : ArithmeticState → ℕ) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (initial : inv 0 {s with pc := 0, nr := Function.update s.nr index 0})
    (control : ∀ i m, inv i m →
      m.pc = 0 ∧ m.halted = false ∧ m.nr index = i ∧ m.nr limit = n)
    (iterate : ∀ i < n, ∀ m, inv i m → ∃ t steps,
      let next := {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr one)}
      BlockRuns body steps m t ∧ t.halted = false ∧ inv (i + 1) next ∧
        steps + potential next ≤ base + potential m) :
    ∃ last actual, inv n last ∧
      actual ≤ 1 + (n * (base + 3) +
        potential {s with pc := 0, nr := Function.update s.nr index 0} + 1) ∧
      BlockRuns (countedLoopFromZero one index limit body) actual s
        (relocateState 1 {last with pc := (countedLoop one index limit body).length}) := by
  obtain ⟨last, actual, final, bound, loop⟩ :=
    countedLoop_amortized one index limit n base body inv potential initial control iterate
  exact ⟨last, 1 + actual, final, by omega, (zeroRegister_runs index s entry running).append loop⟩

private def branchOnUnequalPrefix (x y length : ℕ) : List ArithmeticInstruction :=
  [.natBranch x y 1 2, .natBranch y x (3 + length) 3, .jump 3]

/-- Execute the body exactly when the two natural registers differ.
Either outcome uses two control instructions before entering or skipping the body. -/
def branchOnUnequal (x y : ℕ) (body : List ArithmeticInstruction) : List ArithmeticInstruction :=
  branchOnUnequalPrefix x y body.length ++ body.map (relocateInstruction 3)

@[simp] theorem branchOnUnequal_length (x y : ℕ) (body : List ArithmeticInstruction) :
    (branchOnUnequal x y body).length = 3 + body.length := by
  simp [branchOnUnequal, branchOnUnequalPrefix] <;> omega

private theorem branchOnUnequal_trace (x y : ℕ) (body : List ArithmeticInstruction)
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    TraceRuns (branchOnUnequal x y body) 2 s
      {s with pc := if s.nr x = s.nr y then (branchOnUnequal x y body).length else 3} := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    · simp [entry]
    · by_cases order : s.nr x ≤ s.nr y
      · simp [arithmeticStep, entry, running, branchOnUnequal, branchOnUnequalPrefix, order] <;> omega
      · simp [arithmeticStep, entry, running, branchOnUnequal, branchOnUnequalPrefix, order] <;> omega
  · by_cases left : s.nr x ≤ s.nr y
    · by_cases right : s.nr y ≤ s.nr x
      · have eq := Nat.le_antisymm left right
        simp [arithmeticStep, entry, running, branchOnUnequal, branchOnUnequalPrefix,
          Function.iterate_succ_apply', left, right, eq] <;> omega
      · have different : s.nr x ≠ s.nr y := fun eq => right eq.ge
        simp [arithmeticStep, entry, running, branchOnUnequal, branchOnUnequalPrefix,
          Function.iterate_succ_apply', left, right, different]
    · have different : s.nr x ≠ s.nr y := fun eq => left eq.le
      simp [arithmeticStep, entry, running, branchOnUnequal, branchOnUnequalPrefix,
        Function.iterate_succ_apply', left, different]

theorem branchOnUnequal_skip (x y : ℕ) (body : List ArithmeticInstruction)
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false)
    (same : s.nr x = s.nr y) :
    BlockRuns (branchOnUnequal x y body) 2 s {s with pc := (branchOnUnequal x y body).length} := by
  have trace := branchOnUnequal_trace x y body s entry running
  simp only [if_pos same] at trace
  exact ⟨trace.inside, trace.run, rfl⟩

theorem branchOnUnequal_take (x y : ℕ) (body : List ArithmeticInstruction)
    {s t : ArithmeticState} {steps : ℕ} (entry : s.pc = 0) (running : s.halted = false)
    (different : s.nr x ≠ s.nr y) (bodyRun : BlockRuns body steps s t) :
    BlockRuns (branchOnUnequal x y body) (2 + steps) s (relocateState 3 t) := by
  have incoming : TraceRuns (branchOnUnequal x y body) 2 s (relocateState 3 s) := by
    have trace := branchOnUnequal_trace x y body s entry running
    simpa [different, relocateState, entry] using trace
  have bodyTrace : TraceRuns (branchOnUnequal x y body) steps
      (relocateState 3 s) (relocateState 3 t) := by
    simpa [branchOnUnequal, branchOnUnequalPrefix] using
      bodyRun.relocate (branchOnUnequalPrefix x y body.length) []
  have all := incoming.then bodyTrace
  exact ⟨all.inside, all.run, by simp [relocateState, bodyRun.exit]⟩

end VehicleRoutingSurvey.Routing
end RppSource_CountedLoop

/-! runtime/MateTable.lean -/
section RppSource_MateTable
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The partner array for a perfect matching is a fixed-point-free involution
on the set of vertices that require matching. -/
def MateTableOn {n : ℕ} (vertices : Finset (Fin n)) (mate : Fin n → Fin n) : Prop :=
  ∀ v ∈ vertices, mate v ∈ vertices ∧ mate v ≠ v ∧ mate (mate v) = v

noncomputable def pairsOfMate {n : ℕ} (vertices : Finset (Fin n)) (mate : Fin n → Fin n) : List (Fin n × Fin n) :=
  (vertices.toList.filter (fun v => decide (v < mate v))).map fun v => (v, mate v)

theorem mem_pairsOfMate {n : ℕ} {vertices : Finset (Fin n)} {mate : Fin n → Fin n}
    {p : Fin n × Fin n} : p ∈ pairsOfMate vertices mate ↔
      p.1 ∈ vertices ∧ p.1 < mate p.1 ∧ p.2 = mate p.1 := by
  simp only [pairsOfMate, List.mem_map, List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
  constructor
  · rintro ⟨v, ⟨inVertices, least⟩, rfl⟩
    exact ⟨inVertices, least, rfl⟩
  · rintro ⟨inVertices, least, partner⟩
    exact ⟨p.1, ⟨inVertices, least⟩, Prod.ext rfl partner.symm⟩

theorem pairsOfMate_sym2_nodup {n : ℕ} (vertices : Finset (Fin n)) (mate : Fin n → Fin n) :
    ((pairsOfMate vertices mate).map (fun p => s(p.1, p.2))).Nodup := by
  rw [pairsOfMate, List.map_map]
  apply List.Nodup.map_on _ (vertices.nodup_toList.filter _)
  intro a ha b hb equal
  rcases Sym2.eq_iff.mp equal with same | reversed
  · exact same.1
  · have first : a < mate a := of_decide_eq_true (List.mem_filter.mp ha).2
    have second : b < mate b := of_decide_eq_true (List.mem_filter.mp hb).2
    have conflicting : mate a < a := calc
      mate a = b := reversed.2
      _ < mate b := second
      _ = a := reversed.1.symm
    exact (not_lt_of_ge first.le conflicting).elim

noncomputable def mateEdgeSet {n : ℕ} (vertices : Finset (Fin n)) (mate : Fin n → Fin n) : Finset (Sym2 (Fin n)) :=
  ((pairsOfMate vertices mate).map (fun p => s(p.1, p.2))).toFinset

private theorem mateEdgeSet_of_pair {n : ℕ} {vertices : Finset (Fin n)} {mate : Fin n → Fin n}
    {p : Fin n × Fin n} (present : p ∈ pairsOfMate vertices mate) : s(p.1, p.2) ∈ mateEdgeSet vertices mate :=
  List.mem_toFinset.mpr (List.mem_map_of_mem present)

theorem mateEdgeSet_mem_partner {n : ℕ} {vertices : Finset (Fin n)} {mate : Fin n → Fin n}
    (valid : MateTableOn vertices mate) {v : Fin n} (member : v ∈ vertices) :
    s(v, mate v) ∈ mateEdgeSet vertices mate := by
  obtain ⟨partner, different, involutive⟩ := valid v member
  rcases lt_or_gt_of_ne different.symm with forward | backward
  · exact mateEdgeSet_of_pair (p := (v, mate v)) (mem_pairsOfMate.mpr ⟨member, forward, rfl⟩)
  · have ordered : mate v < mate (mate v) := involutive.symm ▸ backward
    have reversed := mateEdgeSet_of_pair (p := (mate v, v))
      (mem_pairsOfMate.mpr ⟨partner, ordered, involutive.symm⟩)
    simpa only [Sym2.eq_swap (a := v) (b := mate v)] using reversed

theorem mateEdgeSet_perfect {n : ℕ} {vertices : Finset (Fin n)} {mate : Fin n → Fin n}
    (valid : MateTableOn vertices mate) : IsPerfectMatchingOn vertices (mateEdgeSet vertices mate) := by
  constructor
  · intro e present
    obtain ⟨p, pIn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    obtain ⟨pFirst, ordered, second⟩ := mem_pairsOfMate.mp pIn
    have pSecond : p.2 ∈ vertices := second.symm ▸ (valid p.1 pFirst).1
    have separate : p.1 ≠ p.2 := ne_of_lt (second.symm ▸ ordered)
    exact ⟨mt Sym2.mk_isDiag_iff.mp separate, fun _ member =>
      (Sym2.mem_iff.mp member).elim (fun h => h.symm ▸ pFirst) (fun h => h.symm ▸ pSecond)⟩
  · intro v member
    refine ⟨s(v, mate v), ⟨mateEdgeSet_mem_partner valid member, Sym2.mem_mk_left _ _⟩, ?_⟩
    intro e other
    obtain ⟨p, pIn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp other.1)
    obtain ⟨pFirst, _, pPartner⟩ := mem_pairsOfMate.mp pIn
    rcases Sym2.mem_iff.mp other.2 with rfl | rfl
    · rw [pPartner]
    · rw [pPartner, (valid p.1 pFirst).2.2]
      exact Sym2.eq_swap

private theorem exists_partner_edge {n : ℕ} {vertices : Finset (Fin n)} {edges : Finset (Sym2 (Fin n))}
    (perfect : IsPerfectMatchingOn vertices edges) {v : Fin n} (member : v ∈ vertices) :
    ∃ w, s(v, w) ∈ edges := by
  obtain ⟨e, ⟨present, incident⟩, _⟩ := perfect.2 v member
  induction e using Sym2.inductionOn with
  | hf a b =>
    rcases Sym2.mem_iff.mp incident with left | right
    · exact ⟨b, left.symm ▸ present⟩
    · exact ⟨a, right.symm ▸ (Sym2.eq_swap ▸ present)⟩

private theorem partner_edge_unique {n : ℕ} {vertices : Finset (Fin n)} {edges : Finset (Sym2 (Fin n))}
    (perfect : IsPerfectMatchingOn vertices edges) {v a b : Fin n} (member : v ∈ vertices)
    (first : s(v, a) ∈ edges) (second : s(v, b) ∈ edges) : a = b := by
  have same := (perfect.2 v member).unique
    ⟨first, Sym2.mem_mk_left _ _⟩ ⟨second, Sym2.mem_mk_left _ _⟩
  exact (Sym2.eq_iff.mp same).elim And.right (fun reversed => reversed.2.trans reversed.1)

noncomputable def mateOfMatching {n : ℕ} {vertices : Finset (Fin n)} {edges : Finset (Sym2 (Fin n))}
    (perfect : IsPerfectMatchingOn vertices edges) (v : Fin n) : Fin n :=
  if member : v ∈ vertices then (exists_partner_edge perfect member).choose else v

theorem mateOfMatching_edge {n : ℕ} {vertices : Finset (Fin n)} {edges : Finset (Sym2 (Fin n))}
    (perfect : IsPerfectMatchingOn vertices edges) {v : Fin n} (member : v ∈ vertices) :
    s(v, mateOfMatching perfect v) ∈ edges := by
  rw [mateOfMatching, dif_pos member]
  exact (exists_partner_edge perfect member).choose_spec

theorem mateOfMatching_valid {n : ℕ} {vertices : Finset (Fin n)} {edges : Finset (Sym2 (Fin n))}
    (perfect : IsPerfectMatchingOn vertices edges) : MateTableOn vertices (mateOfMatching perfect) := by
  intro v member
  let w := mateOfMatching perfect v
  have edge := mateOfMatching_edge perfect member
  have specification := perfect.1 _ edge
  have wIn : w ∈ vertices := specification.2 w (Sym2.mem_mk_right _ _)
  exact ⟨wIn, fun equal => specification.1 (Sym2.mk_isDiag_iff.mpr equal.symm),
    partner_edge_unique perfect wIn (mateOfMatching_edge perfect wIn) (Sym2.eq_swap ▸ edge)⟩

/-- The edge-set and partner-array representations preserve the exact matching. -/
theorem mateEdgeSet_mateOfMatching {n : ℕ} {vertices : Finset (Fin n)} {edges : Finset (Sym2 (Fin n))}
    (perfect : IsPerfectMatchingOn vertices edges) : mateEdgeSet vertices (mateOfMatching perfect) = edges := by
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
    constructor
    · intro found
      obtain ⟨p, pIn, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp found)
      obtain ⟨inVertices, _, partner⟩ := mem_pairsOfMate.mp pIn
      exact equal ▸ (partner.symm ▸ mateOfMatching_edge perfect inVertices)
    · intro found
      have included : a ∈ vertices := (perfect.1 _ found).2 a (Sym2.mem_mk_left _ _)
      have same := partner_edge_unique perfect included (mateOfMatching_edge perfect included) found
      exact same ▸ mateEdgeSet_mem_partner (mateOfMatching_valid perfect) included

end VehicleRoutingSurvey.Routing
end RppSource_MateTable

/-! runtime/CompactMateSpec.lean -/
section RppSource_CompactMateSpec
namespace VehicleRoutingSurvey.Routing

/-- The compact matching input and its two scratch-space boundaries. -/
structure CompactMateInput {k : ℕ} (cost : Fin k → Fin k → ℝ) (s : ArithmeticState) : Prop where
  dimension : s.nr 32 = k
  even : k % 2 = 0
  rows : ∀ i < k, s.nm (s.nr 21 + i) = k * i
  weights : ∀ i j : Fin k, s.rm (s.nr 20 + k * i.val + j.val) = cost i j
  naturalSpace : s.nr 21 + k ≤ s.nr 63
  realSpace : s.nr 20 + k ^ 2 ≤ s.nr 64
  nonnegative : ∀ i j, 0 ≤ cost i j
  symmetric : ∀ i j, cost i j = cost j i
  diagonal : ∀ i, cost i i = 0

/-- A matching program publishes a minimum perfect matching as a mate
table, retaining the input and the registers needed by the routing stages. -/
structure CompactMateBlockSpec (code : List ArithmeticInstruction) (C : ℕ) : Prop where
  run {k : ℕ} {cost : Fin k → Fin k → ℝ} {s : ArithmeticState}
    (input : CompactMateInput cost s) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ (t : ArithmeticState) (mate : Fin k → Fin k) (steps : ℕ),
      BlockRuns code steps s t ∧ t.halted = false ∧ steps ≤ C * (k ^ 3 + 1) ∧
      t.nr 31 = s.nr 31 ∧ t.nr 32 = k ∧ s.nr 63 ≤ t.nr 33 ∧
      (∀ i : Fin k, t.nm (t.nr 33 + i.val) = (mate i).val) ∧
      SupplyChainTheory.IsMinMatchingOn cost Finset.univ (mateEdgeSet Finset.univ mate) ∧
      (∀ r ≥ 100, t.nr r = s.nr r) ∧
      (∀ address < s.nr 63, t.nm address = s.nm address) ∧
      ∀ address < s.nr 64, t.rm address = s.rm address

end VehicleRoutingSurvey.Routing
end RppSource_CompactMateSpec

/-! runtime/FloydRelax.lean -/
section RppSource_FloydRelax
namespace VehicleRoutingSurvey.Routing

/-- One Floyd–Warshall relaxation. Natural registers 0, 1, and 2 address the
destination, left operand, and right operand cells of real memory. -/
def floydRelaxBlock : List ArithmeticInstruction :=
  [.realLoad 0 0, .realLoad 1 1, .realLoad 2 2, .realAdd 1 1 2,
    .realBranch 0 1 5 6, .jump 7, .realStore 0 1]

/-- The block performs the min-plus update in six instructions in either
branch. No assumption about distinct addresses or positive weights is needed. -/
theorem floydRelaxBlock_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let t := (arithmeticStep floydRelaxBlock)^[6] s
    t.pc = floydRelaxBlock.length ∧ t.halted = false ∧ t.nr = s.nr ∧ t.nm = s.nm ∧
      t.rm = Function.update s.rm (s.nr 0)
        (min (s.rm (s.nr 0)) (s.rm (s.nr 1) + s.rm (s.nr 2))) := by
  let old := s.rm (s.nr 0)
  let x := s.rm (s.nr 1)
  let y := s.rm (s.nr 2)
  let readState := {s with
    pc := 4
    rr := Function.update (Function.update (Function.update (Function.update s.rr 0 old) 1 x)
      2 y) 1 (x + y)}
  have prep : (arithmeticStep floydRelaxBlock)^[4] s = readState := by
    simp [readState, old, x, y, floydRelaxBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  rw [show (6 : ℕ) = 2 + 4 by decide, Function.iterate_add_apply, prep]
  by_cases keep : old ≤ x + y
  · simp [readState, old, x, y, arithmeticStep, floydRelaxBlock, running,
      Function.iterate_succ_apply', keep, Function.update_eq_self]
  · simp [readState, old, x, y, arithmeticStep, floydRelaxBlock, running,
      Function.iterate_succ_apply', keep, min_eq_right (le_of_not_ge keep)]

end VehicleRoutingSurvey.Routing
end RppSource_FloydRelax

/-! runtime/FloydCell.lean -/
section RppSource_FloydCell
namespace VehicleRoutingSurvey.Routing

/-- The natural address table and the real matrix occupy distinct memories.
Natural registers 3–6 hold the table base, matrix base, dimension, and one. -/
structure FloydFrame (n table matrix : ℕ) (s : ArithmeticState) : Prop where
  tableBase : s.nr 3 = table
  matrixBase : s.nr 4 = matrix
  dimension : s.nr 5 = n
  one : s.nr 6 = 1
  rows : ∀ i < n, s.nm (table + i) = n * i

def FixedFloydRegisters (endExclusive : ℕ) (s t : ArithmeticState) : Prop :=
  ∀ r, 3 ≤ r → r < endExclusive → t.nr r = s.nr r

theorem FloydFrame.preserved {n table matrix : ℕ} {s t : ArithmeticState}
    (h : FloydFrame n table matrix s) (fixed : FixedFloydRegisters 7 s t)
    (memory : t.nm = s.nm) : FloydFrame n table matrix t := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [fixed 3 (by decide) (by decide), h.tableBase]
  · rw [fixed 4 (by decide) (by decide), h.matrixBase]
  · rw [fixed 5 (by decide) (by decide), h.dimension]
  · rw [fixed 6 (by decide) (by decide), h.one]
  · rw [memory]
    exact h.rows

/-- Update the row-major cell (i,j) with the path via pivot k. -/
noncomputable def floydCellMemory (n matrix k i j : ℕ) (memory : ℕ → ℝ) : ℕ → ℝ :=
  Function.update memory (matrix + n * i + j)
    (min (memory (matrix + n * i + j))
      (memory (matrix + n * i + k) + memory (matrix + n * k + j)))

private def loadMatrixRow (dst index : ℕ) : List ArithmeticInstruction :=
  [.natAdd dst 3 index, .natLoad dst dst, .natAdd dst 4 dst]

private theorem loadMatrixRow_runs (dst index : ℕ) (notBase : dst ≠ 4) (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns (loadMatrixRow dst index) 3 s
      {s with pc := 3, nr := Function.update s.nr dst (s.nr 4 + s.nm (s.nr 3 + s.nr index))} := by
  refine ⟨?_, ?_, rfl⟩
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [loadMatrixRow, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [loadMatrixRow, arithmeticStep, entry, running, Function.iterate_succ_apply',
      Function.update_of_ne (Ne.symm notBase), Function.update_idem]

private def loadCellAddresses : List ArithmeticInstruction :=
  [.natAdd 0 10 9, .natAdd 1 10 7, .natAdd 2 11 9]

private theorem loadCellAddresses_runs (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns loadCellAddresses 3 s
      {s with
        pc := 3
        nr := Function.update (Function.update (Function.update s.nr 0 (s.nr 10 + s.nr 9))
          1 (s.nr 10 + s.nr 7)) 2 (s.nr 11 + s.nr 9)} := by
  refine ⟨?_, ?_, rfl⟩
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [loadCellAddresses, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [loadCellAddresses, arithmeticStep, entry, running, Function.iterate_succ_apply']

private theorem floydRelaxBlock_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns floydRelaxBlock 6 s ((arithmeticStep floydRelaxBlock)^[6] s) := by
  refine ⟨?_, rfl, (floydRelaxBlock_correct s entry running).1⟩
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [floydRelaxBlock, arithmeticStep, entry, running, Function.iterate_succ_apply'] <;>
    split <;> decide

/-- The three loop indices are in natural registers k=7, i=8, and j=9. -/
def floydCellBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (loadMatrixRow 10 8) (loadMatrixRow 11 7))
    (appendBlock loadCellAddresses floydRelaxBlock)

theorem floydCellBlock_correct {n table matrix : ℕ} {s : ArithmeticState}
    (frame : FloydFrame n table matrix s) (entry : s.pc = 0) (running : s.halted = false)
    (kBound : s.nr 7 < n) (iBound : s.nr 8 < n) :
    ∃ t, BlockRuns floydCellBlock 15 s t ∧ t.halted = false ∧
      FixedFloydRegisters 10 s t ∧ t.nm = s.nm ∧
      t.rm = floydCellMemory n matrix (s.nr 7) (s.nr 8) (s.nr 9) s.rm := by
  let rowI := s.nr 4 + s.nm (s.nr 3 + s.nr 8)
  let rowK := s.nr 4 + s.nm (s.nr 3 + s.nr 7)
  let first := {s with pc := 3, nr := Function.update s.nr 10 rowI}
  let both := {s with pc := 6, nr := Function.update first.nr 11 rowK}
  have loadI : BlockRuns (loadMatrixRow 10 8) 3 s first :=
    loadMatrixRow_runs 10 8 (by decide) s entry running
  have loadK := loadMatrixRow_runs 11 7 (by decide) {first with pc := 0} rfl running
  have loaded : BlockRuns (appendBlock (loadMatrixRow 10 8) (loadMatrixRow 11 7)) 6 s both := by
    simpa [rowK, both, first, relocateState, loadMatrixRow] using loadI.append loadK
  let addressed := {both with
    pc := 3
    nr := Function.update (Function.update (Function.update both.nr 0 (rowI + s.nr 9))
      1 (rowI + s.nr 7)) 2 (rowK + s.nr 9)}
  have addresses : BlockRuns loadCellAddresses 3 {both with pc := 0} addressed := by
    simpa [both, first, addressed] using
      loadCellAddresses_runs {both with pc := 0} rfl running
  let reduced := (arithmeticStep floydRelaxBlock)^[6] {addressed with pc := 0}
  have relax : BlockRuns floydRelaxBlock 6 {addressed with pc := 0} reduced :=
    floydRelaxBlock_runs {addressed with pc := 0} rfl running
  have result := floydRelaxBlock_correct {addressed with pc := 0} rfl running
  have complete : BlockRuns floydCellBlock 15 s (relocateState 6 (relocateState 3 reduced)) :=
    loaded.append (addresses.append relax)
  refine ⟨_, complete, result.2.1, ?_, result.2.2.2.1, ?_⟩
  · intro r lower upper
    change reduced.nr r = s.nr r
    rw [result.2.2.1]
    simp [addressed, both, first,
      Function.update_of_ne (show r ≠ 0 by omega), Function.update_of_ne (show r ≠ 1 by omega),
      Function.update_of_ne (show r ≠ 2 by omega), Function.update_of_ne (show r ≠ 10 by omega),
      Function.update_of_ne (show r ≠ 11 by omega)]
  · change reduced.rm = _
    rw [result.2.2.2.2]
    simp [floydCellMemory, addressed, both, first, rowI, rowK, frame.matrixBase, frame.tableBase,
      frame.rows _ iBound, frame.rows _ kBound]

end VehicleRoutingSurvey.Routing
end RppSource_FloydCell

/-! runtime/APSPSetup.lean -/
section RppSource_APSPSetup
namespace VehicleRoutingSurvey.Routing

/-- Allocate the reverse-search work slices above the natural row offsets
and direct-link IDs. The direct-link matrix immediately follows the row
offsets. The last row offset plus n gives n squared in constant time. -/
def apspQueueLayoutBlock : List ArithmeticInstruction :=
  [.natLoad 10 6, .natAdd 11 3 5, .natSub 22 5 6, .natAdd 22 3 22,
    .natLoad 22 22, .natAdd 22 22 5, .natAdd 19 11 22, .natAdd 20 19 5, .natAdd 26 20 5]

private def apspQueueLayoutResult (s : ArithmeticState) : ArithmeticState :=
  let ids := s.nr 3 + s.nr 5
  let cells := s.nm (s.nr 3 + (s.nr 5 - s.nr 6)) + s.nr 5
  let rank := ids + cells
  let queue := rank + s.nr 5
  let next := queue + s.nr 5
  let common := Function.update (Function.update (Function.update s.nr 10 (s.nm (s.nr 6)))
    11 ids) 22 cells
  {s with
    pc := 9
    nr := Function.update (Function.update (Function.update common 19 rank) 20 queue) 26 next}

private theorem apspQueueLayoutBlock_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns apspQueueLayoutBlock 9 s (apspQueueLayoutResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i inside
    interval_cases i <;> simp [apspQueueLayoutBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  · simp [apspQueueLayoutBlock, apspQueueLayoutResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem]

/-- Initialize the next-path work areas from an existing Floyd frame and
the link count at input address 1. Neither input memory is written. -/
theorem apspQueueLayoutBlock_correct {n table matrix links : ℕ} {s : ArithmeticState}
    (frame : FloydFrame n table matrix s) (positive : 0 < n)
    (count : s.nm 1 = links) (entry : s.pc = 0) (running : s.halted = false) :
    let ids := table + n
    let rank := ids + n * n
    let queue := rank + n
    let next := queue + n
    ∃ t, BlockRuns apspQueueLayoutBlock 9 s t ∧ t.halted = false ∧
      FloydFrame n table matrix t ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 10 = links ∧ t.nr 11 = ids ∧ t.nr 19 = rank ∧ t.nr 20 = queue ∧ t.nr 26 = next := by
  let t := apspQueueLayoutResult s
  have previous : n - 1 < n := by omega
  have cells : s.nm (s.nr 3 + (s.nr 5 - s.nr 6)) + s.nr 5 = n * n := by
    rw [frame.tableBase, frame.dimension, frame.one, frame.rows _ previous]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    simp [Nat.mul_succ]
  have size : s.nm (table + (n - 1)) + n = n * n := by
    simpa only [frame.tableBase, frame.dimension, frame.one] using cells
  have fixed : FixedFloydRegisters 7 s t := by
    intro r lower upper
    simp [t, apspQueueLayoutResult, Function.update_of_ne (show r ≠ 10 by omega),
      Function.update_of_ne (show r ≠ 11 by omega), Function.update_of_ne (show r ≠ 19 by omega),
      Function.update_of_ne (show r ≠ 20 by omega), Function.update_of_ne (show r ≠ 22 by omega),
      Function.update_of_ne (show r ≠ 26 by omega)]
  refine ⟨t, apspQueueLayoutBlock_runs s entry running, running, frame.preserved fixed rfl,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [t, apspQueueLayoutResult, size, frame.dimension, frame.tableBase, frame.one, count]

end VehicleRoutingSurvey.Routing
end RppSource_APSPSetup

/-! runtime/FloydLoop.lean -/
section RppSource_FloydLoop
namespace VehicleRoutingSurvey.Routing

/-- Level zero is one update. Levels one, two, and three add the j, i,
and k loops respectively. The loops use registers 9, 8, and 7. -/
def floydLoopCode : ℕ → List ArithmeticInstruction
  | 0 => floydCellBlock
  | depth + 1 => countedLoopFromZero 6 (9 - depth) 5 (floydLoopCode depth)

def floydLoopSteps (n : ℕ) : ℕ → ℕ
  | 0 => 15
  | depth + 1 => 1 + (n * (floydLoopSteps n depth + 3) + 1)

noncomputable def floydLoopFold (n matrix : ℕ) :
    ℕ → (ℕ → ℕ) → (ℕ → ℝ) → ℕ → ℝ
  | 0, registers, memory =>
    floydCellMemory n matrix (registers 7) (registers 8) (registers 9) memory
  | depth + 1, registers, memory =>
    (List.range n).foldl
      (fun current i => floydLoopFold n matrix depth
        (Function.update registers (9 - depth) i) current) memory

private theorem floydLoopFold_congr (n matrix depth : ℕ) (supported : depth ≤ 3)
    {left right : ℕ → ℕ} (same : ∀ r, 7 ≤ r → r < 10 - depth → left r = right r)
    (memory : ℕ → ℝ) :
    floydLoopFold n matrix depth left memory = floydLoopFold n matrix depth right memory := by
  induction depth generalizing left right memory with
  | zero => simp [floydLoopFold, same 7 (by decide) (by decide),
      same 8 (by decide) (by decide), same 9 (by decide) (by decide)]
  | succ depth ih =>
    simp only [floydLoopFold]
    congr 1
    funext current i
    apply ih (by omega)
    intro r lower upper
    by_cases eq : r = 9 - depth
    · subst r
      simp
    · rw [Function.update_of_ne eq, Function.update_of_ne eq]
      exact same _ lower (by omega)

theorem floydLoopSteps_three (n : ℕ) :
    floydLoopSteps n 3 = 18 * n ^ 3 + 5 * n ^ 2 + 5 * n + 2 := by
  simp [floydLoopSteps]
  ring

theorem floydLoopCode_correct {n table matrix : ℕ} (depth : ℕ) (supported : depth ≤ 3)
    {s : ArithmeticState} (frame : FloydFrame n table matrix s)
    (entry : s.pc = 0) (running : s.halted = false)
    (bounded : ∀ r, 7 ≤ r → r < 10 - depth → s.nr r < n) :
    ∃ t, BlockRuns (floydLoopCode depth) (floydLoopSteps n depth) s t ∧
      t.halted = false ∧ FixedFloydRegisters (10 - depth) s t ∧ t.nm = s.nm ∧
      t.rm = floydLoopFold n matrix depth s.nr s.rm := by
  induction depth generalizing s with
  | zero =>
    exact floydCellBlock_correct frame entry running
      (bounded 7 (by decide) (by decide)) (bounded 8 (by decide) (by decide))
  | succ depth ih =>
    let index := 9 - depth
    have outer : 10 - (depth + 1) = index := by dsimp [index]; omega
    have inner : 10 - depth = index + 1 := by dsimp [index]; omega
    have inRange : 7 ≤ index := by dsimp [index]; omega
    let through (cut : ℕ) : ℕ → ℝ :=
      (List.range cut).foldl
        (fun memory i => floydLoopFold n matrix depth (Function.update s.nr index i) memory) s.rm
    let inv (cut : ℕ) (m : ArithmeticState) : Prop :=
      m.pc = 0 ∧ m.halted = false ∧ m.nr index = cut ∧ FixedFloydRegisters index s m ∧
      m.nm = s.nm ∧ m.rm = through cut
    have initial : inv 0 {s with pc := 0, nr := Function.update s.nr index 0} := by
      refine ⟨rfl, running, Function.update_self _ _ _, ?_, rfl, rfl⟩
      intro r _ before
      exact Function.update_of_ne (Nat.ne_of_lt before) _ _
    have control : ∀ cut m, inv cut m →
        m.pc = 0 ∧ m.halted = false ∧ m.nr index = cut ∧ m.nr 5 = n := by
      intro cut m hm
      exact ⟨hm.1, hm.2.1, hm.2.2.1,
        (hm.2.2.2.1 5 (by decide) (by omega)).trans frame.dimension⟩
    have runBody : ∀ cut < n, ∀ m, inv cut m → ∃ t,
        BlockRuns (floydLoopCode depth) (floydLoopSteps n depth) m t ∧ t.halted = false ∧
        inv (cut + 1) {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr 6)} := by
      intro cut more m hm
      obtain ⟨mEntry, mRunning, atCut, mFixed, mNatural, mReal⟩ := hm
      have mFrame : FloydFrame n table matrix m :=
        frame.preserved (fun r lower earlier => mFixed r lower (by omega)) mNatural
      have mBounded (r : ℕ) (lower : 7 ≤ r) (upper : r < 10 - depth) : m.nr r < n := by
        by_cases eq : r = index
        · subst r
          simpa only [atCut] using more
        · have earlier : r < index := by omega
          rw [mFixed r (by omega) earlier]
          exact bounded r lower (by omega)
      obtain ⟨t, executes, ready, bodyFixed, bodyNatural, bodyReal⟩ :=
        ih (by omega) mFrame mEntry mRunning mBounded
      have indexBound : index < 10 - depth := by omega
      have atCut' : t.nr index = cut := (bodyFixed index (by omega) indexBound).trans atCut
      have one : t.nr 6 = 1 := (bodyFixed 6 (by decide) (by omega)).trans mFrame.one
      refine ⟨t, executes, ready, rfl, ready, ?_, ?_, bodyNatural.trans mNatural, ?_⟩
      · simp [atCut', one]
      · intro r lower earlier
        change Function.update t.nr index (t.nr index + t.nr 6) r = s.nr r
        rw [Function.update_of_ne (Nat.ne_of_lt earlier)]
        exact (bodyFixed r lower (by omega)).trans (mFixed r lower earlier)
      · change t.rm = through (cut + 1)
        rw [bodyReal]
        have same (r : ℕ) (lower : 7 ≤ r) (upper : r < 10 - depth) :
            m.nr r = Function.update s.nr index cut r := by
          by_cases eq : r = index
          · subst r
            simp [atCut]
          · rw [Function.update_of_ne eq]
            exact mFixed r (by omega) (by omega)
        rw [floydLoopFold_congr n matrix depth (by omega) same, mReal]
        simp [through, List.range_succ, List.foldl_append]
    obtain ⟨last, lastOK, run⟩ := countedLoopFromZero_correct 6 index 5 n
      (floydLoopSteps n depth) (floydLoopCode depth) inv entry running initial control runBody
    obtain ⟨_, lastRunning, _, lastFixed, lastNatural, lastReal⟩ := lastOK
    refine ⟨_, run, lastRunning, ?_, lastNatural, lastReal⟩
    change FixedFloydRegisters (10 - (depth + 1)) s last
    rwa [outer]

noncomputable def floydMatrixMemory (n matrix : ℕ) (memory : ℕ → ℝ) : ℕ → ℝ :=
  (List.range n).foldl (fun atPivot k =>
    (List.range n).foldl (fun atRow i =>
      (List.range n).foldl (fun atColumn j => floydCellMemory n matrix k i j atColumn)
        atRow) atPivot) memory

def floydWarshallBlock : List ArithmeticInstruction := floydLoopCode 3

/-- The exact machine executes the three in-place Floyd–Warshall loops.
The input matrix and the row-offset table are supplied by the caller. -/
theorem floydWarshallBlock_correct {n table matrix : ℕ} {s : ArithmeticState}
    (frame : FloydFrame n table matrix s) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns floydWarshallBlock (18 * n ^ 3 + 5 * n ^ 2 + 5 * n + 2) s t ∧
      t.halted = false ∧ FixedFloydRegisters 7 s t ∧ t.nm = s.nm ∧
      t.rm = floydMatrixMemory n matrix s.rm := by
  simpa [floydWarshallBlock, floydLoopSteps_three, floydLoopFold, floydMatrixMemory] using
    floydLoopCode_correct 3 (by decide) frame entry running (fun r lower upper => by omega)

end VehicleRoutingSurvey.Routing
end RppSource_FloydLoop

/-! runtime/RowOffsets.lean -/
section RppSource_RowOffsets
namespace VehicleRoutingSurvey.Routing

/-- Fill a dense matrix address table by repeated addition, so a parallel
link needs only a constant-time table lookup to address its matrix cells.
Registers 0 and 1 hold 1 and the number of rows. Registers 3, 4 and 5 hold
the table cursor, row index, and current row offset. -/
def rowOffsetBlock : List ArithmeticInstruction :=
  [.natBranch 1 4 6 1, .natStore 3 5, .natAdd 3 3 0,
    .natAdd 4 4 0, .natAdd 5 5 1, .jump 0]

private structure RowScan (n base : ℕ) (original : ℕ → ℕ) (i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  one : s.nr 0 = 1
  count : s.nr 1 = n
  cursor : s.nr 3 = base + i
  index : s.nr 4 = i
  offset : s.nr 5 = n * i
  stored : ∀ k, s.nm k =
    if base ≤ k ∧ k < base + i then n * (k - base) else original k

private theorem rowScan_cycle (n base i : ℕ) (original : ℕ → ℕ) (s : ArithmeticState)
    (before : RowScan n base original i s) (hi : i < n) :
    RowScan n base original (i + 1) ((arithmeticStep rowOffsetBlock)^[6] s) := by
  have enter : arithmeticStep rowOffsetBlock s = {s with pc := 1} := by
    simp [arithmeticStep, rowOffsetBlock, before.entry, before.running, before.count,
      before.index, not_le.mpr hi]
  let after := {s with
    pc := 0
    nr := Function.update (Function.update (Function.update s.nr 3 (base + i + 1))
      4 (i + 1)) 5 (n * i + n)
    nm := Function.update s.nm (base + i) (n * i)}
  have cycle : (arithmeticStep rowOffsetBlock)^[6] s = after := by
    rw [show (6 : ℕ) = 5 + 1 by decide, Function.iterate_add_apply, Function.iterate_one, enter]
    simp [after, arithmeticStep, rowOffsetBlock, Function.iterate_succ_apply', before.running,
      before.cursor, before.offset, before.one, before.index, before.count]
  rw [cycle]
  refine ⟨rfl, before.running, by simpa [after] using before.one,
    by simpa [after] using before.count, by simp [after, Nat.add_assoc],
    by simp [after], by simp [after, Nat.mul_succ], ?_⟩
  intro k
  change Function.update s.nm (base + i) (n * i) k =
    if base ≤ k ∧ k < base + (i + 1) then n * (k - base) else original k
  by_cases equal : k = base + i
  · subst k
    rw [Function.update_self, if_pos (by omega)]
    simp
  · rw [Function.update_of_ne equal, before.stored]
    have same : (base ≤ k ∧ k < base + i) ↔ base ≤ k ∧ k < base + (i + 1) := by omega
    simp [same]

private theorem rowScan_progress (n base : ℕ) (s : ArithmeticState)
    (initial : RowScan n base s.nm 0 s) (i : ℕ) (hi : i ≤ n) :
    RowScan n base s.nm i ((arithmeticStep rowOffsetBlock)^[6 * i] s) := by
  induction i with
  | zero => exact initial
  | succ i ih =>
    rw [Nat.mul_succ, Nat.add_comm (6 * i), Function.iterate_add_apply]
    exact rowScan_cycle n base i s.nm _ (ih (Nat.le_of_succ_le hi)) hi

/-- The row-offset table is computed in six steps per row and one exit
branch. The block preserves all input cells before the table base. -/
theorem rowOffsetBlock_correct (n base : ℕ) (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 0 = 1)
    (count : s.nr 1 = n) (cursor : s.nr 3 = base) (index : s.nr 4 = 0)
    (offset : s.nr 5 = 0) :
    let t := (arithmeticStep rowOffsetBlock)^[6 * n + 1] s
    t.pc = rowOffsetBlock.length ∧ t.halted = false ∧
      (∀ i < n, t.nm (base + i) = n * i) ∧ (∀ j < base, t.nm j = s.nm j) := by
  have initial : RowScan n base s.nm 0 s :=
    ⟨entry, running, one, count, by simpa using cursor, index, by simpa using offset,
      fun k => by simp⟩
  let m := (arithmeticStep rowOffsetBlock)^[6 * n] s
  have complete : RowScan n base s.nm n m := rowScan_progress n base s initial n le_rfl
  have jumpOut : arithmeticStep rowOffsetBlock m = {m with pc := 6} := by
    simp [arithmeticStep, rowOffsetBlock, complete.entry, complete.running, complete.count,
      complete.index]
  rw [Nat.add_comm (6 * n), Function.iterate_add_apply, Function.iterate_one, jumpOut]
  refine ⟨rfl, complete.running, ?_, ?_⟩
  · intro i hi
    change m.nm (base + i) = n * i
    rw [complete.stored]
    simp [hi]
  · intro j hj
    change m.nm j = s.nm j
    rw [complete.stored, if_neg (fun inside => (not_le.mpr hj) inside.1)]

theorem ruralNatInput_length (I : Service) :
    (ruralNatInput I).length = 2 + 3 * I.graph.q := by
  simp [ruralNatInput, Nat.mul_comm]
  omega

/-- With columns in range, the row-offset lookup and addition give injective
addresses for a dense square matrix. -/
theorem denseMatrixOffset_eq_iff {n i j i' j' : ℕ} (hj : j < n) (hj' : j' < n) :
    n * i + j = n * i' + j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro address
    have preceding (r c r' : ℕ) (nextRow : r < r') (column : c < n) :
        n * r + c < n * r' := by
      calc
        n * r + c < n * (r + 1) := by simpa [Nat.mul_succ] using Nat.add_lt_add_left column (n * r)
        _ ≤ n * r' := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt nextRow)
    have row : i = i' := by
      rcases lt_trichotomy i i' with earlier | same | later
      · have strict := preceding i j i' earlier hj
        omega
      · exact same
      · have strict := preceding i' j' i later hj'
        omega
    subst i'
    exact ⟨rfl, Nat.add_left_cancel address⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end VehicleRoutingSurvey.Routing
end RppSource_RowOffsets

/-! runtime/FloydMemory.lean -/
section RppSource_FloydMemory
namespace VehicleRoutingSurvey.Routing

private def cellAddress (n matrix i j : ℕ) : ℕ := matrix + n * i + j

private theorem cellAddress_pair_eq {n matrix i j x y : ℕ} (hj : j < n) (hy : y < n)
    (same : cellAddress n matrix i j = cellAddress n matrix x y) : (i, j) = (x, y) := by
  have offsets : matrix + (n * i + j) = matrix + (n * x + y) := by
    simpa only [cellAddress, Nat.add_assoc] using same
  obtain ⟨rows, columns⟩ := (denseMatrixOffset_eq_iff hj hy).mp (Nat.add_left_cancel offsets)
  exact Prod.ext rows columns

private theorem cellMemory_other {n matrix pivot i j x y : ℕ} {memory : ℕ → ℝ}
    (jBound : j < n) (yBound : y < n) (different : (x, y) ≠ (i, j)) :
    floydCellMemory n matrix pivot i j memory (cellAddress n matrix x y) =
      memory (cellAddress n matrix x y) := by
  unfold floydCellMemory
  exact Function.update_of_ne (fun same => different (cellAddress_pair_eq yBound jBound same)) _ _

private theorem cellMemory_pivotBorder {n matrix pivot i j x y : ℕ} {memory : ℕ → ℝ}
    (diagonal : memory (cellAddress n matrix pivot pivot) = 0)
    (jBound : j < n) (yBound : y < n) (border : x = pivot ∨ y = pivot) :
    floydCellMemory n matrix pivot i j memory (cellAddress n matrix x y) =
      memory (cellAddress n matrix x y) := by
  by_cases same : (x, y) = (i, j)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    unfold cellAddress at diagonal
    rcases border with rfl | rfl <;> simp [floydCellMemory, cellAddress, diagonal]
  · exact cellMemory_other jBound yBound same

private noncomputable def sweepCells (n matrix pivot : ℕ) (cells : List (ℕ × ℕ))
    (memory : ℕ → ℝ) : ℕ → ℝ :=
  cells.foldl (fun current ij => floydCellMemory n matrix pivot ij.1 ij.2 current) memory

private theorem sweepCells_read {n matrix pivot x y : ℕ} (pivotBound : pivot < n)
    (yBound : y < n) (cells : List (ℕ × ℕ)) (unique : cells.Nodup)
    (columns : ∀ ij ∈ cells, ij.2 < n) (memory : ℕ → ℝ)
    (diagonal : memory (cellAddress n matrix pivot pivot) = 0) :
    sweepCells n matrix pivot cells memory (cellAddress n matrix x y) =
      if (x, y) ∈ cells then
        min (memory (cellAddress n matrix x y))
          (memory (cellAddress n matrix x pivot) + memory (cellAddress n matrix pivot y))
      else memory (cellAddress n matrix x y) := by
  induction cells generalizing memory with
  | nil => simp [sweepCells]
  | cons ij cells ih =>
    obtain ⟨i, j⟩ := ij
    obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
    have jBound : j < n := columns (i, j) List.mem_cons_self
    let next := floydCellMemory n matrix pivot i j memory
    have nextDiagonal : next (cellAddress n matrix pivot pivot) = 0 :=
      (cellMemory_pivotBorder diagonal jBound pivotBound (.inl rfl)).trans diagonal
    change sweepCells n matrix pivot cells next (cellAddress n matrix x y) = _
    rw [ih tailUnique (fun p hp => columns p (List.mem_cons_of_mem _ hp)) next nextDiagonal]
    by_cases seen : (x, y) ∈ cells
    · have different : (x, y) ≠ (i, j) := fun same => fresh (same ▸ seen)
      have current := cellMemory_other (pivot := pivot) (memory := memory)
        (matrix := matrix) jBound yBound different
      have left := cellMemory_pivotBorder (i := i) (j := j) diagonal jBound pivotBound
        (Or.inr rfl : x = pivot ∨ pivot = pivot)
      have right := cellMemory_pivotBorder (i := i) (j := j) diagonal jBound yBound
        (Or.inl rfl : pivot = pivot ∨ y = pivot)
      simp [List.mem_cons, seen, next, current, left, right]
    · by_cases same : (x, y) = (i, j)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        simp [List.mem_cons, seen, next, floydCellMemory, cellAddress]
      · simp [List.mem_cons, seen, same, next,
          cellMemory_other (pivot := pivot) (memory := memory) (matrix := matrix)
            jBound yBound same]

private def pivotCells (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).product (List.range n)

private noncomputable def floydPivotMemory (n matrix pivot : ℕ) (memory : ℕ → ℝ) :
    ℕ → ℝ :=
  (List.range n).foldl (fun atRow i =>
    (List.range n).foldl (fun atColumn j => floydCellMemory n matrix pivot i j atColumn)
      atRow) memory

private theorem floydPivotMemory_eq_sweepCells (n matrix pivot : ℕ) (memory : ℕ → ℝ) :
    floydPivotMemory n matrix pivot memory = sweepCells n matrix pivot (pivotCells n) memory := by
  simp [floydPivotMemory, sweepCells, pivotCells, List.product, List.foldl_flatMap, List.foldl_map]

private theorem floydPivotMemory_correct {n matrix pivot i j : ℕ} (pivotBound : pivot < n)
    (iBound : i < n) (jBound : j < n) (memory : ℕ → ℝ)
    (diagonal : memory (cellAddress n matrix pivot pivot) = 0) :
    floydPivotMemory n matrix pivot memory (cellAddress n matrix i j) =
      min (memory (cellAddress n matrix i j))
        (memory (cellAddress n matrix i pivot) + memory (cellAddress n matrix pivot j)) := by
  have unique : (pivotCells n).Nodup := List.nodup_range.product List.nodup_range
  have columns (ij : ℕ × ℕ) (present : ij ∈ pivotCells n) : ij.2 < n := by
    exact List.mem_range.mp (List.mem_product.mp present).2
  have present : (i, j) ∈ pivotCells n :=
    List.mem_product.mpr ⟨List.mem_range.mpr iBound, List.mem_range.mpr jBound⟩
  rw [floydPivotMemory_eq_sweepCells, sweepCells_read pivotBound jBound _ unique columns _
    diagonal, if_pos present]

/-- One Floyd layer reads all operands from the preceding layer. -/
noncomputable def floydLayer (pivot : ℕ) (distance : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun i j => min (distance i j) (distance i pivot + distance pivot j)

private theorem floydLayer_valid {n pivot : ℕ} {distance : ℕ → ℕ → ℝ}
    (pivotBound : pivot < n) (diagonal : ∀ i < n, distance i i = 0)
    (nonnegative : ∀ i < n, ∀ j < n, 0 ≤ distance i j) :
    (∀ i < n, floydLayer pivot distance i i = 0) ∧
      (∀ i < n, ∀ j < n, 0 ≤ floydLayer pivot distance i j) := by
  constructor
  · intro i hi
    rw [floydLayer, diagonal i hi, min_eq_left]
    exact add_nonneg (nonnegative i hi pivot pivotBound) (nonnegative pivot pivotBound i hi)
  · intro i hi j hj
    exact le_min (nonnegative i hi j hj)
      (add_nonneg (nonnegative i hi pivot pivotBound) (nonnegative pivot pivotBound j hj))

private theorem floydFold_correct {n matrix : ℕ} (pivots : List ℕ)
    (bounded : ∀ k ∈ pivots, k < n) (memory : ℕ → ℝ) (distance : ℕ → ℕ → ℝ)
    (agree : ∀ i < n, ∀ j < n, memory (cellAddress n matrix i j) = distance i j)
    (diagonal : ∀ i < n, distance i i = 0)
    (nonnegative : ∀ i < n, ∀ j < n, 0 ≤ distance i j) (i : ℕ) (hi : i < n)
    (j : ℕ) (hj : j < n) :
    (pivots.foldl (fun m pivot => floydPivotMemory n matrix pivot m) memory)
        (cellAddress n matrix i j) =
      (pivots.foldl (fun d pivot => floydLayer pivot d) distance) i j := by
  induction pivots generalizing memory distance with
  | nil => exact agree i hi j hj
  | cons pivot pivots ih =>
    have pivotBound := bounded pivot List.mem_cons_self
    obtain ⟨updatedDiagonal, updatedNonnegative⟩ :=
      floydLayer_valid pivotBound diagonal nonnegative
    have updatedAgree (x : ℕ) (hx : x < n) (y : ℕ) (hy : y < n) :
        floydPivotMemory n matrix pivot memory (cellAddress n matrix x y) =
          floydLayer pivot distance x y := by
      rw [floydPivotMemory_correct pivotBound hx hy memory
        ((agree pivot pivotBound pivot pivotBound).trans (diagonal pivot pivotBound))]
      rw [agree x hx y hy, agree x hx pivot pivotBound, agree pivot pivotBound y hy]
      rfl
    exact ih (fun k hk => bounded k (List.mem_cons_of_mem _ hk)) _ _
      updatedAgree updatedDiagonal updatedNonnegative

/-- On initialized nonnegative matrices with zero diagonal, machine memory
agrees with the recurrence that snapshots the complete preceding layer. -/
theorem floydMatrixMemory_correct (n matrix : ℕ) (memory : ℕ → ℝ)
    (diagonal : ∀ i < n, memory (matrix + n * i + i) = 0)
    (nonnegative : ∀ i < n, ∀ j < n, 0 ≤ memory (matrix + n * i + j))
    (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < n) :
    floydMatrixMemory n matrix memory (matrix + n * i + j) =
      ((List.range n).foldl (fun d pivot => floydLayer pivot d)
        (fun x y => memory (matrix + n * x + y))) i j :=
  floydFold_correct (List.range n) (fun _ hk => List.mem_range.mp hk) memory _
    (fun _ _ _ _ => rfl) diagonal nonnegative i hi j hj

private theorem foldl_preserves_real_cell {α : Type*} (updates : List α)
    (step : (ℕ → ℝ) → α → ℕ → ℝ) (memory : ℕ → ℝ) (address : ℕ)
    (same : ∀ m i, step m i address = m address) :
    updates.foldl step memory address = memory address := by
  induction updates generalizing memory with
  | nil => rfl
  | cons i updates ih =>
    rw [List.foldl_cons, ih, same]

/-- The in-place distance updates preserve the real input cells when
the distance matrix is allocated above them. -/
theorem floydMatrixMemory_preserves_input (n matrix : ℕ) (memory : ℕ → ℝ)
    {address : ℕ} (below : address < matrix) :
    floydMatrixMemory n matrix memory address = memory address := by
  unfold floydMatrixMemory
  apply foldl_preserves_real_cell
  intro beforePivot pivot
  apply foldl_preserves_real_cell
  intro beforeRow row
  apply foldl_preserves_real_cell
  intro beforeColumn column
  unfold floydCellMemory
  exact Function.update_of_ne (show address ≠ matrix + n * row + column by omega) _ _

theorem floydWarshallBlock_preserves_input {n table matrix : ℕ} {s t : ArithmeticState}
    (frame : FloydFrame n table matrix s) (entry : s.pc = 0) (running : s.halted = false)
    (run : BlockRuns floydWarshallBlock (18 * n ^ 3 + 5 * n ^ 2 + 5 * n + 2) s t)
    {address : ℕ} (below : address < matrix) : t.rm address = s.rm address := by
  obtain ⟨result, executes, _, _, _, memory⟩ := floydWarshallBlock_correct frame entry running
  have same : t = result := run.run.symm.trans executes.run
  rw [same, memory]
  exact floydMatrixMemory_preserves_input n matrix s.rm below

end VehicleRoutingSurvey.Routing
end RppSource_FloydMemory

/-! runtime/FloydPaths.lean -/
section RppSource_FloydPaths
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

private def PathInterior (u v : Fin G.n) (ts : List (Traversal G)) (x : Fin G.n) : Prop :=
  ∃ left right, ts = left ++ right ∧ left ≠ [] ∧ right ≠ [] ∧
    IsPath G u left x ∧ IsPath G x right v

private theorem pathEnd_mem_finishes {u v : Fin G.n} {ts : List (Traversal G)}
    (path : IsPath G u ts v) (nonempty : ts ≠ []) : v ∈ ts.map (finish G) := by
  induction ts generalizing u with
  | nil => exact (nonempty rfl).elim
  | cons first tail ih =>
    cases tail with
    | nil =>
      have endAt : finish G first = v := path.2.2
      simp [endAt]
    | cons step tail =>
      exact List.mem_cons_of_mem _ (ih path.2.2 (List.cons_ne_nil _ _))

private theorem pathVertices_append_nodup {u : Fin G.n}
    {left right : List (Traversal G)}
    (simple : (u :: (left ++ right).map (finish G)).Nodup) :
    (u :: left.map (finish G)).Nodup ∧ (right.map (finish G)).Nodup ∧
      ∀ x ∈ u :: left.map (finish G), ∀ y ∈ right.map (finish G), x ≠ y := by
  apply List.nodup_append.mp
  simpa only [List.cons_append, List.map_append] using simple

private theorem simplePath_end_not_interior {u v : Fin G.n} {ts : List (Traversal G)}
    (simple : (u :: ts.map (finish G)).Nodup) : ¬ PathInterior u v ts v := by
  rintro ⟨left, right, rfl, moreLeft, moreRight, first, second⟩
  have distinct := (pathVertices_append_nodup simple).2.2
  exact distinct v (List.mem_cons_of_mem _ (pathEnd_mem_finishes first moreLeft))
    v (pathEnd_mem_finishes second moreRight) rfl

private theorem simplePath_start_not_interior {u v : Fin G.n} {ts : List (Traversal G)}
    (simple : (u :: ts.map (finish G)).Nodup) : ¬ PathInterior u v ts u := by
  rintro ⟨left, right, rfl, moreLeft, _, first, _⟩
  apply (List.nodup_cons.mp simple).1
  rw [List.map_append, List.mem_append]
  exact Or.inl (pathEnd_mem_finishes first moreLeft)

private theorem interior_append_left {u mid v x : Fin G.n} {left right : List (Traversal G)}
    (interior : PathInterior u mid left x) (rest : IsPath G mid right v) :
    PathInterior u v (left ++ right) x := by
  obtain ⟨before, after, rfl, beforeNonempty, afterNonempty, first, second⟩ := interior
  exact ⟨before, after ++ right, List.append_assoc .., beforeNonempty,
    List.append_ne_nil_of_left_ne_nil afterNonempty _, first, isPath_append second rest⟩

private theorem interior_append_right {u mid v x : Fin G.n} {left right : List (Traversal G)}
    (rest : IsPath G u left mid) (interior : PathInterior mid v right x) :
    PathInterior u v (left ++ right) x := by
  obtain ⟨before, after, rfl, beforeNonempty, afterNonempty, first, second⟩ := interior
  exact ⟨left ++ before, after, (List.append_assoc ..).symm,
    List.append_ne_nil_of_right_ne_nil _ beforeNonempty, afterNonempty,
    isPath_append rest first, second⟩

private theorem floyd_upper_of_simplePath (input : ℕ → ℕ → ℝ)
    (diagonal : ∀ u : Fin G.n, input u u = 0)
    (edgeUpper : ∀ step : Traversal G, (G.directed step.1 = false ∨ step.2 = true) →
      input (start G step) (finish G step) ≤ G.weight step.1)
    (pivots : List ℕ) :
    ∀ {u v : Fin G.n} {ts : List (Traversal G)}, IsPath G u ts v →
      (u :: ts.map (finish G)).Nodup →
      (∀ x, PathInterior u v ts x → x.val ∈ pivots) →
      (pivots.foldl (fun d pivot => floydLayer pivot d) input) u v ≤ pathCost G ts := by
  induction pivots using List.reverseRecOn with
  | nil =>
    intro u v ts path _ permitted
    cases ts with
    | nil =>
      have endpoints : u = v := path
      subst v
      simp [diagonal, pathCost]
    | cons step tail =>
      cases tail with
      | nil =>
        have startAt : u = start G step := path.1
        have endAt : finish G step = v := path.2.2
        simpa [startAt, endAt, pathCost] using edgeUpper step path.2.1
      | cons next tail =>
        have first : IsPath G u [step] (finish G step) := ⟨path.1, path.2.1, rfl⟩
        have interior : PathInterior u v (step :: next :: tail) (finish G step) :=
          ⟨[step], next :: tail, rfl, by simp, by simp, first, path.2.2⟩
        exact False.elim (List.not_mem_nil (permitted _ interior))
  | append_singleton earlier pivot ih =>
    intro u v ts path simple permitted
    rw [List.foldl_append]
    change min _ _ ≤ _
    by_cases hits : ∃ x : Fin G.n, x.val = pivot ∧ PathInterior u v ts x
    · obtain ⟨mid, rfl, left, right, rfl, moreLeft, _, first, second⟩ := hits
      obtain ⟨simpleLeft, simpleRightTail, disjoint⟩ := pathVertices_append_nodup simple
      have midInLeft : mid ∈ u :: left.map (finish G) :=
        List.mem_cons_of_mem _ (pathEnd_mem_finishes first moreLeft)
      have simpleRight : (mid :: right.map (finish G)).Nodup :=
        List.nodup_cons.mpr ⟨fun seen => disjoint mid midInLeft mid seen rfl, simpleRightTail⟩
      have leftAllowed (x : Fin G.n) (internal : PathInterior u mid left x) : x.val ∈ earlier := by
        have seen := permitted x (interior_append_left internal second)
        refine (List.mem_append.mp seen).resolve_right ?_
        intro same
        have sameVertex : x = mid := Fin.ext (List.mem_singleton.mp same)
        subst x
        exact simplePath_end_not_interior simpleLeft internal
      have rightAllowed (x : Fin G.n) (internal : PathInterior mid v right x) : x.val ∈ earlier := by
        have seen := permitted x (interior_append_right first internal)
        refine (List.mem_append.mp seen).resolve_right ?_
        intro same
        have sameVertex : x = mid := Fin.ext (List.mem_singleton.mp same)
        subst x
        exact simplePath_start_not_interior simpleRight internal
      exact (min_le_right _ _).trans (by
        rw [pathCost_append]
        exact add_le_add (ih first simpleLeft leftAllowed) (ih second simpleRight rightAllowed))
    · apply (min_le_left _ _).trans
      exact ih path simple fun x internal => (List.mem_append.mp (permitted x internal)).resolve_right
        (fun same => hits ⟨x, List.mem_singleton.mp same, internal⟩)

private theorem floyd_lower_of_distance (connected : Connected G) (nonnegative : Nonnegative G)
    (pivots : List ℕ) (bounded : ∀ p ∈ pivots, p < G.n) (input : ℕ → ℕ → ℝ)
    (lower : ∀ u v : Fin G.n, distance G u v ≤ input u v) (u v : Fin G.n) :
    distance G u v ≤ (pivots.foldl (fun d pivot => floydLayer pivot d) input) u v := by
  induction pivots generalizing input with
  | nil => exact lower u v
  | cons p tail ih =>
    let mid : Fin G.n := ⟨p, bounded p List.mem_cons_self⟩
    have nextLower (x y : Fin G.n) : distance G x y ≤ floydLayer p input x y :=
      le_min (lower x y) ((distance_triangle connected nonnegative x mid y).trans
        (add_le_add (lower x mid) (lower mid y)))
    exact ih (fun k seen => bounded k (List.mem_cons_of_mem _ seen)) _ nextLower

/-- Floyd's snapshot recurrence returns the mission's shortest distance.
The initial matrix bounds every direct traversal and every graph distance
in the directions shown. This accommodates a finite absent-edge sentinel. -/
theorem floydLayers_eq_distance (connected : Connected G) (nonnegative : Nonnegative G)
    (input : ℕ → ℕ → ℝ) (diagonal : ∀ u : Fin G.n, input u u = 0)
    (edgeUpper : ∀ step : Traversal G, (G.directed step.1 = false ∨ step.2 = true) →
      input (start G step) (finish G step) ≤ G.weight step.1)
    (lower : ∀ u v : Fin G.n, distance G u v ≤ input u v) (u v : Fin G.n) :
    ((List.range G.n).foldl (fun d pivot => floydLayer pivot d) input) u v =
      distance G u v := by
  obtain ⟨ts, shortest, _, simple⟩ := exists_shortest_path connected nonnegative u v
  refine le_antisymm ?_
    (floyd_lower_of_distance connected nonnegative _ (fun _ member => List.mem_range.mp member)
      input lower u v)
  rw [distance_eq_of_shortestPath shortest]
  exact floyd_upper_of_simplePath input diagonal edgeUpper (List.range G.n) shortest.1 simple
    (fun x _ => List.mem_range.mpr x.isLt)

/-- The actual instruction block writes exact graph distances into the
initialized row-major distance matrix in cubic time. -/
theorem floydWarshallBlock_distances {table matrix : ℕ} {s : ArithmeticState}
    (connected : Connected G) (nonnegative : Nonnegative G)
    (frame : FloydFrame G.n table matrix s) (entry : s.pc = 0) (running : s.halted = false)
    (diagonal : ∀ u : Fin G.n, s.rm (matrix + G.n * u.val + u.val) = 0)
    (edgeUpper : ∀ step : Traversal G, (G.directed step.1 = false ∨ step.2 = true) →
      s.rm (matrix + G.n * (start G step).val + (finish G step).val) ≤ G.weight step.1)
    (lower : ∀ u v : Fin G.n, distance G u v ≤ s.rm (matrix + G.n * u.val + v.val)) :
    ∃ t, BlockRuns floydWarshallBlock (18 * G.n ^ 3 + 5 * G.n ^ 2 + 5 * G.n + 2) s t ∧
      t.halted = false ∧ FixedFloydRegisters 7 s t ∧ t.nm = s.nm ∧
      ∀ u v : Fin G.n, t.rm (matrix + G.n * u.val + v.val) = distance G u v := by
  obtain ⟨t, run, ready, fixed, natural, real⟩ := floydWarshallBlock_correct frame entry running
  refine ⟨t, run, ready, fixed, natural, fun u v => ?_⟩
  have nonnegativeInput (i : ℕ) (hi : i < G.n) (j : ℕ) (hj : j < G.n) :
      0 ≤ s.rm (matrix + G.n * i + j) :=
    (distance_nonnegative connected nonnegative ⟨i, hi⟩ ⟨j, hj⟩).trans (lower ⟨i, hi⟩ ⟨j, hj⟩)
  rw [real, floydMatrixMemory_correct G.n matrix s.rm
    (fun i hi => diagonal ⟨i, hi⟩) nonnegativeInput u.val u.isLt v.val v.isLt]
  exact floydLayers_eq_distance connected nonnegative _ diagonal edgeUpper lower u v

end VehicleRoutingSurvey.Routing
end RppSource_FloydPaths

/-! runtime/TightQueueCell.lean -/
section RppSource_TightQueueCell
namespace VehicleRoutingSurvey.Routing

/-- Consider an incoming edge in a reverse shortest-path search. Registers
12, 13, and 14 address the candidate vertex's rank, the next queue slot,
and its next-edge entry. Register 15 holds the link ID (the link count
in register 10 marks absent links), 16 the queue length, 17 the unvisited
rank sentinel, and 9 the candidate vertex. Real registers 1, 2, and 3
hold the candidate distance, edge weight, and distance of the vertex
already dequeued. Every branch costs eleven instructions. -/
def tightQueueCellBlock : List ArithmeticInstruction :=
  [.natLoad 18 12, .realAdd 2 2 3,
    .natBranch 10 15 11 3, .natBranch 17 18 4 12,
    .realBranch 1 2 5 13, .realBranch 2 1 6 14,
    .natStore 12 16, .natStore 13 9, .natStore 14 15, .natAdd 16 16 6, .jump 19,
    .jump 12, .jump 13, .jump 14, .jump 15, .jump 16, .jump 17, .jump 18, .jump 19]

def tightQueueCandidate (s : ArithmeticState) : Prop :=
  s.nr 15 < s.nr 10 ∧ s.nr 17 ≤ s.nm (s.nr 12) ∧ s.rr 1 = s.rr 2 + s.rr 3

noncomputable def tightQueueCellResult (s : ArithmeticState) : ArithmeticState := by
  classical
  let prep := {s with
    pc := tightQueueCellBlock.length
    nr := Function.update s.nr 18 (s.nm (s.nr 12))
    rr := Function.update s.rr 2 (s.rr 2 + s.rr 3)}
  exact if tightQueueCandidate s then
    {prep with
      nr := Function.update prep.nr 16 (s.nr 16 + s.nr 6)
      nm := Function.update
        (Function.update (Function.update s.nm (s.nr 12) (s.nr 16)) (s.nr 13) (s.nr 9))
        (s.nr 14) (s.nr 15)}
  else prep

/-- At a tight, previously undiscovered vertex the scanner adds its queue
entry, discovery rank, and next edge. All skip paths take the same time. -/
theorem tightQueueCellBlock_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns tightQueueCellBlock 11 s (tightQueueCellResult s) := by
  have inside (i : ℕ) (less : i < 11) :
      ((arithmeticStep tightQueueCellBlock)^[i] s).pc < tightQueueCellBlock.length := by
    by_cases missing : s.nr 10 ≤ s.nr 15
    · interval_cases i <;> simp [tightQueueCellBlock, arithmeticStep, entry, running,
        Function.iterate_succ_apply', missing]
    · by_cases fresh : s.nr 17 ≤ s.nm (s.nr 12)
      · by_cases below : s.rr 1 ≤ s.rr 2 + s.rr 3
        · by_cases above : s.rr 2 + s.rr 3 ≤ s.rr 1
          · interval_cases i <;> simp [tightQueueCellBlock, arithmeticStep, entry, running,
              Function.iterate_succ_apply', missing, fresh, below, above]
          · interval_cases i <;> simp [tightQueueCellBlock, arithmeticStep, entry, running,
              Function.iterate_succ_apply', missing, fresh, below, above]
        · interval_cases i <;> simp [tightQueueCellBlock, arithmeticStep, entry, running,
            Function.iterate_succ_apply', missing, fresh, below]
      · interval_cases i <;> simp [tightQueueCellBlock, arithmeticStep, entry, running,
          Function.iterate_succ_apply', missing, fresh]
  have result : (arithmeticStep tightQueueCellBlock)^[11] s = tightQueueCellResult s := by
    by_cases missing : s.nr 10 ≤ s.nr 15
    · simp [tightQueueCellBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
        tightQueueCellResult, tightQueueCandidate, missing, not_lt_of_ge missing]
    · have present : s.nr 15 < s.nr 10 := lt_of_not_ge missing
      by_cases fresh : s.nr 17 ≤ s.nm (s.nr 12)
      · by_cases below : s.rr 1 ≤ s.rr 2 + s.rr 3
        · by_cases above : s.rr 2 + s.rr 3 ≤ s.rr 1
          · have same := le_antisymm below above
            simp [tightQueueCellBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
              tightQueueCellResult, tightQueueCandidate, missing, present, fresh, below, above, same]
          · have different : s.rr 1 ≠ s.rr 2 + s.rr 3 := fun same => above same.ge
            simp [tightQueueCellBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
              tightQueueCellResult, tightQueueCandidate, missing, present, fresh, below, above, different]
        · have different : s.rr 1 ≠ s.rr 2 + s.rr 3 := fun same => below same.le
          simp [tightQueueCellBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
            tightQueueCellResult, tightQueueCandidate, missing, present, fresh, below, different]
      · simp [tightQueueCellBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
          tightQueueCellResult, tightQueueCandidate, missing, present, fresh]
  refine ⟨inside, result, ?_⟩
  classical
  unfold tightQueueCellResult
  split <;> rfl

end VehicleRoutingSurvey.Routing
end RppSource_TightQueueCell

/-! runtime/TightQueueScan.lean -/
section RppSource_TightQueueScan
namespace VehicleRoutingSurvey.Routing

/-- Load the reverse-search test for incoming edge u→v and destination
t. Registers 7, 8, and 9 hold t, v, and u respectively. Register 11
holds the direct-link matrix base. Registers 19, 20, and 21 hold the rank
table, queue, and current destination's next-edge row bases. The
distance matrix and row offsets use the Floyd frame bases. -/
def tightQueueReadBlock : List ArithmeticInstruction :=
  [.natAdd 22 3 9, .natLoad 22 22, .natAdd 23 3 8, .natLoad 23 23,
    .natAdd 12 19 9, .natAdd 13 20 16, .natAdd 14 21 9,
    .natAdd 15 22 8, .natAdd 15 11 15, .natLoad 15 15,
    .natAdd 24 4 22, .natAdd 24 24 7, .realLoad 1 24, .realLoad 2 15,
    .natAdd 25 4 23, .natAdd 25 25 7, .realLoad 3 25]

def tightQueueReadResult (s : ArithmeticState) : ArithmeticState :=
  let rowU := s.nm (s.nr 3 + s.nr 9)
  let rowV := s.nm (s.nr 3 + s.nr 8)
  let rows := Function.update (Function.update s.nr 22 rowU) 23 rowV
  let outputAddresses := Function.update
    (Function.update (Function.update rows 12 (s.nr 19 + s.nr 9)) 13 (s.nr 20 + s.nr 16))
    14 (s.nr 21 + s.nr 9)
  let link := s.nm (s.nr 11 + (rowU + s.nr 8))
  let distU := s.nr 4 + rowU + s.nr 7
  let distV := s.nr 4 + rowV + s.nr 7
  {
    s with
    pc := 17
    nr := Function.update (Function.update (Function.update outputAddresses 15 link) 24 distU)
      25 distV
    rr := Function.update
      (Function.update (Function.update s.rr 1 (s.rm distU)) 2 (s.rm link)) 3 (s.rm distV) }

private theorem tightQueueReadBlock_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns tightQueueReadBlock 17 s (tightQueueReadResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    interval_cases i <;>
      simp [tightQueueReadBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [tightQueueReadBlock, tightQueueReadResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem]

def tightQueueScanBlock : List ArithmeticInstruction :=
  appendBlock tightQueueReadBlock tightQueueCellBlock

/-- Loading the operands and processing one candidate edge takes exactly
28 machine instructions. -/
theorem tightQueueScanBlock_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns tightQueueScanBlock 28 s
      (relocateState tightQueueReadBlock.length
        (tightQueueCellResult {tightQueueReadResult s with pc := 0})) :=
  (tightQueueReadBlock_runs s entry running).append
    (tightQueueCellBlock_correct {tightQueueReadResult s with pc := 0} rfl running)

end VehicleRoutingSurvey.Routing
end RppSource_TightQueueScan

/-! runtime/PathReconstruction.lean -/
section RppSource_PathReconstruction
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- A traversal is tight toward a target if its weight accounts for the
decrease in distance to that target. -/
def tightTraversal (G : Network) (target : Fin G.n) (step : Traversal G) : Prop :=
  distance G (start G step) target =
    G.weight step.1 + distance G (finish G step) target

private theorem pathCost_cons (step : Traversal G) (tail : List (Traversal G)) :
    pathCost G (step :: tail) = G.weight step.1 + pathCost G tail := by
  simp [pathCost]

private theorem shortestPath_tail {u target : Fin G.n} {step : Traversal G}
    {tail : List (Traversal G)} (shortest : ShortestPath G u target (step :: tail)) :
    ShortestPath G (finish G step) target tail := by
  refine ⟨shortest.1.2.2, fun other valid => ?_⟩
  have comparison := shortest.2 (step :: other) ⟨shortest.1.1, shortest.1.2.1, valid⟩
  rw [pathCost_cons, pathCost_cons, add_le_add_iff_left] at comparison
  exact comparison

theorem shortestPath_all_tight {u target : Fin G.n} {ts : List (Traversal G)}
    (shortest : ShortestPath G u target ts) :
    ∀ step ∈ ts, tightTraversal G target step := by
  induction ts generalizing u with
  | nil => simp
  | cons first tail ih =>
    have shortestTail := shortestPath_tail shortest
    intro step occurs
    rcases List.mem_cons.mp occurs with rfl | inTail
    · rw [tightTraversal, ← shortest.1.1, distance_eq_of_shortestPath shortest,
        distance_eq_of_shortestPath shortestTail, pathCost_cons]
    · exact ih shortestTail _ inTail

/-- Reversing all tight traversals lets a search from the target reach every
source, via a walk whose length is strictly below the vertex count. -/
theorem exists_tight_path (connected : Connected G) (nonnegative : Nonnegative G)
    (u target : Fin G.n) :
    ∃ ts, IsPath G u ts target ∧ ts.length < G.n ∧
      (∀ step ∈ ts, tightTraversal G target step) := by
  obtain ⟨ts, shortest, length, _⟩ := exists_shortest_path connected nonnegative u target
  exact ⟨ts, shortest.1, length, shortestPath_all_tight shortest⟩

/-- Discovery numbers in a reverse search make tight traversal pointers into
simple shortest paths, including when some tight traversals have zero weight. -/
theorem exists_shortestPath_of_tight_pointers (nonnegative : Nonnegative G)
    (target : Fin G.n) (rank : Fin G.n → ℕ)
    (next : ∀ u, u ≠ target → Traversal G)
    (starts : ∀ u different, start G (next u different) = u)
    (allowed : ∀ u different, G.directed (next u different).1 = false ∨
      (next u different).2 = true)
    (tight : ∀ u different, tightTraversal G target (next u different))
    (decreases : ∀ u different, rank (finish G (next u different)) < rank u)
    (u : Fin G.n) :
    ∃ ts, ShortestPath G u target ts ∧ ts.length ≤ rank u ∧
      (u :: ts.map (finish G)).Nodup ∧
      (∀ x ∈ u :: ts.map (finish G), rank x ≤ rank u) := by
  generalize current : rank u = level
  induction level using Nat.strong_induction_on generalizing u with
  | h level ih =>
    subst level
    by_cases done : u = target
    · subst u
      exact ⟨[], ⟨rfl, fun ss _ => pathCost_nonnegative nonnegative ss⟩,
        Nat.zero_le _, by simp, by simp⟩
    · let first := next u done
      let after := finish G first
      have lower : rank after < rank u := decreases u done
      obtain ⟨tail, shortestTail, tailLength, uniqueTail, tailRanks⟩ :=
        ih (rank after) lower after rfl
      have valid : IsPath G u (first :: tail) target :=
        ⟨(starts u done).symm, allowed u done, shortestTail.1⟩
      have cost : pathCost G (first :: tail) = distance G u target := by
        have firstTight := tight u done
        rw [tightTraversal, starts u done] at firstTight
        rw [pathCost_cons, ← distance_eq_of_shortestPath shortestTail, firstTight]
      have shortest : ShortestPath G u target (first :: tail) :=
        ⟨valid, fun other path => cost.symm ▸ distance_le_pathCost nonnegative path⟩
      have length : (first :: tail).length ≤ rank u := by
        exact (Nat.succ_le_succ tailLength).trans lower
      have avoids : u ∉ after :: tail.map (finish G) :=
        fun seen => (Nat.not_le_of_gt lower) (tailRanks u seen)
      refine ⟨first :: tail, shortest, length, List.nodup_cons.mpr ⟨avoids, uniqueTail⟩, ?_⟩
      intro x seen
      rcases List.mem_cons.mp seen with rfl | inTail
      · exact le_rfl
      · exact (tailRanks x inTail).trans lower.le

end VehicleRoutingSurvey.Routing
end RppSource_PathReconstruction

/-! runtime/TightFrontier.lean -/
section RppSource_TightFrontier
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- Keeping only a lightest traversal between each ordered pair preserves
all incoming tight adjacencies. Parallel links can tie. -/
theorem tightTraversal_of_parallel_le (connected : Connected G) (nonnegative : Nonnegative G)
    {target : Fin G.n} {original replacement : Traversal G}
    (tight : tightTraversal G target original)
    (usable : G.directed replacement.1 = false ∨ replacement.2 = true)
    (sameStart : start G replacement = start G original)
    (sameFinish : finish G replacement = finish G original)
    (noHeavier : G.weight replacement.1 ≤ G.weight original.1) :
    tightTraversal G target replacement := by
  have direct : IsPath G (start G replacement) [replacement] (finish G replacement) :=
    ⟨rfl, usable, rfl⟩
  have distanceLE : distance G (start G replacement) (finish G replacement) ≤
      G.weight replacement.1 := by
    simpa [pathCost] using distance_le_pathCost nonnegative direct
  unfold tightTraversal at tight ⊢
  refine le_antisymm
    ((distance_triangle connected nonnegative (start G replacement) (finish G replacement) target).trans
      (add_le_add distanceLE le_rfl)) ?_
  rw [sameStart, sameFinish]
  exact (add_le_add noHeavier le_rfl).trans tight.ge

/-- The dense adjacency table retains a lightest usable direct link for
every ordered pair of distinct vertices joined by an input link. -/
def DirectLinkRepresentatives (G : Network) (chosen : Traversal G → Prop) : Prop :=
  ∀ original : Traversal G, (G.directed original.1 = false ∨ original.2 = true) →
    start G original ≠ finish G original →
    ∃ replacement : Traversal G, chosen replacement ∧
      (G.directed replacement.1 = false ∨ replacement.2 = true) ∧
      start G replacement = start G original ∧ finish G replacement = finish G original ∧
      G.weight replacement.1 ≤ G.weight original.1

/-- A list containing the target and closed under tight predecessors
contains every vertex. The scanner can use one minimum-weight directed
representative for each pair of distinct endpoints. -/
theorem tightSearch_closed_all (connected : Connected G) (nonnegative : Nonnegative G)
    (target : Fin G.n) (chosen : Traversal G → Prop)
    (representative : DirectLinkRepresentatives G chosen)
    (queue : List (Fin G.n)) (seed : target ∈ queue)
    (closed : ∀ step, chosen step → tightTraversal G target step →
      finish G step ∈ queue → start G step ∈ queue)
    (u : Fin G.n) : u ∈ queue := by
  obtain ⟨ts, shortest, _⟩ := exists_shortest_path connected nonnegative u target
  have arrives : ∀ {u : Fin G.n} {ts : List (Traversal G)},
      IsPath G u ts target → (∀ step ∈ ts, tightTraversal G target step) → u ∈ queue := by
    intro u ts path tight
    induction ts generalizing u with
    | nil =>
      have endpoints : u = target := path
      exact endpoints.symm ▸ seed
    | cons step tail ih =>
      have after : finish G step ∈ queue :=
        ih path.2.2 (fun e present => tight e (List.mem_cons_of_mem _ present))
      have firstTight := tight step List.mem_cons_self
      by_cases loop : start G step = finish G step
      · exact (path.1.trans loop).symm ▸ after
      · obtain ⟨replacement, selected, usable, sameStart, sameFinish, noHeavier⟩ :=
          representative step path.2.1 loop
        have replacementTight :=
          tightTraversal_of_parallel_le connected nonnegative firstTight usable sameStart sameFinish noHeavier
        exact (sameStart.trans path.1.symm) ▸
          closed replacement selected replacementTight (sameFinish.symm ▸ after)
  exact arrives shortest.1 (shortestPath_all_tight shortest)

/-- If every dequeued vertex has had its incoming row scanned, the queue
has an entry at the next index until all n vertices have been dequeued. -/
theorem tightQueue_no_underflow (connected : Connected G) (nonnegative : Nonnegative G)
    (target : Fin G.n) (chosen : Traversal G → Prop)
    (representative : DirectLinkRepresentatives G chosen)
    (queue : List (Fin G.n)) (seed : target ∈ queue) (processed : ℕ)
    (scanned : ∀ step, chosen step → tightTraversal G target step →
      finish G step ∈ queue.take processed → start G step ∈ queue)
    (remaining : processed < G.n) : processed < queue.length := by
  by_contra exhausted
  have lengthLE : queue.length ≤ processed := Nat.le_of_not_gt exhausted
  have fullyScanned : queue.take processed = queue := List.take_of_length_le lengthLE
  rw [fullyScanned] at scanned
  have reaches := tightSearch_closed_all connected nonnegative target chosen representative
    queue seed scanned
  have complete : queue.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun v => List.mem_toFinset.mpr (reaches v)
  have queueLength : G.n ≤ queue.length := by
    simpa [complete] using List.toFinset_card_le queue
  exact (Nat.not_lt_of_ge (queueLength.trans lengthLE)) remaining

end VehicleRoutingSurvey.Routing
end RppSource_TightFrontier

/-! runtime/TightQueueInvariant.lean -/
section RppSource_TightQueueInvariant
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

structure TightSearchState (G : Network) where
  queue : List (Fin G.n)
  rank : Fin G.n → ℕ
  next : Fin G.n → Option (Traversal G)

structure TightSearchInvariant (target : Fin G.n) (s : TightSearchState G) : Prop where
  unique : s.queue.Nodup
  seed : target ∈ s.queue
  ranks : ∀ u ∈ s.queue, s.rank u < s.queue.length
  unseen : ∀ u ∉ s.queue, s.rank u = G.n
  pointers : ∀ u ∈ s.queue, u ≠ target → ∃ step, s.next u = some step ∧
    start G step = u ∧ (G.directed step.1 = false ∨ step.2 = true) ∧
    tightTraversal G target step ∧ finish G step ∈ s.queue ∧
    s.rank (finish G step) < s.rank u

def initialTightSearch (target : Fin G.n) : TightSearchState G where
  queue := [target]
  rank := Function.update (fun _ => G.n) target 0
  next := fun _ => none

theorem initialTightSearch_invariant (target : Fin G.n) :
    TightSearchInvariant target (initialTightSearch target) := by
  refine ⟨by simp [initialTightSearch], by simp [initialTightSearch], ?_, ?_, ?_⟩
  · intro u found
    have same : u = target := List.mem_singleton.mp found
    subst u
    simp [initialTightSearch]
  · intro u missing
    have different : u ≠ target := fun same => missing (List.mem_singleton.mpr same)
    change Function.update (fun _ : Fin G.n => G.n) target 0 u = G.n
    rw [Function.update_of_ne different]
  · intro u found different
    exact (different (List.mem_singleton.mp found)).elim

def appendTightDiscovery (s : TightSearchState G) (u : Fin G.n) (edge : Traversal G) :
    TightSearchState G where
  queue := s.queue ++ [u]
  rank := Function.update s.rank u s.queue.length
  next := Function.update s.next u (some edge)

theorem appendTightDiscovery_invariant {target u : Fin G.n} {s : TightSearchState G}
    (valid : TightSearchInvariant target s) (fresh : u ∉ s.queue) (edge : Traversal G)
    (starts : start G edge = u) (usable : G.directed edge.1 = false ∨ edge.2 = true)
    (tight : tightTraversal G target edge) (parentKnown : finish G edge ∈ s.queue) :
    TightSearchInvariant target (appendTightDiscovery s u edge) := by
  have remains (x : Fin G.n) (found : x ∈ s.queue) : x ∈ (appendTightDiscovery s u edge).queue :=
    List.mem_append.mpr (.inl found)
  have oldRank (x : Fin G.n) (found : x ∈ s.queue) :
      (appendTightDiscovery s u edge).rank x = s.rank x := by
    have different : x ≠ u := fun same => fresh (same ▸ found)
    exact Function.update_of_ne different _ _
  refine ⟨?_, remains _ valid.seed, ?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨valid.unique, by simp, ?_⟩
    intro x old y new same
    exact fresh ((same.trans (List.mem_singleton.mp new)) ▸ old)
  · intro x found
    rcases List.mem_append.mp found with old | new
    · rw [oldRank _ old]
      exact (valid.ranks x old).trans (by simp [appendTightDiscovery])
    · have same : x = u := List.mem_singleton.mp new
      subst x
      simp [appendTightDiscovery]
  · intro x missing
    have different : x ≠ u :=
      fun same => missing (List.mem_append.mpr (.inr (List.mem_singleton.mpr same)))
    exact (Function.update_of_ne different _ _).trans
      (valid.unseen x (fun found => missing (remains x found)))
  · intro x found away
    rcases List.mem_append.mp found with old | new
    · obtain ⟨step, stored, begins, legal, isTight, endKnown, lower⟩ := valid.pointers x old away
      have different : x ≠ u := fun same => fresh (same ▸ old)
      exact ⟨step, (Function.update_of_ne different _ _).trans stored, begins, legal, isTight,
        remains _ endKnown, by rwa [oldRank _ endKnown, oldRank x old]⟩
    · have same : x = u := List.mem_singleton.mp new
      subst x
      refine ⟨edge, Function.update_self _ _ _, starts, usable, tight, remains _ parentKnown, ?_⟩
      rw [oldRank _ parentKnown]
      simpa [appendTightDiscovery] using valid.ranks _ parentKnown

abbrev DirectLinkTable (G : Network) := Fin G.n → Fin G.n → Option (Traversal G)

def DirectLinkTableSound (table : DirectLinkTable G) : Prop :=
  ∀ u v step, table u v = some step →
    start G step = u ∧ finish G step = v ∧ (G.directed step.1 = false ∨ step.2 = true)

def tableChooses (table : DirectLinkTable G) (step : Traversal G) : Prop :=
  table (start G step) (finish G step) = some step

noncomputable def scanTightCandidate (target : Fin G.n) (table : DirectLinkTable G)
    (v u : Fin G.n) (s : TightSearchState G) : TightSearchState G := by
  classical
  exact match table u v with
  | none => s
  | some step =>
    if u ∉ s.queue ∧ tightTraversal G target step then appendTightDiscovery s u step else s

theorem scanTightCandidate_correct {target : Fin G.n} {table : DirectLinkTable G}
    (sound : DirectLinkTableSound table) (u v : Fin G.n) (s : TightSearchState G)
    (known : v ∈ s.queue) (valid : TightSearchInvariant target s) :
    let t := scanTightCandidate target table v u s
    TightSearchInvariant target t ∧ s.queue <+: t.queue ∧
      ∀ step, table u v = some step → tightTraversal G target step → u ∈ t.queue := by
  classical
  cases cell : table u v with
  | none => simp [scanTightCandidate, cell, valid]
  | some edge =>
    obtain ⟨starts, finishes, usable⟩ := sound u v edge cell
    by_cases push : u ∉ s.queue ∧ tightTraversal G target edge
    · simp only [scanTightCandidate, cell, if_pos push]
      change TightSearchInvariant target (appendTightDiscovery s u edge) ∧
        s.queue <+: s.queue ++ [u] ∧
        ∀ step, some edge = some step → tightTraversal G target step → u ∈ s.queue ++ [u]
      exact ⟨appendTightDiscovery_invariant valid push.1 edge starts usable push.2
          (finishes.symm ▸ known), ⟨[u], rfl⟩, fun _ _ _ => by simp⟩
    · simp only [scanTightCandidate, cell, if_neg push]
      refine ⟨valid, ⟨[], List.append_nil _⟩, ?_⟩
      intro step equal tight
      have same : edge = step := Option.some.inj equal
      subst step
      by_contra missing
      exact push ⟨missing, tight⟩

noncomputable def scanTightIncoming (target : Fin G.n) (table : DirectLinkTable G)
    (v : Fin G.n) (s : TightSearchState G) : TightSearchState G :=
  (List.finRange G.n).foldl (fun q u => scanTightCandidate target table v u q) s

theorem scanTightIncoming_correct {target : Fin G.n} {table : DirectLinkTable G}
    (sound : DirectLinkTableSound table) (v : Fin G.n) (s : TightSearchState G)
    (known : v ∈ s.queue) (valid : TightSearchInvariant target s) :
    let t := scanTightIncoming target table v s
    TightSearchInvariant target t ∧ s.queue <+: t.queue ∧
      ∀ u step, table u v = some step → tightTraversal G target step → u ∈ t.queue := by
  have scan (sources : List (Fin G.n)) (q : TightSearchState G) (known : v ∈ q.queue)
      (valid : TightSearchInvariant target q) :
      let out := sources.foldl (fun st u => scanTightCandidate target table v u st) q
      TightSearchInvariant target out ∧ q.queue <+: out.queue ∧
        ∀ u ∈ sources, ∀ step, table u v = some step → tightTraversal G target step → u ∈ out.queue := by
    induction sources generalizing q with
    | nil => exact ⟨valid, ⟨[], List.append_nil _⟩, by simp⟩
    | cons first sources ih =>
      let after := scanTightCandidate target table v first q
      obtain ⟨afterValid, afterPrefix, firstDone⟩ :=
        scanTightCandidate_correct sound first v q known valid
      obtain ⟨finalValid, finalPrefix, moreDone⟩ :=
        ih after (afterPrefix.sublist.subset known) afterValid
      refine ⟨finalValid, afterPrefix.trans finalPrefix, ?_⟩
      intro u considered step selected tight
      rcases List.mem_cons.mp considered with rfl | later
      · exact finalPrefix.sublist.subset (firstDone step selected tight)
      · exact moreDone u later step selected tight
  obtain ⟨complete, extendsQueue, checked⟩ := scan (List.finRange G.n) s known valid
  exact ⟨complete, extendsQueue, fun u => checked u (List.mem_finRange u)⟩

def TightRowsScanned (target : Fin G.n) (table : DirectLinkTable G)
    (processed : ℕ) (s : TightSearchState G) : Prop :=
  ∀ step, tableChooses table step → tightTraversal G target step →
    finish G step ∈ s.queue.take processed → start G step ∈ s.queue

noncomputable def scanTightQueueIndex (target : Fin G.n) (table : DirectLinkTable G)
    (processed : ℕ) (s : TightSearchState G) : TightSearchState G :=
  match s.queue[processed]? with
  | none => s
  | some v => scanTightIncoming target table v s

private theorem scanTightQueueIndex_correct {target : Fin G.n} {table : DirectLinkTable G}
    (sound : DirectLinkTableSound table) (processed : ℕ) (s : TightSearchState G)
    (hasEntry : processed < s.queue.length) (valid : TightSearchInvariant target s)
    (scanned : TightRowsScanned target table processed s) :
    let out := scanTightQueueIndex target table processed s
    TightSearchInvariant target out ∧ TightRowsScanned target table (processed + 1) out := by
  let v := s.queue[processed]
  have known : v ∈ s.queue := List.getElem_mem hasEntry
  obtain ⟨afterValid, grows, incoming⟩ := scanTightIncoming_correct sound v s known valid
  let after := scanTightIncoming target table v s
  have next : scanTightQueueIndex target table processed s = after := by
    simp [scanTightQueueIndex, List.getElem?_eq_getElem hasEntry, after, v]
  suffices TightSearchInvariant target after ∧
      TightRowsScanned target table (processed + 1) after by
    simpa only [next] using this
  refine ⟨afterValid, ?_⟩
  intro edge selected tight endpoint
  have firstRows : after.queue.take (processed + 1) = s.queue.take (processed + 1) := by
    obtain ⟨more, exactQueue⟩ := grows
    rw [← exactQueue, List.take_append_of_le_length (Nat.succ_le_of_lt hasEntry)]
  rw [firstRows, List.take_succ_eq_append_getElem hasEntry] at endpoint
  rcases List.mem_append.mp endpoint with earlier | current
  · exact grows.sublist.subset (scanned edge selected tight earlier)
  · have eq : finish G edge = v := List.mem_singleton.mp current
    have atCell : table (start G edge) v = some edge := eq ▸ selected
    exact incoming (start G edge) edge atCell tight

/-- The abstract list-and-pointer state after the indicated number of
dequeues in the dense reverse search. -/
noncomputable def tightSearchAfter (target : Fin G.n) (table : DirectLinkTable G)
    (processed : ℕ) : TightSearchState G :=
  (List.range processed).foldl (fun s i => scanTightQueueIndex target table i s)
    (initialTightSearch target)

theorem tightSearchAfter_invariant (connected : Connected G) (nonnegative : Nonnegative G)
    (target : Fin G.n) (table : DirectLinkTable G) (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table))
    (processed : ℕ) (bounded : processed ≤ G.n) :
    TightSearchInvariant target (tightSearchAfter target table processed) ∧
      TightRowsScanned target table processed (tightSearchAfter target table processed) := by
  induction processed with
  | zero => exact ⟨initialTightSearch_invariant target, by simp [TightRowsScanned]⟩
  | succ processed ih =>
    obtain ⟨valid, scanned⟩ := ih (Nat.le_of_succ_le bounded)
    have existsEntry := tightQueue_no_underflow connected nonnegative target (tableChooses table)
      representative _ valid.seed processed scanned bounded
    simpa [tightSearchAfter, List.range_succ, List.foldl_append] using
      scanTightQueueIndex_correct sound processed _ existsEntry valid scanned

/-- Every vertex has a queue rank after exactly n dequeues. The preserved
pointer invariant gives valid tight next edges with decreasing rank. -/
theorem tightSearchAfter_complete (connected : Connected G) (nonnegative : Nonnegative G)
    (target : Fin G.n) (table : DirectLinkTable G) (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table)) :
    let out := tightSearchAfter target table G.n
    TightSearchInvariant target out ∧ ∀ u, u ∈ out.queue := by
  obtain ⟨valid, scanned⟩ :=
    tightSearchAfter_invariant connected nonnegative target table sound representative G.n le_rfl
  refine ⟨valid, ?_⟩
  have bounded : (tightSearchAfter target table G.n).queue.length ≤ G.n := by
    simpa using valid.unique.length_le_card
  have closed : ∀ step, tableChooses table step → tightTraversal G target step →
      finish G step ∈ (tightSearchAfter target table G.n).queue →
      start G step ∈ (tightSearchAfter target table G.n).queue := by
    simpa only [TightRowsScanned, List.take_of_length_le bounded] using scanned
  exact tightSearch_closed_all connected nonnegative target (tableChooses table)
    representative _ valid.seed closed

end VehicleRoutingSurvey.Routing
end RppSource_TightQueueInvariant

/-! runtime/TightQueueMemory.lean -/
section RppSource_TightQueueMemory
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- The data a dense reverse-search candidate reads from the mission's two
memories. A direct-link cell stores the link ID, or the input link count. -/
structure TightQueueCandidateFrame (rowOffsets distances : ℕ) (target v u : Fin G.n)
    (edge : Option (Traversal G)) (model : TightSearchState G) (s : ArithmeticState) : Prop where
  rows : FloydFrame G.n rowOffsets distances s
  targetReg : s.nr 7 = target.val
  dequeueReg : s.nr 8 = v.val
  candidateReg : s.nr 9 = u.val
  linkCountReg : s.nr 10 = G.q
  sentinelReg : s.nr 17 = G.n
  fromRank : s.nm (s.nr 19 + u.val) = model.rank u
  directLink : s.nm (s.nr 11 + G.n * u.val + v.val) =
    (edge.map (fun step => step.1.val)).getD G.q
  weightInput : ∀ e : Fin G.q, s.rm e.val = G.weight e
  sourceDistance : s.rm (distances + G.n * u.val + target.val) = distance G u target
  parentDistance : s.rm (distances + G.n * v.val + target.val) = distance G v target
  oriented : ∀ step, edge = some step → start G step = u ∧ finish G step = v

/-- The exact RAM test accepts precisely an unvisited source with a tight
direct link to the vertex currently dequeued. -/
theorem tightQueueCandidate_iff {rowOffsets distances : ℕ} {target v u : Fin G.n}
    {edge : Option (Traversal G)} {model : TightSearchState G} {s : ArithmeticState}
    (frame : TightQueueCandidateFrame rowOffsets distances target v u edge model s)
    (invariant : TightSearchInvariant target model) :
    tightQueueCandidate (tightQueueReadResult s) ↔
      ∃ step, edge = some step ∧ u ∉ model.queue ∧ tightTraversal G target step := by
  let read := tightQueueReadResult s
  have fromRow : s.nm (s.nr 3 + s.nr 9) = G.n * u.val := by
    rw [frame.rows.tableBase, frame.candidateReg, frame.rows.rows _ u.isLt]
  have parentRow : s.nm (s.nr 3 + s.nr 8) = G.n * v.val := by
    rw [frame.rows.tableBase, frame.dequeueReg, frame.rows.rows _ v.isLt]
  have link : read.nr 15 = (edge.map (fun step => step.1.val)).getD G.q := by
    simpa [read, tightQueueReadResult, fromRow, frame.dequeueReg, Nat.add_assoc] using frame.directLink
  have total : read.nr 10 = G.q := by
    simp [read, tightQueueReadResult, frame.linkCountReg]
  have sentinel : read.nr 17 = G.n := by
    simp [read, tightQueueReadResult, frame.sentinelReg]
  have rank : read.nm (read.nr 12) = model.rank u := by
    simpa [read, tightQueueReadResult, frame.candidateReg] using frame.fromRank
  have source : read.rr 1 = distance G u target := by
    simpa [read, tightQueueReadResult, fromRow, frame.rows.matrixBase, frame.targetReg] using
      frame.sourceDistance
  have parent : read.rr 3 = distance G v target := by
    simpa [read, tightQueueReadResult, parentRow, frame.rows.matrixBase, frame.targetReg] using
      frame.parentDistance
  have absent : G.n ≤ model.rank u ↔ u ∉ model.queue := by
    constructor
    · intro atLeast known
      have bounded : model.queue.length ≤ G.n := by simpa using invariant.unique.length_le_card
      exact (Nat.not_lt_of_ge atLeast) ((invariant.ranks u known).trans_le bounded)
    · intro unseen
      rw [invariant.unseen u unseen]
  change tightQueueCandidate read ↔ _
  unfold tightQueueCandidate
  rw [link, total, sentinel, rank, absent, source, parent]
  cases edge with
  | none => simp
  | some step =>
    obtain ⟨starts, finishes⟩ := frame.oriented step rfl
    have weight : read.rr 2 = G.weight step.1 := by
      have readID : s.nm (s.nr 11 + (s.nm (s.nr 3 + s.nr 9) + s.nr 8)) = step.1.val := by
        simpa [read, tightQueueReadResult] using link
      simp [read, tightQueueReadResult, readID, frame.weightInput]
    simp [step.1.isLt, weight, tightTraversal, starts, finishes]

/-- The machine appends the accepted source and its link ID to the three
queue arrays. Register 20 addresses the queue, and 21 the next-edge row. -/
theorem tightQueueScanBlock_updates {rowOffsets distances : ℕ} {target v u : Fin G.n}
    {edge : Option (Traversal G)} {model : TightSearchState G} {s : ArithmeticState}
    (frame : TightQueueCandidateFrame rowOffsets distances target v u edge model s)
    (invariant : TightSearchInvariant target model) (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns tightQueueScanBlock 28 s t ∧ t.halted = false ∧ t.rm = s.rm ∧
      (∀ step, edge = some step → u ∉ model.queue → tightTraversal G target step →
        t.nr 16 = s.nr 16 + 1 ∧
        t.nm = Function.update (Function.update
          (Function.update s.nm (s.nr 19 + u.val) (s.nr 16)) (s.nr 20 + s.nr 16) u.val)
          (s.nr 21 + u.val) step.1.val) ∧
      ((¬∃ step, edge = some step ∧ u ∉ model.queue ∧ tightTraversal G target step) →
        t.nr 16 = s.nr 16 ∧ t.nm = s.nm) := by
  classical
  let read := tightQueueReadResult s
  let t := relocateState tightQueueReadBlock.length (tightQueueCellResult {read with pc := 0})
  have agrees := tightQueueCandidate_iff frame invariant
  have test : tightQueueCandidate {read with pc := 0} = tightQueueCandidate read := rfl
  have link (step : Traversal G) (present : edge = some step) : read.nr 15 = step.1.val := by
    have offset : s.nm (s.nr 3 + s.nr 9) = G.n * u.val := by
      rw [frame.rows.tableBase, frame.candidateReg, frame.rows.rows _ u.isLt]
    simpa [read, tightQueueReadResult, offset, frame.dequeueReg, Nat.add_assoc, present]
      using frame.directLink
  have unchanged : t.halted = false ∧ t.rm = s.rm := by
    unfold t tightQueueCellResult relocateState
    split <;> exact ⟨running, rfl⟩
  refine ⟨t, tightQueueScanBlock_correct s entry running, unchanged.1, unchanged.2, ?_, ?_⟩
  · intro step present fresh tight
    have accepted : tightQueueCandidate {read with pc := 0} :=
      test.symm ▸ agrees.mpr ⟨step, present, fresh, tight⟩
    have readID := link step present
    unfold t tightQueueCellResult relocateState
    simp only [if_pos accepted]
    change s.nr 16 + s.nr 6 = s.nr 16 + 1 ∧
      Function.update (Function.update (Function.update s.nm (read.nr 12) (s.nr 16))
        (read.nr 13) (read.nr 9)) (read.nr 14) (read.nr 15) = _
    rw [readID, frame.rows.one]
    simp [read, tightQueueReadResult, frame.candidateReg]
  · intro noCandidate
    have rejected : ¬tightQueueCandidate {read with pc := 0} := fun accepted =>
      noCandidate (agrees.mp (test ▸ accepted))
    unfold t tightQueueCellResult relocateState
    simp only [if_neg rejected]
    exact ⟨by simp [read, tightQueueReadResult], rfl⟩

end VehicleRoutingSurvey.Routing
end RppSource_TightQueueMemory

/-! runtime/TightQueueArrays.lean -/
section RppSource_TightQueueArrays
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

def DisjointNaturalSlices (left right length : ℕ) : Prop :=
  ∀ i < length, ∀ j < length, left + i ≠ right + j

structure QueueSlicesSeparated (rankBase queueBase nextBase length : ℕ) : Prop where
  rankQueue : DisjointNaturalSlices rankBase queueBase length
  rankNext : DisjointNaturalSlices rankBase nextBase length
  queueNext : DisjointNaturalSlices queueBase nextBase length

structure TightQueueNaturalMemory (rankBase queueBase nextBase : ℕ)
    (model : TightSearchState G) (memory : ℕ → ℕ) : Prop where
  rank : ∀ u : Fin G.n, memory (rankBase + u.val) = model.rank u
  queue : ∀ i (bound : i < model.queue.length), memory (queueBase + i) = model.queue[i].val
  next : ∀ (u : Fin G.n) (step : Traversal G),
    model.next u = some step → memory (nextBase + u.val) = step.1.val

/-- After resetting ranks, the three seed stores give exactly the initial
queue, initial rank, and empty pointer table of the abstract search. -/
theorem tightSearchSeed_memory (target : Fin G.n) (rankBase queueBase nextBase : ℕ)
    (memory : ℕ → ℕ) (separation : QueueSlicesSeparated rankBase queueBase nextBase G.n)
    (cleared : ∀ u : Fin G.n, memory (rankBase + u.val) = G.n) :
    TightQueueNaturalMemory rankBase queueBase nextBase (initialTightSearch target)
      (Function.update (Function.update
        (Function.update memory (rankBase + target.val) 0) queueBase target.val)
        (nextBase + target.val) G.q) := by
  have nonempty : 0 < G.n := Nat.zero_lt_of_lt target.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro u
    have otherNext := separation.rankNext u.val u.isLt target.val target.isLt
    have otherQueue : rankBase + u.val ≠ queueBase := by
      simpa using separation.rankQueue u.val u.isLt 0 nonempty
    rw [Function.update_of_ne otherNext, Function.update_of_ne otherQueue]
    by_cases same : u = target
    · subst u
      simp [initialTightSearch]
    · have otherRank : rankBase + u.val ≠ rankBase + target.val :=
        fun eq => same (Fin.ext (Nat.add_left_cancel eq))
      rw [Function.update_of_ne otherRank, cleared u]
      simp [initialTightSearch, Function.update_of_ne same]
  · intro i bounded
    have zero : i = 0 := by simpa [initialTightSearch] using bounded
    subst i
    have otherNext : queueBase ≠ nextBase + target.val := by
      simpa using separation.queueNext 0 nonempty target.val target.isLt
    simp [initialTightSearch, Function.update_of_ne otherNext]
  · intro _ _ impossible
    cases impossible

private def appendQueueMemory (rankBase queueBase nextBase : ℕ)
    (model : TightSearchState G) (memory : ℕ → ℕ) (u : Fin G.n)
    (step : Traversal G) : ℕ → ℕ :=
  Function.update (Function.update
    (Function.update memory (rankBase + u.val) model.queue.length)
      (queueBase + model.queue.length) u.val)
    (nextBase + u.val) step.1.val

/-- The three physical writes in a successful queue-cell update implement
the abstract discovery, when the rank, queue, and next-edge slices are disjoint. -/
theorem appendTightDiscovery_memory {rankBase queueBase nextBase : ℕ}
    {model : TightSearchState G} {memory : ℕ → ℕ} {u : Fin G.n}
    (step : Traversal G) (room : model.queue.length < G.n)
    (separation : QueueSlicesSeparated rankBase queueBase nextBase G.n)
    (encoded : TightQueueNaturalMemory rankBase queueBase nextBase model memory) :
    TightQueueNaturalMemory rankBase queueBase nextBase (appendTightDiscovery model u step)
      (appendQueueMemory rankBase queueBase nextBase model memory u step) := by
  have off (base : ℕ) (x : Fin G.n) (differs : x ≠ u) : base + x.val ≠ base + u.val :=
    fun equal => differs (Fin.ext (Nat.add_left_cancel equal))
  constructor
  · intro x
    have otherQueue := separation.rankQueue x.val x.isLt model.queue.length room
    have otherNext := separation.rankNext x.val x.isLt u.val u.isLt
    simp only [appendQueueMemory, Function.update_of_ne otherNext, Function.update_of_ne otherQueue]
    by_cases same : x = u
    · subst x
      simp [appendTightDiscovery]
    · rw [Function.update_of_ne (off _ x same), encoded.rank]
      exact (Function.update_of_ne same _ _).symm
  · intro i bound
    have endBound : i < model.queue.length + 1 := by
      simpa [appendTightDiscovery] using bound
    have bounded : i < G.n := endBound.trans_le room
    have otherRank := (separation.rankQueue u.val u.isLt i bounded).symm
    have otherNext := separation.queueNext i bounded u.val u.isLt
    simp only [appendQueueMemory, Function.update_of_ne otherNext]
    change Function.update (Function.update memory (rankBase + u.val) model.queue.length)
      (queueBase + model.queue.length) u.val (queueBase + i) = ((model.queue ++ [u])[i]).val
    by_cases before : i < model.queue.length
    · have different : queueBase + i ≠ queueBase + model.queue.length :=
        fun eq => (Nat.ne_of_lt before) (Nat.add_left_cancel eq)
      rw [Function.update_of_ne different, Function.update_of_ne otherRank, encoded.queue i before]
      exact congrArg Fin.val (List.getElem_append_left' before [u])
    · have atEnd : i = model.queue.length := by omega
      subst i
      rw [Function.update_self]
      have last : u = (model.queue ++ [u])[model.queue.length]'(by simp) := by
        simpa using (List.getElem_append_right' model.queue (l₂ := [u]) (i := 0) (by simp))
      exact congrArg Fin.val last
  · intro x chosen stored
    by_cases same : x = u
    · subst x
      have chosenEq : step = chosen := Option.some.inj (by simpa [appendTightDiscovery] using stored)
      simp [appendQueueMemory, chosenEq]
    · have otherRank := (separation.rankNext u.val u.isLt x.val x.isLt).symm
      have otherQueue := (separation.queueNext model.queue.length room x.val x.isLt).symm
      rw [appendQueueMemory, Function.update_of_ne (off _ x same),
        Function.update_of_ne otherQueue, Function.update_of_ne otherRank]
      exact encoded.next x chosen (by simpa [appendTightDiscovery, Function.update_of_ne same] using stored)

/-- One exact machine scan refines the abstract queue candidate transition,
including the queue tail and all occupied rank, queue, and pointer cells. -/
theorem tightQueueScanBlock_refines {rowOffsets distances : ℕ} {target v u : Fin G.n}
    {table : DirectLinkTable G} {model : TightSearchState G} {s : ArithmeticState}
    (frame : TightQueueCandidateFrame rowOffsets distances target v u (table u v) model s)
    (valid : TightSearchInvariant target model) (sound : DirectLinkTableSound table)
    (parentKnown : v ∈ model.queue) (tail : s.nr 16 = model.queue.length)
    (separation : QueueSlicesSeparated (s.nr 19) (s.nr 20) (s.nr 21) G.n)
    (encoded : TightQueueNaturalMemory (s.nr 19) (s.nr 20) (s.nr 21) model s.nm)
    (entry : s.pc = 0) (running : s.halted = false) :
    let after := scanTightCandidate target table v u model
    ∃ t, BlockRuns tightQueueScanBlock 28 s t ∧ t.halted = false ∧ t.rm = s.rm ∧
      t.nr 16 = after.queue.length ∧
      TightQueueNaturalMemory (s.nr 19) (s.nr 20) (s.nr 21) after t.nm := by
  classical
  obtain ⟨t, run, ready, real, accept, reject⟩ :=
    tightQueueScanBlock_updates frame valid entry running
  refine ⟨t, run, ready, real, ?_⟩
  cases chosen : table u v with
  | none =>
    have unchanged := reject (by simp [chosen])
    simpa [scanTightCandidate, chosen, unchanged.2] using And.intro (unchanged.1.trans tail) encoded
  | some edge =>
    by_cases enqueue : u ∉ model.queue ∧ tightTraversal G target edge
    · obtain ⟨starts, ends, allowed⟩ := sound u v edge chosen
      have updatedValid := appendTightDiscovery_invariant valid enqueue.1 edge starts allowed
        enqueue.2 (ends.symm ▸ parentKnown)
      have appendedBound : (appendTightDiscovery model u edge).queue.length ≤ G.n := by
        simpa using updatedValid.unique.length_le_card
      have room : model.queue.length < G.n := by
        simpa [appendTightDiscovery] using appendedBound
      have writes := accept edge chosen enqueue.1 enqueue.2
      simp only [scanTightCandidate, chosen, if_pos enqueue]
      refine ⟨by simp [appendTightDiscovery, writes.1, tail], ?_⟩
      rw [writes.2, tail]
      exact appendTightDiscovery_memory edge room separation encoded
    · have noCandidate : ¬∃ step, table u v = some step ∧
          u ∉ model.queue ∧ tightTraversal G target step := by
        intro option
        obtain ⟨step, stepChosen, fresh, tight⟩ := option
        have same := Option.some.inj (chosen.symm.trans stepChosen)
        subst step
        exact enqueue ⟨fresh, tight⟩
      have unchanged := reject noCandidate
      simpa [scanTightCandidate, chosen, enqueue, unchanged.2] using
        And.intro (unchanged.1.trans tail) encoded

/-- A search whose work arrays start above a prefix preserves all natural
input and operand cells in that prefix. -/
theorem tightQueueScanBlock_preserves_prefix {rowOffsets distances : ℕ} {target v u : Fin G.n}
    {edge : Option (Traversal G)} {model : TightSearchState G} {s t : ArithmeticState}
    (frame : TightQueueCandidateFrame rowOffsets distances target v u edge model s)
    (valid : TightSearchInvariant target model) (entry : s.pc = 0)
    (running : s.halted = false) (run : BlockRuns tightQueueScanBlock 28 s t)
    (address : ℕ) (belowRank : address < s.nr 19) (belowQueue : address < s.nr 20)
    (belowNext : address < s.nr 21) : t.nm address = s.nm address := by
  classical
  obtain ⟨after, executes, _, _, append, skip⟩ :=
    tightQueueScanBlock_updates frame valid entry running
  have same : t = after := run.run.symm.trans executes.run
  rw [same]
  by_cases candidate : ∃ step, edge = some step ∧ u ∉ model.queue ∧ tightTraversal G target step
  · obtain ⟨step, selected, fresh, tight⟩ := candidate
    rw [(append step selected fresh tight).2,
      Function.update_of_ne (show address ≠ s.nr 21 + u.val by omega),
      Function.update_of_ne (show address ≠ s.nr 20 + s.nr 16 by omega),
      Function.update_of_ne (show address ≠ s.nr 19 + u.val by omega)]
  · rw [(skip candidate).2]

/-- Addresses outside the three bounded work slices include all other
destination rows of the global next-edge table. -/
def OutsideQueueSlices (rankBase queueBase nextBase length address : ℕ) : Prop :=
  (∀ i < length, address ≠ rankBase + i) ∧
    (∀ i < length, address ≠ queueBase + i) ∧
    (∀ i < length, address ≠ nextBase + i)

/-- A stage keeps the three physical slice bases and touches no other
natural memory. The property composes across machine blocks. -/
structure QueueWriteFootprint (length : ℕ) (before after : ArithmeticState) : Prop where
  rankBase : after.nr 19 = before.nr 19
  queueBase : after.nr 20 = before.nr 20
  nextBase : after.nr 21 = before.nr 21
  outside : ∀ address, OutsideQueueSlices (before.nr 19) (before.nr 20) (before.nr 21)
    length address → after.nm address = before.nm address

theorem QueueWriteFootprint.noMemoryWrites {n : ℕ} {s t : ArithmeticState}
    (rank : t.nr 19 = s.nr 19) (queue : t.nr 20 = s.nr 20) (next : t.nr 21 = s.nr 21)
    (memory : t.nm = s.nm) : QueueWriteFootprint n s t :=
  ⟨rank, queue, next, fun i _ => congrFun memory i⟩

theorem QueueWriteFootprint.trans {n : ℕ} {s t u : ArithmeticState}
    (first : QueueWriteFootprint n s t) (second : QueueWriteFootprint n t u) :
    QueueWriteFootprint n s u := by
  refine ⟨second.rankBase.trans first.rankBase, second.queueBase.trans first.queueBase,
    second.nextBase.trans first.nextBase, fun address outside => ?_⟩
  have middle : OutsideQueueSlices (t.nr 19) (t.nr 20) (t.nr 21) n address := by
    simpa only [first.rankBase, first.queueBase, first.nextBase] using outside
  exact (second.outside address middle).trans (first.outside address outside)

/-- A candidate may write only its rank, the next bounded queue cell,
and its pointer within the current destination row. -/
theorem tightQueueScanBlock_preserves_other_cells
    {rowOffsets distances address : ℕ} {target v u : Fin G.n}
    {table : DirectLinkTable G} {model : TightSearchState G} {s t : ArithmeticState}
    (frame : TightQueueCandidateFrame rowOffsets distances target v u (table u v) model s)
    (valid : TightSearchInvariant target model) (sound : DirectLinkTableSound table)
    (parentKnown : v ∈ model.queue) (tail : s.nr 16 = model.queue.length)
    (entry : s.pc = 0) (running : s.halted = false)
    (run : BlockRuns tightQueueScanBlock 28 s t)
    (outside : OutsideQueueSlices (s.nr 19) (s.nr 20) (s.nr 21) G.n address) :
    t.nm address = s.nm address := by
  classical
  obtain ⟨after, executes, _, _, append, skip⟩ :=
    tightQueueScanBlock_updates frame valid entry running
  have same : t = after := run.run.symm.trans executes.run
  rw [same]
  by_cases candidate : ∃ step, table u v = some step ∧
      u ∉ model.queue ∧ tightTraversal G target step
  · obtain ⟨step, selected, fresh, tight⟩ := candidate
    obtain ⟨starts, ends, allowed⟩ := sound u v step selected
    have appended := appendTightDiscovery_invariant valid fresh step starts allowed tight (ends.symm ▸ parentKnown)
    have room : s.nr 16 < G.n := by
      have capped : (appendTightDiscovery model u step).queue.length ≤ G.n := by
        simpa using appended.unique.length_le_card
      simpa [tail, appendTightDiscovery] using capped
    rw [(append step selected fresh tight).2,
      Function.update_of_ne (outside.2.2 u.val u.isLt),
      Function.update_of_ne (outside.2.1 (s.nr 16) room),
      Function.update_of_ne (outside.1 u.val u.isLt)]
  · rw [(skip candidate).2]

end VehicleRoutingSurvey.Routing
end RppSource_TightQueueArrays

/-! runtime/TightQueueLoop.lean -/
section RppSource_TightQueueLoop
namespace VehicleRoutingSurvey.Routing

def tightQueueSetupBlock : List ArithmeticInstruction :=
  [.natConst 28 0, .natAdd 17 5 28]

def tightQueueClearRankBlock : List ArithmeticInstruction :=
  [.natAdd 12 19 9, .natStore 12 17]

def tightQueueClearBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 9 5 tightQueueClearRankBlock

def tightQueueSeedBlock : List ArithmeticInstruction :=
  [.natAdd 12 19 7, .natStore 12 28, .natStore 20 7, .natConst 16 1,
    .natAdd 21 3 7, .natLoad 21 21, .natAdd 21 26 21,
    .natAdd 14 21 7, .natStore 14 10]

def tightQueueDequeueBlock : List ArithmeticInstruction :=
  [.natAdd 13 20 27, .natLoad 8 13]

def tightQueueScanRowBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 9 5 tightQueueScanBlock

def tightQueueHandleVertexBlock : List ArithmeticInstruction :=
  appendBlock tightQueueDequeueBlock tightQueueScanRowBlock

def tightQueueTargetBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock tightQueueClearBlock tightQueueSeedBlock)
    (countedLoopFromZero 6 27 5 tightQueueHandleVertexBlock)

/-- Visit each destination in turn, preparing its queue and scanning all
incoming adjacencies of each dequeued vertex. Register 26 holds the
base of the complete table of next-edge rows. -/
def tightQueueAllBlock : List ArithmeticInstruction :=
  appendBlock tightQueueSetupBlock (countedLoopFromZero 6 7 5 tightQueueTargetBlock)

def tightQueueClearSteps (n : ℕ) : ℕ := 1 + (n * (2 + 3) + 1)

def tightQueueScanRowSteps (n : ℕ) : ℕ := 1 + (n * (28 + 3) + 1)

def tightQueueHandleVertexSteps (n : ℕ) : ℕ := 2 + tightQueueScanRowSteps n

def tightQueueTargetSteps (n : ℕ) : ℕ :=
  (tightQueueClearSteps n + 9) + (1 + (n * (tightQueueHandleVertexSteps n + 3) + 1))

def tightQueueAllSteps (n : ℕ) : ℕ :=
  2 + (1 + (n * (tightQueueTargetSteps n + 3) + 1))

theorem tightQueueAllSteps_eq (n : ℕ) :
    tightQueueAllSteps n = 31 * n ^ 3 + 12 * n ^ 2 + 16 * n + 4 := by
  simp [tightQueueAllSteps, tightQueueTargetSteps, tightQueueClearSteps,
    tightQueueHandleVertexSteps, tightQueueScanRowSteps]
  ring

private def setIndex (s : ArithmeticState) (index value : ℕ) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr index value}

private def loopResult (code : List ArithmeticInstruction) (index : ℕ)
    (body : ArithmeticState → ArithmeticState) (s : ArithmeticState) : ArithmeticState :=
  let n := s.nr 5
  let last := (List.range n).foldl (fun m i => body (setIndex m index i)) s
  relocateState 1 {(setIndex last index n) with pc := (countedLoop 6 index 5 code).length}

private theorem loopResult_runs (code : List ArithmeticInstruction) (time : ℕ → ℕ)
    (index : ℕ) (notDimension : index ≠ 5) (notOne : index ≠ 6)
    (body : ArithmeticState → ArithmeticState)
    (executes : ∀ s : ArithmeticState, s.pc = 0 → s.halted = false → s.nr 6 = 1 →
      BlockRuns code (time (s.nr 5)) s (body s))
    (ready : ∀ s, (body s).halted = s.halted)
    (dimension : ∀ s, (body s).nr 5 = s.nr 5)
    (oneFixed : ∀ s, (body s).nr 6 = s.nr 6)
    (indexFixed : ∀ s, (body s).nr index = s.nr index)
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) :
    BlockRuns (countedLoopFromZero 6 index 5 code)
      (1 + (s.nr 5 * (time (s.nr 5) + 3) + 1)) s (loopResult code index body s) := by
  let n := s.nr 5
  let loopState (cut : ℕ) :=
    (List.range cut).foldl (fun m i => body (setIndex m index i)) s
  let inv (cut : ℕ) (m : ArithmeticState) :=
    m = setIndex (loopState cut) index cut ∧ m.halted = false ∧ m.nr 5 = n ∧ m.nr 6 = 1
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr index 0} := by
    exact ⟨rfl, running, by simp [n, Function.update_of_ne notDimension.symm],
      by simp [Function.update_of_ne notOne.symm, one]⟩
  have control (cut : ℕ) (m : ArithmeticState) (valid : inv cut m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr index = cut ∧ m.nr 5 = n := by
    refine ⟨congrArg ArithmeticState.pc valid.1, valid.2.1, ?_, valid.2.2.1⟩
    rw [valid.1]
    simp [setIndex]
  have advance (cut : ℕ) (_ : cut < n) (m : ArithmeticState) (valid : inv cut m) :
      ∃ t, BlockRuns code (time n) m t ∧ t.halted = false ∧
        inv (cut + 1) {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr 6)} := by
    obtain ⟨entryM, readyM, indexM, dimensionM⟩ := control cut m valid
    have oneM := valid.2.2.2
    have block := executes m entryM readyM oneM
    rw [dimensionM] at block
    have afterReady := (ready m).trans readyM
    have afterDimension := (dimension m).trans dimensionM
    have afterOne := (oneFixed m).trans oneM
    have afterIndex := (indexFixed m).trans indexM
    have foldNext : loopState (cut + 1) = body m := by
      simp only [loopState, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact congrArg body valid.1.symm
    refine ⟨body m, block, afterReady, ?_, afterReady, ?_, ?_⟩
    · simp [foldNext, setIndex, afterIndex, afterOne]
    · simpa [Function.update_of_ne notDimension.symm] using afterDimension
    · simpa [Function.update_of_ne notOne.symm] using afterOne
  obtain ⟨last, final, run⟩ :=
    countedLoopFromZero_correct 6 index 5 n (time n) code inv entry running initial control advance
  rw [final.1] at run
  exact run

private theorem loopResult_preserves {α : Sort*} (project : ArithmeticState → α)
    (code : List ArithmeticInstruction) (index : ℕ) (body : ArithmeticState → ArithmeticState)
    (blockKeeps : ∀ s, project (body s) = project s)
    (indexKeeps : ∀ s i, project (setIndex s index i) = project s)
    (exitKeeps : ∀ s k, project {s with pc := k} = project s) (s : ArithmeticState) :
    project (loopResult code index body s) = project s := by
  have foldKeeps (indices : List ℕ) (current : ArithmeticState) :
      project (indices.foldl (fun m i => body (setIndex m index i)) current) = project current := by
    induction indices generalizing current with
    | nil => rfl
    | cons i indices ih =>
      rw [List.foldl_cons, ih, blockKeeps, indexKeeps]
  unfold loopResult relocateState
  rw [exitKeeps, exitKeeps, indexKeeps, foldKeeps]

private structure ExactQueueBlock (code : List ArithmeticInstruction) (time : ℕ → ℕ)
    (result : ArithmeticState → ArithmeticState) (writes : List ℕ) : Prop where
  executes : ∀ s : ArithmeticState, s.pc = 0 → s.halted = false → s.nr 6 = 1 →
    BlockRuns code (time (s.nr 5)) s (result s)
  halt : ∀ s, (result s).halted = s.halted
  real : ∀ s, (result s).rm = s.rm
  registers : ∀ s r, r ∉ writes → (result s).nr r = s.nr r

private def appendResult (code : List ArithmeticInstruction)
    (left right : ArithmeticState → ArithmeticState) (s : ArithmeticState) : ArithmeticState :=
  relocateState code.length (right {left s with pc := 0})

private theorem ExactQueueBlock.append {a b : List ArithmeticInstruction} {timeA timeB : ℕ → ℕ}
    {left right : ArithmeticState → ArithmeticState} {writesA writesB : List ℕ}
    (first : ExactQueueBlock a timeA left writesA) (second : ExactQueueBlock b timeB right writesB)
    (dimensionA : 5 ∉ writesA) (oneA : 6 ∉ writesA) :
    ExactQueueBlock (appendBlock a b) (fun n => timeA n + timeB n)
      (appendResult a left right) (writesA ++ writesB) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s entry running one
    have runLeft := first.executes s entry running one
    have runRight := second.executes {left s with pc := 0} rfl
      ((first.halt s).trans running) ((first.registers s 6 oneA).trans one)
    change BlockRuns b (timeB ((left s).nr 5)) {left s with pc := 0} _ at runRight
    rw [first.registers s 5 dimensionA] at runRight
    exact runLeft.append runRight
  · intro s
    exact (second.halt {left s with pc := 0}).trans (first.halt s)
  · intro s
    exact (second.real {left s with pc := 0}).trans (first.real s)
  · intro s r untouched
    exact (second.registers {left s with pc := 0} r
      (fun mem => untouched (List.mem_append.mpr (.inr mem)))).trans
      (first.registers s r (fun mem => untouched (List.mem_append.mpr (.inl mem))))

private theorem ExactQueueBlock.loop {code : List ArithmeticInstruction} {time : ℕ → ℕ}
    {body : ArithmeticState → ArithmeticState} {writes : List ℕ}
    (block : ExactQueueBlock code time body writes)
    (index : ℕ) (notDimension : index ≠ 5) (notOne : index ≠ 6)
    (dimensionFixed : 5 ∉ writes) (oneFixed : 6 ∉ writes) (indexFixed : index ∉ writes) :
    ExactQueueBlock (countedLoopFromZero 6 index 5 code)
      (fun n => 1 + (n * (time n + 3) + 1)) (loopResult code index body) (index :: writes) := by
  refine ⟨loopResult_runs code time index notDimension notOne body block.executes block.halt
      (fun s => block.registers s 5 dimensionFixed) (fun s => block.registers s 6 oneFixed)
      (fun s => block.registers s index indexFixed), ?_, ?_, ?_⟩
  · exact loopResult_preserves ArithmeticState.halted code index body block.halt
      (fun _ _ => rfl) (fun _ _ => rfl)
  · exact loopResult_preserves ArithmeticState.rm code index body block.real
      (fun _ _ => rfl) (fun _ _ => rfl)
  · intro s r untouched
    have different : r ≠ index := fun equal => untouched (List.mem_cons.mpr (.inl equal))
    exact loopResult_preserves (fun s => s.nr r) code index body
      (fun s => block.registers s r (fun mem => untouched (List.mem_cons.mpr (.inr mem))))
      (fun _ _ => Function.update_of_ne different _ _) (fun _ _ => rfl) s

private def clearRankResult (s : ArithmeticState) : ArithmeticState :=
  let rankAddress := s.nr 19 + s.nr 9
  {s with
    pc := 2
    nr := Function.update s.nr 12 rankAddress
    nm := Function.update s.nm rankAddress (s.nr 17)}

private theorem clearRank_correct :
    ExactQueueBlock tightQueueClearRankBlock (fun _ => 2) clearRankResult [12] := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · intro s entry running _
    refine ⟨?_, ?_, rfl⟩
    · intro i less
      interval_cases i <;>
        simp [tightQueueClearRankBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · simp [tightQueueClearRankBlock, clearRankResult, arithmeticStep, entry, running,
        Function.iterate_succ_apply']
  · intro s r untouched
    exact Function.update_of_ne (by simpa using untouched) _ _

private def setupResult (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 2
    nr := Function.update (Function.update s.nr 28 0) 17 (s.nr 5)}

private theorem setup_correct :
    ExactQueueBlock tightQueueSetupBlock (fun _ => 2) setupResult [28, 17] := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · intro s entry running _
    refine ⟨?_, ?_, rfl⟩
    · intro i less
      interval_cases i <;>
        simp [tightQueueSetupBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · simp [tightQueueSetupBlock, setupResult, arithmeticStep, entry, running,
        Function.iterate_succ_apply']
  · intro s r untouched
    obtain ⟨notZero, notSentinel⟩ : r ≠ 28 ∧ r ≠ 17 := by simpa using untouched
    simp [setupResult, Function.update_of_ne notZero, Function.update_of_ne notSentinel]

theorem tightQueueSetupBlock_correct (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) :
    BlockRuns tightQueueSetupBlock 2 s
      {s with pc := 2, nr := Function.update (Function.update s.nr 28 0) 17 (s.nr 5)} :=
  setup_correct.executes s entry running one

private def seedResult (s : ArithmeticState) : ArithmeticState :=
  let rankAddress := s.nr 19 + s.nr 7
  let seeded := Function.update (Function.update s.nm rankAddress (s.nr 28)) (s.nr 20) (s.nr 7)
  let nextRow := s.nr 26 + seeded (s.nr 3 + s.nr 7)
  let nextAddress := nextRow + s.nr 7
  {s with
    pc := 9
    nr := Function.update
      (Function.update (Function.update (Function.update s.nr 12 rankAddress) 16 1)
        21 nextRow) 14 nextAddress
    nm := Function.update seeded nextAddress (s.nr 10)}

private theorem seed_correct :
    ExactQueueBlock tightQueueSeedBlock (fun _ => 9) seedResult [12, 16, 21, 14] := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · intro s entry running _
    refine ⟨?_, ?_, rfl⟩
    · intro i less
      interval_cases i <;>
        simp [tightQueueSeedBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · simp [tightQueueSeedBlock, seedResult, arithmeticStep, entry, running,
        Function.iterate_succ_apply', Function.update_idem]
  · intro s r untouched
    obtain ⟨notAddress, notTail, notRow, notNext⟩ :
      r ≠ 12 ∧ r ≠ 16 ∧ r ≠ 21 ∧ r ≠ 14 := by simpa using untouched
    simp [seedResult, Function.update_of_ne notAddress, Function.update_of_ne notTail,
      Function.update_of_ne notRow, Function.update_of_ne notNext]

private def dequeueResult (s : ArithmeticState) : ArithmeticState :=
  let queueAddress := s.nr 20 + s.nr 27
  {s with
    pc := 2
    nr := Function.update (Function.update s.nr 13 queueAddress) 8 (s.nm queueAddress)}

private theorem dequeue_correct :
    ExactQueueBlock tightQueueDequeueBlock (fun _ => 2) dequeueResult [13, 8] := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · intro s entry running _
    refine ⟨?_, ?_, rfl⟩
    · intro i less
      interval_cases i <;>
        simp [tightQueueDequeueBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · simp [tightQueueDequeueBlock, dequeueResult, arithmeticStep, entry, running,
        Function.iterate_succ_apply']
  · intro s r untouched
    obtain ⟨notAddress, notVertex⟩ : r ≠ 13 ∧ r ≠ 8 := by simpa using untouched
    simp [dequeueResult, Function.update_of_ne notAddress, Function.update_of_ne notVertex]

/-- Dequeueing the current queue entry reads natural memory at the queue
base plus the head, without changing either memory array. -/
theorem tightQueueDequeueBlock_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 6 = 1) :
    ∃ t, BlockRuns tightQueueDequeueBlock 2 s t ∧ t.halted = false ∧
      t.nr 8 = s.nm (s.nr 20 + s.nr 27) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      (∀ r ∉ ([13, 8] : List ℕ), t.nr r = s.nr r) := by
  exact ⟨dequeueResult s, dequeue_correct.executes s entry running one, running,
    by simp [dequeueResult], rfl, rfl, dequeue_correct.registers s⟩

private noncomputable def scanResult (s : ArithmeticState) : ArithmeticState :=
  relocateState tightQueueReadBlock.length
    (tightQueueCellResult {tightQueueReadResult s with pc := 0})

private theorem scan_correct :
    ExactQueueBlock tightQueueScanBlock (fun _ => 28) scanResult
      [12, 13, 14, 15, 16, 18, 22, 23, 24, 25] := by
  refine ⟨fun s entry running _ => tightQueueScanBlock_correct s entry running, ?_, ?_, ?_⟩
  · intro s
    unfold scanResult tightQueueCellResult relocateState
    split <;> rfl
  · intro s
    unfold scanResult tightQueueCellResult relocateState
    split <;> rfl
  · intro s r untouched
    have different (k : ℕ) (changed : k ∈ [12, 13, 14, 15, 16, 18, 22, 23, 24, 25]) :
        r ≠ k := fun eq => untouched (eq.symm ▸ changed)
    unfold scanResult tightQueueCellResult relocateState
    split <;>
      simp [tightQueueReadResult, Function.update_of_ne (different 12 (by decide)),
        Function.update_of_ne (different 13 (by decide)),
        Function.update_of_ne (different 14 (by decide)),
        Function.update_of_ne (different 15 (by decide)),
        Function.update_of_ne (different 16 (by decide)),
        Function.update_of_ne (different 18 (by decide)),
        Function.update_of_ne (different 22 (by decide)),
        Function.update_of_ne (different 23 (by decide)),
        Function.update_of_ne (different 24 (by decide)),
        Function.update_of_ne (different 25 (by decide))]

/-- Any execution of the exact scan leaves all registers outside its
listed working registers, including all loop controls, unchanged. -/
theorem tightQueueScanBlock_fixed {s t : ArithmeticState}
    (run : BlockRuns tightQueueScanBlock 28 s t) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 6 = 1)
    (r : ℕ) (untouched : r ∉ [12, 13, 14, 15, 16, 18, 22, 23, 24, 25]) :
    t.nr r = s.nr r := by
  rw [← run.run, (scan_correct.executes s entry running one).run]
  exact scan_correct.registers s r untouched

private def clearResult : ArithmeticState → ArithmeticState :=
  loopResult tightQueueClearRankBlock 9 clearRankResult

private theorem clearRankFold (indices : List ℕ) (s : ArithmeticState) :
    ((indices.foldl (fun m i => clearRankResult (setIndex m 9 i)) s).nm) =
      indices.foldl (fun m i => Function.update m (s.nr 19 + i) (s.nr 17)) s.nm := by
  induction indices generalizing s with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    simp [clearRankResult, setIndex]

private theorem clearInterval_read (rankBase sentinel n : ℕ) (memory : ℕ → ℕ) (address : ℕ) :
    (List.range n).foldl (fun m i => Function.update m (rankBase + i) sentinel) memory address =
      if rankBase ≤ address ∧ address < rankBase + n then sentinel else memory address := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases same : address = rankBase + n
    · subst address
      rw [Function.update_self, if_pos (by omega)]
    · rw [Function.update_of_ne same, ih]
      have interval : (rankBase ≤ address ∧ address < rankBase + (n + 1)) ↔
          rankBase ≤ address ∧ address < rankBase + n := by omega
      simp [interval]

/-- The rank clear touches the contiguous rank table and leaves every
other natural cell and all real memory unchanged. -/
theorem tightQueueClearBlock_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 6 = 1) :
    ∃ t, BlockRuns tightQueueClearBlock (tightQueueClearSteps (s.nr 5)) s t ∧
      t.halted = false ∧ t.rm = s.rm ∧
      (∀ r ∉ ([9, 12] : List ℕ), t.nr r = s.nr r) ∧
      ∀ a, t.nm a =
        if s.nr 19 ≤ a ∧ a < s.nr 19 + s.nr 5 then s.nr 17 else s.nm a := by
  have summary := clearRank_correct.loop 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨clearResult s, summary.executes s entry running one, (summary.halt s).trans running,
    summary.real s, summary.registers s, fun a => ?_⟩
  unfold clearResult loopResult
  change ((List.range (s.nr 5)).foldl (fun m i => clearRankResult (setIndex m 9 i)) s).nm a = _
  rw [clearRankFold]
  exact clearInterval_read (s.nr 19) (s.nr 17) (s.nr 5) s.nm a

/-- Seeding sets the target's rank and first queue entry and records the
empty next edge for the target itself. The next row is located via the
same natural row-offset table already used by Floyd. -/
theorem tightQueueSeedBlock_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 6 = 1) :
    let initialized := Function.update
      (Function.update s.nm (s.nr 19 + s.nr 7) (s.nr 28)) (s.nr 20) (s.nr 7)
    let nextRow := s.nr 26 + initialized (s.nr 3 + s.nr 7)
    ∃ t, BlockRuns tightQueueSeedBlock 9 s t ∧ t.halted = false ∧ t.rm = s.rm ∧
      (∀ r ∉ ([12, 16, 21, 14] : List ℕ), t.nr r = s.nr r) ∧
      t.nr 16 = 1 ∧ t.nr 21 = nextRow ∧
      t.nm = Function.update initialized (nextRow + s.nr 7) (s.nr 10) := by
  exact ⟨seedResult s, seed_correct.executes s entry running one, running, rfl,
    seed_correct.registers s, by simp [seedResult], by simp [seedResult], rfl⟩

private noncomputable def scanRowResult : ArithmeticState → ArithmeticState :=
  loopResult tightQueueScanBlock 9 scanResult

/-- The n-column loop keeps registers outside its counter and scan
scratch space, including the enclosing queue head and destination. -/
theorem tightQueueScanRowBlock_fixed {s t : ArithmeticState} {n : ℕ}
    (run : BlockRuns tightQueueScanRowBlock (tightQueueScanRowSteps n) s t)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (dimension : s.nr 5 = n) (r : ℕ)
    (untouched : r ∉ [9, 12, 13, 14, 15, 16, 18, 22, 23, 24, 25]) :
    t.nr r = s.nr r := by
  have summary := scan_correct.loop 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have exactRun := summary.executes s entry running one
  rw [dimension] at exactRun
  have same : t = loopResult tightQueueScanBlock 9 scanResult s :=
    run.run.symm.trans exactRun.run
  rw [same]
  exact summary.registers s r untouched

private noncomputable def handleVertexResult : ArithmeticState → ArithmeticState :=
  appendResult tightQueueDequeueBlock dequeueResult scanRowResult

theorem tightQueueFromSeed_fixedNextRow {s t : ArithmeticState} {n : ℕ}
    (run : BlockRuns (countedLoopFromZero 6 27 5 tightQueueHandleVertexBlock)
      (1 + (n * (tightQueueHandleVertexSteps n + 3) + 1)) s t)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (dimension : s.nr 5 = n) : t.nr 21 = s.nr 21 := by
  have scanRow := scan_correct.loop 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have vertex := dequeue_correct.append scanRow (by decide) (by decide)
  have summary := vertex.loop 27 (by decide) (by decide) (by decide) (by decide) (by decide)
  have exactRun := summary.executes s entry running one
  rw [dimension] at exactRun
  have same : t = loopResult tightQueueHandleVertexBlock 27 handleVertexResult s :=
    run.run.symm.trans exactRun.run
  rw [same]
  exact summary.registers s 21 (by decide)

private noncomputable def targetResult : ArithmeticState → ArithmeticState :=
  appendResult (appendBlock tightQueueClearBlock tightQueueSeedBlock)
    (appendResult tightQueueClearBlock clearResult seedResult)
    (loopResult tightQueueHandleVertexBlock 27 handleVertexResult)

private def targetWrites : List ℕ :=
  ([9, 12] ++ [12, 16, 21, 14]) ++ 27 :: ([13, 8] ++ [9, 12, 13, 14, 15, 16, 18, 22, 23, 24, 25])

private theorem target_correct :
    ExactQueueBlock tightQueueTargetBlock tightQueueTargetSteps targetResult targetWrites := by
  have clear := clearRank_correct.loop 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have scanRow := scan_correct.loop 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have vertex := dequeue_correct.append scanRow (by decide) (by decide)
  have dequeues := vertex.loop 27 (by decide) (by decide) (by decide) (by decide) (by decide)
  have setup := clear.append seed_correct (by decide) (by decide)
  exact setup.append dequeues (by decide) (by decide)

def tightQueueGlobalRegisters : List ℕ := [3, 4, 5, 6, 7, 10, 11, 17, 19, 20, 26, 28]

/-- The target code leaves the shared operand registers and the real
memory untouched, so it may be called for the next row. -/
theorem tightQueueTargetBlock_preserves {s t : ArithmeticState} {n : ℕ}
    (run : BlockRuns tightQueueTargetBlock (tightQueueTargetSteps n) s t)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (dimension : s.nr 5 = n) :
    t.rm = s.rm ∧ ∀ r ∈ tightQueueGlobalRegisters, t.nr r = s.nr r := by
  have executes := target_correct.executes s entry running one
  rw [dimension] at executes
  have same : t = targetResult s := run.run.symm.trans executes.run
  rw [same]
  refine ⟨target_correct.real s, fun r member => target_correct.registers s r ?_⟩
  intro touch
  simp [targetWrites] at touch
  simp [tightQueueGlobalRegisters] at member
  omega

/-- The exact state transition of the nested search, expressed as folds
over the prescribed range of destination, queue, and row indices. -/
noncomputable def tightQueueAllResult : ArithmeticState → ArithmeticState :=
  appendResult tightQueueSetupBlock setupResult (loopResult tightQueueTargetBlock 7 targetResult)

private theorem tightQueueAll_correct :
    ExactQueueBlock tightQueueAllBlock tightQueueAllSteps tightQueueAllResult
      ([28, 17] ++ 7 :: (([9, 12] ++ [12, 16, 21, 14]) ++
        27 :: ([13, 8] ++ [9, 12, 13, 14, 15, 16, 18, 22, 23, 24, 25]))) := by
  have targets := target_correct.loop 7 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact setup_correct.append targets (by decide) (by decide)

/-- The queue program has exact cubic execution time and preserves the
real-memory matrices. Its graph invariants govern the interpretation of
the resulting next-edge entries. -/
theorem tightQueueAllBlock_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 6 = 1) :
    BlockRuns tightQueueAllBlock
        (31 * (s.nr 5) ^ 3 + 12 * (s.nr 5) ^ 2 + 16 * (s.nr 5) + 4) s
        (tightQueueAllResult s) ∧
      (tightQueueAllResult s).halted = false ∧ (tightQueueAllResult s).rm = s.rm := by
  exact ⟨tightQueueAllSteps_eq _ ▸ tightQueueAll_correct.executes s entry running one,
    (tightQueueAll_correct.halt s).trans running, tightQueueAll_correct.real s⟩

/-- The complete pointer program keeps the existing Floyd frame
registers available to path decoding and later blocks. -/
theorem tightQueueAllBlock_fixedFloydRegisters {s t : ArithmeticState} {n : ℕ}
    (run : BlockRuns tightQueueAllBlock (31 * n ^ 3 + 12 * n ^ 2 + 16 * n + 4) s t)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (dimension : s.nr 5 = n) : FixedFloydRegisters 7 s t := by
  have exactRun := tightQueueAll_correct.executes s entry running one
  rw [dimension, tightQueueAllSteps_eq] at exactRun
  have same : t = tightQueueAllResult s := run.run.symm.trans exactRun.run
  rw [same]
  intro r lower upper
  apply tightQueueAll_correct.registers
  intro changes
  simp at changes
  omega

end VehicleRoutingSurvey.Routing
end RppSource_TightQueueLoop


