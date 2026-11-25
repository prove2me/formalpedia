-- Prove2me | Definitions.Def_DetDLP_M89_BitCompiler
-- name    : DetDLP_M89_BitCompiler
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T17:09:50.403639+00:00
-- url     : https://prove2.me/theorems/e26e5f7a-d6c9-4570-b75a-481c62400aa8
-- title:
--   Finite bit-program compiler and structured calls
-- statement:
--   Finite bit-program compiler and structured calls. This module supports bounded execution of finite Boolean-stack programs on the primitive multitape machine.
-- source:
--   OpenAI math, lean/OAI/Algorithms/SubexponentialSAT; local verified port, as credited in the module header.

import Definitions.Def_DetDLP_M89_StackEncoding

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000


namespace OAI.Algorithms

/-!
A global finite controller for one-head finite stack programs. A source step
first inspects one finite-alphabet stack top, then changes finite control and
keeps, pops, or pushes that stack. The compiled controller performs only the
primitive bit reads, moves, and writes of StackMachine.controlStep.
-/

namespace SubexponentialSAT.StackCompiler

open Turing SubexponentialSAT.Computation SubexponentialSAT.StackMachine SubexponentialSAT.StackEncoding

inductive Mutation (α : Type) where
  | keep
  | pop
  | push (value : α)
  deriving Fintype

def Mutation.apply {α : Type} : Mutation α → List α → List α
  | .keep, s => s
  | .pop, s => s.tail
  | .push a, s => a :: s

def mutationActions {α : Type} (code : BlockCode α) : Mutation α → List Action
  | .keep => []
  | .pop => popBits code.width
  | .push a => pushBits (code.block a)

theorem mutationActions_length {α : Type} (code : BlockCode α) (op : Mutation α) :
    (mutationActions code op).length ≤ 2 * code.width := by
  cases op <;> simp [mutationActions, code.length_block]

theorem mutationActions_correct {α : Type} (code : BlockCode α)
    (op : Mutation α) (stack : List α) :
    execute (mutationActions code op) (dataTape (encodeDataStack code stack)) =
      dataTape (encodeDataStack code (op.apply stack)) := by
  cases op with
  | keep => rfl
  | pop =>
      simpa [mutationActions, Mutation.apply, drop_width_eq_tail] using
        execute_popBits_drop code.width (encodeDataStack code stack)
  | push a =>
      simpa [mutationActions, Mutation.apply, encodeDataStack_cons] using
        execute_pushBits (code.block a) (encodeDataStack code stack)

structure StackProgram (Q : Type) {t : ℕ} (Γ : Fin t → Type) where
  inputTape : Fin t
  start : Q
  select : Q → Fin t
  transition : (q : Q) → Option (Γ (select q)) →
    Bool ⊕ (Q × Mutation (Γ (select q)))

structure StackCfg (Q : Type) {t : ℕ} (Γ : Fin t → Type) where
  state : Bool ⊕ Q
  stk : ∀ k, List (Γ k)

def stackStep {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (c : StackCfg Q Γ) : Option (StackCfg Q Γ) :=
  match c.state with
  | .inl _ => none
  | .inr q =>
    match p.transition q (c.stk (p.select q)).head? with
    | .inl answer => some ⟨.inl answer, c.stk⟩
    | .inr (q', op) => some ⟨.inr q',
        Function.update c.stk (p.select q) (op.apply (c.stk (p.select q)))⟩

/-- The source input stack uses its given Boolean interface; all other stacks are empty. -/
def initialCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (inputAlphabet : Γ p.inputTape ≃ Bool)
    (input : List Bool) : StackCfg Q Γ :=
  ⟨.inr p.start, Function.update (fun _ => []) p.inputTape
    (input.map inputAlphabet.symm)⟩

abbrev CodeFamily {t : ℕ} (Γ : Fin t → Type) := ∀ k, BlockCode (Γ k)

abbrev State {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ) :=
  Q ⊕ (((q : Q) × ReaderState (codes (p.select q)).width) ⊕
    ((k : Fin t) × (Q × Mutation (Γ k) × Fin (2 * (codes k).width + 1))))

def ready {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    {p : StackProgram Q Γ} {codes : CodeFamily Γ} (q : Q) : State p codes := .inl q

def reading {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    {p : StackProgram Q Γ} {codes : CodeFamily Γ}
    (q : Q) (r : ReaderState (codes (p.select q)).width) : State p codes :=
  .inr (.inl ⟨q, r⟩)

def acting {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    {p : StackProgram Q Γ} {codes : CodeFamily Γ}
    (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (i : Fin (2 * (codes k).width + 1)) : State p codes :=
  .inr (.inr ⟨k, q, op, i⟩)

def controller {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ)
    (decode : ∀ k, List Bool → Option (Γ k)) : Controller (State p codes) t where
  inputTape := p.inputTape
  start := ready p.start
  scan
    | .inl q => p.select q
    | .inr (.inl ⟨q, _⟩) => p.select q
    | .inr (.inr ⟨k, _⟩) => k
  transition
    | .inl q, bit => .inr (reading q (0, fun _ => none), .write bit)
    | .inr (.inl ⟨q, r⟩), bit =>
      let width := (codes (p.select q)).width
      if h : r.1.val < width then
        .inr (reading q (⟨r.1.val + 1, by omega⟩,
          Function.update r.2 ⟨r.1.val, h⟩ bit), .move .right)
      else if h' : r.1.val < 2 * width then
        .inr (reading q (⟨r.1.val + 1, by omega⟩, r.2), .move .left)
      else
        match p.transition q (decode (p.select q) (registerBits r.2)) with
        | .inl answer => .inl answer
        | .inr (q', op) => .inr (acting (p.select q) q' op 0, .write bit)
    | .inr (.inr ⟨k, q, op, i⟩), bit =>
      let actions := mutationActions (codes k) op
      if h : i.val < actions.length then
        .inr (acting k q op ⟨i.val + 1,
          Nat.lt_succ_of_le (Nat.le_trans (Nat.succ_le_of_lt h)
            (mutationActions_length (codes k) op))⟩, actions[i.val])
      else .inr (ready q, .write bit)

def tapeEncoding {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (codes : CodeFamily Γ) (c : StackCfg Q Γ) : Fin t → BitTape :=
  fun k => dataTape (encodeDataStack (codes k) (c.stk k))

def encodeCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ) (c : StackCfg Q Γ) :
    ControlCfg (State p codes) t :=
  ⟨c.state.map id ready, tapeEncoding codes c⟩

def readCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ)
    (q : Q) (base : Fin t → BitTape)
    (r : ReaderState (codes (p.select q)).width) (tape : BitTape) :
    ControlCfg (State p codes) t :=
  ⟨.inr (reading q r), Function.update base (p.select q) tape⟩

def actionCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ)
    (k : Fin t) (q : Q) (op : Mutation (Γ k)) (base : Fin t → BitTape)
    (i : Fin ((mutationActions (codes k) op).length + 1)) (tape : BitTape) :
    ControlCfg (State p codes) t :=
  ⟨.inr (acting k q op ⟨i.val,
      lt_of_lt_of_le i.isLt (Nat.succ_le_succ (mutationActions_length (codes k) op))⟩),
    Function.update base k tape⟩

section Fragments

variable {Q : Type} {t : ℕ} {Γ : Fin t → Type}
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))

theorem reader_scan_table (q : Q) (base : Fin t → BitTape)
    (i : ℕ) (hi : i < (codes (p.select q)).width)
    (r : Registers (codes (p.select q)).width) (tape : BitTape) :
    controlStep (controller p codes decode)
      (readCfg p codes q base (⟨i, by omega⟩, r) tape) =
    some (readCfg p codes q base
      (⟨i + 1, by omega⟩, Function.update r ⟨i, hi⟩ tape.head) (tape.move .right)) := by
  simp [controlStep, controller, readCfg, reading, hi, applyAction,
    Function.update_idem]

theorem reader_back_table (q : Q) (base : Fin t → BitTape)
    (i : ℕ) (hlo : (codes (p.select q)).width ≤ i)
    (hi : i < 2 * (codes (p.select q)).width)
    (r : Registers (codes (p.select q)).width) (tape : BitTape) :
    controlStep (controller p codes decode)
      (readCfg p codes q base (⟨i, by omega⟩, r) tape) =
    some (readCfg p codes q base (⟨i + 1, by omega⟩, r) (tape.move .left)) := by
  have hn : ¬ i < (codes (p.select q)).width := by omega
  simp [controlStep, controller, readCfg, reading, hn, hi, applyAction,
    Function.update_idem]

theorem read_trace (q : Q) (base : Fin t → BitTape)
    (r : Registers (codes (p.select q)).width) (tape : BitTape) :
    Trace (controlStep (controller p codes decode)) (2 * (codes (p.select q)).width)
      (readCfg p codes q base (0, r) tape)
      (readCfg p codes q base (⟨2 * (codes (p.select q)).width, by omega⟩,
        fun i => tape.nth i.val) tape) :=
  reader_fragment_trace _ _ (readCfg p codes q base)
    (reader_scan_table p codes decode q base)
    (reader_back_table p codes decode q base) r tape

theorem action_table (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (base : Fin t → BitTape) (i : ℕ)
    (hi : i < (mutationActions (codes k) op).length) (tape : BitTape) :
    controlStep (controller p codes decode)
      (actionCfg p codes k q op base ⟨i, by omega⟩ tape) =
    some (actionCfg p codes k q op base ⟨i + 1, by omega⟩
      (applyAction (mutationActions (codes k) op)[i] tape)) := by
  simp [controlStep, controller, actionCfg, acting, hi, Function.update_idem]

theorem action_trace (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (base : Fin t → BitTape) (tape : BitTape) :
    Trace (controlStep (controller p codes decode)) (mutationActions (codes k) op).length
      (actionCfg p codes k q op base 0 tape)
      (actionCfg p codes k q op base
        ⟨(mutationActions (codes k) op).length, by omega⟩
        (execute (mutationActions (codes k) op) tape)) :=
  program_fragment_trace _ _ (actionCfg p codes k q op base)
    (action_table p codes decode k q op base) tape

end Fragments

section Assembly

variable {Q : Type} {t : ℕ} {Γ : Fin t → Type}
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))

theorem dispatch_step (q : Q) (base : Fin t → BitTape) :
    controlStep (controller p codes decode) ⟨.inr (ready q), base⟩ =
      some (readCfg p codes q base (0, fun _ => none) (base (p.select q))) := by
  simp [controlStep, controller, ready, readCfg, reading, applyAction, Tape.write_self]

theorem reader_halt_step (q : Q) (base : Fin t → BitTape)
    (r : Registers (codes (p.select q)).width) (answer : Bool)
    (h : p.transition q (decode (p.select q) (registerBits r)) = .inl answer) :
    controlStep (controller p codes decode)
      (readCfg p codes q base (⟨2 * (codes (p.select q)).width, by omega⟩, r)
        (base (p.select q))) =
      some ⟨.inl answer, base⟩ := by
  have hn : ¬ 2 * (codes (p.select q)).width < (codes (p.select q)).width := by omega
  simp [controlStep, controller, readCfg, reading, hn, h]

theorem reader_action_step (q q' : Q) (base : Fin t → BitTape)
    (r : Registers (codes (p.select q)).width)
    (op : Mutation (Γ (p.select q)))
    (h : p.transition q (decode (p.select q) (registerBits r)) = .inr (q', op)) :
    controlStep (controller p codes decode)
      (readCfg p codes q base (⟨2 * (codes (p.select q)).width, by omega⟩, r)
        (base (p.select q))) =
      some (actionCfg p codes (p.select q) q' op base 0 (base (p.select q))) := by
  have hn : ¬ 2 * (codes (p.select q)).width < (codes (p.select q)).width := by omega
  simp [controlStep, controller, readCfg, reading, actionCfg, acting, hn, h,
    applyAction, Tape.write_self]

theorem action_return_step (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (base : Fin t → BitTape) (tape : BitTape) :
    controlStep (controller p codes decode)
      (actionCfg p codes k q op base
        ⟨(mutationActions (codes k) op).length, by omega⟩ tape) =
      some ⟨.inr (ready q), Function.update base k tape⟩ := by
  simp [controlStep, controller, actionCfg, acting, ready, applyAction, Tape.write_self]

theorem tapeEncoding_update (q : Q) (S : ∀ k, List (Γ k))
    (k : Fin t) (s : List (Γ k)) :
    tapeEncoding codes (⟨.inr q, Function.update S k s⟩ : StackCfg Q Γ) =
      Function.update (fun j => dataTape (encodeDataStack (codes j) (S j))) k
        (dataTape (encodeDataStack (codes k) s)) := by
  funext j
  by_cases h : j = k
  · subst j
    simp [tapeEncoding]
  · simp [tapeEncoding, Function.update_of_ne h]

theorem action_execution (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (S : ∀ k, List (Γ k)) :
    Trace (controlStep (controller p codes decode))
      ((mutationActions (codes k) op).length + 1)
      (actionCfg p codes k q op
        (fun j => dataTape (encodeDataStack (codes j) (S j))) 0
        (dataTape (encodeDataStack (codes k) (S k))))
      (encodeCfg p codes ⟨.inr q, Function.update S k (op.apply (S k))⟩) := by
  let base := fun j => dataTape (encodeDataStack (codes j) (S j))
  have hrun := action_trace p codes decode k q op base (base k)
  change Trace _ _ _ (actionCfg p codes k q op base _ _) at hrun
  have hcorrect :
      execute (mutationActions (codes k) op) (base k) =
        dataTape (encodeDataStack (codes k) (op.apply (S k))) :=
    mutationActions_correct (codes k) op (S k)
  rw [hcorrect] at hrun
  have hlast := action_return_step p codes decode k q op base
    (dataTape (encodeDataStack (codes k) (op.apply (S k))))
  have hall := hrun.trans (Trace.cons hlast (Trace.refl _))
  simpa only [encodeCfg, Sum.map_inr, tapeEncoding_update, base, ready] using hall

theorem read_entry_trace (q : Q) (base : Fin t → BitTape) :
    Trace (controlStep (controller p codes decode))
      (1 + 2 * (codes (p.select q)).width)
      ⟨.inr (ready q), base⟩
      (readCfg p codes q base (⟨2 * (codes (p.select q)).width, by omega⟩,
        fun i => (base (p.select q)).nth i.val) (base (p.select q))) :=
  (Trace.cons (dispatch_step p codes decode q base) (Trace.refl _)).trans
    (read_trace p codes decode q base (fun _ => none) (base (p.select q)))

end Assembly

/-- This bound is fixed by the finite stack alphabet codes. -/
def compilerOverhead {t : ℕ} {Γ : Fin t → Type} (codes : CodeFamily Γ) : ℕ :=
  (Finset.univ : Finset (Fin t)).sup (fun k => 4 * (codes k).width + 3)

theorem localCost_le_overhead {t : ℕ} {Γ : Fin t → Type}
    (codes : CodeFamily Γ) (k : Fin t) :
    4 * (codes k).width + 3 ≤ compilerOverhead codes :=
  Finset.le_sup (f := fun k => 4 * (codes k).width + 3) (Finset.mem_univ k)

theorem compilerOverhead_pos {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ) : 0 < compilerOverhead codes :=
  lt_of_lt_of_le (by omega) (localCost_le_overhead codes p.inputTape)

section Simulation

variable {Q : Type} {t : ℕ} {Γ : Fin t → Type}
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))
  (decode_nil : ∀ k, decode k [] = none)
  (decode_block : ∀ k a, decode k ((codes k).block a) = some a)

include decode_nil decode_block

/-- One source stack transition is implemented by actual primitive transitions. -/
theorem one_step_execution {a b : StackCfg Q Γ}
    (hstep : stackStep p a = some b) :
    RunsIn (controlStep (controller p codes decode)) (compilerOverhead codes)
      (encodeCfg p codes a) (encodeCfg p codes b) := by
  rcases a with ⟨state, S⟩
  cases state with
  | inl answer => simp [stackStep] at hstep
  | inr q =>
      let base : Fin t → BitTape := fun k => dataTape (encodeDataStack (codes k) (S k))
      let regs : Registers (codes (p.select q)).width :=
        fun i => (base (p.select q)).nth i.val
      have hdecode : decode (p.select q) (registerBits regs) = (S (p.select q)).head? :=
        decode_registers (codes (p.select q)) (decode (p.select q))
          (decode_nil (p.select q)) (decode_block (p.select q)) (S (p.select q))
      have hread := read_entry_trace p codes decode q base
      cases hd : p.transition q (S (p.select q)).head? with
      | inl answer =>
          simp only [stackStep, hd, Option.some.injEq] at hstep
          subst b
          have hlast := reader_halt_step p codes decode q base regs answer
            (by rw [hdecode]; exact hd)
          have hall := hread.trans (Trace.cons hlast (Trace.refl _))
          refine ⟨1 + 2 * (codes (p.select q)).width + 1, ?_, ?_⟩
          · exact le_trans (by omega) (localCost_le_overhead codes (p.select q))
          · change Trace (controlStep (controller p codes decode))
              (1 + 2 * (codes (p.select q)).width + 1)
              ⟨.inr (ready q), base⟩ ⟨.inl answer, base⟩
            simpa only [Nat.zero_add] using hall
      | inr next =>
          rcases next with ⟨q', op⟩
          simp only [stackStep, hd, Option.some.injEq] at hstep
          subst b
          have hdispatch := reader_action_step p codes decode q q' base regs op
            (by rw [hdecode]; exact hd)
          have hwork := action_execution p codes decode (p.select q) q' op S
          have hall := hread.trans ((Trace.cons hdispatch (Trace.refl _)).trans hwork)
          refine ⟨(1 + 2 * (codes (p.select q)).width) +
            (1 + ((mutationActions (codes (p.select q)) op).length + 1)), ?_, ?_⟩
          · have hlen := mutationActions_length (codes (p.select q)) op
            exact le_trans (by omega) (localCost_le_overhead codes (p.select q))
          · change Trace (controlStep (controller p codes decode))
              ((1 + 2 * (codes (p.select q)).width) +
                (1 + ((mutationActions (codes (p.select q)) op).length + 1)))
              ⟨.inr (ready q), base⟩
              (encodeCfg p codes
                ⟨.inr q', Function.update S (p.select q) (op.apply (S (p.select q)))⟩)
            simpa only [Nat.zero_add, encodeCfg, Sum.map_inr] using hall

/-- The simulation theorem does not assume a cost annotation for stack operations. -/
theorem controller_simulation :
    BoundedSimulation (stackStep p) (controlStep (controller p codes decode))
      (fun a b => b = encodeCfg p codes a) (compilerOverhead codes) := by
  intro a a' b hb hstep
  subst b
  exact ⟨encodeCfg p codes a', rfl,
    one_step_execution p codes decode decode_nil decode_block hstep⟩

end Simulation

section FiniteController

variable {Q : Type} [Fintype Q] {t : ℕ} {Γ : Fin t → Type}
  [∀ k, Fintype (Γ k)]
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))

instance stateFintype : Fintype (State p codes) := inferInstance

/-- The assembled finite control is a genuine primitive bit machine. -/
noncomputable def compiledMachine : PrimitiveMachine :=
  reindex (Fintype.equivFin (State p codes)) (controller p codes decode)

noncomputable def compiledCfg (a : StackCfg Q Γ) : (compiledMachine p codes decode).Cfg :=
  reindexCfg (Fintype.equivFin (State p codes)) (controller p codes decode)
    (encodeCfg p codes a)

/-- Reindexing the finite controller changes no primitive transition counts. -/
theorem primitive_one_step
    (decode_nil : ∀ k, decode k [] = none)
    (decode_block : ∀ k a, decode k ((codes k).block a) = some a)
    {a b : StackCfg Q Γ} (hstep : stackStep p a = some b) :
    RunsIn (compiledMachine p codes decode).step (compilerOverhead codes)
      (compiledCfg p codes decode a) (compiledCfg p codes decode b) := by
  obtain ⟨steps, hsteps, htrace⟩ :=
    one_step_execution p codes decode decode_nil decode_block hstep
  exact ⟨steps, hsteps, reindex_trace _ _ htrace⟩

theorem primitive_simulation
    (decode_nil : ∀ k, decode k [] = none)
    (decode_block : ∀ k a, decode k ((codes k).block a) = some a) :
    BoundedSimulation (stackStep p) (compiledMachine p codes decode).step
      (fun a b => b = compiledCfg p codes decode a) (compilerOverhead codes) := by
  intro a a' b hb hstep
  subst b
  exact ⟨compiledCfg p codes decode a', rfl,
    primitive_one_step p codes decode decode_nil decode_block hstep⟩

/-- Width-one input coding identifies the simulated input with the physical raw input. -/
theorem compiled_initial (inputAlphabet : Γ p.inputTape ≃ Bool)
    (code_input : codes p.inputTape = codeOfBoolEquiv inputAlphabet)
    (input : List Bool) :
    compiledCfg p codes decode (initialCfg p inputAlphabet input) =
      (compiledMachine p codes decode).init input := by
  have htapes :
      tapeEncoding codes (initialCfg p inputAlphabet input) =
        fun k => if k = p.inputTape then Tape.mk₁ (input.map some) else Tape.mk₁ [] := by
    funext k
    by_cases hk : k = p.inputTape
    · subst k
      simp only [tapeEncoding, initialCfg, Function.update_self, code_input, ↓reduceIte]
      exact dataTape_input inputAlphabet input
    · simp [tapeEncoding, initialCfg, hk, dataTape]
  unfold compiledCfg reindexCfg encodeCfg
  rw [htapes]
  rfl

theorem compiled_terminal (a : StackCfg Q Γ) (answer : Bool)
    (ha : a.state = .inl answer) :
    (compiledCfg p codes decode a).state = .inl answer := by
  unfold compiledCfg reindexCfg encodeCfg
  rw [ha]
  rfl


end FiniteController

end SubexponentialSAT.StackCompiler

end OAI.Algorithms


namespace OAI.Algorithms

/-! A first-order finite program language. Unbounded data lives only in Boolean
stacks; every register is one bit and all control labels are fixed finite data. -/

namespace SubexponentialSAT.BitProgram

inductive Instr (r s l : ℕ) where
  | halt
  | goto (next : Fin l)
  | set (dst : Fin r) (value : Bool) (next : Fin l)
  | copy (dst src : Fin r) (next : Fin l)
  | bnot (dst src : Fin r) (next : Fin l)
  | band (dst left right : Fin r) (next : Fin l)
  | bor (dst left right : Fin r) (next : Fin l)
  | bxor (dst left right : Fin r) (next : Fin l)
  | branch (test : Fin r) (yes no : Fin l)
  | push (stack : Fin s) (src : Fin r) (next : Fin l)
  | peek (stack : Fin s) (value present : Fin r) (next : Fin l)
  | pop (stack : Fin s) (value present : Fin r) (next : Fin l)
  deriving DecidableEq, Fintype

structure Program (r s l : ℕ) where
  inputStack : Fin s
  outputStack : Fin s
  entry : Fin l
  code : Fin l → Instr r s l

structure Cfg (r s l : ℕ) where
  pc : Option (Fin l)
  regs : Fin r → Bool
  «stacks» : Fin s → List Bool

def readRegs {r : ℕ} (regs : Fin r → Bool) (value present : Fin r)
    (top : Option Bool) : Fin r → Bool :=
  Function.update (Function.update regs value (top.getD false)) present top.isSome

/-- One source instruction performs at most one stack operation. -/
def execInstr {r s l : ℕ} (instr : Instr r s l) (c : Cfg r s l) : Cfg r s l :=
  match instr with
  | .halt => { c with pc := none }
  | .goto next => { c with pc := some next }
  | .set dst value next =>
      { c with pc := some next, regs := Function.update c.regs dst value }
  | .copy dst src next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs src) }
  | .bnot dst src next =>
      { c with pc := some next, regs := Function.update c.regs dst (!(c.regs src)) }
  | .band dst a b next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs a && c.regs b) }
  | .bor dst a b next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs a || c.regs b) }
  | .bxor dst a b next =>
      { c with pc := some next, regs := Function.update c.regs dst (c.regs a ^^ c.regs b) }
  | .branch test yes no => { c with pc := some (if c.regs test then yes else no) }
  | .push stack src next =>
      { c with pc := some next, «stacks» := Function.update c.stacks stack (c.regs src :: c.stacks stack) }
  | .peek stack value present next =>
      { c with pc := some next, regs := readRegs c.regs value present (c.stacks stack).head? }
  | .pop stack value present next =>
      { pc := some next, regs := readRegs c.regs value present (c.stacks stack).head?, «stacks» := Function.update c.stacks stack (c.stacks stack).tail }

abbrev step {r s l : ℕ} (p : Program r s l) (c : Cfg r s l) : Option (Cfg r s l) :=
  c.pc.map fun label => execInstr (p.code label) c

abbrev initial {r s l : ℕ} (p : Program r s l) (input : List Bool) : Cfg r s l :=
  ⟨some p.entry, fun _ => false, fun stack => if stack = p.inputStack then input else []⟩

/-- A canonical output boundary, for the strong TM2 input/output convention. -/
abbrev terminal {r s l : ℕ} (p : Program r s l) (output : List Bool) : Cfg r s l :=
  ⟨none, fun _ => false, fun stack => if stack = p.outputStack then output else []⟩

abbrev Trace {r s l : ℕ} (p : Program r s l) := SubexponentialSAT.Computation.Trace (step p)
abbrev RunsIn {r s l : ℕ} (p : Program r s l) := SubexponentialSAT.Computation.RunsIn (step p)

@[simp] theorem step_none {r s l : ℕ} (p : Program r s l) (c : Cfg r s l)
    (h : c.pc = none) : step p c = none := by simp [step, h]

theorem step_code {r s l : ℕ} (p : Program r s l) (c : Cfg r s l)
    (label : Fin l) (instr : Instr r s l) (hp : c.pc = some label)
    (hc : p.code label = instr) : step p c = some (execInstr instr c) := by
  simp [step, hp, hc]

@[simp] theorem readRegs_present {r : ℕ} (regs : Fin r → Bool)
    (value present : Fin r) (top : Option Bool) :
    readRegs regs value present top present = top.isSome := by
  simp [readRegs]

theorem readRegs_value {r : ℕ} (regs : Fin r → Bool)
    (value present : Fin r) (top : Option Bool) (h : value ≠ present) :
    readRegs regs value present top value = top.getD false := by
  simp [readRegs, h]

end SubexponentialSAT.BitProgram

end OAI.Algorithms


/-! A width-one compilation of Boolean programs, with empty pop guarded before
the primitive stack compiler. The output contract reads the entire tape. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler

open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.StackCompiler OAI.Algorithms.SubexponentialSAT.StackEncoding OAI.Algorithms.SubexponentialSAT.StackMachine
open scoped BigOperators

abbrev State (r l : ℕ) := Fin l × (Fin r → Bool)

def selected {r s l : ℕ} (p : BitProgram.Program r s l) (q : State r l) : Fin s :=
  match p.code q.1 with
  | .halt => p.outputStack
  | .push stack _ _ | .peek stack _ _ _ | .pop stack _ _ _ => stack
  | _ => p.inputStack

def guardedPop : Option Bool → Mutation Bool
  | none => .keep
  | some _ => .pop

theorem guardedPop_apply (bits : List Bool) :
    (guardedPop bits.head?).apply bits = bits.tail := by
  cases bits <;> rfl

theorem guardedPop_empty_actions : mutationActions boolCode (guardedPop none) = [] := rfl

def transition {r s l : ℕ} (p : BitProgram.Program r s l) (q : State r l)
    (top : Option Bool) : Bool ⊕ (State r l × Mutation Bool) :=
  match p.code q.1 with
  | .halt => .inl (top.getD false)
  | .goto next => .inr ((next, q.2), .keep)
  | .set dst value next => .inr ((next, Function.update q.2 dst value), .keep)
  | .copy dst src next => .inr ((next, Function.update q.2 dst (q.2 src)), .keep)
  | .bnot dst src next => .inr ((next, Function.update q.2 dst (!(q.2 src))), .keep)
  | .band dst a b next => .inr ((next, Function.update q.2 dst (q.2 a && q.2 b)), .keep)
  | .bor dst a b next => .inr ((next, Function.update q.2 dst (q.2 a || q.2 b)), .keep)
  | .bxor dst a b next => .inr ((next, Function.update q.2 dst (q.2 a ^^ q.2 b)), .keep)
  | .branch test yes no => .inr (((if q.2 test then yes else no), q.2), .keep)
  | .push _ src next => .inr ((next, q.2), .push (q.2 src))
  | .peek _ value present next =>
      .inr ((next, BitProgram.readRegs q.2 value present top), .keep)
  | .pop _ value present next =>
      .inr ((next, BitProgram.readRegs q.2 value present top), guardedPop top)

def stackProgram {r s l : ℕ} (p : BitProgram.Program r s l) :
    StackProgram (State r l) (fun _ : Fin s => Bool) where
  inputTape := p.inputStack
  start := (p.entry, fun _ => false)
  select := selected p
  transition := transition p

theorem transition_empty_ne_pop {r s l : ℕ} (p : BitProgram.Program r s l)
    (q q' : State r l) : transition p q none ≠ .inr (q', .pop) := by
  cases h : p.code q.1 <;> simp [transition, h, guardedPop]

theorem push_actions (bit : Bool) :
    mutationActions boolCode (.push bit) = [.move .left, .write (some bit)] := rfl

theorem pop_actions : mutationActions boolCode .pop = [.write none, .move .right] := rfl

theorem mutation_displacement (displacement : Action → ℤ)
    (left : displacement (.move .left) = -1)
    (right : displacement (.move .right) = 1)
    (write : ∀ bit, displacement (.write bit) = 0)
    (op : Mutation Bool) (bits : List Bool) (safe : op = .pop → bits ≠ []) :
    ((mutationActions boolCode op).map displacement).sum =
      (bits.length : ℤ) - (op.apply bits).length := by
  cases op with
  | keep => simp [mutationActions, Mutation.apply]
  | pop =>
      cases bits with
      | nil => exact False.elim (safe rfl rfl)
      | cons bit bits => simp [pop_actions, Mutation.apply, right, write]
  | push bit => simp [push_actions, Mutation.apply, left, write]

theorem transition_mutation_displacement {r s l : ℕ} (p : BitProgram.Program r s l)
    (q q' : State r l) (op : Mutation Bool) (bits : List Bool)
    (h : transition p q bits.head? = .inr (q', op))
    (displacement : Action → ℤ)
    (left : displacement (.move .left) = -1)
    (right : displacement (.move .right) = 1)
    (write : ∀ bit, displacement (.write bit) = 0) :
    ((mutationActions boolCode op).map displacement).sum =
      (bits.length : ℤ) - (op.apply bits).length := by
  apply mutation_displacement displacement left right write
  intro hop hempty
  subst op
  subst bits
  exact transition_empty_ne_pop p q q' h

def stackCfg {r s l : ℕ} (p : BitProgram.Program r s l) (c : BitProgram.Cfg r s l) :
    StackCfg (State r l) (fun _ : Fin s => Bool) :=
  ⟨match c.pc with
    | none => .inl ((c.stacks p.outputStack).head?.getD false)
    | some label => .inr (label, c.regs), c.stacks⟩

theorem stack_step {r s l : ℕ} (p : BitProgram.Program r s l) (c : BitProgram.Cfg r s l) :
    stackStep (stackProgram p) (stackCfg p c) = (BitProgram.step p c).map (stackCfg p) := by
  rcases c with ⟨pc, regs, stk⟩
  cases pc with
  | none => rfl
  | some label =>
      cases h : p.code label <;>
        simp [stackStep, stackProgram, stackCfg, selected, transition, h,
          BitProgram.step, BitProgram.execInstr, Mutation.apply,
          Function.update_eq_self]
      exact congrArg (Function.update stk _) (guardedPop_apply _)

theorem stack_trace {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : BitProgram.Cfg r s l} {n : ℕ} (h : BitProgram.Trace p n a b) :
    Trace (stackStep (stackProgram p)) n (stackCfg p a) (stackCfg p b) := by
  induction h with
  | refl => exact .refl _
  | cons hs _ ih =>
      apply Trace.cons _ ih
      rw [stack_step, hs]
      rfl

def codes (s : ℕ) : CodeFamily (fun _ : Fin s => Bool) := fun _ => boolCode

def decoder (s : ℕ) : (i : Fin s) → List Bool → Option Bool := fun _ => List.head?

theorem decoder_nil (s : ℕ) (i : Fin s) : decoder s i [] = none := rfl

theorem decoder_block (s : ℕ) (i : Fin s) (b : Bool) :
    decoder s i ((codes s i).block b) = some b := rfl

noncomputable abbrev primitive {r s l : ℕ} (p : BitProgram.Program r s l) : PrimitiveMachine :=
  reindex (Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s)))
    (controller (stackProgram p) (codes s) (decoder s))

noncomputable abbrev primitiveCfg {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : BitProgram.Cfg r s l) : (primitive p).Cfg :=
  reindexCfg (Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s)))
    (controller (stackProgram p) (codes s) (decoder s))
    (encodeCfg (stackProgram p) (codes s) (stackCfg p c))

noncomputable abbrev primitiveControlCfg {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : ControlCfg (StackCompiler.State (stackProgram p) (codes s)) s) :
    (primitive p).Cfg :=
  reindexCfg (Fintype.equivFin _) (controller (stackProgram p) (codes s) (decoder s)) c

@[simp] theorem reindex_tapeCount {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t) : (reindex e p).tapeCount = t := rfl

@[simp] theorem primitive_tapeCount {r s l : ℕ} (p : BitProgram.Program r s l) :
    (primitive p).tapeCount = s := rfl

theorem compiler_overhead {r s l : ℕ} (p : BitProgram.Program r s l) :
    compilerOverhead (codes s) = 7 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    rfl
  · exact localCost_le_overhead (codes s) p.inputStack

theorem primitive_execution {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : BitProgram.Cfg r s l} {n : ℕ} (h : BitProgram.RunsIn p n a b) :
    RunsIn (primitive p).step (7 * n) (primitiveCfg p a) (primitiveCfg p b) := by
  obtain ⟨steps, hsteps, htrace⟩ := h
  have hstack : RunsIn (stackStep (stackProgram p)) n (stackCfg p a) (stackCfg p b) :=
    ⟨steps, hsteps, stack_trace p htrace⟩
  obtain ⟨c, hc, hrun⟩ := simulate_runsIn
    (primitive_simulation (stackProgram p) (codes s) (decoder s)
      (decoder_nil s) (decoder_block s)) hstack rfl
  rw [hc] at hrun
  change RunsIn (primitive p).step (compilerOverhead (codes s) * n)
    (primitiveCfg p a) (primitiveCfg p b) at hrun
  simpa only [compiler_overhead p] using hrun

theorem primitive_initial {r s l : ℕ} (p : BitProgram.Program r s l) (input : List Bool) :
    primitiveCfg p (BitProgram.initial p input) = (primitive p).init input := by
  have h : stackCfg p (BitProgram.initial p input) =
      initialCfg (stackProgram p) (Equiv.refl Bool) input := by
    simp [stackCfg, initialCfg, stackProgram,
      Function.update_apply, funext_iff]
  unfold primitiveCfg primitive
  rw [h]
  exact compiled_initial (stackProgram p) (codes s) (decoder s) (Equiv.refl Bool) rfl input

theorem tapeEncoding_bool {r s l : ℕ}
    (a : StackCfg (State r l) (fun _ : Fin s => Bool)) :
    StackCompiler.tapeEncoding (codes s) a = fun i => dataTape (a.stk i) := by
  funext i
  exact congrArg dataTape (encodeDataStack_boolCode (a.stk i))

theorem primitive_tape {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : BitProgram.Cfg r s l) (i : Fin s) :
    (primitiveCfg p c).tapes i = Turing.Tape.mk₁ ((c.stacks i).map some) := by
  change dataTape (encodeDataStack boolCode (c.stacks i)) = _
  rw [encodeDataStack_boolCode]
  rfl

theorem primitive_halted {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : BitProgram.Cfg r s l) (h : c.pc = none) :
    (primitiveCfg p c).state = .inl ((c.stacks p.outputStack).head?.getD false) := by
  apply compiled_terminal
  simp [stackCfg, h]

theorem primitive_word_execution {r s l : ℕ} (p : BitProgram.Program r s l)
    {input output : List Bool} {n : ℕ} {final : BitProgram.Cfg r s l}
    (h : BitProgram.RunsIn p n (BitProgram.initial p input) final)
    (halted : final.pc = none) (hout : final.stacks p.outputStack = output) :
    ∃ c : (primitive p).Cfg,
      RunsIn (primitive p).step (7 * n) ((primitive p).init input) c ∧
      c.state = .inl (output.head?.getD false) ∧
      c.tapes p.outputStack = Turing.Tape.mk₁ (output.map some) := by
  refine ⟨primitiveCfg p final, ?_, ?_, ?_⟩
  · simpa only [primitive_initial] using primitive_execution p h
  · rw [primitive_halted p final halted, hout]
  · rw [primitive_tape, hout]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler

/-! Structured syntax and subroutine linking from upstream StructuredProgram
(the TM2-only primitive wrapper is omitted), ProgramLinking, StructuredCalls,
and BitProgramSpace. All costs remain actual BitProgram transition counts. -/

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

def stackBits {s : ℕ} (stk : Fin s → List Bool) : ℕ :=
  ∑ k, (stk k).length

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

def dataBits {r s l : ℕ} (c : Cfg r s l) : ℕ := stackBits c.stacks

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

theorem runsIn_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : RunsIn p n a b) : dataBits b ≤ dataBits a + n := by
  obtain ⟨t, ht, htrace⟩ := h
  exact (trace_dataBits p htrace).trans (Nat.add_le_add_left ht _)

@[simp] theorem initial_dataBits {r s l : ℕ} (p : Program r s l) (input : List Bool) :
    dataBits (initial p input) = input.length := by
  simp only [dataBits, stackBits ]
  have lengths (k : Fin s) : (if k = p.inputStack then input else []).length =
      if k = p.inputStack then input.length else 0 := by split_ifs <;> rfl
  simp_rw [lengths]
  simp

theorem input_runsIn_dataBits {r s l : ℕ} (p : Program r s l)
    {input : List Bool} {b : Cfg r s l} {n : ℕ}
    (h : RunsIn p n (initial p input) b) : dataBits b ≤ input.length + n := by
  simpa using runsIn_dataBits p h

end SubexponentialSAT.BitProgram

end OAI.Algorithms


namespace OAI.Algorithms

/-!
# Structured programs compiled to finite bit instruction tables

The syntax has no unbounded natural-number registers or semantic-function
instructions. All data operations are the concrete Boolean-register and stack
instructions of BitProgram. Loops inspect a Boolean register, and changing data
never changes the finite generated instruction table.
-/

namespace SubexponentialSAT.StructuredProgram

open SubexponentialSAT.BitProgram

/-- Data separate from the finite program counter. -/
structure State (r s : ℕ) where
  regs : Fin r → Bool
  «stacks» : Fin s → List Bool

namespace State

abbrev withPC {r s l : ℕ} (d : State r s) (pc : Option (Fin l)) : Cfg r s l :=
  ⟨pc, d.regs, d.stacks⟩

def ofCfg {r s l : ℕ} (c : Cfg r s l) : State r s := ⟨c.regs, c.stacks⟩

@[simp] theorem ofCfg_withPC {r s l : ℕ} (d : State r s) (pc : Option (Fin l)) :
    ofCfg (d.withPC pc) = d := rfl

end State

/-- Every atom is a single existing instruction with its continuation omitted. -/
inductive Atom (r s : ℕ) where
  | set (dst : Fin r) (value : Bool)
  | copy (dst src : Fin r)
  | bnot (dst src : Fin r)
  | band (dst left right : Fin r)
  | bor (dst left right : Fin r)
  | bxor (dst left right : Fin r)
  | push (stack : Fin s) (src : Fin r)
  | peek (stack : Fin s) (value present : Fin r)
  | pop (stack : Fin s) (value present : Fin r)
  deriving DecidableEq, Fintype

namespace Atom

def instr {r s l : ℕ} (a : Atom r s) (next : Fin l) : Instr r s l :=
  match a with
  | .set dst value => .set dst value next
  | .copy dst src => .copy dst src next
  | .bnot dst src => .bnot dst src next
  | .band dst left right => .band dst left right next
  | .bor dst left right => .bor dst left right next
  | .bxor dst left right => .bxor dst left right next
  | .push stack src => .push stack src next
  | .peek stack value present => .peek stack value present next
  | .pop stack value present => .pop stack value present next

/-- Atom evaluation uses the existing instruction evaluator itself. -/
def eval {r s : ℕ} (a : Atom r s) (d : State r s) : State r s :=
  State.ofCfg (execInstr (a.instr (0 : Fin 1)) (d.withPC none))

theorem exec_instr {r s l : ℕ} (a : Atom r s) (d : State r s)
    (pc : Option (Fin l)) (next : Fin l) :
    execInstr (a.instr next) (d.withPC pc) = (a.eval d).withPC (some next) := by
  cases a <;> rfl

end Atom

inductive Cmd (r s : ℕ) where
  | skip
  | atom (a : Atom r s)
  | seq (first second : Cmd r s)
  | ite (test : Fin r) (yes no : Cmd r s)
  | while (test : Fin r) (body : Cmd r s)

/-- Finite executions count exactly the atom and Boolean-test instructions. -/
inductive Eval {r s : ℕ} : Cmd r s → ℕ → State r s → State r s → Prop
  | skip (d) : Eval .skip 0 d d
  | atom (a) (d) : Eval (.atom a) 1 d (a.eval d)
  | seq {first second n m a b c} : Eval first n a b → Eval second m b c →
      Eval (.seq first second) (n + m) a c
  | ite_true {test yes no n a b} : a.regs test = true → Eval yes n a b →
      Eval (.ite test yes no) (n + 1) a b
  | ite_false {test yes no n a b} : a.regs test = false → Eval no n a b →
      Eval (.ite test yes no) (n + 1) a b
  | while_false {test body a} : a.regs test = false → Eval (.while test body) 1 a a
  | while_true {test body n m a b c} : a.regs test = true → Eval body n a b →
      Eval (.while test body) m b c → Eval (.while test body) (n + m + 1) a c

/-- One static site per atom or guard; sequencing introduces no instruction. -/
abbrev Site {r s : ℕ} : Cmd r s → Type
  | .skip => Empty
  | .atom _ => Unit
  | .seq first second => Site first ⊕ Site second
  | .ite _ yes no => Option (Site yes ⊕ Site no)
  | .while _ body => Option (Site body)

instance siteFintype {r s : ℕ} : (c : Cmd r s) → Fintype (Site c)
  | .skip => inferInstanceAs (Fintype Empty)
  | .atom _ => inferInstanceAs (Fintype Unit)
  | .seq first second => by
      letI := siteFintype first
      letI := siteFintype second
      exact inferInstanceAs (Fintype (Site first ⊕ Site second))
  | .ite _ yes no => by
      letI := siteFintype yes
      letI := siteFintype no
      exact inferInstanceAs (Fintype (Option (Site yes ⊕ Site no)))
  | .while _ body => by
      letI := siteFintype body
      exact inferInstanceAs (Fintype (Option (Site body)))

/-- Entry address when the command's continuation is a given address. -/
abbrev entry {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) : Fin l :=
  match c with
  | .skip => exit
  | .atom _ => embed ()
  | .seq first second =>
      entry first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
  | .ite _ _ _ => embed none
  | .while _ _ => embed none

/-- Actual instruction at each static site. While bodies return to their guard. -/
abbrev code {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) :
    Site c → Instr r s l :=
  match c with
  | .skip => fun q => nomatch q
  | .atom a => fun _ => a.instr exit
  | .seq first second => fun q => match q with
      | .inl x => code first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit) x
      | .inr x => code second (embed ∘ Sum.inr) exit x
  | .ite test yes no => fun q => match q with
      | none => .branch test (entry yes (fun x => embed (some (.inl x))) exit)
          (entry no (fun x => embed (some (.inr x))) exit)
      | some (.inl x) => code yes (fun x => embed (some (.inl x))) exit x
      | some (.inr x) => code no (fun x => embed (some (.inr x))) exit x
  | .while test body => fun q => match q with
      | none => .branch test (entry body (embed ∘ some) (embed none)) exit
      | some x => code body (embed ∘ some) (embed none) x

/-- The compiler correctness statement is about the actual BitProgram step.
The local table-agreement premise is discharged by the whole-program compiler. -/
theorem eval_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) :
    ∀ {l : ℕ} (p : Program r s l) (embed : Site c → Fin l) (exit : Fin l),
    (∀ q, p.code (embed q) = code c embed exit q) →
    Trace p n (a.withPC (some (entry c embed exit))) (b.withPC (some exit)) := by
  induction h with
  | skip d =>
      intro l p embed exit hcode
      exact .refl _
  | atom op d =>
      intro l p embed exit hcode
      refine .cons ?_ (.refl _)
      rw [← Atom.exec_instr op d (some (entry (.atom op) embed exit)) exit]
      exact step_code p _ (embed ()) (op.instr exit) rfl (hcode ())
  | @seq first second n m a b c hf hs ihf ihs =>
      intro l p embed exit hcode
      exact (ihf p (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
        (fun q => hcode (.inl q))).trans
        (ihs p (embed ∘ Sum.inr) exit (fun q => hcode (.inr q)))
  | @ite_true test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q))))
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]
  | @ite_false test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q))))
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_false test body a ht =>
      intro l p embed exit hcode
      refine .cons ?_ (.refl _)
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_true test body n m a b c ht hb hw ihb ihw =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        ((ihb p (embed ∘ some) (embed none) (fun q => hcode (some q))).trans
          (ihw p embed exit hcode))
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]

/-- Syntactic control size, independent of all runtime stack lengths. -/
abbrev size {r s : ℕ} : Cmd r s → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq first second => size first + size second
  | .ite _ yes no => size yes + size no + 1
  | .while _ body => size body + 1

/-- An explicit computable enumeration of control sites; no finite-choice
oracle is used to construct the generated instruction table. -/
abbrev siteEquiv {r s : ℕ} : (c : Cmd r s) → Site c ≃ Fin (size c)
  | .skip => finZeroEquiv.symm
  | .atom _ => finOneEquiv.symm
  | .seq first second =>
      ((siteEquiv first).sumCongr (siteEquiv second)).trans finSumFinEquiv
  | .ite _ yes no =>
      (((siteEquiv yes).sumCongr (siteEquiv no)).trans finSumFinEquiv).optionCongr.trans
        (finSuccEquiv _).symm
  | .while _ body => (siteEquiv body).optionCongr.trans (finSuccEquiv _).symm

/-- The extra address is the common final halt instruction. -/
abbrev labelEquiv {r s : ℕ} (c : Cmd r s) : Option (Site c) ≃ Fin (size c + 1) :=
  (siteEquiv c).optionCongr.trans (finSuccEquiv _).symm

abbrev siteAddress {r s : ℕ} (c : Cmd r s) (q : Site c) : Fin (size c + 1) :=
  labelEquiv c (some q)

abbrev exitAddress {r s : ℕ} (c : Cmd r s) : Fin (size c + 1) := labelEquiv c none

/-- A concrete, computably generated finite bit program. -/
def compiled {r s : ℕ} (c : Cmd r s) (inputStack outputStack : Fin s) :
    Program r s (size c + 1) where
  inputStack := inputStack
  outputStack := outputStack
  entry := entry c (siteAddress c) (exitAddress c)
  code label := match (labelEquiv c).symm label with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q

@[simp] theorem compiled_site {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) (q : Site c) :
    (compiled c inputStack outputStack).code (siteAddress c q) =
      code c (siteAddress c) (exitAddress c) q := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) (some q)) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem compiled_exit {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) :
    (compiled c inputStack outputStack).code (exitAddress c) = Instr.halt := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) none) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

/-- Whole-program correctness: n structured steps become n actual bit-program
steps to the exit address, with no unresolved compiler-certificate premise. -/
theorem compiled_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) n
      (a.withPC (some (compiled c inputStack outputStack).entry))
      (b.withPC (some (exitAddress c))) :=
  eval_trace h _ _ _ (compiled_site c inputStack outputStack)

/-- Executing the generated final halt costs one additional instruction. -/
theorem compiled_halt_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (a.withPC (some (compiled c inputStack outputStack).entry)) (b.withPC none) := by
  apply (compiled_trace h inputStack outputStack).trans
  refine .cons ?_ (.refl _)
  rw [step]
  simp only [State.withPC, Option.map_some]
  rw [compiled_exit]
  rfl

/-- Canonical stack input/output data, including all cleared work registers. -/
abbrev ioState {r s : ℕ} (stack : Fin s) (word : List Bool) : State r s :=
  ⟨fun _ => false, fun i => if i = stack then word else []⟩

theorem compiled_io_trace {r s : ℕ} {c : Cmd r s} {n : ℕ}
    (inputStack outputStack : Fin s) {input output : List Bool}
    (h : Eval c n (ioState inputStack input) (ioState outputStack output)) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (initial (compiled c inputStack outputStack) input)
      (terminal (compiled c inputStack outputStack) output) :=
  compiled_halt_trace h inputStack outputStack


end SubexponentialSAT.StructuredProgram

end OAI.Algorithms


namespace OAI.Algorithms

/-!
# Finite program relocation and linking

Every linked block is an instruction table inside one finite program.  A block's
halt can be replaced by a jump to a caller-specified continuation.  The proofs
below transfer actual instruction traces, including that final instruction, and
preserve all ambient registers and stacks outside the block's assigned ports.

The finite sizes and maps are fixed when the linked program is constructed; they
do not inspect the unbounded input stacks.
-/

namespace SubexponentialSAT.ProgramLinking

open BitProgram

variable {r s l R S L : ℕ}

/-- Relocate all finite references, optionally replacing halt by a return jump. -/
def relocateInstr (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) :
    Instr r s l → Instr R S L
  | .halt => match returnPc with | none => .halt | some pc => .goto pc
  | .goto next => .goto (label next)
  | .set dst value next => .set (register dst) value (label next)
  | .copy dst src next => .copy (register dst) (register src) (label next)
  | .bnot dst src next => .bnot (register dst) (register src) (label next)
  | .band dst left right next =>
      .band (register dst) (register left) (register right) (label next)
  | .bor dst left right next =>
      .bor (register dst) (register left) (register right) (label next)
  | .bxor dst left right next =>
      .bxor (register dst) (register left) (register right) (label next)
  | .branch test yes no => .branch (register test) (label yes) (label no)
  | .push port src next => .push (stack port) (register src) (label next)
  | .peek port value present next =>
      .peek (stack port) (register value) (register present) (label next)
  | .pop port value present next =>
      .pop (stack port) (register value) (register present) (label next)

def relocatePc (label : Fin l → Fin L) (returnPc : Option (Fin L)) :
    Option (Fin l) → Option (Fin L)
  | none => returnPc
  | some pc => some (label pc)

/-- A mathematical embedding into the caller's frame.  The executable program
does not evaluate this function: it uses the finite relocated instruction table. -/
noncomputable def embedCfg (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (c : Cfg r s l) : Cfg R S L where
  pc := relocatePc label returnPc c.pc
  regs := Function.extend register c.regs frame.regs
  «stacks» := Function.extend stack c.stacks frame.stacks

theorem extend_update {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (g : α → γ) (base : β → γ)
    (a : α) (value : γ) :
    Function.extend f (Function.update g a value) base =
      Function.update (Function.extend f g base) (f a) value := by
  classical
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨x, rfl⟩ := hb
    simp only [hf.extend_apply, Function.update_apply, hf.eq_iff]
  · have hne : b ≠ f a := by
      intro h
      exact hb ⟨a, h.symm⟩
    simp only [Function.extend_apply' _ _ _ hb, Function.update_of_ne hne]

@[simp] theorem extend_id {α γ : Type*} (g base : α → γ) :
    Function.extend id g base = g := by
  funext a
  exact Function.injective_id.extend_apply g base a

@[simp] theorem embedCfg_register (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (hinj : Function.Injective register) (a : Fin r) :
    (embedCfg register stack label returnPc frame c).regs (register a) = c.regs a :=
  hinj.extend_apply _ _ _

@[simp] theorem embedCfg_stack (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (hinj : Function.Injective stack) (a : Fin s) :
    (embedCfg register stack label returnPc frame c).stacks (stack a) = c.stacks a :=
  hinj.extend_apply _ _ _

theorem embedCfg_register_frame (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (a : Fin R) (ha : ¬ ∃ b, register b = a) :
    (embedCfg register stack label returnPc frame c).regs a = frame.regs a :=
  Function.extend_apply' _ _ _ ha

theorem embedCfg_stack_frame (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (frame : Cfg R S L) (c : Cfg r s l)
    (a : Fin S) (ha : ¬ ∃ b, stack b = a) :
    (embedCfg register stack label returnPc frame c).stacks a = frame.stacks a :=
  Function.extend_apply' _ _ _ ha

/-- Relocation commutes with every instruction, even when read value/presence
registers alias.  Injective port maps preserve exactly the source aliases. -/
theorem execInstr_relocate (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (instr : Instr r s l) (c : Cfg r s l) :
    execInstr (relocateInstr register stack label returnPc instr)
        (embedCfg register stack label returnPc frame c) =
      embedCfg register stack label returnPc frame (execInstr instr c) := by
  cases instr <;> cases returnPc <;>
    simp [relocateInstr, execInstr, embedCfg, relocatePc, readRegs,
      hregister.extend_apply, hstack.extend_apply,
      extend_update hregister, extend_update hstack, apply_ite]
  all_goals split <;> simp_all

/-- Code agreement is an ordinary equality of actual finite table entries. -/
abbrev CodeEmbedding (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) : Prop :=
  ∀ pc, q.code (label pc) = relocateInstr register stack label returnPc (p.code pc)

theorem relocate_step_at (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {c c' : Cfg r s l}
    (hcode : ∀ pc, c.pc = some pc →
      q.code (label pc) = relocateInstr register stack label returnPc (p.code pc))
    (hstep : step p c = some c') :
    step q (embedCfg register stack label returnPc frame c) =
      some (embedCfg register stack label returnPc frame c') := by
  cases hpc : c.pc with
  | none => simp [step, hpc] at hstep
  | some pc =>
      have hc' : execInstr (p.code pc) c = c' := by
        simpa [step, hpc] using hstep
      simp only [step, embedCfg, hpc, relocatePc, Option.map_some]
      rw [hcode pc hpc]
      change some (execInstr (relocateInstr register stack label returnPc (p.code pc))
        (embedCfg register stack label returnPc frame c)) = _
      rw [execInstr_relocate register stack label returnPc frame hregister hstack, hc']
      rfl

theorem relocate_step (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : CodeEmbedding p q register stack label returnPc)
    {c c' : Cfg r s l} (hstep : step p c = some c') :
    step q (embedCfg register stack label returnPc frame c) =
      some (embedCfg register stack label returnPc frame c') :=
  relocate_step_at p q register stack label returnPc frame hregister hstack
    (fun pc _ => hcode pc) hstep

/-- Complete block traces transfer with exactly the same number of steps.
In particular a source halt is the target's actual return-jump instruction. -/
theorem relocate_trace (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : CodeEmbedding p q register stack label returnPc)
    {steps : ℕ} {c c' : Cfg r s l} (htrace : Trace p steps c c') :
    Trace q steps (embedCfg register stack label returnPc frame c)
      (embedCfg register stack label returnPc frame c') := by
  induction htrace with
  | refl c => exact .refl _
  | cons hs ht ih =>
      exact .cons
        (relocate_step p q register stack label returnPc frame hregister hstack hcode hs) ih

theorem relocate_runsIn (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : CodeEmbedding p q register stack label returnPc)
    {bound : ℕ} {c c' : Cfg r s l} (htrace : RunsIn p bound c c') :
    RunsIn q bound (embedCfg register stack label returnPc frame c)
      (embedCfg register stack label returnPc frame c') := by
  obtain ⟨steps, hsteps, ht⟩ := htrace
  exact ⟨steps, hsteps,
    relocate_trace p q register stack label returnPc frame hregister hstack hcode ht⟩

/-- Install a standalone program on a larger port set, keeping its labels. -/
abbrev liftProgram (p : Program r s l) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) : Program R S l where
  inputStack := stack p.inputStack
  outputStack := stack p.outputStack
  entry := p.entry
  code := fun pc => relocateInstr register stack id none (p.code pc)

theorem liftProgram_trace (p : Program r s l) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) :
    Trace (liftProgram p register stack) n
      (embedCfg register stack id none frame a) (embedCfg register stack id none frame b) :=
  relocate_trace p _ register stack id none frame hregister hstack (fun _ => rfl) h

theorem liftProgram_runsIn (p : Program r s l) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {n : ℕ} {a b : Cfg r s l} (h : RunsIn p n a b) :
    RunsIn (liftProgram p register stack) n
      (embedCfg register stack id none frame a) (embedCfg register stack id none frame b) :=
  relocate_runsIn p _ register stack id none frame hregister hstack (fun _ => rfl) h

theorem trace_from_halted (p : Program r s l) {n : ℕ} {a b : Cfg r s l}
    (h : Trace p n a b) (ha : a.pc = none) : b.pc = none := by
  cases h with
  | refl => exact ha
  | cons hs _ => simp [step, ha] at hs

/-- A trace ending at an active label has not executed any halt instruction.
Thus the target may give all source halt labels an arbitrary continuation body. -/
theorem relocate_trace_before_halt (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ∀ pc, p.code pc ≠ .halt →
      q.code (label pc) = relocateInstr register stack label returnPc (p.code pc))
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) (hb : b.pc ≠ none) :
    Trace q n (embedCfg register stack label returnPc frame a)
      (embedCfg register stack label returnPc frame b) := by
  induction h with
  | refl => exact .refl _
  | @cons n a c b hs ht ih =>
      have hlocal : ∀ pc, a.pc = some pc →
          q.code (label pc) = relocateInstr register stack label returnPc (p.code pc) := by
        intro pc hpc
        apply hcode pc
        intro hhalt
        have hc : c = execInstr .halt a := by
          simpa [step, hpc, hhalt] using hs.symm
        have hcpc : c.pc = none := by simp [hc, execInstr]
        exact hb (trace_from_halted p ht hcpc)
      exact .cons
        (relocate_step_at p q register stack label returnPc frame hregister hstack hlocal hs)
        (ih hb)

/-- Designated-exit version: the exit's instruction can be replaced without
charging a step until the caller actually executes that instruction. -/
theorem relocate_trace_to_exit (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (exit : Fin l) (hexit : p.code exit = .halt)
    (hcode : ∀ pc, pc ≠ exit →
      q.code (label pc) = relocateInstr register stack label returnPc (p.code pc))
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) (hb : b.pc = some exit) :
    Trace q n (embedCfg register stack label returnPc frame a)
      (embedCfg register stack label returnPc frame b) := by
  apply relocate_trace_before_halt p q register stack label returnPc frame
    hregister hstack ?_ h (by simp [hb])
  intro pc hpc
  apply hcode pc
  intro heq
  exact hpc (heq ▸ hexit)

/-! ## Concrete disjoint linking -/

/-- Install two finite tables in disjoint label ranges.  The first block's halts
jump to the second block's entry; the second block's halts stop the program.
Register and stack assignments can share ports between the two blocks. -/
abbrev linkInto {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S) :
    Program R S (l + m) where
  inputStack := stackP p.inputStack
  outputStack := stackQ q.outputStack
  entry := Fin.castAdd m p.entry
  code := Fin.addCases
    (fun pc => relocateInstr registerP stackP (Fin.castAdd m)
      (some (Fin.natAdd l q.entry)) (p.code pc))
    (fun pc => relocateInstr registerQ stackQ (Fin.natAdd l) none (q.code pc))

theorem linkInto_leftCode {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S) :
    CodeEmbedding p (linkInto p q registerP stackP registerQ stackQ)
      registerP stackP (Fin.castAdd m) (some (Fin.natAdd l q.entry)) := by
  intro pc
  simp []

theorem linkInto_rightCode {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S) :
    CodeEmbedding q (linkInto p q registerP stackP registerQ stackQ)
      registerQ stackQ (Fin.natAdd l) none := by
  intro pc
  simp []

/-- Linking with port assignments uses a checked equality at the shared data
boundary.  Both source traces execute inside the concrete table above. -/
theorem linkInto_trace {r' s' m : ℕ} (p : Program r s l) (q : Program r' s' m)
    (registerP : Fin r → Fin R) (stackP : Fin s → Fin S)
    (registerQ : Fin r' → Fin R) (stackQ : Fin s' → Fin S)
    (hregisterP : Function.Injective registerP) (hstackP : Function.Injective stackP)
    (hregisterQ : Function.Injective registerQ) (hstackQ : Function.Injective stackQ)
    (frameP frameQ : Cfg R S (l + m)) {n₁ n₂ : ℕ}
    {a b : Cfg r s l} {c d : Cfg r' s' m}
    (hp : Trace p n₁ a b) (hq : Trace q n₂ c d)
    (boundary : embedCfg registerP stackP (Fin.castAdd m)
        (some (Fin.natAdd l q.entry)) frameP b =
      embedCfg registerQ stackQ (Fin.natAdd l) none frameQ c) :
    Trace (linkInto p q registerP stackP registerQ stackQ) (n₁ + n₂)
      (embedCfg registerP stackP (Fin.castAdd m)
        (some (Fin.natAdd l q.entry)) frameP a)
      (embedCfg registerQ stackQ (Fin.natAdd l) none frameQ d) := by
  have hp' := relocate_trace p _ registerP stackP (Fin.castAdd m)
    (some (Fin.natAdd l q.entry)) frameP hregisterP hstackP
    (linkInto_leftCode p q registerP stackP registerQ stackQ) hp
  have hq' := relocate_trace q _ registerQ stackQ (Fin.natAdd l) none
    frameQ hregisterQ hstackQ
    (linkInto_rightCode p q registerP stackP registerQ stackQ) hq
  rw [boundary] at hp'
  exact hp'.trans hq'

/-- Only change the finite program counter, keeping all data verbatim. -/
abbrev relabelCfg (label : Fin l → Fin L) (returnPc : Option (Fin L))
    (c : Cfg r s l) : Cfg r s L where
  pc := relocatePc label returnPc c.pc
  regs := c.regs
  «stacks» := c.stacks

@[simp] theorem embedCfg_id (label : Fin l → Fin L) (returnPc : Option (Fin L))
    (frame : Cfg r s L) (c : Cfg r s l) :
    embedCfg id id label returnPc frame c = relabelCfg label returnPc c := by
  simp [embedCfg, relabelCfg]

/-- Start another finite table with the current register and stack contents. -/
abbrev enter {m : ℕ} (q : Program r s m) (c : Cfg r s l) : Cfg r s m where
  pc := some q.entry
  regs := c.regs
  «stacks» := c.stacks

/-- Sequential composition when both blocks already use the same port set. -/
abbrev link {m : ℕ} (p : Program r s l) (q : Program r s m) : Program r s (l + m) :=
  linkInto p q id id id id

@[simp] theorem link_initial {m : ℕ} (p : Program r s l) (q : Program r s m)
    (input : List Bool) :
    relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) (initial p input) =
      initial (link p q) input := rfl

@[simp] theorem link_terminal {m : ℕ} (p : Program r s l) (q : Program r s m)
    (output : List Bool) :
    relabelCfg (Fin.natAdd l) none (terminal q output) =
      terminal (link p q) output := rfl

theorem link_left_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) :
    Trace (link p q) n
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a)
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) b) := by
  let frame := relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a
  simpa only [embedCfg_id] using
    relocate_trace p (link p q) id id (Fin.castAdd m)
      (some (Fin.natAdd l q.entry)) frame Function.injective_id Function.injective_id
      (linkInto_leftCode p q id id id id) h

theorem link_right_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n : ℕ} {a b : Cfg r s m} (h : Trace q n a b) :
    Trace (link p q) n
      (relabelCfg (Fin.natAdd l) none a) (relabelCfg (Fin.natAdd l) none b) := by
  let frame := relabelCfg (Fin.natAdd l) none a
  simpa only [embedCfg_id] using
    relocate_trace q (link p q) id id (Fin.natAdd l) none frame
      Function.injective_id Function.injective_id (linkInto_rightCode p q id id id id) h

/-- No dispatcher or subroutine oracle is added: the replaced halt itself is
the one-step return jump, so the composed trace length is exactly the sum. -/
theorem link_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n₁ n₂ : ℕ} {a b : Cfg r s l} {c : Cfg r s m}
    (hp : Trace p n₁ a b) (hb : b.pc = none)
    (hq : Trace q n₂ (enter q b) c) :
    Trace (link p q) (n₁ + n₂)
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a)
      (relabelCfg (Fin.natAdd l) none c) := by
  have boundary : relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) b =
      relabelCfg (Fin.natAdd l) none (enter q b) := by
    simp [relabelCfg, relocatePc, hb]
  have hp' := link_left_trace p q hp
  rw [boundary] at hp'
  exact hp'.trans (link_right_trace p q hq)

theorem link_runsIn {m : ℕ} (p : Program r s l) (q : Program r s m)
    {n₁ n₂ : ℕ} {a b : Cfg r s l} {c : Cfg r s m}
    (hp : RunsIn p n₁ a b) (hb : b.pc = none)
    (hq : RunsIn q n₂ (enter q b) c) :
    RunsIn (link p q) (n₁ + n₂)
      (relabelCfg (Fin.castAdd m) (some (Fin.natAdd l q.entry)) a)
      (relabelCfg (Fin.natAdd l) none c) := by
  obtain ⟨i, hi, hpi⟩ := hp
  obtain ⟨j, hj, hqj⟩ := hq
  exact ⟨i + j, Nat.add_le_add hi hj, link_trace p q hpi hb hqj⟩

/-- End-to-end sequential execution from raw program input to canonical output.
The second routine starts with the first routine's actual data, not a reset. -/
theorem link_complete_trace {m : ℕ} (p : Program r s l) (q : Program r s m)
    (input output : List Bool) {n₁ n₂ : ℕ} {b : Cfg r s l}
    (hp : Trace p n₁ (initial p input) b) (hb : b.pc = none)
    (hq : Trace q n₂ (enter q b) (terminal q output)) :
    Trace (link p q) (n₁ + n₂) (initial (link p q) input) (terminal (link p q) output) := by
  rw [← link_initial p q input, ← link_terminal p q output]
  exact link_trace p q hp hb hq

theorem link_complete_runsIn {m : ℕ} (p : Program r s l) (q : Program r s m)
    (input output : List Bool) {n₁ n₂ : ℕ} {b : Cfg r s l}
    (hp : RunsIn p n₁ (initial p input) b) (hb : b.pc = none)
    (hq : RunsIn q n₂ (enter q b) (terminal q output)) :
    RunsIn (link p q) (n₁ + n₂) (initial (link p q) input) (terminal (link p q) output) := by
  rw [← link_initial p q input, ← link_terminal p q output]
  exact link_runsIn p q hp hb hq

end SubexponentialSAT.ProgramLinking

end OAI.Algorithms


namespace OAI.Algorithms

/-!
# Structured invocation of existing finite bit programs

A call contains a fixed finite instruction table. Its execution premise is an
actual trace of that table, rather than a semantic or cost oracle. Compilation
relocates all its instructions and replaces each halt by a return jump. Thus
arbitrary cyclic subroutines can occur inside structured loops without manually
assigning global labels.
-/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

abbrev State := StructuredProgram.State

inductive Cmd (r s : ℕ) where
  | base (c : StructuredProgram.Cmd r s)
  | call {labels : ℕ} (program : Program r s labels)
  | seq (first second : Cmd r s)
  | ite (test : Fin r) (yes no : Cmd r s)
  | while (test : Fin r) (body : Cmd r s)

/-- A call's cost is its actual instruction-trace length, including the source
halt which becomes the compiled return jump. -/
inductive Eval {r s : ℕ} : Cmd r s → ℕ → State r s → State r s → Prop
  | base {c n a b} : StructuredProgram.Eval c n a b → Eval (.base c) n a b
  | call {labels} (p : Program r s labels) {n a b} :
      Trace p n (a.withPC (some p.entry)) (b.withPC none) → Eval (.call p) n a b
  | seq {first second n m a b c} : Eval first n a b → Eval second m b c →
      Eval (.seq first second) (n + m) a c
  | ite_true {test yes no n a b} : a.regs test = true → Eval yes n a b →
      Eval (.ite test yes no) (n + 1) a b
  | ite_false {test yes no n a b} : a.regs test = false → Eval no n a b →
      Eval (.ite test yes no) (n + 1) a b
  | while_false {test body a} : a.regs test = false → Eval (.while test body) 1 a a
  | while_true {test body n m a b c} : a.regs test = true → Eval body n a b →
      Eval (.while test body) m b c → Eval (.while test body) (n + m + 1) a c

abbrev Site {r s : ℕ} : Cmd r s → Type
  | .base c => StructuredProgram.Site c
  | @Cmd.call _ _ labels _ => Fin labels
  | .seq first second => Site first ⊕ Site second
  | .ite _ yes no => Option (Site yes ⊕ Site no)
  | .while _ body => Option (Site body)

abbrev size {r s : ℕ} : Cmd r s → ℕ
  | .base c => StructuredProgram.size c
  | @Cmd.call _ _ labels _ => labels
  | .seq first second => size first + size second
  | .ite _ yes no => size yes + size no + 1
  | .while _ body => size body + 1

/-- Finite control enumeration is computed directly from the fixed syntax. -/
abbrev siteEquiv {r s : ℕ} : (c : Cmd r s) → Site c ≃ Fin (size c)
  | .base c => StructuredProgram.siteEquiv c
  | .call _ => Equiv.refl _
  | .seq first second =>
      ((siteEquiv first).sumCongr (siteEquiv second)).trans finSumFinEquiv
  | .ite _ yes no =>
      (((siteEquiv yes).sumCongr (siteEquiv no)).trans finSumFinEquiv).optionCongr.trans
        (finSuccEquiv _).symm
  | .while _ body => (siteEquiv body).optionCongr.trans (finSuccEquiv _).symm

abbrev entry {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) : Fin l :=
  match c with
  | .base c => StructuredProgram.entry c embed exit
  | .call p => embed p.entry
  | .seq first second =>
      entry first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
  | .ite _ _ _ => embed none
  | .while _ _ => embed none

/-- Calls use the proved concrete instruction relocation, including every
internal branch and each return instruction. -/
abbrev code {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) :
    Site c → Instr r s l :=
  match c with
  | .base c => StructuredProgram.code c embed exit
  | .call p => fun q => ProgramLinking.relocateInstr id id embed (some exit) (p.code q)
  | .seq first second => fun q => match q with
      | .inl x => code first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit) x
      | .inr x => code second (embed ∘ Sum.inr) exit x
  | .ite test yes no => fun q => match q with
      | none => .branch test (entry yes (fun x => embed (some (.inl x))) exit)
          (entry no (fun x => embed (some (.inr x))) exit)
      | some (.inl x) => code yes (fun x => embed (some (.inl x))) exit x
      | some (.inr x) => code no (fun x => embed (some (.inr x))) exit x
  | .while test body => fun q => match q with
      | none => .branch test (entry body (embed ∘ some) (embed none)) exit
      | some x => code body (embed ∘ some) (embed none) x

/-- Exact execution preservation, proved with the concrete subroutine linker
in the call case. -/
theorem eval_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) :
    ∀ {l : ℕ} (p : Program r s l) (embed : Site c → Fin l) (exit : Fin l),
    (∀ q, p.code (embed q) = code c embed exit q) →
    Trace p n (a.withPC (some (entry c embed exit))) (b.withPC (some exit)) := by
  induction h with
  | base he =>
      intro l p embed exit hcode
      exact StructuredProgram.eval_trace he p embed exit hcode
  | @call labels routine n a b ht =>
      intro l p embed exit hcode
      have hrun := ProgramLinking.relocate_trace routine p id id embed (some exit)
        (a.withPC (some (embed routine.entry))) Function.injective_id Function.injective_id
        hcode ht
      simpa [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
        StructuredProgram.State.withPC, entry] using hrun
  | @seq first second n m a b c hf hs ihf ihs =>
      intro l p embed exit hcode
      exact (ihf p (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
        (fun q => hcode (.inl q))).trans
        (ihs p (embed ∘ Sum.inr) exit (fun q => hcode (.inr q)))
  | @ite_true test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q))))
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]
  | @ite_false test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q))))
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_false test body a ht =>
      intro l p embed exit hcode
      refine .cons ?_ (.refl _)
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_true test body n m a b c ht hb hw ihb ihw =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        ((ihb p (embed ∘ some) (embed none) (fun q => hcode (some q))).trans
          (ihw p embed exit hcode))
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]

abbrev labelEquiv {r s : ℕ} (c : Cmd r s) : Option (Site c) ≃ Fin (size c + 1) :=
  (siteEquiv c).optionCongr.trans (finSuccEquiv _).symm

abbrev siteAddress {r s : ℕ} (c : Cmd r s) (q : Site c) : Fin (size c + 1) :=
  labelEquiv c (some q)

abbrev exitAddress {r s : ℕ} (c : Cmd r s) : Fin (size c + 1) := labelEquiv c none

/-- The full finite instruction table is computably generated from the fixed
syntax and finite subroutine tables. No runtime stack data is inspected. -/
def compiled {r s : ℕ} (c : Cmd r s) (inputStack outputStack : Fin s) :
    Program r s (size c + 1) where
  inputStack := inputStack
  outputStack := outputStack
  entry := entry c (siteAddress c) (exitAddress c)
  code label := match (labelEquiv c).symm label with
    | none => .halt
    | some q => code c (siteAddress c) (exitAddress c) q

@[simp] theorem compiled_site {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) (q : Site c) :
    (compiled c inputStack outputStack).code (siteAddress c q) =
      code c (siteAddress c) (exitAddress c) q := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) (some q)) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem compiled_exit {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) :
    (compiled c inputStack outputStack).code (exitAddress c) = Instr.halt := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) none) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

theorem compiled_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) n
      (a.withPC (some (compiled c inputStack outputStack).entry))
      (b.withPC (some (exitAddress c))) :=
  eval_trace h _ _ _ (compiled_site c inputStack outputStack)

theorem compiled_halt_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (a.withPC (some (compiled c inputStack outputStack).entry)) (b.withPC none) := by
  apply (compiled_trace h inputStack outputStack).trans
  refine .cons ?_ (.refl _)
  rw [step]
  simp only [StructuredProgram.State.withPC, Option.map_some]
  rw [compiled_exit]
  rfl

theorem compiled_io_trace {r s : ℕ} {c : Cmd r s} {n : ℕ}
    (inputStack outputStack : Fin s) {input output : List Bool}
    (h : Eval c n (StructuredProgram.ioState inputStack input)
      (StructuredProgram.ioState outputStack output)) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (initial (compiled c inputStack outputStack) input)
      (terminal (compiled c inputStack outputStack) output) :=
  compiled_halt_trace h inputStack outputStack

/-- Mathematical data embedding for a subroutine's assigned ports. The finite
compiled instructions use the port maps directly; they never execute this
Function.extend expression. -/
noncomputable def embedState {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) : State R S :=
  ⟨Function.extend register d.regs frame.regs, Function.extend stack d.stacks frame.stacks⟩

theorem embedState_register {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s)
    (hinj : Function.Injective register) (i : Fin r) :
    (embedState register stack frame d).regs (register i) = d.regs i :=
  hinj.extend_apply _ _ _

theorem embedState_stack {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s)
    (hinj : Function.Injective stack) (i : Fin s) :
    (embedState register stack frame d).stacks (stack i) = d.stacks i :=
  hinj.extend_apply _ _ _

theorem embedState_register_frame {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (i : Fin R)
    (hi : ¬ ∃ j, register j = i) :
    (embedState register stack frame d).regs i = frame.regs i :=
  Function.extend_apply' _ _ _ hi

theorem embedState_stack_frame {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (i : Fin S)
    (hi : ¬ ∃ j, stack j = i) :
    (embedState register stack frame d).stacks i = frame.stacks i :=
  Function.extend_apply' _ _ _ hi

/-- Invoke an existing smaller program using fixed injective port assignments.
Its exact trace count is retained, and all unassigned caller data is framed. -/
theorem eval_call_lifted {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (frame : State R S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {n : ℕ} {a b : State r s}
    (h : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p register stack)) n
      (embedState register stack frame a) (embedState register stack frame b) := by
  apply Eval.call
  simpa [ProgramLinking.embedCfg, ProgramLinking.relocatePc, embedState,
    StructuredProgram.State.withPC, ProgramLinking.liftProgram] using
    ProgramLinking.liftProgram_trace p register stack (frame.withPC none) hregister hstack h

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms


