-- Prove2me | Definitions.Def_ArrighiStarFree_HalfLevel_SpaceMachine
-- name    : ArrighiStarFree_HalfLevel_SpaceMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:06:10.677586+00:00
-- url     : https://prove2.me/theorems/d4b37504-76ef-49a4-87fd-adb607dd31db
-- title:
--   Concrete space-bounded machines and promise classes L and NL
-- statement:
--   A machine has fixed finite state and work alphabets and a fixed positive number of work tapes. Its input is read-only with two endmarkers. Each transition reads the control state, the scanned input symbol and one symbol on each work tape; it writes those work cells and moves each head at most one cell. A binary choice supplies nondeterminism. Determinism requires the two choices to give identical actions. A halt label is acceptance or rejection; terminal configurations remain fixed.
--
--   All work tapes start blank at cell zero. Work usage counts all visited cells, including blank cells, summed across tapes. An optional bit is appended to a write-only output stream; neither its content nor its position is readable by the control.
--
--   A promise problem consists of a domain $D$ of legal bit strings and an answer predicate $Y$. Membership in NL asserts
--   $$\exists M,c>0\quad \forall x,\omega,t,\quad \operatorname{space}_M(x,\omega,t)\le c\lfloor\log_2(|x|+2)\rfloor,$$
--   with every branch halting on every string, and $x\in D$ implying that $Y(x)$ holds exactly when some branch accepts. Membership in L additionally requires determinism. Off-promise answers are unconstrained. Ordinary languages use domain all strings. A logspace-computable string map is produced by a deterministic machine satisfying the same space bound and halting with precisely that output on every input.
--
--   The machine and constant are fixed before all inputs. These are resource definitions with explicit transition semantics, independent of any automaton decision problem.
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), §2, printed pp. 23:3–23:4, PDF pp. 3–4; standard finite-tape conventions made explicit

import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

namespace ArrighiStarFree.HalfLevel

inductive HeadMove where
  | left | stay | right
  deriving DecidableEq

def HeadMove.apply : HeadMove → ℕ → ℕ
  | .left, i => i - 1
  | .stay, i => i
  | .right, i => i + 1

inductive InputSymbol where
  | leftEnd | bit (b : Bool) | rightEnd
  deriving DecidableEq

def inputAt (x : List Bool) (i : ℕ) : InputSymbol :=
  if i = 0 then .leftEnd else
    match x[i - 1]? with
    | some b => .bit b
    | none => .rightEnd

/-- A local step: finitely many symbols read/written; at most one cell per head move.
The optional output bit is appended to a write-only output stream. -/
structure SpaceAction (q g k : ℕ) where
  next : Fin (q + 1)
  write : Fin (k + 1) → Fin (g + 1)
  inputMove : HeadMove
  workMove : Fin (k + 1) → HeadMove
  emit : Option Bool

/-- One finite-control multitape machine. A Boolean choice gives binary nondeterminism.
State, alphabet and tape counts are fixed with the machine, never with the input. -/
structure SpaceMachine where
  states : ℕ
  symbols : ℕ
  tapes : ℕ
  start : Fin (states + 1)
  halt : Fin (states + 1) → Option Bool
  transition : Fin (states + 1) → InputSymbol →
    (Fin (tapes + 1) → Fin (symbols + 1)) → Bool → SpaceAction states symbols tapes

structure SpaceConfig (M : SpaceMachine) where
  state : Fin (M.states + 1)
  inputHead : ℕ
  tape : Fin (M.tapes + 1) → ℕ → Fin (M.symbols + 1)
  head : Fin (M.tapes + 1) → ℕ
  visited : Fin (M.tapes + 1) → ℕ
  output : List Bool

def SpaceMachine.initial (M : SpaceMachine) : SpaceConfig M where
  state := M.start
  inputHead := 0
  tape := fun _ _ => 0
  head := fun _ => 0
  visited := fun _ => 1
  output := []

def SpaceMachine.step (M : SpaceMachine) (x : List Bool) (b : Bool)
    (s : SpaceConfig M) : SpaceConfig M :=
  if (M.halt s.state).isSome then s else
    let a := M.transition s.state (inputAt x s.inputHead) (fun i => s.tape i (s.head i)) b
    { state := a.next
      inputHead := min (a.inputMove.apply s.inputHead) (x.length + 1)
      tape := fun i j => if j = s.head i then a.write i else s.tape i j
      head := fun i => (a.workMove i).apply (s.head i)
      visited := fun i => max (s.visited i) ((a.workMove i).apply (s.head i) + 1)
      output := s.output ++ a.emit.toList }

def SpaceMachine.run (M : SpaceMachine) (x : List Bool) (choices : ℕ → Bool) :
    ℕ → SpaceConfig M
  | 0 => M.initial
  | t + 1 => M.step x (choices t) (M.run x choices t)

def SpaceMachine.Deterministic (M : SpaceMachine) : Prop :=
  ∀ q a w, M.transition q a w false = M.transition q a w true

def SpaceMachine.Accepts (M : SpaceMachine) (x : List Bool) : Prop :=
  ∃ choices t, M.halt (M.run x choices t).state = some true

def SpaceMachine.Halts (M : SpaceMachine) (x : List Bool) : Prop :=
  ∀ choices, ∃ t, (M.halt (M.run x choices t).state).isSome = true

/-- One uniform bound on all branches, including rejecting runs and off-promise inputs.
Visits count blank cells as well as written cells, summed over all work tapes. -/
def SpaceMachine.Logspace (M : SpaceMachine) (c : ℕ) : Prop :=
  ∀ x choices t,
    (∑ i : Fin (M.tapes + 1), (M.run x choices t).visited i) ≤ c * Nat.log2 (x.length + 2)

/-- A general promise problem; on its domain, the answer is a Boolean proposition. -/
structure PromiseProblem where
  domain : Set (List Bool)
  answer : List Bool → Prop

def totalProblem (L : Set (List Bool)) : PromiseProblem := ⟨Set.univ, fun x => x ∈ L⟩

def InNL (P : PromiseProblem) : Prop :=
  ∃ (M : SpaceMachine) (c : ℕ), 0 < c ∧ M.Logspace c ∧
    (∀ x, M.Halts x) ∧ ∀ x ∈ P.domain, (M.Accepts x ↔ P.answer x)

def InL (P : PromiseProblem) : Prop :=
  ∃ (M : SpaceMachine) (c : ℕ), 0 < c ∧ M.Deterministic ∧ M.Logspace c ∧
    (∀ x, M.Halts x) ∧ ∀ x ∈ P.domain, (M.Accepts x ↔ P.answer x)

/-- Ordinary deterministic logspace string transduction, with no readable output tape. -/
def LogspaceComputable (f : List Bool → List Bool) : Prop :=
  ∃ (M : SpaceMachine) (c : ℕ), 0 < c ∧ M.Deterministic ∧ M.Logspace c ∧
    ∀ x, ∃ t, M.halt (M.run x (fun _ => false) t).state = some true ∧
      (M.run x (fun _ => false) t).output = f x

end ArrighiStarFree.HalfLevel


