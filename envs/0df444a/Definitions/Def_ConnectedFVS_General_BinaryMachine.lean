-- Prove2me | Definitions.Def_ConnectedFVS_General_BinaryMachine
-- name    : ConnectedFVS_General_BinaryMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:17:29.776979+00:00
-- url     : https://prove2.me/theorems/1398debc-8358-477b-a1d8-4c9c679db41b
-- title:
--   Finite binary-stack programs, execution, space and oracle reductions
-- statement:
--   A deterministic program has finitely many control states and a fixed finite positive number of stacks, each with alphabet $\{0,1\}$. Its finite instruction table permits pushing one bit, popping and branching on empty/zero/one, jumping, halting with a Boolean answer, or querying an oracle on the contents of a specified stack. An ordinary program has no query instructions. All stacks are empty initially except stack zero, which contains the input, and control starts at state zero.
--
--   Each instruction takes one step, and halting configurations remain fixed. Space at an instant is one unit of finite control plus the sum of all current stack lengths, including input storage. A bounded run halts by its time limit and satisfies the space limit at every instant through halting; its history is mathematical bookkeeping, not machine memory. Deciding a language means halting on every bit word, accepting exactly its members. An oracle program may also halt within a step bound on the run with a given oracle (`HaltsWithin`), and the word it submits to the oracle in a configuration executing a query is observable (`queryWord`); reductions are stated with these. No source decision oracle is provided. These are general computation definitions, independent of graphs.
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), §2–§3, PDF pp. 3–6; explicit finite-alphabet operational convention

import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ConnectedFVS.General

/-- Finite-control instructions on finitely many binary stacks. `query` is reserved
for oracle reductions; ordinary programs explicitly exclude it. -/
inductive StackInstruction (s q : ℕ) where
  | push (stack : Fin (s + 1)) (bit : Bool) (next : Fin (q + 1))
  | pop (stack : Fin (s + 1)) (empty zero one : Fin (q + 1))
  | jump (next : Fin (q + 1))
  | query (stack : Fin (s + 1)) (no yes : Fin (q + 1))
  | halt (answer : Bool)

structure BinaryMachine where
  stackCount : ℕ
  states : ℕ
  code : Fin (states + 1) → StackInstruction stackCount states

structure BinaryMachine.Config (M : BinaryMachine) where
  pc : Fin (M.states + 1)
  data : Fin (M.stackCount + 1) → List Bool

def BinaryMachine.initial (M : BinaryMachine) (w : List Bool) : M.Config :=
  ⟨0, fun i => if i = 0 then w else []⟩

def BinaryMachine.output (M : BinaryMachine) (c : M.Config) : Option Bool :=
  match M.code c.pc with
  | .halt b => some b
  | _ => none

/-- Each nonhalting instruction costs one step. A halted configuration is fixed. -/
def BinaryMachine.step (M : BinaryMachine) (oracle : List Bool → Bool)
    (c : M.Config) : M.Config :=
  match M.code c.pc with
  | .push i b next => ⟨next, Function.update c.data i (b :: c.data i)⟩
  | .pop i empty zero one =>
      match c.data i with
      | [] => ⟨empty, c.data⟩
      | b :: bs => ⟨if b then one else zero, Function.update c.data i bs⟩
  | .jump next => ⟨next, c.data⟩
  | .query i no yes => ⟨if oracle (c.data i) then yes else no, c.data⟩
  | .halt _ => c

def BinaryMachine.run (M : BinaryMachine) (oracle : List Bool → Bool)
    (w : List Bool) : ℕ → M.Config
  | 0 => M.initial w
  | t + 1 => M.step oracle (M.run oracle w t)

/-- Live bits on all stacks, including the input, and one unit for finite control.
The execution history is not stored by the machine. -/
def BinaryMachine.space (M : BinaryMachine) (c : M.Config) : ℕ :=
  1 + ∑ i, (c.data i).length

def BinaryMachine.Ordinary (M : BinaryMachine) : Prop :=
  ∀ pc, match M.code pc with
    | .query _ _ _ => False
    | _ => True

/-- One total deterministic oracle decider; malformed words belong to neither
decision language and must also receive a correct halting answer. -/
def BinaryMachine.DecidesWith (M : BinaryMachine) (oracle : List Bool → Bool)
    (L : List Bool → Prop) : Prop :=
  ∀ w, ∃ t b, M.output (M.run oracle w t) = some b ∧ (b = true ↔ L w)

def BinaryMachine.Decides (M : BinaryMachine) (L : List Bool → Prop) : Prop :=
  M.Ordinary ∧ M.DecidesWith (fun _ => false) L

/-- Actual halting by T with at most S live cells at every preceding instant. -/
def BinaryMachine.Bounded (M : BinaryMachine) (w : List Bool) (T S : ℕ) : Prop :=
  ∃ t, t ≤ T ∧ (M.output (M.run (fun _ => false) w t)).isSome ∧
    ∀ j ≤ t, M.space (M.run (fun _ => false) w j) ≤ S

def BinaryMachine.TimeBounded (M : BinaryMachine) (w : List Bool) (T : ℕ) : Prop :=
  ∃ t, t ≤ T ∧ (M.output (M.run (fun _ => false) w t)).isSome

/-- Actual halting by step T of the run with the given oracle. -/
def BinaryMachine.HaltsWithin (M : BinaryMachine) (oracle : List Bool → Bool)
    (w : List Bool) (T : ℕ) : Prop :=
  ∃ t, t ≤ T ∧ (M.output (M.run oracle w t)).isSome

/-- The word submitted to the oracle in configuration `c`, if `c` executes a query. -/
def BinaryMachine.queryWord (M : BinaryMachine) (c : M.Config) : Option (List Bool) :=
  match M.code c.pc with
  | .query i _ _ => some (c.data i)
  | _ => none

end ConnectedFVS.General


