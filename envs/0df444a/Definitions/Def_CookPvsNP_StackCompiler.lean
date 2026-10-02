-- Prove2me | Definitions.Def_CookPvsNP_StackCompiler
-- name    : CookPvsNP_StackCompiler
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T11:01:22.431012+00:00
-- url     : https://prove2.me/theorems/4db1eb41-5f4e-482f-86d0-d3e2ec7f5967
-- title:
--   A concrete one-tape Cook compiler for finite stack machines
-- statement:
--   The tape alphabet contains tagged input, output, origin, and finite stack columns. Setup places an origin and converts input; each source instruction performs a right and left sweep; cleanup emits the designated output stack and returns to its beginning. Every state and work symbol belongs to a fixed finite type chosen before the input.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackModel

set_option autoImplicit false
namespace CookPvsNP

inductive StackSym (K A : Type) where
  | input (a : A)
  | output (a : A)
  | origin
  | work (c : StackCol K A)

noncomputable instance {K A : Type} : DecidableEq (StackSym K A) := Classical.decEq _
noncomputable instance {K A : Type} [Fintype K] [Fintype A] : Fintype (StackSym K A) := by
  classical
  exact Fintype.ofInjective (fun s : StackSym K A => match s with
    | .input x => ((0 : Fin 4), some x, none)
    | .output x => (1, some x, none)
    | .origin => (2, none, none)
    | .work c => (3, none, some c))
    (by intro x y h; cases x <;> cases y <;> simp_all)

inductive StackQ (K A Q : Type) where
  | start
  | mark
  | setup
  | setupBack
  | ready (q : Q)
  | scanR (q : Q) (a : K → StackAct A) (carry : StackCol K A)
  | scanL (q : Q) (a : K → StackAct A) (carry : StackCol K A)
  | clean
  | cleanBack
  | accept
  | reject

noncomputable instance {K A Q : Type} : DecidableEq (StackQ K A Q) := Classical.decEq _
noncomputable instance {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q] :
    Fintype (StackQ K A Q) := by
  classical
  exact Fintype.ofInjective (fun s : StackQ K A Q => match s with
    | .start => ((0 : Fin 11), none, none, none)
    | .mark => (1, none, none, none)
    | .setup => (2, none, none, none)
    | .setupBack => (3, none, none, none)
    | .ready q => (4, some q, none, none)
    | .scanR q a c => (5, some q, some a, some c)
    | .scanL q a c => (6, some q, some a, some c)
    | .clean => (7, none, none, none)
    | .cleanBack => (8, none, none, none)
    | .accept => (9, none, none, none)
    | .reject => (10, none, none, none))
    (by intro x y h; cases x <;> cases y <;> simp_all)

def stackInput {K A : Type} : A ↪ StackSym K A :=
  ⟨StackSym.input, by intro x y h; cases h; rfl⟩

def stackOutput {K A : Type} : A ↪ StackSym K A :=
  ⟨StackSym.output, by intro x y h; cases h; rfl⟩

def stackInitialCol {K A : Type} [DecidableEq K] (ki : K) (x : A) : StackCol K A :=
  fun k => if k = ki then some x else none

/-- Concrete Cook machine: each stack instruction takes one right and one left sweep. -/
noncomputable def stackTM {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) : TM (StackSym K A) where
  Q := StackQ K A Q
  q₀ := .start
  qaccept := .accept
  qreject := .reject
  accept_ne_reject := by intro h; cases h
  δ := fun q s =>
    match q with
    | .start => (.mark, s, .left)
    | .mark => (.setup, some .origin, .right)
    | .setup => match s with
      | some (.input x) => (.setup, some (.work (stackInitialCol ki x)), .right)
      | _ => (.setupBack, some (.work stackZero), .left)
    | .setupBack => match s with
      | some .origin => (.ready P.initial, s, .right)
      | _ => (.setupBack, s, .left)
    | .ready q => match s with
      | some (.work x) =>
        if P.done q then (.clean, (x ko).map StackSym.output, .right) else
          let d := P.next q x
          (.scanR d.1 d.2 (stackPushNext d.2 x),
            some (.work (stackPushCell d.2 (stackPushCarry d.2) x)), .right)
      | _ => (.reject, s, .right)
    | .scanR q a c => match s with
      | some (.work x) =>
        (.scanR q a (stackPushNext a x), some (.work (stackPushCell a c x)), .right)
      | _ => (.scanL q a c, some (.work c), .left)
    | .scanL q a c => match s with
      | some (.work x) =>
        (.scanL q a x, some (.work (stackPopCell a c x)), .left)
      | some .origin => (.ready q, s, .right)
      | _ => (.reject, s, .right)
    | .clean => match s with
      | some (.work x) => (.clean, (x ko).map StackSym.output, .right)
      | _ => (.cleanBack, none, .left)
    | .cleanBack => match s with
      | some .origin => (.accept, s, .right)
      | _ => (.cleanBack, s, .left)
    | .accept => (.accept, s, .right)
    | .reject => (.reject, s, .right)

def stackFrame {K A Q : Type} (q : Q) (r : List (StackCol K A)) :
    Cfg (StackSym K A) (StackQ K A Q) :=
  ⟨.ready q, [some .origin],
    (r.map (some ∘ StackSym.work)).headD none,
    (r.map (some ∘ StackSym.work)).tail⟩

end CookPvsNP


