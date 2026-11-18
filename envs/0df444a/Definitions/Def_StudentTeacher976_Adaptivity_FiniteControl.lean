-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_FiniteControl
-- name    : StudentTeacher976_Adaptivity_FiniteControl
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T01:37:40.110258+00:00
-- url     : https://prove2.me/theorems/30cca961-c014-4320-b4c7-0246cc20f1bc
-- title:
--   Finite-control two-tape oracle programs
-- statement:
--   A finite-control program has a fixed finite state set and a fixed finite tape alphabet containing blank and the two input bits. Each instruction writes and moves the two heads, halts with a Boolean result, or branches on the current oracle query. Its operational semantics retains the complete tapes and head positions.
--
--   The interface also supplies a core semantics for programs without oracle instructions. The core omits visited-cell bookkeeping; it makes no assumption about running time. These programs serve as an intermediate language for explicit machine constructions used in the student–teacher games.
-- source:
--   Operational implementation interface for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, §1.2.1 pp.6–7 and §3.1 p.19. Pinned source: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf. The finite-control language explicitly implements the finite oracle-machine model used by this formalization.

import Definitions.Def_StudentTeacher976_Adaptivity_Complexity
set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl

abbrev Cell (A : Type) := Option (Bool ⊕ A)

inductive Instr (Q A : Type)
  | move (next : Q) (work : Cell A) (wm : Fin 3) (query : Cell A) (qm : Fin 3)
  | stop (result : Bool) (work : Cell A) (wm : Fin 3) (query : Cell A) (qm : Fin 3)
  | ask (yes no : Q)
  | halt (result : Bool)

structure Program (Q A : Type) where
  start : Q
  code : Q → Cell A → Cell A → Instr Q A

structure Cfg (Q A : Type) where
  state : Bool ⊕ Q
  work : ℤ → Cell A
  wh : ℤ
  query : ℤ → Cell A
  qh : ℤ
  wlo : ℤ
  whi : ℤ
  qlo : ℤ
  qhi : ℤ

def bit {A : Type} (b : Bool) : Cell A := some (.inl b)
def readBit {A : Type} : Cell A → Option Bool
  | some (.inl b) => some b
  | _ => none

def readWord {A : Type} (t : ℤ → Cell A) (hi : ℤ) : List Bool :=
  (((List.range (hi + 1).toNat).map (fun i : ℕ => readBit (t (i : ℤ)))).takeWhile
    (·.isSome)).reduceOption

def Program.initial {Q A : Type} (P : Program Q A) (x : List Bool) : Cfg Q A where
  state := .inr P.start
  work := fun i => if 0 ≤ i ∧ i < x.length then bit (x.getD i.toNat false) else none
  wh := 0
  query := fun _ => none
  qh := 0
  wlo := 0
  whi := x.length
  qlo := 0
  qhi := 0

def Program.step {Q A : Type} (P : Program Q A) (O : Oracle) (c : Cfg Q A) : Cfg Q A :=
  match c.state with
  | .inl _ => c
  | .inr q => match P.code q (c.work c.wh) (c.query c.qh) with
    | .halt b => {c with state := .inl b}
    | .ask yes no => {c with state := .inr (if O (readWord c.query c.qhi) then yes else no)}
    | .move q' a wm b qm =>
      let wh := c.wh + (wm.val : ℤ) - 1
      let qh := c.qh + (qm.val : ℤ) - 1
      { state := .inr q'
        work := Function.update c.work c.wh a
        wh := wh
        query := Function.update c.query c.qh b
        qh := qh
        wlo := min c.wlo wh
        whi := max c.whi wh
        qlo := min c.qlo qh
        qhi := max c.qhi qh }

    | .stop result a wm b qm =>
      let wh := c.wh + (wm.val : ℤ) - 1
      let qh := c.qh + (qm.val : ℤ) - 1
      { state := .inl result
        work := Function.update c.work c.wh a
        wh := wh
        query := Function.update c.query c.qh b
        qh := qh
        wlo := min c.wlo wh
        whi := max c.whi wh
        qlo := min c.qlo qh
        qhi := max c.qhi qh }

section Interfaces
variable {Q A : Type}
/-- For programs without oracle calls, only the tapes and heads are needed in
semantic proofs. Bookkeeping bounds are supplied by the compiler simulation. -/
@[ext] structure Core (Q A : Type) where
  state : Bool ⊕ Q
  work : ℤ → Cell A
  wh : ℤ
  query : ℤ → Cell A
  qh : ℤ

def Cfg.core {Q A : Type} (c : Cfg Q A) : Core Q A :=
  ⟨c.state, c.work, c.wh, c.query, c.qh⟩

def Program.Pure (P : Program Q A) : Prop :=
  ∀ q a b yes no, P.code q a b ≠ .ask yes no

def Program.coreStep (P : Program Q A) (c : Core Q A) : Core Q A :=
  match c.state with
  | .inl _ => c
  | .inr q => match P.code q (c.work c.wh) (c.query c.qh) with
    | .halt b => {c with state := .inl b}
    | .ask _ _ => c
    | .move next a wm b qm =>
      { state := .inr next
        work := Function.update c.work c.wh a
        wh := c.wh + (wm.val : ℤ) - 1
        query := Function.update c.query c.qh b
        qh := c.qh + (qm.val : ℤ) - 1 }

    | .stop result a wm b qm =>
      { state := .inl result
        work := Function.update c.work c.wh a
        wh := c.wh + (wm.val : ℤ) - 1
        query := Function.update c.query c.qh b
        qh := c.qh + (qm.val : ℤ) - 1 }

def bitTape {A : Type} (x : List Bool) : ℤ → Cell A :=
  fun i => if 0 ≤ i ∧ i < x.length then bit (x.getD i.toNat false) else none

def Program.coreInitial (P : Program Q A) (x : List Bool) : Core Q A :=
  ⟨.inr P.start, bitTape x, 0, fun _ => none, 0⟩

end Interfaces
end QAdvFew.PoQOracle.OTM.FiniteControl


