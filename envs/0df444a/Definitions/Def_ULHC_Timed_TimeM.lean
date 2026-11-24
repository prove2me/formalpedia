-- Prove2me | Definitions.Def_ULHC_Timed_TimeM
-- name    : ULHC_Timed_TimeM
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:04:20.962028+00:00
-- url     : https://prove2.me/theorems/0799631b-a27f-4631-9885-0c4b546eb9e7
-- title:
--   Time M
-- statement:
--   Definitions and structural lemmas for Time M, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean

import Definitions.Def_ULHC_Algorithm
set_option autoImplicit true
namespace ULHC.T
open Finset
structure TimeM (α : Type) where
  ret : α
  time : ℕ
instance : Monad TimeM where
  pure a := ⟨a, 0⟩
  bind m f := let r := f m.ret; ⟨r.ret, m.time + r.time⟩
variable {α β : Type}
def tick (n : ℕ) : TimeM _root_.Unit := ⟨(), n⟩
def memT [DecidableEq α] (x : α) (s : Finset α) : TimeM Bool := ⟨decide (x ∈ s), 1⟩
def insertT [DecidableEq α] (x : α) (s : Finset α) : TimeM (Finset α) := ⟨insert x s, 1⟩
def eraseT [DecidableEq α] (x : α) (s : Finset α) : TimeM (Finset α) := ⟨s.erase x, 1⟩
def symmDiffT [DecidableEq α] (s E : Finset α) : TimeM (Finset α) := ⟨symmDiff s E, 2 * E.card⟩
def unionT [DecidableEq α] (A B : Finset α) : TimeM (Finset α) := ⟨A ∪ B, A.card + B.card⟩
def cardT (s : Finset α) : TimeM ℕ := ⟨s.card, s.card + 1⟩
def filterT (p : α → TimeM Bool) (s : Finset α) : TimeM (Finset α) :=
  ⟨s.filter (fun x => (p x).ret = true), ∑ x ∈ s, ((p x).time + 1)⟩
def allT (p : α → TimeM Bool) (s : Finset α) : TimeM Bool :=
  ⟨decide (∀ x ∈ s, (p x).ret = true), ∑ x ∈ s, ((p x).time + 1)⟩
def imageT [DecidableEq β] (f : α → TimeM β) (s : Finset α) : TimeM (Finset β) :=
  ⟨s.image (fun x => (f x).ret), ∑ x ∈ s, ((f x).time + 1)⟩
def imageSetsT (f : α → TimeM (Finset Pt)) (s : Finset α) : TimeM (Finset (Finset Pt)) :=
  ⟨s.image (fun x => (f x).ret), ∑ x ∈ s, (let r := f x; r.time + r.ret.card)⟩
def biUnionT [DecidableEq β] (f : α → TimeM (Finset β)) (s : Finset α) : TimeM (Finset β) :=
  ⟨s.biUnion (fun x => (f x).ret), ∑ x ∈ s, (let r := f x; r.time + r.ret.card + 1)⟩
def sortT [LinearOrder α] (s : Finset α) : TimeM (List α) := ⟨s.sort (· ≤ ·), s.card ^ 2⟩
def pickT (S : Finset Pt) : TimeM (Option Pt) := ⟨TF.pick S, 2 * S.card + 2⟩
def lmapT (f : α → TimeM β) (l : List α) : TimeM (List β) :=
  ⟨l.map (fun x => (f x).ret), (l.map (fun x => (f x).time + 1)).sum⟩
def lfilterT (p : α → TimeM Bool) (l : List α) : TimeM (List α) :=
  ⟨l.filter (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩
def lallT (p : α → TimeM Bool) (l : List α) : TimeM Bool :=
  ⟨l.all (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩
def lanyT (p : α → TimeM Bool) (l : List α) : TimeM Bool :=
  ⟨l.any (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩
def lflatMapT (f : α → TimeM (List β)) (l : List α) : TimeM (List β) :=
  ⟨l.flatMap (fun x => (f x).ret), (l.map (fun x => let r := f x; r.time + r.ret.length + 1)).sum⟩
def lfindT (p : α → TimeM Bool) (l : List α) : TimeM (Option α) :=
  ⟨l.find? (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩
def lengthT (l : List α) : TimeM ℕ := ⟨l.length, l.length + 1⟩
def rangeT (n : ℕ) : TimeM (List ℕ) := ⟨List.range n, n + 1⟩
def toFinsetT [DecidableEq α] (l : List α) : TimeM (Finset α) := ⟨l.toFinset, l.length + 1⟩
def eqP (a b : Pt) : Bool := decide (a = b)
def eqE (a b : Edge) : Bool := decide (a = b)
def eqN (a b : ℕ) : Bool := decide (a = b)
def pick2 {β : Type} (a b : Option (ℕ × β)) : Option (ℕ × β) := MP.pick a b
def extend (x : α) (wx : ℕ) (tf : Option (ℕ × List α)) : Option (ℕ × List α) :=
  tf.map (fun r => (wx + r.1, x :: r.2))
def dropW {β : Type} (r : Option (ℕ × β)) : Option β := r.map Prod.snd
def optStrips (c : Pt) (s : Side) (o : Option ℕ) : Finset StripSpec :=
  (o.map (fun n => StripSpec.mk c s n)).toFinset
end ULHC.T


