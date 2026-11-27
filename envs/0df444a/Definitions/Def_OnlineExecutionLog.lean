-- Prove2me | Definitions.Def_OnlineExecutionLog
-- name    : OnlineExecutionLog
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T04:40:55.755917+00:00
-- url     : https://prove2.me/theorems/276caac7-0d28-44ce-b880-3ba5671dd4a9
-- title:
--   Two-phase crossing records for a one-way input machine
-- statement:
--   The work cells have one ownership mask before a handoff and another afterward. A record stores the control state, head position and input index at each ownership change and at the end. The handoff additionally stores the transferred work cells.
-- source:
--   Finite crossing records for an explicit-read work-tape machine.

import Definitions.Def_OnlineRegionalTrace

set_option autoImplicit false

namespace PvsNP.OnlineRegionRead

open WorkBoundarySplice

variable {Q Γ : Type}

structure Stamp (Q : Type) where
  control : Q
  head : ℤ
  input : ℕ
  deriving DecidableEq

def Cursor.stamp (a : Cursor Q Γ) : Stamp Q :=
  ⟨a.work.state,a.work.head,a.input⟩

inductive Boundary (Γ : Type)
  | cross
  | handoff (values : List Γ)
  | finish
  deriving DecidableEq

structure LogEntry (Q Γ : Type) where
  owner : Bool
  atEnd : Stamp Q
  kind : Boundary Γ
  deriving DecidableEq

/-- Control, head and input index are recorded at every owner change and at
the end. The single change of mask also records the transferred cells. -/
inductive Logged (M : Program Q Γ) (word : Word) (mask : Bool → ℤ → Bool) (strip : List ℤ) :
    Bool → Cursor Q Γ → List (LogEntry Q Γ) → Cursor Q Γ → Prop
  | finish {phase owner : Bool} {start finish : Cursor Q Γ} {stamp : Stamp Q}
      {reads : List ℕ} {steps : ℕ} :
      mask phase start.work.head = owner →
      Segment M word (mask phase) owner start finish reads steps →
      finish.stamp = stamp →
      Logged M word mask strip phase start [⟨owner,stamp,.finish⟩] finish
  | cross {phase owner : Bool} {start middle finish : Cursor Q Γ} {stamp : Stamp Q}
      {reads : List ℕ} {steps : ℕ} {tail : List (LogEntry Q Γ)} :
      mask phase start.work.head = owner →
      Segment M word (mask phase) owner start middle reads steps →
      mask phase middle.work.head ≠ owner →
      middle.stamp = stamp →
      Logged M word mask strip phase middle tail finish →
      Logged M word mask strip phase start (⟨owner,stamp,.cross⟩ :: tail) finish
  | handoff {owner : Bool} {start middle finish : Cursor Q Γ} {stamp : Stamp Q}
      {reads : List ℕ} {steps : ℕ} {tail : List (LogEntry Q Γ)} {values : List Γ} :
      mask false start.work.head = owner →
      Segment M word (mask false) owner start middle reads steps →
      middle.stamp = stamp →
      strip.map middle.work.tape = values →
      Logged M word mask strip true middle tail finish →
      Logged M word mask strip false start (⟨owner,stamp,.handoff values⟩ :: tail) finish

def routeFrom : List (LogEntry Q Γ) → ℕ → Bool
  | [], _ => false
  | first :: rest, i => if i < first.atEnd.input then first.owner else routeFrom rest i

/-- A realized route is constant on the contiguous read interval of each
logged region, even when a region has no input reads. -/
def Routes (route : ℕ → Bool) : ℕ → List (LogEntry Q Γ) → Prop
  | _, [] => True
  | start, event :: rest =>
      (∀ i, start ≤ i → i < event.atEnd.input → route i = event.owner) ∧
      Routes route event.atEnd.input rest

def ownerChange (mask : ℤ → Bool) (a b : Cursor Q Γ) : ℕ :=
  if mask a.work.head = mask b.work.head then 0 else 1

def scannedOwners (mask : ℤ → Bool) (a : Cursor Q Γ) (scanned : Option ℕ) : List (ℕ × Bool) :=
  scanned.toList.map fun i => (i,mask a.work.head)

/-- The actual run with a count of adjacent ownership changes and the
owner at each explicit input request. -/
inductive CountedRun (M : Program Q Γ) (word : Word) (mask : ℤ → Bool) :
    Cursor Q Γ → Cursor Q Γ → ℕ → ℕ → List (ℕ × Bool) → Prop
  | refl (a : Cursor Q Γ) : CountedRun M word mask a a 0 0 []
  | next {a b z : Cursor Q Γ} {scanned : Option ℕ} {steps changes : ℕ} {reads : List (ℕ × Bool)} :
      tick M word a = some (b,scanned) →
      CountedRun M word mask b z steps changes reads →
      CountedRun M word mask a z (steps+1) (ownerChange mask a b + changes)
        (scannedOwners mask a scanned ++ reads)

end PvsNP.OnlineRegionRead


