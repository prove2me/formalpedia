-- Prove2me | Definitions.Def_OnlineRegionalTrace
-- name    : OnlineRegionalTrace
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T04:24:02.572041+00:00
-- url     : https://prove2.me/theorems/16a127af-db56-4f92-83cd-fc7a2be315e9
-- title:
--   Regional traces for machines with separately marked input reads
-- statement:
--   A local machine has explicit monotone input reads and ordinary work-tape transitions. A segment reads and writes in its active region, and records which input indices it reads. A joint certificate aligns the two runs at segment boundaries and records agreement on cells transferred at handoffs.
-- source:
--   A trace model for communication rectangles on one-work-tape machines.

import Definitions.Def_SingleTapeWorkBoundary

set_option autoImplicit false

namespace PvsNP.OnlineRegionRead

open WorkBoundarySplice

variable {Q Γ : Type}

inductive Command (Q Γ : Type)
  | localStep (state : Q) (value : Γ) (motion : Motion)
  | read (next : Option Bool → Q)
  | halt

abbrev Program (Q Γ : Type) := Q → Γ → Command Q Γ
abbrev Word := ℕ → Option Bool

structure Cursor (Q Γ : Type) where
  work : Config Q Γ
  input : ℕ

def tick (M : Program Q Γ) (word : Word) (a : Cursor Q Γ) :
    Option (Cursor Q Γ × Option ℕ) :=
  match M a.work.state (a.work.tape a.work.head) with
  | .localStep q value d =>
      some (⟨⟨q,d.shift a.work.head,write a.work.tape a.work.head value⟩,a.input⟩,none)
  | .read next =>
      some (⟨{a.work with state := next (word a.input)}, a.input+1⟩,some a.input)
  | .halt => none

def merge (mask : ℤ → Bool) (owner : Bool) (a outside : Cursor Q Γ) : Cursor Q Γ :=
  {a with work := {a.work with tape := fun i => if mask i = owner then a.work.tape i else outside.work.tape i}}

/-- The pre-step work head remains in the active region. The final
transition may leave it and is included in the segment. -/
inductive Segment (M : Program Q Γ) (word : Word) (mask : ℤ → Bool) (owner : Bool) :
    Cursor Q Γ → Cursor Q Γ → List ℕ → ℕ → Prop
  | refl (a : Cursor Q Γ) : Segment M word mask owner a a [] 0
  | next {a b c : Cursor Q Γ} {scanned : Option ℕ} {more : List ℕ} {n : ℕ} :
      mask a.work.head = owner → tick M word a = some (b,scanned) →
      Segment M word mask owner b c more n →
      Segment M word mask owner a c (scanned.toList ++ more) (n+1)

structure Aligned (a b : Cursor Q Γ) : Prop where
  state : a.work.state = b.work.state
  head : a.work.head = b.work.head
  input : a.input = b.input

def hybridWord (route : ℕ → Bool) (one zero : Word) : Word :=
  fun i => if route i then one i else zero i

inductive Run (M : Program Q Γ) (word : Word) : Cursor Q Γ → Cursor Q Γ → ℕ → Prop
  | refl (a : Cursor Q Γ) : Run M word a a 0
  | next {a b c : Cursor Q Γ} {scanned : Option ℕ} {n : ℕ} :
      tick M word a = some (b,scanned) → Run M word b c n → Run M word a c (n+1)

/-- A trace certificate aligns control, head and input position at segment
boundaries. When ownership changes, the two runs agree on exactly the
transferred cells. Segment clocks may differ across the two runs. -/
inductive JointTrace (M : Program Q Γ) (one zero : Word) (route : ℕ → Bool) :
    (ℤ → Bool) → Cursor Q Γ → Cursor Q Γ →
      (ℤ → Bool) → Cursor Q Γ → Cursor Q Γ → Prop
  | refl (mask : ℤ → Bool) (a b : Cursor Q Γ) : JointTrace M one zero route mask a b mask a b
  | segment {mask after : ℤ → Bool} {owner : Bool} {a a' a'' b b' b'' : Cursor Q Γ}
      {readsA readsB : List ℕ} {n m : ℕ} :
      Aligned a b → Aligned a' b' →
      Segment M one mask owner a a' readsA n → Segment M zero mask owner b b' readsB m →
      (owner = true → ∀ i ∈ readsA, route i = true) →
      (owner = false → ∀ i ∈ readsB, route i = false) →
      JointTrace M one zero route mask a' b' after a'' b'' →
      JointTrace M one zero route mask a b after a'' b''
  | handoff {before switched after : ℤ → Bool} {a a' b b' : Cursor Q Γ} :
      (∀ z, before z ≠ switched z → a.work.tape z = b.work.tape z) →
      JointTrace M one zero route switched a b after a' b' →
      JointTrace M one zero route before a b after a' b'

end PvsNP.OnlineRegionRead


