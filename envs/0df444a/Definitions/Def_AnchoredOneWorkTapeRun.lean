-- Prove2me | Definitions.Def_AnchoredOneWorkTapeRun
-- name    : AnchoredOneWorkTapeRun
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T06:28:17.748419+00:00
-- url     : https://prove2.me/theorems/7a3a43fd-5ac2-50c0-8e2d-b443829af240
-- title:
--   Segmented runs returning to a fixed work-tape head position
-- statement:
--   A segmented run is a finite succession of bounded-length online work-tape operations whose boundary heads are all at the same absolute position.
-- source:
--   Single-work-tape model with one-way read-only input.

import Mathlib
set_option autoImplicit false
namespace PvsNP.WorkBoundarySplice
/-- A local one-tape move has unit displacement. -/
inductive Motion
  | left
  | stay
  | right

def Motion.shift : Motion → ℤ → ℤ
  | .left, h => h - 1
  | .stay, h => h
  | .right, h => h + 1

structure Config (Q Γ : Type*) where
  state : Q
  head : ℤ
  tape : ℤ → Γ

abbrev Machine (Q Γ : Type*) := Q → Γ → Option (Q × Γ × Motion)

variable {Q Γ : Type*}

def write (tape : ℤ → Γ) (head : ℤ) (value : Γ) (cell : ℤ) : Γ :=
  if cell = head then value else tape cell

end PvsNP.WorkBoundarySplice
namespace PvsNP.OnlineWindowIO
open WorkBoundarySplice
abbrev OnlineMachine (S A : Type) := S → A → Option Bool → Option (S × A × Motion × Bool)

def unreadAfter (consume : Bool) (raw : List Bool) : List Bool :=
  if consume then raw.tail else raw

abbrev OnlineConfig (S A : Type) := Config S A × List Bool

def onlineStep {S A : Type} (M : OnlineMachine S A) (a : OnlineConfig S A) : Option (OnlineConfig S A) :=
  (M a.1.state (a.1.tape a.1.head) a.2.head?).map fun (s,value,d,consume) =>
    (⟨s,d.shift a.1.head,write a.1.tape a.1.head value⟩,unreadAfter consume a.2)

inductive OnlineRun {S A : Type} (M : OnlineMachine S A) :
    OnlineConfig S A → OnlineConfig S A → ℕ → Prop
  | refl (a : OnlineConfig S A) : OnlineRun M a a 0
  | next {a b c : OnlineConfig S A} {n : ℕ} :
      onlineStep M a = some b → OnlineRun M b c n → OnlineRun M a c (n+1)

end PvsNP.OnlineWindowIO
namespace PvsNP.OnlineBoundedConsumer
open WorkBoundarySplice
variable {Q P : Type}
def InWindow (base : ℤ) (w : ℕ) (a : Config Q P) : Prop :=
  base ≤ a.head ∧ a.head < base+(w : ℤ)

end PvsNP.OnlineBoundedConsumer
namespace PvsNP.AnchoredOnlineRun
open OnlineWindowIO
variable {S A : Type}
/-- A sequence of short operations returning the head to the same anchor. -/
inductive Segments (M : OnlineMachine S A) (anchor : ℤ) (limit : ℕ) :
    OnlineConfig S A → OnlineConfig S A → ℕ → Prop
  | nil {a} : a.1.head = anchor → Segments M anchor limit a a 0
  | cons {a b c n k} : a.1.head = anchor → n ≤ limit → OnlineRun M a b n →
      Segments M anchor limit b c k → Segments M anchor limit a c (n+k)

end PvsNP.AnchoredOnlineRun


