-- Prove2me | Definitions.Def_NativeOnlineSingleTape
-- name    : NativeOnlineSingleTape
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T04:18:42.954804+00:00
-- url     : https://prove2.me/theorems/b1cf544b-6ce3-5769-b958-a22159031715
-- title:
--   Native descriptors for finite online single-work-tape programs
-- statement:
--   Each local instruction depends on the control, the currently scanned work cell, and the current input symbol or EOF. The input move is stay or right. The compiler lists all finite states and symbols in the native universal table.
-- source:
--   A finite transition compiler for an online work-tape model.

import Definitions.Def_SingleTapeWorkBoundary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Correct

set_option autoImplicit false

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

namespace PvsNP.OnlineWindowIO.Native

open WorkBoundarySplice
open Turing.MultiTapeTM.Universal

variable {S A : Type}

def motion : Motion → SignType
  | .left => .neg
  | .stay => .zero
  | .right => .pos

def rawCode : Option Bool → Option ℕ := Option.map Bool.toNat

def rowKey (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (e : S × A × Option Bool) : Key :=
  ⟨state e.1,rawCode e.2.2,[symbol e.2.1]⟩

def action (M : OnlineMachine S A) (state : S ↪ ℕ) (symbol : A ↪ Option ℕ)
    (verdict : S → Option ℕ) (e : S × A × Option Bool) : Act :=
  match M e.1 e.2.1 e.2.2 with
  | none => ⟨.zero,[],verdict e.1,none⟩
  | some (next,value,d,advance) =>
      ⟨if advance then .pos else .zero,[(some (symbol value),motion d)],none,some (state next)⟩

noncomputable def desc [Fintype S] [Fintype A] (M : OnlineMachine S A)
    (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (initial : S) (verdict : S → Option ℕ) : Desc :=
  let rows := (Finset.univ : Finset (S × A × Option Bool)).toList
  ⟨1,state initial,rows.map fun e => (rowKey state symbol e,action M state symbol verdict e)⟩

end PvsNP.OnlineWindowIO.Native


