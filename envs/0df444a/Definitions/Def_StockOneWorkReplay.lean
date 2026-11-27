-- Prove2me | Definitions.Def_StockOneWorkReplay
-- name    : StockOneWorkReplay
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T02:42:12.346462+00:00
-- url     : https://prove2.me/theorems/90b5b038-9c8f-4349-a0ff-5844e6b8f395
-- title:
--   Encoding atomic stock tape machines as native one-work-tape tables
-- statement:
--   Decode a native work-tape zipper into a stock tape. A finite table has one row per stock state and symbol, is active at the right end of the physical input, and reserves states 0, 1, and 2 for initialization.
-- source:
--   Mathlib TM0 and the Complexitylib universal multitape model.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib.Computability.TuringMachine.PostTuringMachine

import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

namespace PvsNP.NativeStockTape

abbrev WorkTape := Turing.MultiTapeTM.Universal.Tape

variable {Γ : Type} [Inhabited Γ]

/-- Read both finite zipper halves as tapes extending by the stock blank. -/
def view (decode : Option ℕ → Γ) (t : WorkTape) : Turing.Tape Γ :=
  Turing.Tape.mk' (Turing.ListBlank.mk (t.left.map decode))
    (Turing.ListBlank.mk (t.right.map decode))

/-- Direct validity of both atomic stock TM0 operations on one work tape. -/
def nativeOp (encode : Γ → Option ℕ) :
    Turing.TM0.Stmt Γ → Option (Option ℕ) × SignType
  | .move .left => (none,.neg)
  | .move .right => (none,.pos)
  | .write a => (some (encode a),.zero)

section

open Turing.MultiTapeTM.Universal

variable {Γ Λ : Type} [Inhabited Λ]

def replayKey (encodeState : Λ ↪ ℕ) (encodeSymbol : Γ → Option ℕ) (q : Λ) (a : Γ) : Key :=
  ⟨encodeState q+3,none,[encodeSymbol a]⟩

def replayRow (M : Turing.TM0.Machine Γ Λ) (encodeState : Λ ↪ ℕ)
    (encodeSymbol : Γ → Option ℕ) (answer : Γ → Option ℕ) (q : Λ) (a : Γ) : Key × Act :=
  (replayKey encodeState encodeSymbol q a,
    match M q a with
    | none => ⟨.zero,[],answer a,none⟩
    | some (next,op) => ⟨.zero,[nativeOp encodeSymbol op],none,some (encodeState next+3)⟩)

noncomputable def replayRows [Fintype Γ] [Fintype Λ] (M : Turing.TM0.Machine Γ Λ)
    (encodeState : Λ ↪ ℕ) (encodeSymbol : Γ → Option ℕ) (answer : Γ → Option ℕ) : List (Key × Act) :=
  (Finset.univ : Finset (Λ × Γ)).toList.map fun p => replayRow M encodeState encodeSymbol answer p.1 p.2

noncomputable def replayDescriptor [Fintype Γ] [Fintype Λ] (M : Turing.TM0.Machine Γ Λ)
    (encodeState : Λ ↪ ℕ) (encodeSymbol : Γ → Option ℕ) (answer : Γ → Option ℕ)
    (setup : List (Key × Act)) : Desc :=
  ⟨1,0,setup ++ replayRows M encodeState encodeSymbol answer⟩

def EncodedTape (encode : Γ → Option ℕ) (t : WorkTape) : Prop :=
  (∀ b ∈ t.left, b ∈ Set.range encode) ∧ ∀ b ∈ t.right, b ∈ Set.range encode

def packConfig (data : List ℕ) (encodeState : Λ ↪ ℕ) (q : Λ) (t : WorkTape) : SCfg :=
  ⟨some (encodeState q+3), data.length+1, [t]⟩

end

end PvsNP.NativeStockTape


