-- Prove2me | Definitions.Def_NativeOnePassCompiler
-- name    : NativeOnePassCompiler
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T02:28:46.713891+00:00
-- url     : https://prove2.me/theorems/7958e139-19c2-5829-9627-b8f9d4ac5a37
-- title:
--   A native one-pass compiler with a copied input tape
-- statement:
--   Copy the binary input to one extra work tape between distinct sentinels. Rewind that tape and simulate the original machine by using the buffered symbol wherever the source reads its input. The physical input head is stationary after copying.
-- source:
--   Copy-and-replay construction in the Complexitylib universal multitape model.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false

namespace NativeOnePass

open Turing.MultiTapeTM.Universal

def tokens (x : List ℕ) : List (Option ℕ) :=
  some 0 :: (x.map (fun a => some (a+2)) ++ [some 1])

def splitTape (cells : List (Option ℕ)) (p : ℕ) : Tape :=
  ⟨p,(cells.take p).reverse,cells.drop p⟩

def bufferTape (x : List ℕ) (p : ℕ) : Tape := splitTape (tokens x) p

/-- The copied input distinguishes both endmarkers from every input symbol. -/
def taggedRead (a : Option ℕ) (left : Bool) : ℕ :=
  match a with
  | some i => i+2
  | none => if left then 0 else 1

/-- Boundary sentinels reproduce the saturation of native input moves. -/
def bufferMove (tag : ℕ) (direction : SignType) : SignType :=
  if tag = 0 ∧ direction = .neg then .zero
  else if tag = 1 ∧ direction = .pos then .zero else direction

def keyAt (q tag : ℕ) (work : List (Option ℕ)) : Key :=
  ⟨q+3,none,some tag :: work⟩

def rowAt (e : Key × Act) (tag : ℕ) : Key × Act :=
  (keyAt e.1.state tag e.1.work,
    ⟨.zero,(none,bufferMove tag e.2.inputTape)::e.2.workTapes,e.2.output,e.2.state.map (·+3)⟩)

def rowsFor (e : Key × Act) : List (Key × Act) :=
  match e.1.input with
  | none => [rowAt e 0,rowAt e 1]
  | some a => [rowAt e (a+2)]

def replayRows (d : Desc) : List (Key × Act) := d.table.flatMap rowsFor

/-- A compiled simulator may prepend arbitrary prefix-control rows in states 0, 1 and 2. -/
def replayDesc (d : Desc) (preamble : List (Key × Act)) : Desc :=
  ⟨d.tapes+1,0,preamble ++ replayRows d⟩

/-- Once copying and rewinding finish, the physical input head stays on the
right endmarker and the added work tape represents the virtual input head. -/
def replayConfig (x : List ℕ) (c : SCfg) : SCfg :=
  ⟨c.state.map (·+3),x.length+1,bufferTape x c.inputPos :: c.workTapes⟩

def setupRow (d : Desc) (q : ℕ) (input tag : Option ℕ)
    (move : SignType) (work : Option (Option ℕ) × SignType) (next : ℕ) : Key × Act :=
  (⟨q,input,tag :: List.replicate d.tapes none⟩,⟨move,[work],none,some next⟩)

/-- The input is binary. States 0, 1 and 2 initialize, copy, and rewind. -/
def copyRows (d : Desc) : List (Key × Act) :=
  [setupRow d 0 none none .zero (some (some 0),.pos) 1,
   setupRow d 0 (some 0) none .zero (some (some 0),.pos) 1,
   setupRow d 0 (some 1) none .zero (some (some 0),.pos) 1,
   setupRow d 1 none none .zero (some (some 1),.neg) 2,
   setupRow d 1 (some 0) none .pos (some (some 2),.pos) 1,
   setupRow d 1 (some 1) none .pos (some (some 3),.pos) 1,
   setupRow d 2 none (some 2) .zero (none,.neg) 2,
   setupRow d 2 none (some 3) .zero (none,.neg) 2,
   setupRow d 2 none (some 0) .zero (none,.pos) (d.q₀+3)]

def onePassDesc (d : Desc) : Desc := replayDesc d (copyRows d)

end NativeOnePass


