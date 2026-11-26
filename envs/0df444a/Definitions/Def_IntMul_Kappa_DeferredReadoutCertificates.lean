-- Prove2me | Definitions.Def_IntMul_Kappa_DeferredReadoutCertificates
-- name    : IntMul_Kappa_DeferredReadoutCertificates
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T07:52:51.361866+00:00
-- url     : https://prove2.me/theorems/a1c1cdc4-e019-4e02-8415-4eb2d22d8ff1
-- title:
--   Rational row certificates for chronological deferred readouts
-- statement:
--   A readout frame is the rational span of a finite list of integer rows in $\mathbb Q^{23}$. A block stores the coordinate rows, the frames, and one chronological list of readout events for each target. An event names its original slot and its frame. Coordinates are stored in five-bit digits with bias 16, with coordinate zero in the least significant digit.
--
--   A change of frame carries a certificate of membership for every earlier generator. A certificate records an integer row identity
--   $$d u=\sum_i c_i v_i,\qquad d>0,$$
--   whose supporting rows belong to the later frame. The three Boolean checks verify the coordinate identities, the edge certificates, and the chronological endpoints. Equal consecutive frames need no certificate.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/joint-frame-stack/check_design.py#L78-L103 and https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/deferred-readout/check_frames.py#L124-L146. Round seven, deferred readout nesting checks.

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.List.Chain

/-! A certificate proves that every generating row of one frame lies in the next
rational row span. Transitivity then gives the inclusion for any two readouts in
their original time order. IDs label rows of the exact integer matrices. -/
namespace IntMul.Kappa.DeferredReadout

abbrev VectorQ (n : Nat) := Fin n → ℚ
abbrev RowTable := Nat → Nat → Int
abbrev Frame := List Nat

def row (n : Nat) (table : RowTable) (r : Nat) : VectorQ n :=
  fun j => (table r j.val : ℚ)

def space (n : Nat) (table : RowTable) (B : Frame) : Submodule ℚ (VectorQ n) :=
  Submodule.span ℚ {x | ∃ r ∈ B, x = row n table r}

/-- A rational row identity with its denominator cleared. A term is a row ID
followed by its signed integer numerator. -/
structure Identity where
  lhs : Nat
  den : Nat
  terms : List (Nat × Int)
deriving Inhabited

def combination (table : RowTable) (terms : List (Nat × Int)) (j : Nat) : Int :=
  match terms with
  | [] => 0
  | (r, c) :: rest => c * table r j + combination table rest j

def validIdentity (n : Nat) (table : RowTable) (e : Identity) : Bool :=
  decide (0 < e.den) && (List.range n).all (fun j =>
    (e.den : Int) * table e.lhs j == combination table e.terms j)

/-- Identity indices are shared across edges; validate each numerical identity
once and check its supporting rows on every edge where it is used. -/
def covers (ids : Nat → Identity) (B : Frame) (r idx : Nat) : Bool :=
  let e := ids idx
  e.lhs == r && e.terms.all (fun t => B.contains t.1)

def edgeCheck (ids : Nat → Identity) (A B : Frame) (refs : List Nat) : Bool :=
  A.all fun r => B.contains r || refs.any (covers ids B r)

structure Edge where
  first : Nat
  second : Nat
  refs : List Nat
deriving Inhabited

/-- Each event retains the source slot. The edge index certifies its transition
to the next event and is unused at the end of a target's timeline. -/
structure Event where
  slot : Nat
  frame : Nat
  edge : Nat
deriving Inhabited

structure Block where
  rows : Array Nat
  frames : Array Frame
  ids : Array Identity
  edges : Array Edge
  targets : Array (List Event)

/-- Every signed coordinate in the source fits in five bits with bias 16. -/
def Block.entry (d : Block) : RowTable := fun r j =>
  (((d.rows[r]?.getD 0 >>> (5 * j)) % 32 : Nat) : Int) - 16

def Block.basis (d : Block) (f : Nat) : Frame := d.frames[f]?.getD []
def Block.identity (d : Block) (i : Nat) : Identity := d.ids[i]?.getD default
def Block.edge (d : Block) (i : Nat) : Edge := d.edges[i]?.getD default

def Block.identitiesOK (d : Block) : Bool := d.ids.toList.all (validIdentity 23 d.entry)

def Block.edgeOK (d : Block) (e : Edge) : Bool :=
  (e.refs.all fun i => decide (i < d.ids.size)) &&
    edgeCheck d.identity (d.basis e.first) (d.basis e.second) e.refs

def Block.edgesOK (d : Block) : Bool := d.edges.toList.all d.edgeOK

def Block.transitionOK (d : Block) (a b : Event) : Bool :=
  a.frame == b.frame || (decide (a.edge < d.edges.size) &&
    (d.edge a.edge).first == a.frame && (d.edge a.edge).second == b.frame)

def Block.timelineOK (d : Block) : List Event → Bool
  | [] | [_] => true
  | a :: b :: rest => d.transitionOK a b && d.timelineOK (b :: rest)

def Block.timelinesOK (d : Block) : Bool := d.targets.toList.all d.timelineOK

def Block.atEvent (d : Block) (e : Event) : Submodule ℚ (VectorQ 23) :=
  space 23 d.entry (d.basis e.frame)

end IntMul.Kappa.DeferredReadout


