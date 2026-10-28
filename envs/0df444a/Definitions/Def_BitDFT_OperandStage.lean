-- Prove2me | Definitions.Def_BitDFT_OperandStage
-- name    : BitDFT_OperandStage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T15:03:42.628998+00:00
-- url     : https://prove2.me/theorems/60873beb-8051-4da5-9752-d8f11a854ce5
-- title:
--   A finite controller for placing a dimension and coordinate in a multiplier caller buffer
-- statement:
--   A finite multitape controller stages two binary operands in an integer multiplier caller buffer. It writes a zero prefix, scans and copies a dimension word in reverse into its padded field, writes a separator, and copies a coordinate word. The controller is parameterized by source tapes and buffer tape, so its transition table works uniformly at every precision.
-- source:
--   Reusable finite-state component for the integer-multiplication-to-Fourier output scaling construction. Exact execution and tape-layout theorems are stated separately.

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_MachineSequence
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace BitDFT.OperandStage
open IntMul MachineSequence

inductive State
  | skipSign | skipHigh | fillZeros | seekDimension | copyDimensionBackward
  | alignDimension | writeSeparator | rewindCoordinate | skipSignAgain
  | skipHighAgain | copyCoordinate | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.skipSign,.skipHigh,.fillZeros,.seekDimension,.copyDimensionBackward,
    .alignDimension,.writeSeparator,.rewindCoordinate,.skipSignAgain,.skipHighAgain,
    .copyCoordinate,.halt}
  complete := by intro q; cases q <;> simp

def protect {N : MultitapeTM} (old write : N.Sym) (move : Move) : N.Sym × Move := by
  classical
  exact if old = N.startSym then (N.startSym, if move = .left then .stay else move)
    else (if write = N.startSym then old else write, move)

private theorem protect_self {N : MultitapeTM} (a : N.Sym) :
    protect a a .stay = (a,.stay) := by
  classical
  by_cases h : a = N.startSym <;> simp [protect,h]

/-- Read a signed coordinate and the parsed dimension from disjoint host banks.
    On exit, tape `out` contains `bin q n ++ sep ++` the coordinate's low q bits,
    exactly in the tracked-call caller-buffer alphabet. -/
def raw (N : MultitapeTM) (coord dim out : Fin N.k) (q : State)
    (a : Fin N.k → N.Sym) : State × (Fin N.k → N.Sym × Move) := by
  classical
  exact match q with
  | .skipSign => (.skipHigh, fun i => (a i,
      if i = coord ∨ i = out then .right else .stay))
  | .skipHigh => (.fillZeros, fun i => (a i, if i = coord then .right else .stay))
  | .fillZeros =>
      if a coord = N.zero ∨ a coord = N.one then
        (.fillZeros, fun i => (if i = out then N.zero else a i,
          if i = coord ∨ i = out then .right else .stay))
      else (.seekDimension, fun i => (a i,.stay))
  | .seekDimension =>
      if a dim = N.zero ∨ a dim = N.one then
        (.seekDimension, fun i => (a i, if i = dim then .right else .stay))
      else (.copyDimensionBackward, fun i =>
        (a i, if i = dim then .left else if i = out then .left else .stay))
  | .copyDimensionBackward =>
      if a dim = N.zero ∨ a dim = N.one then
        (.copyDimensionBackward, fun i => (if i = out then a dim else a i,
          if i = dim ∨ i = out then .left else .stay))
      else (.alignDimension, fun i =>
        (a i, if i = dim ∨ i = out then .right else .stay))
  | .alignDimension =>
      if a dim = N.zero ∨ a dim = N.one then
        (.alignDimension, fun i => (a i, if i = dim ∨ i = out then .right else .stay))
      else (.writeSeparator, fun i => (a i,.stay))
  | .writeSeparator =>
      (.rewindCoordinate, fun i => (if i = out then N.sep else a i,
        if i = out then .right else .stay))
  | .rewindCoordinate =>
      if a coord = N.startSym then
        (.skipSignAgain, fun i => (a i, if i = coord then .right else .stay))
      else (.rewindCoordinate, fun i => (a i, if i = coord then .left else .stay))
  | .skipSignAgain =>
      (.skipHighAgain, fun i => (a i, if i = coord then .right else .stay))
  | .skipHighAgain =>
      (.copyCoordinate, fun i => (a i, if i = coord then .right else .stay))
  | .copyCoordinate =>
      if a coord = N.zero ∨ a coord = N.one then
        (.copyCoordinate, fun i => (if i = out then a coord else a i,
          if i = coord ∨ i = out then .right else .stay))
      else (.halt, fun i => (a i,.stay))
  | .halt => (.halt, fun i => (a i,.stay))

def transition (N : MultitapeTM) (coord dim out : Fin N.k) (q : State)
    (a : Fin N.k → N.Sym) : State × (Fin N.k → N.Sym × Move) := by
  classical
  let r := raw N coord dim out q a
  exact (r.1, fun i => protect (a i) (r.2 i).1 (r.2 i).2)

def control (N : MultitapeTM) (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out) : Controller N where
  K := State
  entry := .skipSign
  exit := .halt
  distinct := by decide
  transition := transition N coord dim out
  marker := by
    intro q a i hi
    classical
    change (protect (a i) ((raw N coord dim out q a).2 i).1
      ((raw N coord dim out q a).2 i).2).1 = N.startSym ∧
      (protect (a i) ((raw N coord dim out q a).2 i).1
        ((raw N coord dim out q a).2 i).2).2 ≠ .left
    rw [hi]
    simp only [protect, if_pos rfl]
    constructor
    · rfl
    · cases ((raw N coord dim out q a).2 i).2 <;> simp
  noMarker := by
    intro q a i hi
    classical
    change (protect (a i) ((raw N coord dim out q a).2 i).1
      ((raw N coord dim out q a).2 i).2).1 ≠ N.startSym
    have hs : a i ≠ N.startSym := by intro he; exact hi he
    by_cases hw : ((raw N coord dim out q a).2 i).1 = N.startSym
    · simp [protect, hs, hw]
    · simp [protect, hs, hw]
  frozen := by
    intro a
    apply Prod.ext
    · rfl
    · funext i
      exact protect_self _
  readonly := by
    intro q a
    classical
    have hci : N.inTape ≠ coord := Ne.symm hc
    have hdi : N.inTape ≠ dim := Ne.symm hd
    have hoi : N.inTape ≠ out := Ne.symm ho
    have hstay : ((raw N coord dim out q a).2 N.inTape) = (a N.inTape,.stay) := by
      cases q <;> simp [raw,hci,hdi,hoi] <;> split_ifs <;> simp_all
    change (protect (a N.inTape) ((raw N coord dim out q a).2 N.inTape).1
      ((raw N coord dim out q a).2 N.inTape).2).1 = a N.inTape
    rw [hstay]
    exact congrArg Prod.fst (protect_self (a N.inTape))

abbrev machine (N : MultitapeTM) (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out) :=
  (control N coord dim out hc hd ho hcd hco hdo).machine

end BitDFT.OperandStage
end


