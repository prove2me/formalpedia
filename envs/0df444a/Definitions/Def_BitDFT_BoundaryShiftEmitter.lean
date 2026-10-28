-- Prove2me | Definitions.Def_BitDFT_BoundaryShiftEmitter
-- name    : BitDFT_BoundaryShiftEmitter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T20:50:49.813626+00:00
-- url     : https://prove2.me/theorems/9e1c3dff-1910-4c63-8188-da982ddd287f
-- title:
--   Emit a signed fixed-point boundary shift from staged tapes
-- statement:
--   A finite multitape controller reads a staged signed coordinate, its high-magnitude bit, the dimension word, and the low payload. It copies the sign bit, skips the high bit, copies the dimension word, and emits one zero bit for each low payload bit. For valid staged binary words, its phase sequence is sign, skip-high, dimension-copy, zero-write, halt. The controller uses a fixed number of states independent of the word lengths; the corresponding run length is dimensionBits.length + low.length + 4.
-- source:
--   Concrete output-emission component for the integer-multiplication to finite-precision DFT rescaling construction.

import Definitions.Def_BitDFT_MachineSequence

set_option autoImplicit false

namespace BitDFT.BoundaryShiftEmitter
open IntMul MachineSequence

inductive State
  | sign | skipHigh | copyDimension | writeZeros | halt
  deriving DecidableEq

noncomputable instance : Fintype State where
  elems := {.sign, .skipHigh, .copyDimension, .writeZeros, .halt}
  complete := by intro q; cases q <;> simp

noncomputable def protect {N : MultitapeTM} (old write : N.Sym) (move : Move) : N.Sym × Move := by
  classical
  exact if old = N.startSym then (N.startSym, if move = .left then .stay else move)
    else (if write = N.startSym then old else write, move)

private theorem protect_self {N : MultitapeTM} (a : N.Sym) :
    protect a a .stay = (a, .stay) := by
  classical
  by_cases h : a = N.startSym <;> simp [protect, h]

noncomputable def raw (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (q : State) (a : Fin N.k → N.Sym) :
    State × (Fin N.k → N.Sym × Move) := by
  classical
  exact match q with
  | .sign => (.skipHigh, fun i =>
      (if i = output then a coordinate else a i,
        if i = coordinate ∨ i = output then .right else .stay))
  | .skipHigh => (.copyDimension, fun i =>
      (a i, if i = coordinate then .right else .stay))
  | .copyDimension =>
      if a dimension = N.zero ∨ a dimension = N.one then
        (.copyDimension, fun i =>
          (if i = output then a dimension else a i,
            if i = dimension ∨ i = output then .right else .stay))
      else (.writeZeros, fun i => (a i, .stay))
  | .writeZeros =>
      if a coordinate = N.zero ∨ a coordinate = N.one then
        (.writeZeros, fun i =>
          (if i = output then N.zero else a i,
            if i = coordinate ∨ i = output then .right else .stay))
      else (.halt, fun i => (a i, .stay))
  | .halt => (.halt, fun i => (a i, .stay))

noncomputable def transition (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (q : State) (a : Fin N.k → N.Sym) :
    State × (Fin N.k → N.Sym × Move) := by
  classical
  let r := raw N coordinate dimension output q a
  exact (r.1, fun i => protect (a i) (r.2 i).1 (r.2 i).2)

noncomputable def control (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output) :
    Controller N where
  K := State
  entry := .sign
  exit := .halt
  distinct := by decide
  transition := transition N coordinate dimension output
  marker := by
    intro q a i hi
    classical
    change (protect (a i) ((raw N coordinate dimension output q a).2 i).1
      ((raw N coordinate dimension output q a).2 i).2).1 = N.startSym ∧
      (protect (a i) ((raw N coordinate dimension output q a).2 i).1
        ((raw N coordinate dimension output q a).2 i).2).2 ≠ .left
    rw [hi]
    simp only [protect, if_pos rfl]
    constructor
    · rfl
    · cases ((raw N coordinate dimension output q a).2 i).2 <;> simp
  noMarker := by
    intro q a i hi
    classical
    change (protect (a i) ((raw N coordinate dimension output q a).2 i).1
      ((raw N coordinate dimension output q a).2 i).2).1 ≠ N.startSym
    have hs : a i ≠ N.startSym := by intro he; exact hi he
    by_cases hw : ((raw N coordinate dimension output q a).2 i).1 = N.startSym
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
    have hci : N.inTape ≠ coordinate := Ne.symm hc
    have hdi : N.inTape ≠ dimension := Ne.symm hd
    have hoi : N.inTape ≠ output := Ne.symm ho
    have hstay : (raw N coordinate dimension output q a).2 N.inTape =
        (a N.inTape, .stay) := by
      cases q <;> simp [raw, hci, hdi, hoi] <;> split_ifs <;> simp_all
    change (protect (a N.inTape) ((raw N coordinate dimension output q a).2 N.inTape).1
      ((raw N coordinate dimension output q a).2 N.inTape).2).1 = a N.inTape
    rw [hstay]
    exact congrArg Prod.fst (protect_self (a N.inTape))

noncomputable abbrev machine (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output) :=
  (control N coordinate dimension output hc hd ho hcd hco hdo).machine

noncomputable def frame {N : MultitapeTM} (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (q : State) (coordinateWord dimensionWord outputWord : List Bool)
    (coordinateHead dimensionHead outputHead : ℕ) :
    (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg where
  state := q
  cells := fun i => if i = coordinate then N.tapeOf (coordinateWord.map N.bitSym)
    else if i = dimension then N.tapeOf (dimensionWord.map N.bitSym)
    else if i = output then N.tapeOf (outputWord.map N.bitSym) else base.cells i
  head := fun i => if i = coordinate then coordinateHead
    else if i = dimension then dimensionHead else if i = output then outputHead else base.head i

end BitDFT.BoundaryShiftEmitter


