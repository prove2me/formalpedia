-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Layout
-- name    : MIPRE_TM_CookLevin_Layout
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:00:35.802094+00:00
-- url     : https://prove2.me/theorems/314c0fb7-c928-48d8-862e-e646bcd72f14
-- title:
--   Definitions of Layout: The variable format of the describer The binary format of the variables of the Cook–Levin tableau of the interpreter…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Layout` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The variable format of the describer. The binary format of the variables of the Cook–Levin tableau of the interpreter machine `U` (`planning/succinct-cook-levin.md`, S3). An index is a list of `m` bits, least significant first. With its top bit set it is *structured*: a tag (3 bits), the time `t` (`W` bits), the tape `d` (4), the position `p` (`W`), the cell value `v` (3), the state `q` (`Qb`), the thirteen window centers (`13 W`) and the gate `g` (`Gb`); tags `0..6` are `cell`, `head`, `state`, `emitOne`, `emitBad`, `emitted`, `aux`. With its top bit clear and value `j < 4T` it is an…
--
--   **Definitions** (30): `MIPRE.TM.CookLevin.Desc.Fields` (The fields read from an index: the top bit, the structured fields, and for an answer index the decoded tape, position and value with the…); `MIPRE.TM.CookLevin.Desc.Gb` (The width of the gate field for a check circuit of `G` gates.); `MIPRE.TM.CookLevin.Desc.QC` (The number of states, including the halting state.); `MIPRE.TM.CookLevin.Desc.Qb` (The width of the state field.); `MIPRE.TM.CookLevin.Desc.Sof` (The tableau length.); `MIPRE.TM.CookLevin.Desc.W` (The width of the time, position and center fields: `W = e + 4`, where `S = 2^e`.); `MIPRE.TM.CookLevin.Desc.bitField` (The value of the bits `off ..); `MIPRE.TM.CookLevin.Desc.dOff`; `MIPRE.TM.CookLevin.Desc.decodeVar` (The tableau variable denoted by the fields of an index, if any.); `MIPRE.TM.CookLevin.Desc.encodeVar` (The structured index of a tableau variable.); `MIPRE.TM.CookLevin.Desc.fieldsOf` (The fields of the index `ib` (a bit string of length `m`), for the answer length `T`.); `MIPRE.TM.CookLevin.Desc.flagOff`; `MIPRE.TM.CookLevin.Desc.gOff`; `MIPRE.TM.CookLevin.Desc.jsFun` (The window centers of an `aux` variable as a function on tape codes.); `MIPRE.TM.CookLevin.Desc.jsOff`; `MIPRE.TM.CookLevin.Desc.jsPack` (The `w`-bit fields `js a, …, js (a + n - 1)`, concatenated.); `MIPRE.TM.CookLevin.Desc.mOf` (The index width.); `MIPRE.TM.CookLevin.Desc.nbits` (The `w`-bit binary representation of `n`, least significant bit first.); `MIPRE.TM.CookLevin.Desc.pOff`; and 0 more.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_jsPack`, `length_nbits`, `tapeCode_lt`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Layout` (`MIPRE/TM/CookLevin/Layout.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 21 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Layout.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Layout.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine

/-!
# The variable format of the describer

The binary format of the variables of the Cook–Levin tableau of the interpreter machine
`U` (`planning/succinct-cook-levin.md`, S3). An index is a list of `m` bits, least
significant first. With its top bit set it is *structured*: a tag (3 bits), the time `t`
(`W` bits), the tape `d` (4), the position `p` (`W`), the cell value `v` (3), the state `q`
(`Qb`), the thirteen window centers (`13 W`) and the gate `g` (`Gb`); tags `0..6` are
`cell`, `head`, `state`, `emitOne`, `emitBad`, `emitted`, `aux`. With its top bit clear and
value `j < 4T` it is an *answer* variable: the cell at position `j' / 2 + 3` of tape `A` (for
`j < 2T`, `j' = j`) or `B` (`j' = j - 2T`), with the value blank for `j'` even and `1` for `j'`
odd, so that the first `4T` variables are the `tapeBits` of the two answers.

`fieldsOf` reads the fields of an index, `decodeVar` the tableau variable they denote (if
any), and `encodeVar` is the structured index of a variable; `decodeVar_encodeVar` is the
round trip. The circuit computes exactly `fieldsOf` on its input bits (`FieldFml.lean`).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## Codes of symbols, tapes and states -/

/-- The code of a cell value. -/
def symCode : CellVal Sym → ℕ
  | .sym .zero => 0
  | .sym .one => 1
  | .sym .sep => 2
  | .sym .fr => 3
  | .sym .en => 4
  | .blank => 5
  | .bdry => 6

/-- The cell value of a code. -/
def symOfCode : ℕ → Option (CellVal Sym)
  | 0 => some (.sym .zero)
  | 1 => some (.sym .one)
  | 2 => some (.sym .sep)
  | 3 => some (.sym .fr)
  | 4 => some (.sym .en)
  | 5 => some .blank
  | 6 => some .bdry
  | _ => none

/-- The code of a tape: the input tapes `0..6`, the work tapes `7..12`. -/
def tapeCode : Tape 7 6 → ℕ
  | .inl j => j
  | .inr j => 7 + j

/-- The tape of a code. -/
def tapeOfCode (d : ℕ) : Option (Tape 7 6) :=
  if h : d < 7 then some (.inl ⟨d, h⟩) else if h' : d < 13 then some (.inr ⟨d - 7, by omega⟩) else none

theorem tapeCode_lt (d : Tape 7 6) : tapeCode d < 13 := by
  rcases d with ⟨j, hj⟩ | ⟨j, hj⟩ <;> simp [tapeCode] <;> omega

/-- The number of states, including the halting state. Irreducible: a definitional
unfolding evaluates `Fintype.card (Option Ctl)`, which does not terminate in practice. -/
@[irreducible] def QC : ℕ := Fintype.card (Option Ctl)

/-- The code of a state. -/
noncomputable def qCode (q : Option Ctl) : ℕ := Fintype.equivFin (Option Ctl) q

/-- The state of a code. -/
noncomputable def qOfCode (k : ℕ) : Option (Option Ctl) :=
  if h : k < QC then some ((Fintype.equivFin (Option Ctl)).symm ⟨k, by unfold QC at h; exact h⟩) else none

/-! ## Widths and offsets -/

/-- The width of the state field. -/
@[irreducible] def Qb : ℕ := Nat.size QC

/-- The width of the time, position and center fields: `W = e + 4`, where `S = 2^e`. -/
def W (e : ℕ) : ℕ := e + 4

/-- The tableau length. -/
def Sof (e : ℕ) : ℕ := 2 ^ e

/-- The width of the gate field for a check circuit of `G` gates. -/
def Gb (G : ℕ) : ℕ := Nat.size G

/-- The offsets of the fields of a structured index. -/
def tagOff : ℕ := 0
def tOff : ℕ := 3
def dOff (e : ℕ) : ℕ := 3 + W e
def pOff (e : ℕ) : ℕ := 7 + W e
def vOff (e : ℕ) : ℕ := 7 + 2 * W e
def qOff (e : ℕ) : ℕ := 10 + 2 * W e
def jsOff (e : ℕ) (d : ℕ) : ℕ := 10 + 2 * W e + Qb + d * W e
def gOff (e : ℕ) : ℕ := 10 + 15 * W e + Qb
def flagOff (e G : ℕ) : ℕ := 10 + 15 * W e + Qb + Gb G

/-- The index width. -/
def mOf (e G : ℕ) : ℕ := 11 + 15 * W e + Qb + Gb G

/-! ## Bit strings and numbers -/

/-- The value of the bits `off .. off + w` of a bit string. -/
def bitField (ib : BitStr) (off w : ℕ) : ℕ := bitsVal ((ib.drop off).take w)

/-! ## The fields of an index -/

/-- The fields read from an index: the top bit, the structured fields, and for an answer
index the decoded tape, position and value with the range check `ansOk`. -/
structure Fields where
  flag : Bool
  tag : ℕ
  t : ℕ
  d : ℕ
  p : ℕ
  v : ℕ
  q : ℕ
  js : Fin 13 → ℕ
  g : ℕ
  ansOk : Bool

/-- The fields of the index `ib` (a bit string of length `m`), for the answer length `T`. -/
def fieldsOf (e G T : ℕ) (ib : BitStr) : Fields :=
  if ib.getD (flagOff e G) false then
    { flag := true, tag := bitField ib tagOff 3, t := bitField ib tOff (W e), d := bitField ib (dOff e) 4,
      p := bitField ib (pOff e) (W e), v := bitField ib (vOff e) 3, q := bitField ib (qOff e) Qb,
      js := fun d => bitField ib (jsOff e d) (W e), g := bitField ib (gOff e) (Gb G), ansOk := false }
  else
    let j := bitField ib 0 (flagOff e G)
    let r := if j < 2 * T then j else j - 2 * T
    { flag := false, tag := 0, t := 0, d := if j < 2 * T then 5 else 6, p := (r / 2 + 3) % 2 ^ W e,
      v := if r % 2 = 1 then 1 else 5, q := 0, js := fun _ => 0, g := 0, ansOk := decide (j < 4 * T) }

/-! ## Decoding -/

section Decode

variable (e G : ℕ)

/-- The tableau variable denoted by the fields of an index, if any. -/
noncomputable def decodeVar (F : Fields) : Option (TabVar 7 6 Sym Ctl (Sof e) G) :=
  if F.flag then
    if F.tag = 0 then
      if h : F.t ≤ (Sof e) ∧ F.p < numCells (Sof e) then
        match tapeOfCode F.d, symOfCode F.v with
        | some d, some v => some (.cell ⟨F.t, by omega⟩ d ⟨F.p, h.2⟩ v)
        | _, _ => none
      else none
    else if F.tag = 1 then
      if h : F.t ≤ (Sof e) ∧ F.p < numCells (Sof e) then
        match tapeOfCode F.d with
        | some d => some (.head ⟨F.t, by omega⟩ d ⟨F.p, h.2⟩)
        | none => none
      else none
    else if F.tag = 2 then
      if h : F.t ≤ (Sof e) then
        match qOfCode F.q with
        | some q => some (.state ⟨F.t, by omega⟩ q)
        | none => none
      else none
    else if F.tag = 3 then
      if h : F.t < (Sof e) then some (.emitOne ⟨F.t, h⟩) else none
    else if F.tag = 4 then
      if h : F.t < (Sof e) then some (.emitBad ⟨F.t, h⟩) else none
    else if F.tag = 5 then
      if h : F.t ≤ (Sof e) then some (.emitted ⟨F.t, by omega⟩) else none
    else if F.tag = 6 then
      if h : F.t < (Sof e) ∧ (∀ d, F.js d < 2 * (Sof e) + 3) ∧ F.g < G then
        some (.aux ⟨F.t, h.1⟩ (fun d => ⟨F.js ⟨tapeCode d, tapeCode_lt d⟩, h.2.1 _⟩) ⟨F.g, h.2.2⟩)
      else none
    else none
  else
    if F.ansOk ∧ F.tag = 0 ∧ F.t = 0 then
      if h : F.d < 7 ∧ F.p < numCells (Sof e) then
        match symOfCode F.v with
        | some v => some (.cell 0 (.inl ⟨F.d, h.1⟩) ⟨F.p, h.2⟩ v)
        | none => none
      else none
    else none

end Decode

/-! ## Encoding -/

/-- The `w`-bit binary representation of `n`, least significant bit first. -/
def nbits (w n : ℕ) : BitStr := bitsOfNat w n

@[simp] theorem length_nbits (w n : ℕ) : (nbits w n).length = w := length_bitsOfNat w n

/-- The `w`-bit fields `js a, …, js (a + n - 1)`, concatenated. -/
def jsPack (w : ℕ) (js : ℕ → ℕ) : ℕ → ℕ → BitStr
  | _, 0 => []
  | a, n + 1 => nbits w (js a) ++ jsPack w js (a + 1) n

@[simp] theorem length_jsPack (w : ℕ) (js : ℕ → ℕ) : ∀ (a n : ℕ), (jsPack w js a n).length = n * w
  | _, 0 => by simp [jsPack]
  | a, n + 1 => by simp [jsPack, length_jsPack w js (a + 1) n]; ring

/-- The structured index with the given fields. -/
def packFields (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ) : BitStr :=
  nbits 3 tag ++ (nbits (W e) t ++ (nbits 4 d ++ (nbits (W e) p ++ (nbits 3 v ++ (nbits Qb q ++
    (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true])))))))

section Pack

variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)

end Pack

section Encode

variable (e G : ℕ)

/-- The window centers of an `aux` variable as a function on tape codes. -/
def jsFun (js : Tape 7 6 → Center (Sof e)) (k : ℕ) : ℕ :=
  match tapeOfCode k with
  | some d => js d
  | none => 0

/-- The structured index of a tableau variable. -/
noncomputable def encodeVar : TabVar 7 6 Sym Ctl (Sof e) G → BitStr
  | .cell t d p v => packFields e G 0 t (tapeCode d) p (symCode v) 0 (fun _ => 0) 0
  | .head t d p => packFields e G 1 t (tapeCode d) p 0 0 (fun _ => 0) 0
  | .state t q => packFields e G 2 t 0 0 0 (qCode q) (fun _ => 0) 0
  | .emitOne t => packFields e G 3 t 0 0 0 0 (fun _ => 0) 0
  | .emitBad t => packFields e G 4 t 0 0 0 0 (fun _ => 0) 0
  | .emitted t => packFields e G 5 t 0 0 0 0 (fun _ => 0) 0
  | .aux t js g => packFields e G 6 t 0 0 0 0 (jsFun e js) g

end Encode

end MIPRE.TM.CookLevin.Desc


