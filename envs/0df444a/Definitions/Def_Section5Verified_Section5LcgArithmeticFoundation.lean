-- Prove2me | Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
-- name    : Section5Verified_Section5LcgArithmeticFoundation
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:37:52.185851+00:00
-- url     : https://prove2.me/theorems/8f454ed6-c0be-4b98-8255-4d228438bb01
-- title:
--   Section5LcgArithmeticFoundation — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5LcgArithmeticFoundation; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
section
set_option autoImplicit false

/-! Reused accepted arithmetic proof by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353.
Apache-2.0. This local dependency is not a new contribution.
Helper definitions are exposed to verify their realization over gatesRev. -/

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router




























/-! ### Part 2: Zero-Ancilla Register Primitives -/





































noncomputable def cswapPrefixCircuit (w : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit (1 + w + w)
  | 0, _ => LayeredCircuit.id (1 + w + w)
  | k + 1, hk =>
    let prev := cswapPrefixCircuit w k (by omega)
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hca : c ≠ a := Fin.ne_of_val_ne (by dsimp [c, a]; omega)
    have hcb : c ≠ b := Fin.ne_of_val_ne (by dsimp [c, b]; omega)
    have hab : a ≠ b := Fin.ne_of_val_ne (by dsimp [a, b]; omega)
    prev.seq (cswapOn c a b hca hcb hab)





/-- Controlled swap of two `w`-bit registers using `7 * w` gates (`0` ancillas). -/
noncomputable def cswapRegCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + 0) :=
  cswapPrefixCircuit w w le_rfl


















def ctrlConstPrefixCircuit (w c : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit (1 + w)
  | 0, _ => LayeredCircuit.id (1 + w)
  | k + 1, hk =>
    let prev := ctrlConstPrefixCircuit w c k (by omega)
    let c0 : Fin (1 + w) := ⟨0, by omega⟩
    let tgt : Fin (1 + w) := ⟨1 + k, by omega⟩
    have hne : c0 ≠ tgt := Fin.ne_of_val_ne (by dsimp [c0, tgt]; omega)
    if c.testBit k then prev.seq (cnotGate c0 tgt hne) else prev





/-- Controlled on wire `0`, XORs `natToBitsLSB w c` onto wires `1..w` (`≤ w` gates, `0` ancillas). -/
def ctrlConstXorCircuit (w c : ℕ) : LayeredCircuit ((1 + w) + 0) :=
  ctrlConstPrefixCircuit w c w le_rfl



def ctrlConstXorFn (w c : ℕ) (x : Qubits (1 + w)) : Qubits (1 + w) :=
  fun u => if x ⟨0, by omega⟩ then
    if h : 1 ≤ u.1 then xor (x u) (natToBitsLSB w c ⟨u.1 - 1, by have := u.isLt; omega⟩) else x u
  else x u



/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/

noncomputable def cuccaroMAJ {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : LayeredCircuit m :=
  (cnotGate a b hba.symm).seq ((cnotGate a c hca.symm).seq (toffoliOn c b a hcb hca hba))

noncomputable def cuccaroUMA {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : LayeredCircuit m :=
  (toffoliOn c b a hcb hca hba).seq ((cnotGate a c hca.symm).seq (cnotGate c b hcb))













/-- Shift embedding `Fin (1 + 2 * w) ↪ Fin (1 + 2 * (w + 1))` mapping `0 ↦ 1` (`a_0`) and `1+j ↦ 3+j`. -/
def cuccaroShiftEmb (w : ℕ) : Fin (1 + 2 * w) ↪ Fin (1 + 2 * (w + 1)) where
  toFun i := if i.1 = 0 then ⟨1, by omega⟩ else ⟨i.1 + 2, by have := i.isLt; omega⟩
  inj' a b h := by
    have hv := congrArg Fin.val h; dsimp only at hv
    by_cases ha : a.1 = 0 <;> by_cases hb : b.1 = 0
    · exact Fin.ext (ha.trans hb.symm)
    · simp only [ha, hb, ↓reduceIte] at hv; omega
    · simp only [ha, hb, ↓reduceIte] at hv; omega
    · simp only [ha, hb, ↓reduceIte] at hv; exact Fin.ext (by omega)



/-- Recursive Cuccaro core on interleaved wires `(c0, a_0, b_0, ..., a_{w-1}, b_{w-1})`. -/
noncomputable def cuccaroCore : (w : ℕ) → LayeredCircuit (1 + 2 * w)
  | 0 => LayeredCircuit.id 1
  | w + 1 =>
    let maj0 := cuccaroMAJ (⟨0, by omega⟩ : Fin (1 + 2 * (w + 1))) ⟨2, by omega⟩ ⟨1, by omega⟩
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    let mid := (cuccaroCore w).mapWires (cuccaroShiftEmb w)
    let uma0 := cuccaroUMA (⟨0, by omega⟩ : Fin (1 + 2 * (w + 1))) ⟨2, by omega⟩ ⟨1, by omega⟩
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    maj0.seq (mid.seq uma0)





def cuccaroWireEmb (w : ℕ) : Fin (1 + 2 * w) ↪ Fin ((w + w) + 1) where
  toFun u :=
    if u.1 = 0 then ⟨w + w, by omega⟩
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    else ⟨w + (u.1 - 1) / 2, by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)



/-- In-place `w`-bit adder `(a, b) ↦ (a, natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b))`
in `14 * w` gates with `1` clean ancilla. -/
noncomputable def addInPlaceCircuit (w : ℕ) : LayeredCircuit ((w + w) + 1) :=
  (cuccaroCore w).mapWires (cuccaroWireEmb w)



def addInPlaceFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let sum := natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)
  fun i => if h : i.1 < w then a ⟨i.1, h⟩ else sum ⟨i.1 - w, by omega⟩







def subInPlaceFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let diff := natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a)
  fun i => if h : i.1 < w then a ⟨i.1, h⟩ else diff ⟨i.1 - w, by omega⟩





/-- Recursive Cuccaro carry-out: XORs `decide (2^w ≤ a + b + cin)` into wire `1 + 2*w`. -/
def cuccaroCarryShiftEmb (w : ℕ) :
    Fin (1 + 2 * w + 1) ↪ Fin (1 + 2 * (w + 1) + 1) where
  toFun i :=
    if i.1 = 0 then ⟨1, by omega⟩
    else if i.1 = 1 + 2 * w then ⟨1 + 2 * (w + 1), by omega⟩
    else ⟨i.1 + 2, by have := i.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)



noncomputable def cuccaroCarryOut : (w : ℕ) → LayeredCircuit (1 + 2 * w + 1)
  | 0 => cnotGate ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.ne_of_val_ne (by simp))
  | w + 1 =>
    let maj0 := cuccaroMAJ (⟨0, by omega⟩ : Fin (1 + 2 * (w + 1) + 1)) ⟨2, by omega⟩ ⟨1, by omega⟩
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    let mid := (cuccaroCarryOut w).mapWires (cuccaroCarryShiftEmb w)
    maj0.seq (mid.seq maj0.adj)





def flipRegCircuit (w : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit w
  | 0, _ => LayeredCircuit.id w
  | k + 1, hk => (flipRegCircuit w k (by omega)).seq (pauliXGate ⟨k, by omega⟩)





def ltFlipEmb (w : ℕ) : Fin w ↪ Fin ((w + w + 1) + 1) where
  toFun i := ⟨i.1, by omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; exact this)



def ltCarryEmb (w : ℕ) : Fin (1 + 2 * w + 1) ↪ Fin ((w + w + 1) + 1) where
  toFun u :=
    if u.1 = 0 then ⟨w + w + 1, by omega⟩
    else if u.1 = 1 + 2 * w then ⟨w + w, by omega⟩
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    else ⟨w + (u.1 - 1) / 2, by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)



/-- Unsigned register comparator `(a, b, t) ↦ (a, b, t ^^^ decide (a < b))` in `16 * w + 1` gates with `1` ancilla. -/
noncomputable def ltRegCircuit (w : ℕ) : LayeredCircuit ((w + w + 1) + 1) :=
  let flipA := (flipRegCircuit w w le_rfl).mapWires (ltFlipEmb w)
  let carry := (cuccaroCarryOut w).mapWires (ltCarryEmb w)
  flipA.seq (carry.seq flipA)



def ltRegFn (w : ℕ) (x : Qubits (w + w + 1)) : Qubits (w + w + 1) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  Function.update x ⟨w + w, by omega⟩
    (xor (x ⟨w + w, by omega⟩) (decide (bitsToNatLSB a < bitsToNatLSB b)))



/-! ### Part 5: Sub-register Combinators, Controlled Arithmetic & Bit-Reversal -/


noncomputable def ctrlCopyPrefixCircuit (w : ℕ) :
    (k : ℕ) → k ≤ w → LayeredCircuit (1 + w + w)
  | 0, _ => LayeredCircuit.id (1 + w + w)
  | k + 1, hk =>
    let prev := ctrlCopyPrefixCircuit w k (by omega)
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hca : c ≠ a := Fin.ne_of_val_ne (by dsimp [c, a]; omega)
    have hcb : c ≠ b := Fin.ne_of_val_ne (by dsimp [c, b]; omega)
    have hab : a ≠ b := Fin.ne_of_val_ne (by dsimp [a, b]; omega)
    prev.seq (toffoliOn c a b hca hcb hab)





/-- Controlled bitwise copy `(ctrl, a, b) ↦ (ctrl, a, if ctrl then b ^^^ a else b)` in `5 * w` gates. -/
noncomputable def ctrlCopyRegCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + 0) :=
  ctrlCopyPrefixCircuit w w le_rfl






def cAddCopyEmb (w : ℕ) : Fin (1 + w + w) ↪ Fin ((1 + w + w) + (w + 1)) where
  toFun u :=
    if u.1 < 1 + w then ⟨u.1, by omega⟩ else ⟨u.1 + w, by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)





def cAddCoreMainEmb (w : ℕ) : Fin (w + w) ↪ Fin ((1 + w + w) + (w + 1)) where
  toFun u := if h : u.1 < w then ⟨1 + w + w + u.1, by omega⟩ else ⟨1 + u.1, by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp]  lemma _root_.Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreMainEmb_val (w : ℕ) (u : Fin (w + w)) :
    (cAddCoreMainEmb w u).1 = if u.1 < w then 1 + w + w + u.1 else 1 + u.1 := by
  change (if h : u.1 < w then (⟨1 + w + w + u.1, _⟩ : Fin ((1 + w + w) + (w + 1)))
    else ⟨1 + u.1, _⟩).1 = _
  split_ifs <;> rfl

def cAddCoreAncEmb (w : ℕ) : Fin 1 ↪ Fin ((1 + w + w) + (w + 1)) where
  toFun _ := ⟨1 + w + w + w, by omega⟩
  inj' a b _ := Subsingleton.elim a b

 lemma _root_.Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreAncEmb_val (w : ℕ) (j : Fin 1) :
    (cAddCoreAncEmb w j).1 = 1 + w + w + w := rfl

 lemma _root_.Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreDisj (w : ℕ) (i : Fin (w + w)) (j : Fin 1) :
    cAddCoreMainEmb w i ≠ cAddCoreAncEmb w j := by
  apply Fin.ne_of_val_ne
  rw [Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreMainEmb_val, Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreAncEmb_val]
  split_ifs <;> have := i.isLt <;> omega

/-- Controlled in-place `w`-bit adder `(ctrl, a, b) ↦ (ctrl, a, if ctrl then (a+b) mod 2^w else b)` in `24 * w` gates (`w + 1` ancillas). -/
noncomputable def ctrlAddInPlaceCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + (w + 1)) :=
  let cpy := (ctrlCopyRegCircuit w).mapWires (cAddCopyEmb w)
  let addC := (addInPlaceCircuit w).mapWires (combineEmb (cAddCoreMainEmb w) (cAddCoreAncEmb w) (Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreDisj w))
  cpy.seq (addC.seq cpy)



def ctrlAddInPlaceFn (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  let a : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨1 + w + i.1, by omega⟩
  let s := natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)
  fun u =>
    if x ⟨0, by omega⟩ then
      if h : 1 + w ≤ u.1 then s ⟨u.1 - (1 + w), by omega⟩ else x u
    else x u

def ctrlSubInPlaceFn (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  let a : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨1 + w + i.1, by omega⟩
  let d := natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a)
  fun u =>
    if x ⟨0, by omega⟩ then
      if h : 1 + w ≤ u.1 then d ⟨u.1 - (1 + w), by omega⟩ else x u
    else x u





/-- Controlled in-place `w`-bit subtractor `(ctrl, a, b) ↦ (ctrl, a, if ctrl then (2^w + b - a) mod 2^w else b)` in `24 * w` gates (`w + 1` ancillas). -/
noncomputable def ctrlSubInPlaceCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + (w + 1)) :=
  (ctrlAddInPlaceCircuit w).adj





def cacXorEmb (w : ℕ) : Fin (1 + w) ↪ Fin ((1 + w) + (w + 1)) where
  toFun u := if u.1 = 0 then ⟨0, by omega⟩ else ⟨1 + w + (u.1 - 1), by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)





def cacAddMainEmb (w : ℕ) : Fin (w + w) ↪ Fin ((1 + w) + (w + 1)) where
  toFun u := if h : u.1 < w then ⟨1 + w + u.1, by omega⟩ else ⟨1 + (u.1 - w), by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp]  lemma _root_.Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddMainEmb_val (w : ℕ) (u : Fin (w + w)) :
    (cacAddMainEmb w u).1 = if u.1 < w then 1 + w + u.1 else 1 + (u.1 - w) := by
  change (if h : u.1 < w then (⟨1 + w + u.1, _⟩ : Fin ((1 + w) + (w + 1)))
    else ⟨1 + (u.1 - w), _⟩).1 = _
  split_ifs <;> rfl

def cacAddAncEmb (w : ℕ) : Fin 1 ↪ Fin ((1 + w) + (w + 1)) where
  toFun _ := ⟨1 + w + w, by omega⟩
  inj' a b _ := Subsingleton.elim a b

 lemma _root_.Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddAncEmb_val (w : ℕ) (j : Fin 1) :
    (cacAddAncEmb w j).1 = 1 + w + w := rfl

 lemma _root_.Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddDisj (w : ℕ) (i : Fin (w + w)) (j : Fin 1) :
    cacAddMainEmb w i ≠ cacAddAncEmb w j := by
  apply Fin.ne_of_val_ne
  rw [Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddMainEmb_val, Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddAncEmb_val]
  split_ifs <;> have := i.isLt <;> omega

/-- Controlled in-place `+ c mod 2^w`: `(ctrl, b) ↦ (ctrl, if ctrl then (c % 2^w + b) mod 2^w else b)` in `≤ 16 * w` gates (`w + 1` ancillas). -/
noncomputable def ctrlAddConstInPlaceCircuit (w c : ℕ) : LayeredCircuit ((1 + w) + (w + 1)) :=
  let sc := (ctrlConstXorCircuit w c).mapWires (cacXorEmb w)
  let addC := (addInPlaceCircuit w).mapWires (combineEmb (cacAddMainEmb w) (cacAddAncEmb w) (Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddDisj w))
  sc.seq (addC.seq sc)



def ctrlAddConstInPlaceFn (w c : ℕ) (x : Qubits (1 + w)) : Qubits (1 + w) :=
  let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let s := natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b)
  fun u => if x ⟨0, by omega⟩ then if h : 1 ≤ u.1 then s ⟨u.1 - 1, by omega⟩ else x u else x u

def ctrlSubConstInPlaceFn (w c : ℕ) (x : Qubits (1 + w)) : Qubits (1 + w) :=
  let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let d := natToBitsLSB w (2 ^ w + bitsToNatLSB b - c % 2 ^ w)
  fun u => if x ⟨0, by omega⟩ then if h : 1 ≤ u.1 then d ⟨u.1 - 1, by omega⟩ else x u else x u





/-- Controlled in-place `- (c % 2^w) mod 2^w` in `≤ 16 * w` gates (`w + 1` ancillas). -/
noncomputable def ctrlSubConstInPlaceCircuit (w c : ℕ) : LayeredCircuit ((1 + w) + (w + 1)) :=
  (ctrlAddConstInPlaceCircuit w c).adj





/-! ### MSB-First Circuit Wrappers via Zero-Gate `Fin.revPerm` Conjugation -/













-- 1. setConstMSBCircuit






-- 2. ctrlConstXorMSBCircuit






-- 3. eqConstMSBCircuit






-- 4. ltConstMSBCircuit






-- 5. ltRegMSBCircuit






-- 6 & 7. addInPlaceMSBCircuit & subInPlaceMSBCircuit
















-- 8 & 9. ctrlAddInPlaceMSBCircuit & ctrlSubInPlaceMSBCircuit
















-- 10 & 11. ctrlAddConstInPlaceMSBCircuit & ctrlSubConstInPlaceMSBCircuit












end Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Aux_w54_arith




end


