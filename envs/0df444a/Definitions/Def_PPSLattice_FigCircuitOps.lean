-- Prove2me | Definitions.Def_PPSLattice_FigCircuitOps
-- name    : PPSLattice_FigCircuitOps
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:56:21.532056+00:00
-- url     : https://prove2.me/theorems/d18a8f64-a2c3-45de-9125-89a72c4c9645
-- title:
--   Sequential NAND circuits and hardwired-output circuits
-- statement:
--   This module supplies elementary assembly operations for the NAND circuits used in Figure 1. The **sequential composition** of two circuits with the same $\ell$ input bits appends the second gate list after shifting every non-input wire by the first size, and concatenates the output lists. It evaluates to the concatenation of the two evaluations (when the first circuit's output wires exist), and its gate count is the sum of the two gate counts.
--
--   The **constant-output circuit** $\mathrm{constCircuit}(\ell,u)$ has two initialization gates producing the Boolean constants and outputs any prescribed hardwired string $u$, independently of its $\ell$ input bits. It therefore has exactly two gates. These operations will assemble the three input-independent blocks $(c,P,h)$ with the input-dependent arithmetic block $d$ from Figure 1.
--
--   The module also records the complete wire assignment and its length, together with the semantic and size lemmas for these operations.
--
--   **Formalization Note.** Gate inputs below wire $\ell$ denote input bits and all other indices are shifted. References to nonexistent wires follow the published `RestrictedDec.Circuit` convention and read as $0$.
-- source:
--   Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Claim 4.11, p.23; Figure 1, p.22; §4.2, p.19 (NAND circuits and size).

import Mathlib
import Definitions.Def_RestrictedDec_Circuit
import Definitions.Def_PPSLattice_circSize
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The complete wire assignment of a circuit on an input. -/
def wires (C : RestrictedDec.Circuit) (input : Str) : Str :=
  C.gates.foldl
    (fun ws g => ws ++ [!(ws.getD g.1 false && ws.getD g.2 false)]) input

@[simp] theorem length_wires (C : RestrictedDec.Circuit) (input : Str) :
    (wires C input).length = input.length + C.gates.length := by
  unfold wires
  induction C.gates generalizing input with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private lemma take_wires (C : RestrictedDec.Circuit) (input : Str) (ell : ℕ)
    (h : input.length = ell) : (wires C input).take ell = input := by
  let step : Str → ℕ × ℕ → Str := fun ws g =>
    ws ++ [!(ws.getD g.1 false && ws.getD g.2 false)]
  have aux : ∀ (gs : List (ℕ × ℕ)) (x : Str), ell ≤ x.length →
      (gs.foldl step x).take ell = x.take ell := by
    intro gs
    induction gs with
    | nil => intro x hx; rfl
    | cons g gs ih =>
      intro x hx
      have hstep : ell ≤ (step x g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      simp only [List.foldl_cons]
      rw [ih (step x g) hstep]
      unfold step
      rw [List.take_append_of_le_length hx]
  have hf := aux C.gates input (by omega)
  change (C.gates.foldl (fun ws g =>
    ws ++ [!(ws.getD g.1 false && ws.getD g.2 false)]) input).take ell = input
  calc
    _ = input.take ell := hf
    _ = input := List.take_of_length_le (by omega)

private lemma wires_eq_input_append_drop (C : RestrictedDec.Circuit) (input : Str) (ell : ℕ)
    (h : input.length = ell) : wires C input = input ++ (wires C input).drop ell := by
  calc
    wires C input = (wires C input).take ell ++ (wires C input).drop ell :=
      (List.take_append_drop _ _).symm
    _ = input ++ (wires C input).drop ell := by rw [take_wires C input ell h]

/-- Shift a non-input wire reference by `off`. -/
def shiftWire (ell off w : ℕ) : ℕ := if w < ell then w else w + off

/-- Shift all non-input wire references of a circuit by `off`. -/
def shiftCircuit (ell off : ℕ) (C : RestrictedDec.Circuit) : RestrictedDec.Circuit where
  gates := C.gates.map fun g => (shiftWire ell off g.1, shiftWire ell off g.2)
  outs := C.outs.map (shiftWire ell off)

/-- Sequential composition of circuits with the same `ell` input bits; their outputs are
concatenated. -/
def appendCircuit (ell : ℕ) (C D : RestrictedDec.Circuit) : RestrictedDec.Circuit where
  gates := C.gates ++ (shiftCircuit ell C.gates.length D).gates
  outs := C.outs ++ (shiftCircuit ell C.gates.length D).outs

/-- A circuit on `ell` inputs which outputs hardwired bits. The first two gates produce the
constant wires `true` and `false`. -/
def constCircuit (ell : ℕ) (bits : Str) : RestrictedDec.Circuit where
  gates := [(ell, ell), (ell, ell)]
  outs := bits.map fun b => if b then ell else ell + 1

private lemma getD_shiftWire (input pre ds : Str) (ell w : ℕ)
    (h : input.length = ell) :
    (input ++ pre ++ ds).getD (shiftWire ell pre.length w) false =
      (input ++ ds).getD w false := by
  unfold shiftWire
  split_ifs with hw
  · rw [List.getD_append _ _ _ _ (by simp only [List.length_append, h]; omega)]
    rw [List.getD_append input pre false w (by simpa only [h] using hw)]
    rw [List.getD_append input ds false w (by simpa only [h] using hw)]
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, h]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp only [h]; omega)]
    simp only [List.length_append, h]
    congr 1
    omega

private lemma wires_shift_aux (ell off : ℕ) (input : Str) (h : input.length = ell) :
    ∀ (pre ds : Str), pre.length = off → ∀ gs : List (ℕ × ℕ),
      (gs.map fun g => (shiftWire ell off g.1, shiftWire ell off g.2)).foldl
          (fun ws g => ws ++ [!(ws.getD g.1 false && ws.getD g.2 false)])
          (input ++ pre ++ ds) =
        input ++ pre ++
          ((gs.foldl (fun ws g => ws ++ [!(ws.getD g.1 false && ws.getD g.2 false)])
            (input ++ ds)).drop ell) := by
  intro pre ds hp gs
  induction gs generalizing ds with
  | nil => simp [h]
  | cons g gs ih =>
    subst off
    simp only [List.map_cons, List.foldl_cons]
    have hv : (!((input ++ pre ++ ds).getD (shiftWire ell pre.length g.1) false &&
          (input ++ pre ++ ds).getD (shiftWire ell pre.length g.2) false) : Bool) =
        (!((input ++ ds).getD g.1 false && (input ++ ds).getD g.2 false) : Bool) := by
      have h1 := getD_shiftWire input pre ds ell g.1 h
      have h2 := getD_shiftWire input pre ds ell g.2 h
      simpa using congrArg₂ (fun a b : Bool => !(a && b)) h1 h2
    simp only [hv]
    rw [List.append_assoc (input ++ pre) ds]
    simpa only [List.append_assoc] using ih (ds ++ [!((input ++ ds).getD g.1 false &&
      (input ++ ds).getD g.2 false)])

/-- Evaluating shifted gates after a prefix gives the original wire values, shifted past the
prefix. -/
theorem wires_appendCircuit (ell : ℕ) (C D : RestrictedDec.Circuit) (input : Str)
    (h : input.length = ell) :
    wires (appendCircuit ell C D) input = wires C input ++ (wires D input).drop ell := by
  change (List.foldl _ _ (C.gates ++ (shiftCircuit ell C.gates.length D).gates)) = _
  rw [List.foldl_append]
  change (D.gates.map fun g =>
      (shiftWire ell C.gates.length g.1, shiftWire ell C.gates.length g.2)).foldl _ (wires C input) = _
  rw [wires_eq_input_append_drop C input ell h]
  simpa only [List.append_nil, wires] using
    wires_shift_aux ell C.gates.length input h ((wires C input).drop ell) []
      (by simp [h]) D.gates

private lemma getD_shiftWire_wires (C D : RestrictedDec.Circuit) (input : Str)
    (ell o : ℕ) (h : input.length = ell) :
    (wires C input ++ (wires D input).drop ell).getD (shiftWire ell C.gates.length o) false =
      (input ++ (wires D input).drop ell).getD o false := by
  rw [wires_eq_input_append_drop C input ell h]
  have hc : ((wires C input).drop ell).length = C.gates.length := by simp [h]
  rw [← hc]
  exact getD_shiftWire input ((wires C input).drop ell) ((wires D input).drop ell) ell o h

@[simp] theorem constCircuit_wires (ell : ℕ) (bits input : Str) (h : input.length = ell) :
    wires (constCircuit ell bits) input = input ++ [true, false] := by
  simp [wires, constCircuit, h]

@[simp] theorem constCircuit_eval (ell : ℕ) (bits input : Str) (h : input.length = ell) :
    (constCircuit ell bits).eval input = bits := by
  unfold RestrictedDec.Circuit.eval
  change (constCircuit ell bits).outs.map
    (fun o => (wires (constCircuit ell bits) input).getD o false) = bits
  rw [constCircuit_wires ell bits input h]
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    change ((if b then ell else ell + 1) ::
      (bits.map fun b => if b then ell else ell + 1)).map _ = b :: bits
    rw [List.map_cons]
    have hb : (input ++ [true, false]).getD (if b then ell else ell + 1) false = b := by
      cases b <;> simp [h]
    rw [hb]
    congr 1

/-- Sequential composition evaluates to concatenation when the first circuit's output wires exist.
-/
theorem appendCircuit_eval (ell : ℕ) (C D : RestrictedDec.Circuit) (input : Str)
    (h : input.length = ell)
    (hC : ∀ o ∈ C.outs, o < (wires C input).length) :
    (appendCircuit ell C D).eval input = C.eval input ++ D.eval input := by
  unfold RestrictedDec.Circuit.eval
  change (appendCircuit ell C D).outs.map
    (fun o => (wires (appendCircuit ell C D) input).getD o false) = _
  rw [wires_appendCircuit ell C D input h]
  simp only [appendCircuit, shiftCircuit, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro o ho
    exact List.getD_append _ _ _ _ (hC o ho)
  · apply List.map_congr_left
    intro o ho
    change (wires C input ++ (wires D input).drop ell).getD
      (shiftWire ell C.gates.length o) false = (wires D input).getD o false
    rw [getD_shiftWire_wires C D input ell o h]
    exact congrArg (fun x => x.getD o false) (wires_eq_input_append_drop D input ell h).symm

@[simp] theorem circSize_appendCircuit (ell : ℕ) (C D : RestrictedDec.Circuit) :
    circSize (appendCircuit ell C D) = circSize C + circSize D := by
  simp [circSize, appendCircuit, shiftCircuit]

@[simp] theorem circSize_constCircuit (ell : ℕ) (bits : Str) :
    circSize (constCircuit ell bits) = 2 := rfl

end PPSLattice


