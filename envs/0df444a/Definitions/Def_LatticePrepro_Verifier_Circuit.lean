-- Prove2me | Definitions.Def_LatticePrepro_Verifier_Circuit
-- name    : LatticePrepro_Verifier_Circuit
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:20:52.469208+00:00
-- url     : https://prove2.me/theorems/9e6b3143-be90-4f37-b455-b4196b01e937
-- title:
--   Boolean circuits and the reordering of their wires (Definitions 3.13–3.14)
-- statement:
--   - **Boolean circuit** (`BoolCircuit`): $n$ input wires, $w$ witness wires and $g$ gates in topological order. The wires are numbered $0, \dots, S-1$ with $S = n + w + g$ (`S`): wires $0,\dots,n-1$ carry the instance, wires $n, \dots, n+w-1$ the witness, and wire $n + w + k$ is the output of gate $k$. Gate $k$ reads two (possibly equal) wires among the first $n + w + k$ and applies a Boolean function $f_k\colon \{0,1\}^2 \to \{0,1\}$. One gate is designated as the output; its wire is $o = n + w + (\text{index of the output gate})$ (`outW`).
--   - **Evaluation** (`evalAux`): for an instance $x \in \{0,1\}^n$ and a witness $u \in \{0,1\}^w$, wire $i$ has value $x_i$ if $i < n$, $u_{i-n}$ if $n \le i < n+w$, and $f_k$ applied to the values of its two input wires if $i = n+w+k$ is a gate wire (wires $i \ge S$ get the value $0$).
--   - **Language** (`Language`): $L(C) = \{x \in \{0,1\}^n : \text{the output wire has value } 1 \text{ for some witness } u\}$.
--   - **Reordering** (`coordOfNat`, `coordOf`): the coordinate of wire $i$ in the order "inputs, output wire, remaining wires": $i \mapsto i$ for $i < n$, $o \mapsto n$, $i \mapsto i + 1$ for $n \le i < o$, and $i \mapsto i$ for $i > o$. `gateWire`, `inWire1`, `inWire2` are the output and input wires of gate $k$.
--   - **Gate verifier of a circuit** (`toGateVerifier`): the gate verifier with instance length $n$, $S$ wires and $g$ gates, gate $k$ being the constraint "coordinate of its output wire $= f_k$(coordinates of its input wires)".
--
--   A `BoolCircuit` is a verifier in the sense of Definition 3.13, and the reordering is the coordinate order of assignments in Definition 3.14 (input bits, output of the designated gate, witness bits, remaining gate outputs). `BoolCircuit.language_toGateVerifier` shows that the gate verifier has the same language; the 3SAT verifier is built as a `BoolCircuit`.
--
--   **Formalization Note**: Every gate has exactly two input wires (gates of smaller fan-in are expressed by repeating or ignoring an input), and the designated output gate forces $g \ge 1$. Evaluation is defined by well-founded recursion on the wire index. The bundle also contains the facts $o < S$, $n \le o$, and that the reordering maps wires below $S$ to coordinates below $S$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definitions 3.13–3.14 (\label{def:verifier}, \label{def:computation-assignment}); Lean: LatticePrepro/Verifier/Circuit.lean, LatticePrepro.BoolCircuit, LatticePrepro.BoolCircuit.evalAux, LatticePrepro.BoolCircuit.Language, LatticePrepro.BoolCircuit.toGateVerifier

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates

/-!
# Boolean circuits (Definitions 3.13–3.14)

A `BoolCircuit` has `n` input wires, `w` witness wires and `g` gates of fan-in two in topological
order: gate `k` reads two of the first `n + w + k` wires and writes wire `n + w + k`. A designated
gate is the output. Evaluation (`evalAux`) is defined by well-founded recursion on the wire index,
and the accepted language consists of the instances `x` for which some witness makes the output
wire `true`.

Reordering the wires as in Definition 3.14 (inputs, then the output wire, then the remaining
wires in order) turns a circuit into a `GateVerifier` with the same language
(`BoolCircuit.language_toGateVerifier`): the valid wire assignments of the gate verifier are
exactly the evaluations of the circuit.
-/

namespace LatticePrepro

/-- A Boolean circuit with gates of fan-in two in topological order. -/
structure BoolCircuit where
  /-- Number of input wires. -/
  n : ℕ
  /-- Number of witness wires. -/
  w : ℕ
  /-- Number of gates. -/
  g : ℕ
  /-- Gate `k` reads two of the first `n + w + k` wires. -/
  gateIn : (k : Fin g) → Fin (n + w + k.val) × Fin (n + w + k.val)
  /-- The Boolean function computed by gate `k`. -/
  gateFn : Fin g → Bool → Bool → Bool
  /-- The designated output gate. -/
  output : Fin g

namespace BoolCircuit

variable (C : BoolCircuit)

/-- The number of wires. -/
abbrev S : ℕ := C.n + C.w + C.g

/-- The index of the output wire. -/
def outW : ℕ := C.n + C.w + C.output.val

lemma outW_lt : C.outW < C.n + C.w + C.g := by
  unfold outW; have := C.output.isLt; omega

lemma n_le_outW : C.n ≤ C.outW := by unfold outW; omega

/-- Evaluation of the wire with index `i` on instance `x` and witness `wit`
(wires `≥ n + w + g` evaluate to `false`). -/
def evalAux (x : Fin C.n → Bool) (wit : Fin C.w → Bool) (i : ℕ) : Bool :=
  if h1 : i < C.n then x ⟨i, h1⟩
  else if h2 : i < C.n + C.w then wit ⟨i - C.n, by omega⟩
  else if h3 : i < C.n + C.w + C.g then
    C.gateFn ⟨i - (C.n + C.w), by omega⟩
      (evalAux x wit (C.gateIn ⟨i - (C.n + C.w), by omega⟩).1.val)
      (evalAux x wit (C.gateIn ⟨i - (C.n + C.w), by omega⟩).2.val)
  else false
termination_by i
decreasing_by
  · have h := (C.gateIn ⟨i - (C.n + C.w), by omega⟩).1.isLt
    simp only [Fin.val_mk] at h
    omega
  · have h := (C.gateIn ⟨i - (C.n + C.w), by omega⟩).2.isLt
    simp only [Fin.val_mk] at h
    omega

/-- The language of the circuit: instances with a witness making the output wire `true`. -/
def Language : Set (Fin C.n → Bool) := {x | ∃ wit, C.evalAux x wit C.outW = true}

/-! ### Reordering the wires -/

/-- The coordinate (in the order inputs, output, remaining wires) of a wire. -/
def coordOfNat (wi : ℕ) : ℕ :=
  if wi < C.n then wi else if wi = C.outW then C.n else if wi < C.outW then wi + 1 else wi

lemma coordOfNat_lt {wi : ℕ} (_h : wi < C.n + C.w + C.g) : C.coordOfNat wi < C.n + C.w + C.g := by
  unfold coordOfNat
  have := C.outW_lt; have := C.n_le_outW
  split_ifs <;> omega

/-- The coordinate of a wire, as an element of `Fin S`. -/
def coordOf (wi : Fin C.S) : Fin C.S := ⟨C.coordOfNat wi, C.coordOfNat_lt wi.isLt⟩

/-- The wire written by gate `k`. -/
def gateWire (k : Fin C.g) : Fin C.S :=
  ⟨C.n + C.w + k.val, by show _ < C.n + C.w + C.g; have := k.isLt; omega⟩

/-- The first input wire of gate `k`. -/
def inWire1 (k : Fin C.g) : Fin C.S :=
  ⟨(C.gateIn k).1.val, by have := (C.gateIn k).1.isLt; have := k.isLt; show _ < C.n + C.w + C.g; omega⟩

/-- The second input wire of gate `k`. -/
def inWire2 (k : Fin C.g) : Fin C.S :=
  ⟨(C.gateIn k).2.val, by have := (C.gateIn k).2.isLt; have := k.isLt; show _ < C.n + C.w + C.g; omega⟩

/-- The gate verifier of a circuit (Definition 3.14): the coordinates list the inputs, then the
output wire, then the remaining wires in order. -/
abbrev toGateVerifier : GateVerifier where
  n := C.n
  S := C.S
  n_succ_le := by show C.n + 1 ≤ C.n + C.w + C.g; have := C.output.isLt; omega
  G := C.g
  gate := fun k =>
    (C.coordOf (C.gateWire k), C.coordOf (C.inWire1 k), C.coordOf (C.inWire2 k), C.gateFn k)

end BoolCircuit

end LatticePrepro


