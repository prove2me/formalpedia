-- Prove2me | Definitions.Def_Section5Verified_Section5QFTFoundation
-- name    : Section5Verified_Section5QFTFoundation
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:01.63946+00:00
-- url     : https://prove2.me/theorems/77618325-b2ee-5afa-adbd-851a2902f4ab
-- title:
--   Section5QFTFoundation — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5QFTFoundation; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Mathlib
section
set_option autoImplicit false

open QAlgorithms
open scoped Matrix BigOperators

namespace SolQFTCircuitExact

/-- The single wire `q` as an embedding `Fin 1 ↪ Fin n`. -/
def wire1 {n : ℕ} (q : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => q, fun a b _ => Subsingleton.elim a b⟩

/-- The wires `(c, t)`, `c ≠ t`, as an embedding `Fin 2 ↪ Fin n`. -/
def wire2 {n : ℕ} (c t : Fin n) (hct : c ≠ t) : Fin 2 ↪ Fin n :=
  ⟨Fin.cons c fun _ : Fin 1 => t,
    Fin.cons_injective_iff.2 ⟨by rintro ⟨_, h⟩; exact hct h.symm,
      fun a b _ => Subsingleton.elim a b⟩⟩







/-- Embed a circuit on `n` wires into `n + 1` wires on the first `n` wires `Fin.castSuccEmb`. -/
def liftGateApp {S : Set Gate} {n : ℕ} (g : GateApp S n) : GateApp S (n + 1) :=
  ⟨g.gate, g.mem, g.wires.trans Fin.castSuccEmb⟩

def liftCircuit {S : Set Gate} {n : ℕ} (c : Circuit S n) : Circuit S (n + 1) :=
  c.map liftGateApp



/-- Block-diagonal extension of an `n`-qubit operator to `n + 1` qubits acting on `Fin.init`. -/
def liftInit {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ :=
  Matrix.of fun y z =>
    if y (Fin.last n) = z (Fin.last n) then A (Fin.init y) (Fin.init z) else 0





















/-- Controlled-`R_s` gate application on wires `c ≠ t`. -/
noncomputable def ctrlRotApp {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (c t : Fin n) (hct : c ≠ t) :
    GateApp qftGateSet n :=
  ⟨Gate.ofMatrix2 (controlled (rotR s)),
    Or.inl (Or.inr ⟨s, hs, rfl⟩),
    wire2 c t hct⟩



/-- Phase circuit of `n` controlled-`R_{m+2}` gates on `(castSucc m, last n)`. -/
noncomputable def phaseCircuit (n : ℕ) : Circuit qftGateSet (n + 1) :=
  List.ofFn fun m : Fin n =>
    ctrlRotApp ((m : ℕ) + 2) (by omega) (Fin.castSucc m) (Fin.last n) (Fin.castSucc_ne_last m)







/-- Hadamard gate application on wire `q`. -/
noncomputable def hadApp {n : ℕ} (q : Fin n) : GateApp qftGateSet n :=
  ⟨Gate.ofMatrix1 hadamard, Or.inl (Or.inl rfl), wire1 q⟩



/-- SWAP gate application on wires `c ≠ t`. -/
def swapApp {n : ℕ} (c t : Fin n) (hct : c ≠ t) : GateApp qftGateSet n :=
  ⟨Gate.ofMatrix2 swapGate, Or.inr rfl, wire2 c t hct⟩





/-- Sequence of `n` SWAP gates cycling `(0, 1, ..., n)`. -/
def cycleSwaps : (n : ℕ) → Circuit qftGateSet (n + 1)
  | 0 => []
  | m + 1 =>
      [swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (Fin.castSucc_ne_last _)] ++
        liftCircuit (cycleSwaps m)





















/-- Full QFT circuit on `n` qubits. -/
noncomputable def qftCircuit : (n : ℕ) → Circuit qftGateSet n
  | 0 => []
  | n + 1 =>
      liftCircuit (qftCircuit n) ++ phaseCircuit n ++ [hadApp (Fin.last n)] ++ cycleSwaps n







end SolQFTCircuitExact




end


