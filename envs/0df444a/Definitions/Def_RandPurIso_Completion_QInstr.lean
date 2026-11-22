-- Prove2me | Definitions.Def_RandPurIso_Completion_QInstr
-- name    : RandPurIso_Completion_QInstr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:24.361477+00:00
-- url     : https://prove2.me/theorems/77ce2d44-9969-4fbc-94af-a5cea81d10cc
-- title:
--   Oracle circuits over Clifford+T
-- statement:
--   An **oracle circuit** on $n$ qubits with $q$ oracles is a list of instructions, each either a gate from the Clifford+T set $\{H,S,T,X,\mathrm{CNOT}\}$ or one query to oracle $j$ on a chosen ordered set of $w_j$ wires. Given channels $\Psi_j$ on $w_j$ qubits, a gate acts by conjugation with its unitary and a query applies $\Psi_j\otimes\mathrm{id}$ on its wires; the circuit is run head first. `queryCount j c` counts the queries to oracle $j$. The module also fixes the little-endian binary encoding `binEnc` of natural numbers and the all-zero string.
--
--   This is the cost model in which the paper's "efficiently implementable" and "poly($\cdot$) gates" are read.
--
--   **Formalization Note** The gates are the published `ShiShallow.Instr`; a gate's matrix has as column $y$ the instruction applied to $|y\rangle$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 5.4 and Lemma 3.15, pp. 24, 29–30 (gate counts)

import Mathlib
import Definitions.Def_ShiShallow_Core
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- The unitary matrix of a Clifford+T instruction (`H`, `S`, `T`, `X`, `CNOT` of
`ShiShallow.Instr`) on `n` qubits: column `y` is the instruction applied to the basis state `|y⟩`.

Gate model of Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573: the paper measures efficiency by gate counts ("poly(…) gates", Lemma 3.15,
Theorem 4.1, p. 24, 26; "running in time poly(T, log M)", p. 30). -/
noncomputable def gateU {n : ℕ} (g : Instr n) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of fun x y => g.apply (fun z => if z = y then 1 else 0) x

/-- **Instruction of an oracle circuit** on `n` qubits with `q` oracles, oracle `j` acting on `w j`
qubits: a Clifford+T gate, or one query to oracle `j` on the wires chosen by the embedding `e`
(wire `i` of the oracle register is circuit wire `e i`). -/
inductive QInstr (q : ℕ) (w : Fin q → ℕ) (n : ℕ) where
  | gate (g : Instr n)
  | query (j : Fin q) (e : Fin (w j) ↪ Fin n)

/-- `Ψ ⊗ id`: a map on the qubits `e` applied with the identity on all other wires. -/
noncomputable def onWires {m n : ℕ} (e : Fin m ↪ Fin n)
    (Ψ : Matrix (Bits m) (Bits m) ℂ → Matrix (Bits m) (Bits m) ℂ)
    (ρ : Matrix (Bits n) (Bits n) ℂ) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.of fun z z' =>
    Ψ (Matrix.of fun a b => ρ (Function.extend e a z) (Function.extend e b z')) (z ∘ e) (z' ∘ e)

/-- Action of one instruction: a gate conjugates by its unitary; a query applies the oracle's
channel `Ψ j` on its wires. -/
noncomputable def QInstr.act {q : ℕ} {w : Fin q → ℕ} {n : ℕ}
    (Ψ : (j : Fin q) → Matrix (Bits (w j)) (Bits (w j)) ℂ → Matrix (Bits (w j)) (Bits (w j)) ℂ) :
    QInstr q w n → Matrix (Bits n) (Bits n) ℂ → Matrix (Bits n) (Bits n) ℂ
  | .gate g => fun ρ => gateU g * ρ * (gateU g)ᴴ
  | .query j e => onWires e (Ψ j)

/-- Run a list of instructions, head first. -/
noncomputable def QInstr.evalList {q : ℕ} {w : Fin q → ℕ} {n : ℕ}
    (Ψ : (j : Fin q) → Matrix (Bits (w j)) (Bits (w j)) ℂ → Matrix (Bits (w j)) (Bits (w j)) ℂ)
    (c : List (QInstr q w n)) (ρ : Matrix (Bits n) (Bits n) ℂ) : Matrix (Bits n) (Bits n) ℂ :=
  c.foldl (fun σ i => i.act Ψ σ) ρ

/-- The number of queries to oracle `j` in a list of instructions. -/
def QInstr.queryCount {q : ℕ} {w : Fin q → ℕ} {n : ℕ} (j : Fin q) (c : List (QInstr q w n)) : ℕ :=
  c.countP fun i => match i with
    | .query j' _ => decide (j' = j)
    | .gate _ => false

/-- Little-endian binary encoding of `x` on `m` qubits (bit `i` = `x.testBit i`). -/
def binEnc (m x : ℕ) : Bits m := fun i => x.testBit i.val

/-- The basis label `x ∈ [N]` on `⌈log₂ N⌉` qubits. -/
def finBin {N : ℕ} (x : Fin N) : Bits (Nat.clog 2 N) := binEnc (Nat.clog 2 N) x.val

/-- The all-zero string `|0…0⟩`. -/
def zeroBits (n : ℕ) : Bits n := fun _ => false

end RandPurIso.Completion


