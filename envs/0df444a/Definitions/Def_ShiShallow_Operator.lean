-- Prove2me | Definitions.Def_ShiShallow_Operator
-- name    : ShiShallow_Operator
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-10T03:52:55.211822+00:00
-- url     : https://prove2.me/theorems/bd574754-9e1a-40f4-a996-ddf432d1b55a
-- title:
--   Local operators on n qubits
-- statement:
--   Operators as matrices on bit-strings, the S-locality predicate (entries vanish unless the two basis strings agree off S, and otherwise depend only on the restrictions to S — the tensor-product condition A = A_S ⊗ I written without tensor products), gate and circuit matrices, and the output projector.
-- source:
--   Original work by Yueheng Shi (Apache-2.0), formalised in Lean 4 with Mathlib.

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: declarations are grouped into a definition bundle;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_ShiShallow_Circuit

namespace ShiShallow

/-- An operator on `n` qubits. -/
abbrev Op (n : ℕ) := Matrix (Bits n) (Bits n) ℂ

/-- Overwrite `v` on `S` with the values carried by `w`. -/
def graft {n : ℕ} (S : Finset (Fin n)) (v : Bits n)
    (w : {k : Fin n // k ∈ S} → Bool) : Bits n :=
  fun k => if h : k ∈ S then w ⟨k, h⟩ else v k

theorem graft_of_mem {n : ℕ} (S : Finset (Fin n)) (v : Bits n)
    (w : {k : Fin n // k ∈ S} → Bool) {k : Fin n} (h : k ∈ S) :
    graft S v w k = w ⟨k, h⟩ := dif_pos h

theorem graft_of_not_mem {n : ℕ} (S : Finset (Fin n)) (v : Bits n)
    (w : {k : Fin n // k ∈ S} → Bool) {k : Fin n} (h : k ∉ S) :
    graft S v w k = v k := dif_neg h

/-- `A` acts as the identity outside `S`: entries vanish unless the two basis strings agree
off `S`, and otherwise depend only on the restrictions to `S`. This is the tensor-product
condition `A = A_S ⊗ I`, written without tensor products.

Stated as a conjunction rather than as `∃ B, ...` because both halves are used directly in the
conjugation lemmas below, where reconstructing a full basis string from a restriction would
otherwise be needed inside a double sum. -/
def IsLocal {n : ℕ} (S : Finset (Fin n)) (A : Op n) : Prop :=
  (∀ y z : Bits n, (¬ ∀ k, k ∉ S → y k = z k) → A y z = 0) ∧
  (∀ y z y' z' : Bits n, (∀ k ∈ S, y k = y' k) → (∀ k ∈ S, z k = z' k) →
      (∀ k, k ∉ S → y k = z k) → (∀ k, k ∉ S → y' k = z' k) → A y z = A y' z')

theorem IsLocal.vanish {n : ℕ} {S : Finset (Fin n)} {A : Op n} (h : IsLocal S A)
    {y z : Bits n} (hne : ¬ ∀ k, k ∉ S → y k = z k) : A y z = 0 := h.1 y z hne

theorem IsLocal.entry_congr {n : ℕ} {S : Finset (Fin n)} {A : Op n} (h : IsLocal S A)
    {y z y' z' : Bits n} (hy : ∀ k ∈ S, y k = y' k) (hz : ∀ k ∈ S, z k = z' k)
    (hyz : ∀ k, k ∉ S → y k = z k) (hyz' : ∀ k, k ∉ S → y' k = z' k) :
    A y z = A y' z' := h.2 y z y' z' hy hz hyz hyz'

/-- Matrix of a one-qubit gate on wire `i`, written so that `{i}`-locality is manifest. -/
def apply1Matrix {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) : Op n :=
  Matrix.of fun y z =>
    if (∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k) then U (y i) (z i) else 0

/-- Matrix of CNOT (control `i`, target `j`), written so that `{i,j}`-locality is manifest. -/
def cnotMatrix {n : ℕ} (i j : Fin n) : Op n :=
  Matrix.of fun y z =>
    if (∀ k, k ∉ ({i, j} : Finset (Fin n)) → y k = z k) ∧ z i = y i ∧ z j = xor (y j) (y i)
    then 1 else 0

/-- The matrix of an instruction. -/
noncomputable def gateMatrix {n : ℕ} : Instr n → Op n
  | .h i => apply1Matrix hMat i
  | .s i => apply1Matrix sMat i
  | .t i => apply1Matrix tMat i
  | .cnot i j _ => cnotMatrix i j

/-- The matrix of a layer. Gates are applied left to right, so the matrix product is reversed. -/
noncomputable def layerMatrix {n : ℕ} : List (Instr n) → Op n
  | [] => 1
  | g :: t => layerMatrix t * gateMatrix g

/-- The matrix of a layered circuit. -/
noncomputable def circMatrix {n : ℕ} : Layered n → Op n
  | [] => 1
  | l :: t => circMatrix t * layerMatrix l

theorem layerMatrix_nil {n : ℕ} : layerMatrix ([] : List (Instr n)) = 1 := rfl

theorem layerMatrix_cons {n : ℕ} (g : Instr n) (t : List (Instr n)) :
    layerMatrix (g :: t) = layerMatrix t * gateMatrix g := rfl

theorem circMatrix_nil {n : ℕ} : circMatrix ([] : Layered n) = 1 := rfl

theorem circMatrix_cons {n : ℕ} (l : List (Instr n)) (t : Layered n) :
    circMatrix (l :: t) = circMatrix t * layerMatrix l := rfl

/-- The computational-basis input string: `x` on the input wires, zeros on the ancillas. -/
def padIn {n m : ℕ} (x : Bits n) : Bits (n + m) := Fin.append x (fun _ => false)

/-- The measurement observable: the projector onto `out = 1`. It is `{out}`-local. -/
def projOut {n : ℕ} (out : Fin n) : Op n :=
  Matrix.of fun y z => if y = z ∧ y out = true then 1 else 0

end ShiShallow


