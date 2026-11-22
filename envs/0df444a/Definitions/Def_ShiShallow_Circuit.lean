-- Prove2me | Definitions.Def_ShiShallow_Circuit
-- name    : ShiShallow_Circuit
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-10T03:51:46.468556+00:00
-- url     : https://prove2.me/theorems/2ef529c2-cc28-4f58-b66b-00e021b50aea
-- title:
--   Shallow quantum circuits: gates, layers and acceptance probability
-- statement:
--   Layered quantum circuits over {H, S, T, CNOT} on n wires: states as amplitude functions on bit-strings, gate semantics, layers, the LayerOk well-formedness condition (gates in a layer act on pairwise disjoint wires), and the acceptance probability of measuring one output wire.
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

namespace ShiShallow

abbrev Bits (n : ℕ) := Fin n → Bool

abbrev QState (n : ℕ) := Bits n → ℂ

noncomputable def hMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a && b then -(Real.sqrt 2)⁻¹ else (Real.sqrt 2)⁻¹

noncomputable def sMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then (if a then Complex.I else 1) else 0

noncomputable def tMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    if a = b then (if a then Complex.exp (Complex.I * Real.pi / 4) else 1) else 0

/-- One-qubit gate on wire `i`; equals `I ⊗ ⋯ ⊗ U ⊗ ⋯ ⊗ I` with `U`'s row index on the
output wire. -/
noncomputable def apply1 {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n) :
    QState n :=
  fun x => ∑ b : Bool, U (x i) b * ψ (Function.update x i b)

/-- CNOT with control `i`, target `j`. Only a permutation when `i ≠ j`; `cnotState i i` is a
rank-deficient reset map, so every lemma about it must carry that hypothesis. -/
def cnotState {n : ℕ} (i j : Fin n) (_hij : i ≠ j) (ψ : QState n) : QState n :=
  fun x => ψ (Function.update x j (xor (x j) (x i)))

inductive Instr (n : ℕ) where
  | h (i : Fin n)
  | s (i : Fin n)
  | t (i : Fin n)
  | cnot (i j : Fin n) (hij : i ≠ j)

noncomputable def Instr.apply {n : ℕ} : Instr n → QState n → QState n
  | .h i => apply1 hMat i
  | .s i => apply1 sMat i
  | .t i => apply1 tMat i
  | .cnot i j hij => cnotState i j hij

/-- The wires an instruction touches. -/
def Instr.support {n : ℕ} : Instr n → Finset (Fin n)
  | .h i => {i}
  | .s i => {i}
  | .t i => {i}
  | .cnot i j _ => {i, j}

/-- A layered circuit: a list of layers, each a list of instructions. -/
abbrev Layered (n : ℕ) := List (List (Instr n))

/-- Depth is the number of layers. -/
def depth {n : ℕ} (c : Layered n) : ℕ := c.length

/-- A layer is well-formed when its gates act on pairwise disjoint wires — without this the
doubling bound below is false. -/
def LayerOk {n : ℕ} (l : List (Instr n)) : Prop :=
  l.Pairwise fun a b => Disjoint a.support b.support

noncomputable def runLayer {n : ℕ} (l : List (Instr n)) (ψ : QState n) : QState n :=
  l.foldl (fun st g => g.apply st) ψ

noncomputable def runLayered {n : ℕ} (c : Layered n) (ψ : QState n) : QState n :=
  c.foldl (fun st l => runLayer l st) ψ

def inputState {n m : ℕ} (x : Bits n) : QState (n + m) :=
  fun y => if (∀ i : Fin n, y (Fin.castAdd m i) = x i) ∧ (∀ k : Fin m, y (Fin.natAdd n k) = false)
           then 1 else 0

noncomputable def acceptProb {n m : ℕ} (c : Layered (n + m)) (x : Bits n)
    (out : Fin (n + m)) : ℝ :=
  ∑ y : Bits (n + m), if y out then ‖runLayered c (inputState x) y‖ ^ 2 else 0

theorem depth_nil {n : ℕ} : depth ([] : Layered n) = 0 := rfl

/-- CNOT permutes the computational basis, and is an involution when `i ≠ j`. -/
def cnotEquiv {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Bits n ≃ Bits n where
  toFun x := Function.update x j (xor (x j) (x i))
  invFun x := Function.update x j (xor (x j) (x i))
  left_inv x := by
    funext k
    by_cases hk : k = j
    · rw [hk]
      simp only [Function.update_self, Function.update_of_ne hij]
      cases hxj : x j <;> cases hxi : x i <;> simp
    · simp [Function.update_of_ne hk]
  right_inv x := by
    funext k
    by_cases hk : k = j
    · rw [hk]
      simp only [Function.update_self, Function.update_of_ne hij]
      cases hxj : x j <;> cases hxi : x i <;> simp
    · simp [Function.update_of_ne hk]

theorem cnotEquiv_apply {n : ℕ} (i j : Fin n) (hij : i ≠ j) (w : Bits n) :
    cnotEquiv i j hij w = Function.update w j (xor (w j) (w i)) := rfl

end ShiShallow


