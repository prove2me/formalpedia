-- Prove2me | Definitions.Def_LindbladQueryOptimal_Simulation_Circuits
-- name    : LindbladQueryOptimal_Simulation_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:41.737089+00:00
-- url     : https://prove2.me/theorems/fe83edbd-4d94-4bd2-9226-66b341596495
-- title:
--   Physical oracle circuits, full output channels and independent resource counters
-- statement:
--   A circuit is a finite list of arbitrary unitary gates on one or two selected qubit wires and calls to an individual input oracle or its adjoint, optionally controlled by one distinct wire. Its matrix is the chronological product of these operations. Wire selections merely locate operations; they do not implement a free permutation or an unknown register-sized gate.
--
--   The retained system consists of the first $n$ wires. Every work wire starts in $|0\rangle$, and all work wires are traced out at the end. Equivalently, the output map sums $K_zXK_z^\dagger$ over every work-register basis outcome $z$, so both success and failure outputs are retained. The query counter counts forward, inverse and controlled calls together for each individual oracle. The additional-gate counter counts only the one-/two-qubit constructors.
--
--   Known zero-padding range tests are themselves elementary circuits with clean auxiliary work. They toggle a branch flag exactly when all block-encoding ancillas are zero, and return their work to zero. Their actual total elementary-gate count defines $C_{\rm anc}$. The corresponding embedding identifies the same system wires with this zero-ancilla branch; it requires no system-wide copying operation. The costed tests support the branch changes and controlled rotations used for these embeddings. The gate scale retains the product of the two logarithms in Theorem 19.
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Definition 2, Theorem 19 and §§4.3.2–4.3.5, pp. 6, 26–27, 35–40; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Core

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Apply a matrix to the indicated ordered wires and the identity to all other wires.
Wire placement is syntax, not a free register permutation gate. -/
def onWires {w k : ℕ} (p : Fin k ↪ Fin w) (U : Op (Bits k)) : Op (Bits w) :=
  fun x y => if ∀ i, (∀ j, p j ≠ i) → x i = y i then U (x ∘ p) (y ∘ p) else 0

/-- Elementary gates have at most two wires. A query optionally has one separate
control wire; inverses are charged just like forward queries. -/
inductive CircuitGate (w m : ℕ) (width : Fin m → ℕ) where
  | elementary (k : ℕ) (hk : k = 1 ∨ k = 2) (p : Fin k ↪ Fin w)
      (U : Op (Bits k)) (hU : unitary U)
  | query (j : Fin m) (inverse : Bool) (p : Fin (width j) ↪ Fin w)
      (control : Option (Fin w)) (hc : ∀ c, control = some c → ∀ i, c ≠ p i)

def gateMatrix {w m : ℕ} {width : Fin m → ℕ}
    (O : ∀ j, Op (Bits (width j))) : CircuitGate w m width → Op (Bits w)
  | .elementary _ _ p U _ => onWires p U
  | .query j inverse p control _ =>
    let U := if inverse then (O j)ᴴ else O j
    match control with
    | none => onWires p U
    | some c => fun x y =>
      if x c = true ∧ y c = true then onWires p U x y
      else if x c = false ∧ y c = false ∧ x = y then 1 else 0

def elementaryCount {w m : ℕ} {width : Fin m → ℕ}
    (gates : List (CircuitGate w m width)) : ℕ :=
  (gates.map fun g => match g with | .elementary .. => 1 | .query .. => 0).sum

def oracleCount {w m : ℕ} {width : Fin m → ℕ}
    (gates : List (CircuitGate w m width)) (j : Fin m) : ℕ :=
  (gates.map fun g => match g with
    | .elementary .. => 0 | .query k .. => if k = j then 1 else 0).sum

def circuitMatrix {w m : ℕ} {width : Fin m → ℕ}
    (O : ∀ j, Op (Bits (width j))) (gates : List (CircuitGate w m width)) : Op (Bits w) :=
  gates.foldl (fun A g => gateMatrix O g * A) 1

/-- First n wires are the retained system. All work wires start in zero and are
traced out, without any success projection. -/
structure OracleCircuit (n m : ℕ) (width : Fin m → ℕ) where
  work : ℕ
  gates : List (CircuitGate (n+work) m width)

def joinBits {n w : ℕ} (x : Bits n) (z : Bits w) : Bits (n+w) := fun i =>
  if h : i.val < n then x ⟨i.val,h⟩ else z ⟨i.val-n, by omega⟩

def circuitKraus {n m : ℕ} {width : Fin m → ℕ}
    (C : OracleCircuit n m width) (O : ∀ j, Op (Bits (width j)))
    (z : Bits C.work) : Op (Bits n) := fun x y =>
  circuitMatrix O C.gates (joinBits x z) (joinBits y (fun _ => false))

def circuitChannel {n m : ℕ} {width : Fin m → ℕ}
    (C : OracleCircuit n m width) (O : ∀ j, Op (Bits (width j)))
    (X : Op (Bits n)) : Op (Bits n) :=
  ∑ z, circuitKraus C O z * X * (circuitKraus C O z)ᴴ

/-- Known elementary circuits for the range tests of the standard zero-padding
embeddings. The system wires are spectators: embedding/unembedding is the fixed
identification of the same system wires with the zero-ancilla sector. The test
also implements the controlled change of the public/private flag on that sector. -/
structure AncillaRoutines (n m : ℕ) (width : Fin m → ℕ) where
  tests : ∀ j, OracleCircuit (width j - n + 1) 0 (Fin.elim0)

def rangeFlag (a : ℕ) : Op (Bits (a+1)) := fun x y =>
  if (∀ i : Fin a, x ⟨i.val,by omega⟩ = y ⟨i.val,by omega⟩) ∧
    x ⟨a,by omega⟩ = Bool.xor (y ⟨a,by omega⟩)
      (decide (∀ i : Fin a, y ⟨i.val,by omega⟩ = false)) then 1 else 0

def zeroInput (n w : ℕ) : Matrix (Bits (n+w)) (Bits n) ℂ := fun x y =>
  if x = joinBits y (fun _ => false) then 1 else 0

def validRoutines {n m : ℕ} {width : Fin m → ℕ}
    (R : AncillaRoutines n m width) : Prop :=
  ∀ j, let C := R.tests j
    circuitMatrix (fun i => Fin.elim0 i) C.gates * zeroInput _ C.work =
      zeroInput _ C.work * rangeFlag (width j - n)

def ancillaCost {n m : ℕ} {width : Fin m → ℕ}
    (R : AncillaRoutines n m width) : ℕ := ∑ j, elementaryCount (R.tests j).gates

/-- Index zero is H; the remaining indices are the individual jumps. -/
def inputWidth {m : ℕ} (aH : ℕ) (a : Fin m → ℕ) : Fin (m+1) → ℕ :=
  Fin.cases aH a

def inputOracles {m : ℕ} {aH : ℕ} {a : Fin m → ℕ}
    (OH : Op (Bits aH)) (OL : ∀ j, Op (Bits (a j))) :
    ∀ j, Op (Bits (inputWidth aH a j)) := Fin.cases OH OL

def gateScale (τ ε : ℝ) (m Canc : ℕ) : ℝ :=
  queryScale τ ε * (Canc + m +
    Real.log (Real.exp 1 + (τ+1)/ε) *
    Real.log (Real.exp 1 + ((m+1 : ℕ) : ℝ)*(τ+1)/ε))

end LindbladQueryOptimal.Simulation


