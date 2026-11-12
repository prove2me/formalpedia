-- Prove2me | Definitions.Def_LocalSweepFT_liftOn
-- name    : LocalSweepFT_liftOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:38:28.79187+00:00
-- url     : https://prove2.me/theorems/29be78d7-4344-4823-9d2a-6a7dee19f3af
-- title:
--   Qubit operators: Paulis, transversal Hadamard, operators on a subset of wires, Kraus families
-- statement:
--   Operators on a register of qubits labelled by a finite set $A$ are complex matrices indexed by bit strings $A\to\mathbb F_2$. The file defines
--   1. the Paulis $X^c:|b\rangle\mapsto|b+c\rangle$ and $Z^c:|b\rangle\mapsto(-1)^{\langle c,b\rangle}|b\rangle$;
--   2. the transversal Hadamard $H^{\otimes A}$ with $H=2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$;
--   3. $K\otimes 1$, the operator $K$ acting on the wires $e(A)$ of a larger system and the identity elsewhere;
--   4. the action $\rho\mapsto\sum_K K\rho K^\dagger$ of a Kraus family, and the Kraus family of a composite channel;
--   5. the all-zero state $|0\dots0\rangle\langle0\dots0|$.
--
--   These are the building blocks of the ideal circuits, the sweep cycle and the Toric encoded circuits.
--
--   **Formalization Note** Every use of $K\otimes 1$ in the mission has an injective wire map $e$.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), §3, Quantum notation, p.12

import Mathlib

open Matrix

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…), §3 "Quantum notation" (p.12): qubit registers, Pauli and
Hadamard operators, operators acting on a subset of the wires, and Kraus families. -/

/-- Operators on the qubits labelled by `A`: complex matrices indexed by computational-basis
strings `A → 𝔽₂`. -/
abbrev Op (A : Type) := Matrix (A → ZMod 2) (A → ZMod 2) ℂ

/-- The sign `(−1)^z` of `z ∈ 𝔽₂`. -/
def sgn (z : ZMod 2) : ℂ := if z = 0 then 1 else -1

open Classical in
/-- The Pauli `X^c = ⊗_q X^{c_q}`: `|b⟩ ↦ |b + c⟩`. -/
noncomputable def xOn {A : Type} [DecidableEq A] (c : A → ZMod 2) : Op A :=
  fun a b => if a = b + c then 1 else 0

/-- The Pauli `Z^c = ⊗_q Z^{c_q}`: `|b⟩ ↦ (−1)^{⟨c, b⟩} |b⟩`. -/
def zOn {A : Type} [Fintype A] [DecidableEq A] (c : A → ZMod 2) : Op A :=
  fun a b => if a = b then sgn (∑ q, c q * b q) else 0

/-- The transversal Hadamard `H^{⊗A}`, with `H = 2^{−1/2} [[1, 1], [1, −1]]` (p.12). -/
noncomputable def hadOn {A : Type} [Fintype A] : Op A :=
  fun a b => ((Real.sqrt 2 : ℂ)⁻¹) ^ Fintype.card A * sgn (∑ q, a q * b q)

open Classical in
/-- The operator `K ⊗ 1` on the wires `W`, where `K` acts on the wires `e(A)`, read in the order
given by `e`, and the identity acts on the other wires.

**Formalization Note.** Every use in this mission has `e` injective. -/
noncomputable def liftOn {A W : Type} (e : A → W) (K : Op A) : Op W :=
  fun a b => if ∀ w, w ∉ Set.range e → a w = b w then K (a ∘ e) (b ∘ e) else 0

/-- The action `ρ ↦ Σ_K K ρ K†` of a Kraus family. -/
noncomputable def applyK {X Y : Type} [Fintype X] (Ks : List (Matrix Y X ℂ))
    (ρ : Matrix X X ℂ) : Matrix Y Y ℂ :=
  (Ks.map fun K => K * ρ * K.conjTranspose).sum

/-- The Kraus family of the composite channel: first `F`, then `G` (operators `G_j F_i`). -/
noncomputable def compK {X Y Z : Type} [Fintype Y] (F : List (Matrix Y X ℂ))
    (G : List (Matrix Z Y ℂ)) : List (Matrix Z X ℂ) :=
  (F.product G).map fun p => p.2 * p.1

open Classical in
/-- The all-zero basis state `|0…0⟩⟨0…0|`. -/
noncomputable def zeroState (A : Type) : Op A := fun a b => if a = 0 ∧ b = 0 then 1 else 0

end LocalSweepFT


