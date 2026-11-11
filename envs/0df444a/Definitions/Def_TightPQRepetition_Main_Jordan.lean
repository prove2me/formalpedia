-- Prove2me | Definitions.Def_TightPQRepetition_Main_Jordan
-- name    : TightPQRepetition_Main_Jordan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T23:32:12.98833+00:00
-- url     : https://prove2.me/theorems/2ab9150e-b465-4ada-a567-cbc38b0caf0e
-- title:
--   Jordan decompositions of two projectors, and rotation circuits (Definition 3)
-- statement:
--   Let $\Pi_A,\Pi_B$ be Hermitian projectors. A **Jordan decomposition** writes the space as an orthogonal sum of finitely many subspaces $S_j$ of dimension one or two, with vectors $v_j,v_j^\perp,w_j,w_j^\perp$ spanning $S_j$, so that $\Pi_A$ acts on $S_j$ as $|v_j\rangle\langle v_j|$ and $\Pi_B$ as $|w_j\rangle\langle w_j|$. On a one-dimensional $S_j$ one of $v_j,v_j^\perp$ is a unit vector and the other is zero, and likewise for $w$. On a two-dimensional $S_j$ both pairs are orthonormal. The **singular value** is $\varsigma_j=\langle w_j|v_j\rangle\ge0$.
--
--   Definition 3 is $C_\Pi NOT=X\otimes\Pi+I\otimes(I-\Pi)$. A **rotation program** is a list of calls to $C_{\Pi_A}NOT$, calls to $C_{\Pi_B}NOT$, and gates on one ancilla qubit. Its operator is computed as a $2\times2$ block matrix over the operators on the system, the block index being the ancilla. A program has the properties of Theorem 3.9 for $\varepsilon,\delta$ if it has $m$ calls of each kind and $m$ gates, $m$ is at most $c\log(1/\varepsilon)/\delta$, the ancilla returns exactly to $|0\rangle$ from $|0\rangle$, and the resulting operator $U$ is unitary with
--   $$\Pi_BU\Pi_A=\sum_j\tilde\varsigma_j|w_j\rangle\langle v_j|,\qquad\tilde\varsigma_j\in[1-\varepsilon,1]\text{ if }\varsigma_j\ge\delta,\quad\tilde\varsigma_j\in[-1,1]\text{ otherwise},$$
--   on every finite-dimensional space.
--
--   **Formalization Note** The operator is defined in any complex algebra, so the same program acts on `H →L[ℂ] H` and on matrices. The strict bounds $0<\varsigma_j<1$ on two-dimensional blocks express that the two bases are distinct.
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Lemma 3.8 and the following text, Definition 3, Theorem 3.9, printed pp. 12–13 / PDF pp. 14–15

import Mathlib

namespace TightPQRepetition.Main

/-!
Brakerski, Huang, Kalai, Spooner, STOC 2027 submission #158, §3.4 (PDF pp. 14–15): the joint
decomposition of two Hermitian projectors, Definition 3, and the rotation circuits of Theorem 3.9.
-/

open scoped InnerProductSpace

/-- A Hermitian projector. -/
def IsHermitianProjector {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint P ∧ IsIdempotentElem P

/-- The data of Jordan's lemma (Lemma 3.8 and the convention after it, PDF pp. 14–15): an
orthogonal decomposition `H = ⊕ⱼ Sⱼ` into subspaces of dimension one and two, with bases
`{vⱼ, vⱼ^⊥}` and `{wⱼ, wⱼ^⊥}` of `Sⱼ`, such that `Π_A` projects `Sⱼ` onto `vⱼ` and `Π_B` onto `wⱼ`.
On a one-dimensional `Sⱼ`, one of `vⱼ, vⱼ^⊥` is a unit vector and the other is the zero vector, and
likewise for `wⱼ, wⱼ^⊥`: `vⱼ` is the zero vector exactly when `Π_A` vanishes there. The singular
value is `ςⱼ = ⟨wⱼ|vⱼ⟩ ≥ 0`. -/
structure JordanDecomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (PA PB : H →L[ℂ] H) where
  /-- Index of the blocks. -/
  idx : Type
  /-- There are finitely many blocks. -/
  fin : Fintype idx
  /-- The blocks `Sⱼ`. -/
  S : idx → Submodule ℂ H
  /-- The blocks are pairwise orthogonal. -/
  orthogonal : ∀ i j, i ≠ j → S i ⟂ S j
  /-- The blocks span `H`. -/
  total : iSup S = ⊤
  /-- Each block has dimension one or two. -/
  dim : ∀ j, Module.finrank ℂ (S j) = 1 ∨ Module.finrank ℂ (S j) = 2
  /-- The singular vectors of `Π_A`. -/
  v : idx → H
  /-- Their complements in the block. -/
  vperp : idx → H
  /-- The singular vectors of `Π_B`. -/
  w : idx → H
  /-- Their complements in the block. -/
  wperp : idx → H
  /-- The singular values. -/
  sv : idx → ℝ
  /-- `{vⱼ, vⱼ^⊥}` spans the block. -/
  span_v : ∀ j, S j = Submodule.span ℂ {v j, vperp j}
  /-- `{wⱼ, wⱼ^⊥}` spans the block. -/
  span_w : ∀ j, S j = Submodule.span ℂ {w j, wperp j}
  /-- `Π_A` acts on `Sⱼ` as `|vⱼ⟩⟨vⱼ|`; in particular `Sⱼ` is invariant. -/
  act_A : ∀ j, ∀ x ∈ S j, PA x = ⟪v j, x⟫_ℂ • v j
  /-- `Π_B` acts on `Sⱼ` as `|wⱼ⟩⟨wⱼ|`; in particular `Sⱼ` is invariant. -/
  act_B : ∀ j, ∀ x ∈ S j, PB x = ⟪w j, x⟫_ℂ • w j
  /-- The labelling of a one-dimensional block. -/
  one_dim : ∀ j, Module.finrank ℂ (S j) = 1 →
    ((‖v j‖ = 1 ∧ vperp j = 0) ∨ (v j = 0 ∧ ‖vperp j‖ = 1)) ∧
    ((‖w j‖ = 1 ∧ wperp j = 0) ∨ (w j = 0 ∧ ‖wperp j‖ = 1))
  /-- In a two-dimensional block both pairs are orthonormal, and the two bases are distinct. -/
  two_dim : ∀ j, Module.finrank ℂ (S j) = 2 →
    ‖v j‖ = 1 ∧ ‖vperp j‖ = 1 ∧ ⟪v j, vperp j⟫_ℂ = 0 ∧
    ‖w j‖ = 1 ∧ ‖wperp j‖ = 1 ∧ ⟪w j, wperp j⟫_ℂ = 0 ∧ 0 < sv j ∧ sv j < 1
  /-- `ςⱼ = ⟨wⱼ|vⱼ⟩`, a nonnegative real number. -/
  overlap : ∀ j, ⟪w j, v j⟫_ℂ = (sv j : ℂ)
  /-- Singular values are nonnegative. -/
  sv_nonneg : ∀ j, 0 ≤ sv j

attribute [instance] JordanDecomposition.fin

/-- The rank-one operator `|y⟩⟨x|`. -/
noncomputable def ketBra {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (y x : H) : H →L[ℂ] H :=
  (innerSL ℂ x).smulRight y

/-- The display of Theorem 3.9: `U` is unitary and `Π_B U Π_A = ∑ⱼ ς̃ⱼ |wⱼ⟩⟨vⱼ|`, with `ς̃ⱼ` real,
in `[1 - ε, 1]` when `ςⱼ ≥ δ` and in `[-1, 1]` otherwise. -/
def IsRotationUnitary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {PA PB : H →L[ℂ] H} (J : JordanDecomposition PA PB) (ε δ : ℝ) (U : H →L[ℂ] H) : Prop :=
  U ∈ unitary (H →L[ℂ] H) ∧ ∃ sv' : J.idx → ℝ,
    PB * U * PA = ∑ j, (sv' j : ℂ) • ketBra (J.w j) (J.v j) ∧
    ∀ j, (δ ≤ J.sv j → sv' j ∈ Set.Icc (1 - ε) 1) ∧ (J.sv j < δ → sv' j ∈ Set.Icc (-1) 1)

/-- One instruction of a rotation circuit: a call to `C_{Π_A}NOT`, a call to `C_{Π_B}NOT`, or a gate
on the ancilla. -/
inductive RotationInstr
  | callA
  | callB
  | gate (g : Matrix (Fin 2) (Fin 2) ℂ)

/-- A rotation circuit, in order of application (head first). -/
abbrev RotationProgram := List RotationInstr

/-- Definition 3: `C_Π NOT = X ⊗ Π + I ⊗ (I - Π)`, as a `2 × 2` block matrix over the operators on
the system; the block index is the ancilla, `0` being `|0⟩`. -/
def cNot {A : Type*} [Ring A] (P : A) : Matrix (Fin 2) (Fin 2) A :=
  !![1 - P, P; P, 1 - P]

/-- The operator of one instruction. -/
def instrOp {A : Type*} [Ring A] [Algebra ℂ A] (PA PB : A) :
    RotationInstr → Matrix (Fin 2) (Fin 2) A
  | .callA => cNot PA
  | .callB => cNot PB
  | .gate g => g.map (algebraMap ℂ A)

/-- The operator `C^{Π_B,Π_A}` of a rotation circuit on system ⊗ ancilla. -/
def programOp {A : Type*} [Ring A] [Algebra ℂ A] (PA PB : A) (p : RotationProgram) :
    Matrix (Fin 2) (Fin 2) A :=
  (p.map (instrOp PA PB)).reverse.prod

/-- The number of calls to `C_{Π_A}NOT`. -/
def RotationProgram.callsA (p : RotationProgram) : ℕ :=
  p.countP fun i => match i with | .callA => true | _ => false

/-- The number of calls to `C_{Π_B}NOT`. -/
def RotationProgram.callsB (p : RotationProgram) : ℕ :=
  p.countP fun i => match i with | .callB => true | _ => false

/-- The number of single-qubit gates. -/
def RotationProgram.gates (p : RotationProgram) : ℕ :=
  p.countP fun i => match i with | .gate _ => true | _ => false

/-- A circuit with the properties of Theorem 3.9 for the parameters `ε`, `δ`, with constant `c` in
the `O(·)`: `m` calls to each controlled projector and `m` unitary gates on one ancilla, with
`m ≤ c · log(1/ε)/δ`; and for all Hermitian projectors on every finite-dimensional space, the
ancilla returns exactly to `|0⟩` from `|0⟩` on every input, and the resulting operator `U` satisfies
the display of Theorem 3.9 for every singular value decomposition of `Π_B Π_A`. -/
def IsRotationProgram (c ε δ : ℝ) (p : RotationProgram) : Prop :=
  (∀ g, RotationInstr.gate g ∈ p → g ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
  p.callsA = p.callsB ∧ p.gates = p.callsA ∧ (p.callsA : ℝ) ≤ c * (Real.log (1 / ε) / δ) ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (PA PB : H →L[ℂ] H), IsHermitianProjector PA → IsHermitianProjector PB →
    programOp PA PB p 1 0 = 0 ∧
    programOp PA PB p 0 0 ∈ unitary (H →L[ℂ] H) ∧
    ∀ J : JordanDecomposition PA PB, IsRotationUnitary J ε δ (programOp PA PB p 0 0)

/-- A choice of rotation circuit for all parameters `ε, δ ∈ (0, 1)`, with one constant `c`. -/
def IsRotationFamily (c : ℝ) (prog : ℝ → ℝ → RotationProgram) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → IsRotationProgram c ε δ (prog ε δ)

end TightPQRepetition.Main


