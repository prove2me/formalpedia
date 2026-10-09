-- Prove2me | Definitions.Def_WiesemannRMDP_AffineSDP_ParamSet
-- name    : WiesemannRMDP_AffineSDP_ParamSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:03.746134+00:00
-- url     : https://prove2.me/theorems/02c61f31-4eb5-4458-ae28-38f14a665f26
-- title:
--   Quadratically constrained parameter set Ξ (3b), its standing assumptions, the block matrices [σ, ½sᵀ; ½s, S] and Q_l, and ⪰ 0
-- statement:
--   This module collects the finite-dimensional objects that Proposition 3.7 and Theorem 3.8 of Wiesemann, Kuhn and Rustem speak about, independently of any Markov decision process.
--
--   **The parameter set.** Given symmetric matrices $O_1,\dots,O_L\in\mathbb S^q$, vectors $o_1,\dots,o_L\in\mathbb R^q$ and scalars $\omega_1,\dots,\omega_L\in\mathbb R$, let
--   $$\Xi := \{\xi\in\mathbb R^q : \xi^\top O_l\,\xi + o_l^\top\xi + \omega_l \ge 0\ \ \forall\, l=1,\dots,L\}. \tag{3b}$$
--   The paper's **standing assumptions** on these data are: $O_l\preceq 0$ for every $l$ (so each constraint function is concave and $\Xi$ is convex), $\Xi$ is bounded, and $\Xi$ contains a **Slater point** $\bar\xi$ with $\bar\xi^\top O_l\bar\xi + o_l^\top\bar\xi + \omega_l > 0$ for all $l$.
--
--   **Block matrices.** For $\sigma\in\mathbb R$, $s\in\mathbb R^q$ and a $q\times q$ matrix $S$, write
--   $$\begin{bmatrix}\sigma & \tfrac12 s^\top\\ \tfrac12 s & S\end{bmatrix}\in\mathbb R^{(1+q)\times(1+q)},$$
--   with the scalar entry in the top-left corner; its quadratic form at $(1,\xi)$ is $\sigma + s^\top\xi + \xi^\top S\xi$. The matrix of the $l$-th constraint of (3b) is $Q_l := \begin{bmatrix}\omega_l & \tfrac12 o_l^\top\\ \tfrac12 o_l & O_l\end{bmatrix}$.
--
--   **Semidefiniteness.** A square matrix $A$ satisfies $A\succeq 0$ if $x^\top A x\ge 0$ for every real vector $x$. For symmetric $A$ this is ordinary positive semidefiniteness.
--
--   These are the building blocks of the approximate S-lemma (17) and of the semidefinite program (20).
--
--   **Formalization Note.** Rows and columns of the block matrices are indexed by `Unit ⊕ Fin q`, the `Unit` index being the scalar position. $A\succeq 0$ is defined through the quadratic form (`IsPSDForm`) and not as Mathlib's `PosSemidef`, because the matrices of (20c) have the non-symmetric lower-right block $\lambda K_{sa}^\top W$; Mathlib's `PosSemidef` of a non-symmetric matrix is false. The page prints $\omega$ without the index $l$ in (3b) and the Slater condition; $\omega_l$ is used, as in (16b), (17), (20b) and (20c). $O_l\preceq 0$ is `(-(O l)).PosSemidef`, which includes symmetry.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 1 (Notation: ⪰), p. 6 ((3b), Slater point, boundedness), pp. 20–21 (block matrices of (17), (20b), (20c))

import Mathlib

namespace WiesemannRMDP.AffineSDP

open Matrix

/-- The parameter set (3b) of Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*,
Optimization Online 2610 (revision of February 9, 2012), p. 6:
`Ξ := {ξ ∈ ℝ^q : ξᵀ O_l ξ + o_lᵀ ξ + ω_l ≥ 0 ∀ l = 1, …, L}`.

**Formalization Note.** The page prints `ω` without the index `l` in (3b); (16b), (17), (20b)
and (20c) print `ω_l`, which is used here. -/
def XiSet {q L : ℕ} (O : Fin L → Matrix (Fin q) (Fin q) ℝ) (o : Fin L → Fin q → ℝ)
    (ω : Fin L → ℝ) : Set (Fin q → ℝ) :=
  {ξ | ∀ l : Fin L, 0 ≤ ξ ⬝ᵥ (O l *ᵥ ξ) + o l ⬝ᵥ ξ + ω l}

/-- The standing assumptions on the data of (3b), p. 6: every `O_l` is a symmetric matrix with
`O_l ⪯ 0` (that is, `-O_l` is positive semidefinite), `Ξ` is bounded, and `Ξ` contains a Slater
point `ξ̄` with `ξ̄ᵀ O_l ξ̄ + o_lᵀ ξ̄ + ω_l > 0` for all `l`. -/
def XiStanding {q L : ℕ} (O : Fin L → Matrix (Fin q) (Fin q) ℝ) (o : Fin L → Fin q → ℝ)
    (ω : Fin L → ℝ) : Prop :=
  (∀ l : Fin L, (-(O l)).PosSemidef) ∧
  Bornology.IsBounded (XiSet O o ω) ∧
  ∃ ξbar : Fin q → ℝ, ∀ l : Fin L, 0 < ξbar ⬝ᵥ (O l *ᵥ ξbar) + o l ⬝ᵥ ξbar + ω l

/-- The `(1 + q) × (1 + q)` block matrix `[σ, ½ sᵀ; ½ s, S]` of (17), (20b), (20c), p. 20–21,
with the scalar entry first: rows and columns are indexed by `Unit ⊕ Fin q`, the `Unit` index
being the scalar position. Its quadratic form at `(1, ξ)` is `σ + sᵀ ξ + ξᵀ S ξ`.
`S` need not be symmetric (the lower-right block `λ K_saᵀ W` of (20c) is not). -/
noncomputable def quadBlock {q : ℕ} (σ : ℝ) (s : Fin q → ℝ) (S : Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Unit ⊕ Fin q) (Unit ⊕ Fin q) ℝ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => σ) (Matrix.of fun _ j => s j / 2)
    (Matrix.of fun i _ => s i / 2) S

/-- The block matrix `Q_l := [ω_l, ½ o_lᵀ; ½ o_l, O_l]` of the `l`-th constraint of (3b), which
appears in (17), (20b) and (20c). -/
noncomputable def Qblock {q L : ℕ} (O : Fin L → Matrix (Fin q) (Fin q) ℝ) (o : Fin L → Fin q → ℝ)
    (ω : Fin L → ℝ) (l : Fin L) : Matrix (Unit ⊕ Fin q) (Unit ⊕ Fin q) ℝ :=
  quadBlock (ω l) (o l) (O l)

/-- `A ⪰ 0` in the sense of the paper's Notation paragraph (p. 1: "A ⪰ B indicates that the
matrix A − B is positive semidefinite"), read as nonnegativity of the quadratic form:
`xᵀ A x ≥ 0` for every real vector `x`.

**Formalization Note.** For a symmetric matrix this is equivalent to Mathlib's
`Matrix.PosSemidef`. The quadratic-form reading is used because the matrix of (20c) has the
non-symmetric lower-right block `λ K_saᵀ W`; Mathlib's `PosSemidef` of a non-symmetric matrix is
false, which would make the program (20) infeasible. Only the symmetric part `(A + Aᵀ)/2` of `A`
matters. -/
def IsPSDForm {n : Type*} [Fintype n] (A : Matrix n n ℝ) : Prop :=
  ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)

end WiesemannRMDP.AffineSDP


