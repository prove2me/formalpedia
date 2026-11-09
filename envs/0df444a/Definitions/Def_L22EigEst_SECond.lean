-- Prove2me | Definitions.Def_L22EigEst_SECond
-- name    : L22EigEst_SECond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:14:15.501221+00:00
-- url     : https://prove2.me/theorems/e23522b1-de0e-4cde-8fee-636e2ef333a8
-- title:
--   Subspace embeddings (Definition 2.1) and the subspace embedding condition (Definition 4.12)
-- statement:
--   A square matrix $T$ is an **$\eta$-distortion subspace embedding** of a subspace $V\subseteq\mathbb R^n$ if
--
--   $$\big|\|v\|_2^2-\|Tv\|_2^2\big|\le\eta\|v\|_2^2\qquad\text{for all } v\in V.$$
--
--   Definition 2.1 states this for the column space $\{Xv\}$ of a matrix $X$. For a symmetric $A$ and $\lambda\ge0$, let $V_\lambda(A)$ be the span of the eigenvectors of $A$ whose eigenvalue has magnitude at least $\lambda$. A sampling matrix $S$ satisfies the **subspace embedding condition** for $A$ with parameter $L$ (Definition 4.12) if
--
--   $$\forall\lambda\ge L:\quad S \text{ is a } \min(L/\lambda,1/10)\text{-distortion subspace embedding of } V_\lambda(A).$$
--
--   Event E1 of Definition 4.2 is this condition for $A'$ with $L=\varepsilon\|A\|_F/200$. It is what Lemmas 4.13–4.15 need to compare the eigenvalues of $SAS^\top$ with those of $A$.
--
--   **Formalization Note** $V_\lambda(A)$ is the sum of the eigenspaces of $x\mapsto Ax$ for the eigenvalues $\mu$ with $|\mu|\ge\lambda$, a basis-free description. $S$ is any $n\times n$ real matrix and $L$ an explicit argument.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Definition 2.1, p.9; Definition 4.2 (Event E1), p.13; Definition 4.12, p.19

import Mathlib
open Matrix

namespace L22EigEst

/-- **Distortion subspace embedding** (Definition 2.1, p.9), Menand, Waingarten, STOC 2027
submission (manuscript sha256 b1f6adce…): "we say that a t×n matrix T is an ε-distortion subspace
embedding of X if for all v ∈ ℝ^d, |∥Xv∥2² − ∥TXv∥2²| ≤ ε∥Xv∥2²."

**Formalization Note.** Stated for a subspace `V ⊆ ℝⁿ` (the column space of `X`): `T` is an
`η`-distortion subspace embedding of `V` if `|‖v‖² − ‖Tv‖²| ≤ η‖v‖²` for every `v ∈ V`. Since
`{Xv : v ∈ ℝ^d}` is exactly the column space of `X`, this is Definition 2.1. `T` is a square
`n × n` matrix (the `n × n` view of a sampling matrix, p.9). -/
def IsSubspaceEmbedding {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (V : Submodule ℝ (Fin n → ℝ))
    (η : ℝ) : Prop :=
  ∀ v ∈ V, |v ⬝ᵥ v - (T *ᵥ v) ⬝ᵥ (T *ᵥ v)| ≤ η * (v ⬝ᵥ v)

/-- **The span of the eigenvectors of `A` with eigenvalue of magnitude at least `λ`**
(Definition 4.2, Event E1, p.13; Definition 4.12, p.19): the sum of the eigenspaces of `A` for the
eigenvalues `μ` with `|μ| ≥ λ`.

**Formalization Note.** Basis-free: a supremum of eigenspaces of the linear map `x ↦ Ax`. -/
noncomputable def bigSpan {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (thr : ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  ⨆ (μ : ℝ) (_ : thr ≤ |μ|), Module.End.eigenspace (Matrix.toLin' A) μ

/-- **The subspace embedding condition** (Definition 4.12, p.19; Assumption 4.1 in [SW25]),
Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…): "A sampling matrix S
satisfies the subspace embedding condition for A if for every λ ≥ L, S is a min(L/λ, 1/10)-distortion
subspace embedding on the span of the eigenvectors of A with eigenvalue of magnitude at least λ."
Event E1 of Definition 4.2 (p.13) is `SECond A′ S L` with `L = ε‖A‖_F/200`.

**Formalization Note.** `L` is an explicit argument; the statements that use the condition say
which `L`. `S` is any `n × n` real matrix (the `n × n` view of a sampling matrix). -/
def SECond {n : ℕ} (A S : Matrix (Fin n) (Fin n) ℝ) (L : ℝ) : Prop :=
  ∀ thr : ℝ, L ≤ thr → IsSubspaceEmbedding S (bigSpan A thr) (min (L / thr) (1 / 10))

end L22EigEst


