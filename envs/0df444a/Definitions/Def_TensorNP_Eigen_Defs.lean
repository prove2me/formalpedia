-- Prove2me | Definitions.Def_TensorNP_Eigen_Defs
-- name    : TensorNP_Eigen_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:27.19041+00:00
-- url     : https://prove2.me/theorems/0e6f3434-ae26-4ae0-adad-a0f75e3b99d4
-- title:
--   (3), Problems 1.2 and 2.2, Example 1.4 — tensor eigenvalue, quadratic feasibility, 3-colorability and their languages
-- statement:
--   This file fixes the three decision problems of the reduction of Hillar and Lim's Theorem 1.3.
--
--   **Tensor eigenvalue (eq. (3)).** Let $F$ be a field and $\mathcal A=[\![a_{ijk}]\!]\in F^{n\times n\times n}$ a 3-tensor. A scalar $\lambda\in F$ is an **eigenvalue** of $\mathcal A$ if there is a nonzero $\mathbf x=(x_1,\dots,x_n)\in F^n$ with
--
--   $$\sum_{i,j=1}^{n} a_{ijk}\,x_i x_j=\lambda x_k,\qquad k=1,\dots,n.$$
--
--   The contraction is over the first two indices; there is no normalization of $\mathbf x$.
--
--   **Quadratic feasibility.** A family of $n\times n$ matrices $A_i$ (not necessarily symmetric) defines the homogeneous quadratic system $\{\mathbf x^\top A_i\mathbf x=0\}_i$; the question is whether it has a nonzero solution $\mathbf x\in F^n$.
--
--   **Instances and languages.** All instances are written in binary over the four-letter alphabet $\{0,1,-,\#\}$: a natural number is its binary digits followed by a separator, an integer carries a leading minus sign when negative, and a rational number $q$ is the numerator then the positive denominator of its reduced form.
--
--   1. **Graph 3-colorability.** A simple graph $G$ on the vertices $\{1,\dots,\nu\}$ is coded as $\nu$ followed by its adjacency matrix row by row ($1$ for an edge, $0$ otherwise). The language consists of the codes of the graphs having a proper 3-coloring, i.e. an assignment of one of three colors to every vertex such that adjacent vertices receive different colors.
--   2. **Tensor $\lambda$-eigenvalue over $F$ (Problem 1.2)**, for a fixed $\lambda\in\mathbb Q$. A rational tensor $\mathcal A\in\mathbb Q^{n\times n\times n}$ is coded as $n$ followed by its entries $a_{ijk}$ in lexicographic order of $(i,j,k)$. The language consists of the codes of the tensors for which $\lambda$ is an eigenvalue with an eigenvector in $F^n$. The case $F=\mathbb R$, $\lambda=0$ is the target of Theorem 1.3.
--   3. **Quadratic feasibility over $F$ (Problem 2.2).** A system of rational matrices $A_1,\dots,A_m\in\mathbb Q^{n\times n}$ is coded as $m$, $n$, then the entries $(A_i)_{ab}$ in lexicographic order of $(i,a,b)$. The language consists of the codes of the systems with a nonzero solution $\mathbf x\in F^n$.
--
--   Each code determines its instance. These are the objects whose computational relationship the mission's goal theorem states.
--
--   **Formalization Note** Indices are 0-based: the paper's $a_{ijk}$ is `A (i-1) (j-1) (k-1)`. Rational data are cast into $F$ by `Rat.cast`. Proper 3-colorability is Mathlib's `SimpleGraph.Colorable 3`. The alphabet `BSym` and the codes `encNat`, `encInt`, `encNats` are the published definitions of `ProjSchedTW.Complexity.Encoding`, and `Lang` is from `CookPvsNP_defs`. The graph code is the layout of `maxCutCode` in that file without its threshold.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:4, (3); p. 0:5, Problem 1.2; p. 0:7, Example 1.4; p. 0:12, Problem 2.2

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace TensorNP.Eigen

open CookPvsNP ProjSchedTW.Complexity Matrix

/-! # Tensor eigenvalue, quadratic feasibility and graph 3-colorability as decision problems

Hillar & Lim, *Most Tensor Problems Are NP-Hard*, J. ACM 60(6) (2013): eq. (3) and Problem 1.2
(pp. 0:4–0:5), Problem 2.2 (p. 0:12), Example 1.4 (p. 0:7).

Conventions: the paper's indices `1, …, n` are the Lean indices `0, …, n - 1`; a 3-tensor
`A ∈ F^{n×n×n}` is an array `Fin n → Fin n → Fin n → F`, and the paper's `a_{ijk}` is
`A (i-1) (j-1) (k-1)`. Rational input data are cast into the field `F` with `Rat.cast`. -/

/-- Eq. (3): `λ ∈ F` is an eigenvalue of the 3-tensor `A ∈ F^{n×n×n}` if there is a nonzero
`x ∈ F^n` with `∑_{i,j} a_{ijk} x_i x_j = λ x_k` for every `k`. The contraction is over the first
two indices. -/
def IsEigenvalue {F : Type} [CommRing F] {n : ℕ} (A : Fin n → Fin n → Fin n → F) (lam : F) :
    Prop :=
  ∃ x : Fin n → F, x ≠ 0 ∧ ∀ k : Fin n, ∑ i, ∑ j, A i j k * x i * x j = lam * x k

/-- The system of homogeneous quadratic equations `{xᵀ A_i x = 0}_{i ∈ ι}` in the unknowns
`x ∈ R^κ` has a nonzero solution (the question of Problem 2.2). The matrices `A_i` need not be
symmetric. -/
def QuadSolvable {R : Type} [CommRing R] {ι κ : Type} [Fintype κ]
    (A : ι → Matrix κ κ R) : Prop :=
  ∃ x : κ → R, x ≠ 0 ∧ ∀ i, x ⬝ᵥ (A i *ᵥ x) = 0

/-- A rational 3-tensor viewed over the field `F`. -/
def castTensor (F : Type) [Field F] {n : ℕ} (A : Fin n → Fin n → Fin n → ℚ) :
    Fin n → Fin n → Fin n → F :=
  fun i j k => (A i j k : F)

/-- A family of rational matrices viewed over the field `F`. -/
def castMatrices (F : Type) [Field F] {ι κ : Type} (A : ι → Matrix κ κ ℚ) :
    ι → Matrix κ κ F :=
  fun i => (A i).map (Rat.cast : ℚ → F)

/-! ## Binary codes of instances (alphabet `BSym` of `ProjSchedTW.Complexity.Encoding`) -/

/-- A rational number `q` in binary: the integer numerator, then the positive denominator of its
reduced form. -/
def encRat (q : ℚ) : List BSym := encInt q.num ++ encNat q.den

open Classical in
/-- The code of a simple graph on the vertices `Fin ν`: `ν`, then the adjacency matrix row by row
(`1` for an edge, `0` otherwise), all in binary (the layout of `maxCutCode` without its threshold).
It determines `ν` and `G`. -/
noncomputable def graphCode {ν : ℕ} (G : SimpleGraph (Fin ν)) : List BSym :=
  encNats ([ν] ++ (List.ofFn fun i : Fin ν => List.ofFn fun j : Fin ν =>
    if G.Adj i j then 1 else 0).flatten)

/-- The code of a rational 3-tensor `A ∈ ℚ^{n×n×n}`: `n`, then the entries `a_{ijk}` in
lexicographic order of `(i, j, k)`, each as `encRat`. It determines `n` and `A`. -/
def tensorCode {n : ℕ} (A : Fin n → Fin n → Fin n → ℚ) : List BSym :=
  encNat n ++ (List.ofFn fun i : Fin n => (List.ofFn fun j : Fin n =>
    (List.ofFn fun k : Fin n => encRat (A i j k)).flatten).flatten).flatten

/-- The code of a system of `m` rational `n × n` matrices `A_1, …, A_m`: `m`, `n`, then the
entries `(A_i)_{ab}` in lexicographic order of `(i, a, b)`, each as `encRat`. It determines `m`,
`n` and the matrices. -/
def systemCode {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ) : List BSym :=
  encNat m ++ encNat n ++ (List.ofFn fun i : Fin m => (List.ofFn fun a : Fin n =>
    (List.ofFn fun b : Fin n => encRat (A i a b)).flatten).flatten).flatten

/-! ## The languages -/

/-- GRAPH 3-COLORABILITY (Example 1.4): codes of the simple graphs having a proper 3-coloring,
i.e. an assignment of one of three colors to each vertex such that adjacent vertices receive
different colors (`SimpleGraph.Colorable 3`). -/
def threeColLang : Lang BSym :=
  { w | ∃ (ν : ℕ) (G : SimpleGraph (Fin ν)), G.Colorable 3 ∧ w = graphCode G }

/-- Problem 1.2 (TENSOR λ-EIGENVALUE) over the field `F` for a fixed `λ ∈ ℚ`: codes of the
rational tensors `A ∈ ℚ^{n×n×n}` (any `n`) for which `λ` is an eigenvalue of `A` with an
eigenvector in `F^n`. -/
def tensorEigLang (F : Type) [Field F] (lam : ℚ) : Lang BSym :=
  { w | ∃ (n : ℕ) (A : Fin n → Fin n → Fin n → ℚ),
      IsEigenvalue (castTensor F A) (lam : F) ∧ w = tensorCode A }

/-- Tensor `0`-eigenvalue over `ℝ`: Problem 1.2 with `F = ℝ` and `λ = 0`. -/
def tensorZeroEigLangR : Lang BSym := tensorEigLang ℝ 0

/-- Problem 2.2 (QUADRATIC FEASIBILITY) over the field `F`: codes of the systems of rational
matrices `A_1, …, A_m ∈ ℚ^{n×n}` such that `{xᵀ A_i x = 0}_{i=1}^m` has a nonzero solution
`x ∈ F^n`. -/
def quadFeasLang (F : Type) [Field F] : Lang BSym :=
  { w | ∃ (m n : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℚ),
      QuadSolvable (castMatrices F A) ∧ w = systemCode A }

end TensorNP.Eigen


