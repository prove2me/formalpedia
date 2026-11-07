-- Prove2me | Definitions.Def_AvgCaseTI_hull
-- name    : AvgCaseTI_hull
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:29.240437+00:00
-- url     : https://prove2.me/theorems/c56a6d3b-b9d4-471e-ad17-e510755fda85
-- title:
--   Trace-form orthogonal space, hull, self-dual matrices and lines, conjugate codes
-- statement:
--   Let $\mathrm M(n,\mathbb F)$ be the $n\times n$ matrices over a field $\mathbb F$, with the bilinear form $f(A,B)=\mathrm{Tr}(AB)$. A subspace $\mathcal A\le\mathrm M(n,\mathbb F)$ is a **matrix code**.
--   1. The **orthogonal space** of $\mathcal A$ is $\mathcal A^{\perp}=\{A'\in\mathrm M(n,\mathbb F):\mathrm{Tr}(AA')=0\ \text{for all }A\in\mathcal A\}$.
--   2. The **hull** of $\mathcal A$ is $H(\mathcal A)=\mathcal A\cap\mathcal A^{\perp}$.
--   3. A matrix $A$ is **self-dual** if $\mathrm{Tr}(A^2)=0$.
--   4. A **self-dual line** is a one-dimensional self-orthogonal subspace $L$, i.e. $\dim L=1$ and $L\subseteq L^{\perp}$.
--   5. For $T\in\mathrm{GL}(n,\mathbb F)$, the **conjugate code** is $T\mathcal AT^{-1}=\{TAT^{-1}:A\in\mathcal A\}$; two codes are conjugate when one is a conjugate code of the other.
--
--   The hull is the first canonical object the algorithm of Theorem 1.1 extracts from the slice code of a structure tensor; conjugation of codes is the symmetry it must respect.
--
--   **Formalization Note** `Mat K n` is `Matrix (Fin n) (Fin n) K`; `conjMap T` is $X\mapsto TXT^{-1}$ and `conjCode T C` the image of `C` under it.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Definition 3.1, p.16 (PDF p.18); §2.3 (matrix codes), p.16 (PDF p.18)

import Mathlib

set_option autoImplicit false

namespace AvgCaseTI

/-- `M(n, F)`, the `n × n` matrices over `F`. -/
abbrev Mat (K : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) K

variable {K : Type*} [Field K] {n : ℕ}

/-- **The orthogonal space of a matrix code under the trace form `f(A, B) = Tr(AB)`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Definition 3.1, p.16
(PDF p.18): "The orthogonal space of A ≤ M(n, q) with respect to f is
A^⊥ := {A′ ∈ M(n, q) | f(A, A′) = 0 ∀A ∈ A}." -/
def perp (C : Submodule K (Mat K n)) : Submodule K (Mat K n) where
  carrier := {Y | ∀ X ∈ C, Matrix.trace (X * Y) = 0}
  add_mem' := by
    intro Y Z hY hZ X hX
    simp [Matrix.mul_add, Matrix.trace_add, hY X hX, hZ X hX]
  zero_mem' := by
    intro X _
    simp
  smul_mem' := by
    intro a Y hY X hX
    simp [Matrix.trace_smul, hY X hX]

/-- **The hull `H(A) := A ∩ A^⊥` of a matrix code.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Definition 3.1, p.16
(PDF p.18): "The hull of A is H(A) := A ∩ A^⊥." -/
def hull (C : Submodule K (Mat K n)) : Submodule K (Mat K n) := C ⊓ perp C

/-- **Self-dual matrices**, Definition 3.1, p.16: "For A ∈ M(n, q), we say that A is self-dual if
Tr(A²) = 0." -/
def SelfDual (A : Mat K n) : Prop := Matrix.trace (A * A) = 0

/-- **Self-dual lines**, Definition 3.1, p.16: "A self-dual line will mean a one-dimensional
self-orthogonal subspace" (self-orthogonal: `L ⊆ L^⊥`). -/
def IsSelfDualLine (L : Submodule K (Mat K n)) : Prop :=
  Module.finrank K L = 1 ∧ L ≤ perp L

/-- Conjugation `X ↦ T X T^{−1}` by an invertible matrix, as a linear map. -/
def conjMap (T : GL (Fin n) K) : Mat K n →ₗ[K] Mat K n :=
  (LinearMap.mulLeft K (T : Mat K n)).comp (LinearMap.mulRight K ((T⁻¹ : GL (Fin n) K) : Mat K n))

/-- **The conjugate code `T B T^{−1} = {T B T^{−1} | B ∈ B}`**, §2.3, p.16 (PDF p.18): "Two matrix
codes A, B ≤ M(n, q) are conjugate, if there exists T ∈ GL(n, q) such that
A = TBT^{−1} = {TBT^{−1} | B ∈ B}." -/
def conjCode (T : GL (Fin n) K) (C : Submodule K (Mat K n)) : Submodule K (Mat K n) :=
  C.map (conjMap T)

end AvgCaseTI


