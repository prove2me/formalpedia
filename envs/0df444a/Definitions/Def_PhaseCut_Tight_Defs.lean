-- Prove2me | Definitions.Def_PhaseCut_Tight_Defs
-- name    : PhaseCut_Tight_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:24.843317+00:00
-- url     : https://prove2.me/theorems/8842aad7-8741-44d7-b4dd-b1888b53a649
-- title:
--   §2.2–2.4, §4, §4.3, pp. 3–5, 9, 12 — A† for injective A, M, B, Φ, solvability of |Ax| = b, the feasible and optimal sets of PhaseLift, PhaseCut and PhaseCutMod, tightness
-- statement:
--   This file fixes the objects of the phase recovery problem and of its two semidefinite relaxations, following Waldspurger, d'Aspremont and Mallat.
--
--   Throughout, $A\in\mathbb C^{n\times p}$ is a measurement matrix whose $i$-th row is $a_i^*$, and $b\in\mathbb R^n$ is a vector of measured amplitudes. We write $\mathbf H_m$ for the $m\times m$ Hermitian matrices and $X\succeq 0$ for positive semidefiniteness.
--
--   1. **Diagonal scalings.** $\operatorname{diag}(b)$ is the diagonal matrix with entries $b_1,\dots,b_n$, and $\operatorname{diag}(b)^{-1}$ the diagonal matrix with entries $b_i^{-1}$ (its inverse when all $b_i\neq 0$).
--   2. **Pseudoinverse.** For injective $A$ the matrix $A^*A$ is invertible and the Moore–Penrose pseudoinverse is
--   $$A^\dagger=(A^*A)^{-1}A^*\in\mathbb C^{p\times n}.$$
--   3. **The matrices $M$ and $B$.**
--   $$M=\operatorname{diag}(b)(\mathbf I-AA^\dagger)\operatorname{diag}(b),\qquad B=\operatorname{diag}(b)A^{\dagger *}A^\dagger\operatorname{diag}(b).$$
--   4. **The map $\Phi$.** $\Phi(X)=\operatorname{diag}(b)^{-1}AXA^*\operatorname{diag}(b)^{-1}$, sending $p\times p$ matrices to $n\times n$ matrices.
--   5. **Problem (1).** The phase recovery problem is solvable when there is $x\in\mathbb C^p$ with $|Ax|=b$, i.e. $|(Ax)_i|=b_i$ for every $i$.
--   6. **PhaseLift.** Its feasible set is $\{X\in\mathbf H_p : X\succeq 0,\ \operatorname{Tr}(a_ia_i^*X)=b_i^2,\ i=1,\dots,n\}$, and its optimal set consists of the feasible points of minimal $\operatorname{Tr}(X)$.
--   7. **PhaseCut.** Its feasible set is $\{U\in\mathbf H_n : U\succeq 0,\ \operatorname{diag}(U)=1\}$, and its optimal set consists of the feasible points of minimal $\operatorname{Tr}(UM)$.
--   8. **PhaseCutMod.** Its feasible set is $\{U\in\mathbf H_n : U\succeq 0,\ \operatorname{diag}(U)=1,\ \operatorname{Tr}(MU)=0\}$, and its optimal set consists of the feasible points of minimal $\operatorname{Tr}(BU)$.
--   9. **Tightness.** A relaxation is tight when its optimal set consists of exactly one matrix and that matrix has rank one ("has a unique rank one solution").
--
--   These definitions are shared by every statement of the mission: Proposition 4.2 and Corollary 4.3 compare the feasible and optimal sets of PhaseLift and PhaseCutMod through $\Phi$.
--
--   **Formalization Note** Matrices are indexed by `Fin n` / `Fin p` with complex entries; $X^*$ is `Matrix.conjTranspose`, and $X\succeq 0$ is Mathlib's `Matrix.PosSemidef`, which includes Hermitianity. The pseudoinverse is encoded as `(Aᴴ * A)⁻¹ * Aᴴ` with Mathlib's matrix inverse, which returns $0$ on a non-invertible matrix; it equals $A^\dagger$ only for injective $A$, and every theorem using it assumes injectivity. Likewise $\operatorname{diag}(b)^{-1}$ has entry $0$ where $b_i=0$, and is used only under $b_i\neq 0$. Since $a_i^*$ is the $i$-th row of $A$, $\operatorname{Tr}(a_ia_i^*X)=a_i^*Xa_i$ is the diagonal entry $(AXA^*)_{ii}$. The objectives are the real parts of the (complex) traces; on the feasible sets these traces are real. PhaseCutMod's constraint $\operatorname{Tr}(MU)=0$ is imposed as an equation in $\mathbb C$. Optimal sets are written as sets of minimizers, so "a unique optimal solution" is the statement that this set is a singleton.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, (1) p. 2, §2.2 (2) pp. 3–4, (PhaseCut) §2.4 p. 5, (PhaseLift) §4 p. 9 and its tightness gloss p. 10, (PhaseCutMod) §4.3 p. 12, Proposition 4.2 p. 12, Corollary 4.3 p. 13

import Mathlib

namespace PhaseCut.Tight

open Matrix
open scoped ComplexOrder

/-- `diag(b)`: the `n × n` complex diagonal matrix with the real entries `b i` on its diagonal. -/
noncomputable def D {n : ℕ} (b : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (b i : ℂ))

/-- `diag(b)⁻¹`: the diagonal matrix with entries `(b i)⁻¹`. It is the inverse of `D b` when every
`b i ≠ 0`; every statement of this mission that uses it assumes that. (Lean's `0⁻¹ = 0` makes the
entry `0` when `b i = 0`.) -/
noncomputable def Dinv {n : ℕ} (b : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => ((b i : ℂ))⁻¹)

/-- `A† = (A*A)⁻¹A*`, the Moore–Penrose pseudoinverse of `A` **when `A` is injective** (then `A*A` is
invertible). Here `⁻¹` is Mathlib's `Matrix.inv`, which returns `0` on a non-invertible matrix, so
`pinv A` is the pseudoinverse only under injectivity; every statement of this mission that uses it
assumes `Function.Injective A.mulVec`. No general pseudoinverse is defined. -/
noncomputable def pinv {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) : Matrix (Fin p) (Fin n) ℂ :=
  (Aᴴ * A)⁻¹ * Aᴴ

/-- The matrix `M = diag(b)(I − AA†)diag(b)` of problem (2) (§2.2, p. 3–4). -/
noncomputable def Mmat {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  D b * (1 - A * pinv A) * D b

/-- The matrix `B = diag(b)A†*A†diag(b)` of (PhaseCutMod) (§4.3, p. 12). -/
noncomputable def Bmat {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  D b * (pinv A)ᴴ * pinv A * D b

/-- The map `Φ(X) = diag(b)⁻¹AXA*diag(b)⁻¹` of Proposition 4.2 (p. 12), from `p × p` to
`n × n` complex matrices. -/
noncomputable def Phi {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (X : Matrix (Fin p) (Fin p) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Dinv b * A * X * Aᴴ * Dinv b

/-- Problem (1) is solvable: there is `x ∈ ℂᵖ` with `|Ax| = b`, i.e. `|(Ax)ᵢ| = bᵢ` for every `i`. -/
def IsSolvable {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ) : Prop :=
  ∃ x : Fin p → ℂ, ∀ i, ‖(A *ᵥ x) i‖ = b i

/-- Feasible set of (PhaseLift) (§4, p. 9): Hermitian `X ⪰ 0` with `Tr(aᵢaᵢ*X) = bᵢ²` for all `i`.
Since `aᵢ*` is the `i`-th row of `A`, `Tr(aᵢaᵢ*X) = aᵢ*Xaᵢ = (AXA*)ᵢᵢ`. -/
def phaseLiftFeasible {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ) :
    Set (Matrix (Fin p) (Fin p) ℂ) :=
  {X | X.PosSemidef ∧ ∀ i, (A * X * Aᴴ) i i = ((b i) ^ 2 : ℂ)}

/-- Optimal set of (PhaseLift): feasible points minimizing `Tr(X)` (real, since `X` is Hermitian). -/
def phaseLiftOptimal {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ) :
    Set (Matrix (Fin p) (Fin p) ℂ) :=
  {X | X ∈ phaseLiftFeasible A b ∧ ∀ Y ∈ phaseLiftFeasible A b, (X.trace).re ≤ (Y.trace).re}

/-- Feasible set of (PhaseCut) (§2.4, p. 5): Hermitian `U ⪰ 0` with `diag(U) = 1`. -/
def phaseCutFeasible (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {U | U.PosSemidef ∧ ∀ i, U i i = 1}

/-- Optimal set of (PhaseCut): feasible points minimizing `Tr(UM)` (real for Hermitian `U, M ⪰ 0`). -/
def phaseCutOptimal {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {U | U ∈ phaseCutFeasible n ∧
    ∀ V ∈ phaseCutFeasible n, ((U * Mmat A b).trace).re ≤ ((V * Mmat A b).trace).re}

/-- Feasible set of (PhaseCutMod) (§4.3, p. 12): `U ⪰ 0`, `diag(U) = 1`, `Tr(MU) = 0`. -/
def phaseCutModFeasible {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {U | U.PosSemidef ∧ (∀ i, U i i = 1) ∧ (Mmat A b * U).trace = 0}

/-- Optimal set of (PhaseCutMod): feasible points minimizing `Tr(BU)`. -/
def phaseCutModOptimal {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {U | U ∈ phaseCutModFeasible A b ∧
    ∀ V ∈ phaseCutModFeasible A b, ((Bmat A b * U).trace).re ≤ ((Bmat A b * V).trace).re}

/-- A program is tight when its optimal set `S` consists of exactly one matrix, of rank one
("has a unique rank one solution"). -/
def IsTight {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  ∃ X, S = {X} ∧ X.rank = 1

end PhaseCut.Tight


