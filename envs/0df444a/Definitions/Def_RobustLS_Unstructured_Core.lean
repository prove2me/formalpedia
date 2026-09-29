-- Prove2me | Definitions.Def_RobustLS_Unstructured_Core
-- name    : RobustLS_Unstructured_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:24:18.187744+00:00
-- url     : https://prove2.me/theorems/d6ec4ebd-490b-48b1-9f60-b6d80dd18d52
-- title:
--   Worst-case residual $r(A,b,\rho,x)$ of eq. (1), Euclidean / Frobenius / largest-singular-value norms, and the SOCP (15) constraints
-- statement:
--   This module fixes the objects of El Ghaoui and Lebret's unstructured robust least-squares problem.
--
--   Let $A \in \mathbb{R}^{n\times m}$ and $b \in \mathbb{R}^n$ be given data and $x \in \mathbb{R}^m$. Vectors carry the **Euclidean norm** $\|v\| = \sqrt{\sum_i v_i^2}$. For a matrix $X$, the **Frobenius norm** is $\|X\|_F = \sqrt{\sum_{i,j} X_{ij}^2}$ and $\|X\|$ denotes the **largest singular value**, i.e. the operator norm $\|X\| = \min\{c \ge 0 : \|Xv\| \le c\|v\| \text{ for all } v\}$.
--
--   A perturbation of the data is a pair $(\Delta A, \Delta b)$ with $\Delta A \in \mathbb{R}^{n\times m}$, $\Delta b \in \mathbb{R}^n$, collected in the augmented matrix $\Delta = [\Delta A \ \Delta b] \in \mathbb{R}^{n\times(m+1)}$. For $\rho \ge 0$ the **worst-case residual** is
--
--   $$
--   r(A,b,\rho,x) = \max_{\|[\Delta A\ \Delta b]\|_F \le \rho} \|(A+\Delta A)x - (b+\Delta b)\|,
--   $$
--
--   and its variant with the largest-singular-value norm is $\max_{\|[\Delta A\ \Delta b]\| \le \rho} \|(A+\Delta A)x - (b+\Delta b)\|$. Finally, $[x;1] \in \mathbb{R}^{m+1}$ is $x$ stacked over $1$, and a triple $(x,\lambda,\tau)$ is **feasible for the SOCP (15)** when
--
--   $$
--   \|Ax - b\| \le \lambda - \tau, \qquad \|[x;1]\| \le \tau .
--   $$
--
--   These are the objects of Theorem 3.1: a vector $x$ minimizing $r(A,b,\rho,\cdot)$ is a robust least-squares (RLS) solution.
--
--   **Formalization Note** The Euclidean norm is written out as a square root of a sum of squares because Mathlib's `‖·‖` on `Fin n → ℝ` is the sup norm. The augmented matrix is indexed by `Fin m ⊕ Unit` (the columns of $\Delta A$, then the column $\Delta b$), and $[x;1]$ likewise. The maximum in (1) is encoded as `sSup` of the set of attained residuals; for $\rho \ge 0$ that set is nonempty (it contains $\Delta = 0$) and bounded above, so `sSup` is the true supremum. The largest singular value is the infimum of the admissible operator constants, a nonempty set bounded below by $0$.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1035, Notation; p. 1036, Eq. (1); p. 1040, Theorem 3.1, (15)

import Mathlib

namespace RobustLS.Unstructured

open Matrix

/-- The Euclidean norm `‖v‖ = √(∑ᵢ vᵢ²)` of a real vector indexed by a finite type.
El Ghaoui & Lebret, SIAM J. Matrix Anal. Appl. 18(4) (1997), Notation, p. 1035 (PDF p. 1):
vectors carry the Euclidean norm. (Stated explicitly because `‖v‖` on `ι → ℝ` in Mathlib is the
sup norm.) -/
noncomputable def eucNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The Frobenius norm `‖X‖_F = √(∑ᵢⱼ Xᵢⱼ²)` of a real matrix.
El Ghaoui & Lebret (1997), Notation, p. 1035 (PDF p. 1). -/
noncomputable def frobNorm {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, X i j ^ 2)

/-- The largest singular value `‖X‖` of a real matrix, i.e. its operator norm from Euclidean
space to Euclidean space: the least `c ≥ 0` with `‖X v‖ ≤ c ‖v‖` for every vector `v`
(the set of such `c` is nonempty and bounded below by `0`, so the infimum is the true one).
El Ghaoui & Lebret (1997), Notation, p. 1035 (PDF p. 1): "‖X‖ denotes the largest singular
value". -/
noncomputable def specNorm {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ v : κ → ℝ, eucNorm (X *ᵥ v) ≤ c * eucNorm v}

/-- The augmented perturbation matrix `Δ = [ΔA Δb] ∈ ℝ^{n×(m+1)}`: the columns of `ΔA`
(indexed by `Fin m`) followed by the single column `Δb` (indexed by `Unit`).
El Ghaoui & Lebret (1997), §1, p. 1036 (PDF p. 2). -/
def augment {n m : ℕ} (ΔA : Matrix (Fin n) (Fin m) ℝ) (Δb : Fin n → ℝ) :
    Matrix (Fin n) (Fin m ⊕ Unit) ℝ :=
  Matrix.of fun i j => Sum.elim (fun k => ΔA i k) (fun _ => Δb i) j

/-- The stacked vector `[x; 1] ∈ ℝ^{m+1}` (coordinates of `x`, indexed by `Fin m`, followed by
the single coordinate `1`, indexed by `Unit`). El Ghaoui & Lebret (1997), Theorem 3.1, (15),
p. 1040 (PDF p. 6). -/
def stackOne {m : ℕ} (x : Fin m → ℝ) : Fin m ⊕ Unit → ℝ :=
  Sum.elim x (fun _ => 1)

/-- The residual `‖(A + ΔA)x − (b + Δb)‖` under the perturbation `[ΔA Δb]`. -/
noncomputable def perturbedResidual {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (ΔA : Matrix (Fin n) (Fin m) ℝ) (Δb : Fin n → ℝ) (x : Fin m → ℝ) : ℝ :=
  eucNorm ((A + ΔA) *ᵥ x - (b + Δb))

/-- The worst-case residual, El Ghaoui & Lebret (1997), §1, Eq. (1), p. 1036 (PDF p. 2):
`r(A, b, ρ, x) = max_{‖[ΔA Δb]‖_F ≤ ρ} ‖(A + ΔA)x − (b + Δb)‖`.
Encoded as the supremum of the set of values; for `ρ ≥ 0` this set is nonempty (it contains the
value at `Δ = 0`) and bounded above (by `‖Ax − b‖ + ρ√(‖x‖² + 1)`), so `sSup` is the true
supremum (and the maximum over the compact ball is attained). The paper assumes `ρ ≥ 0`. -/
noncomputable def worstCaseResidual {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (ρ : ℝ) (x : Fin m → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ (ΔA : Matrix (Fin n) (Fin m) ℝ) (Δb : Fin n → ℝ),
    frobNorm (augment ΔA Δb) ≤ ρ ∧ r = perturbedResidual A b ΔA Δb x}

/-- The worst-case residual with the perturbation bound measured in the largest singular value
norm instead of the Frobenius norm: `max_{‖[ΔA Δb]‖ ≤ ρ} ‖(A + ΔA)x − (b + Δb)‖`.
El Ghaoui & Lebret (1997), p. 1040 (PDF p. 6). Same `sSup` encoding as `worstCaseResidual`
(nonempty and bounded above for `ρ ≥ 0`). -/
noncomputable def worstCaseResidualSpec {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (ρ : ℝ) (x : Fin m → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ (ΔA : Matrix (Fin n) (Fin m) ℝ) (Δb : Fin n → ℝ),
    specNorm (augment ΔA Δb) ≤ ρ ∧ r = perturbedResidual A b ΔA Δb x}

/-- Feasibility in the second-order cone program (15) of El Ghaoui & Lebret (1997),
Theorem 3.1, p. 1040 (PDF p. 6): `‖Ax − b‖ ≤ λ − τ` and `‖[x; 1]‖ ≤ τ`. -/
def SocpFeasible {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam τ : ℝ) : Prop :=
  eucNorm (A *ᵥ x - b) ≤ lam - τ ∧ eucNorm (stackOne x) ≤ τ

end RobustLS.Unstructured


