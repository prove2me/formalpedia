-- Prove2me | Definitions.Def_ExpConeIPM_Secant_Recursion
-- name    : ExpConeIPM_Secant_Recursion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:31.068994+00:00
-- url     : https://prove2.me/theorems/b0220ddc-4864-4fc8-a894-37ffe2257364
-- title:
--   The rank-one recursions (25)–(26) and the matrices V, U, L and Ψₖ of Theorem 2
-- statement:
--   Let $Y_0, S_0 \in \mathbb{R}^{n\times p}$ and write $e_k$ for the $k$-th unit vector of $\mathbb{R}^p$ and $\langle\cdot,\cdot\rangle$ for the standard inner product of $\mathbb{R}^n$. For $k = 1, \dots, p$ set
--
--   $$
--   d_k := \langle Y_{k-1}e_k,\, S_{k-1}e_k\rangle, \qquad
--   v_k := \frac{Y_{k-1}e_k}{d_k^{1/2}}, \qquad
--   u_k := \frac{S_{k-1}e_k}{d_k^{1/2}},
--   $$
--
--   $$
--   Y_k := Y_{k-1} - v_k v_k^{T} S_{k-1}, \qquad
--   S_k := S_{k-1} - u_k u_k^{T} Y_{k-1}.
--   $$
--
--   Both updates of step $k$ use the previous pair $(Y_{k-1}, S_{k-1})$. From the recursion one forms
--
--   1. $V := (v_1 \cdots v_p)$ and $U := (u_1 \cdots u_p)$, the $n\times p$ matrices whose $k$-th columns are $v_k$ and $u_k$;
--   2. $L$, the $p\times p$ matrix whose $k$-th column is $Y_{k-1}^{T}S_{k-1}e_k / d_k^{1/2}$;
--   3. $\Psi_k$ ($k = 0, \dots, p$), the principal submatrix of $Y_k^{T}S_k$ formed by its last $p-k$ rows and columns.
--
--   These are the recursions (25)–(26) of Dahl and Andersen's Theorem 2, a sequence of $p$ rank-one updates that computes the multiple-secant term $Y(Y^TS)^{-1}Y^T$ of a BFGS update without forming an inverse; $L$ and $\Psi_k$ are the auxiliary objects of its proof.
--
--   **Formalization Note** Indices are 0-based in Lean: column `j : Fin p` is the paper's $e_{j+1}$, `Ys Y₀ S₀ k` and `Ss Y₀ S₀ k` are $Y_k$ and $S_k$ (after $k$ steps; the pair is left unchanged after step $p$), `d Y₀ S₀ j` is $d_{j+1}$, column `j` of `V`, `U`, `L` is $v_{j+1}$, $u_{j+1}$ and the $(j+1)$-st column of $L$, and `Ψ Y₀ S₀ k` is the submatrix on the 0-based indices $j \ge k$. The square root is `Real.sqrt` and the division is multiplication by an inverse; on a non-positive $d_k$ both return junk values, which never arise under the hypothesis $Y_0^TS_0 \succ 0$ of Theorem 2 (every $d_k$ is then positive).
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 358, Theorem 2, (25)–(26), and the definitions of L and Ψk in its proof

import Mathlib

namespace ExpConeIPM.Secant

open Matrix

/-!
# The rank-one recursions (25)–(26) of Dahl–Andersen, Theorem 2

Dahl, Andersen, *A primal-dual interior-point algorithm for nonsymmetric exponential-cone
optimization*, Math. Program. 194 (2022), pp. 357–358, Theorem 2 and its proof.

Index convention: the paper's columns e₁, …, e_p are 1-based; here column `j : Fin p` is the
paper's e_{j+1}. `Ys Y₀ S₀ k`, `Ss Y₀ S₀ k` are the paper's Y_k, S_k (the matrices after k steps,
k = 0, …, p); step k + 1 uses column `⟨k, hk⟩` (the paper's e_{k+1}). `d Y₀ S₀ j`, column `j` of
`V` and of `U`, and column `j` of `L` are the paper's d_{j+1} = ⟨Y_j e_{j+1}, S_j e_{j+1}⟩,
v_{j+1}, u_{j+1} and Y_jᵀS_j e_{j+1}/d_{j+1}^{1/2}. `Ψ Y₀ S₀ k` is the paper's Ψ_k, the principal
submatrix of Y_kᵀS_k on the 0-based indices j ≥ k (the last p − k rows and columns).

`Real.sqrt` of a negative number and division by zero return junk values (0). This is harmless
only because, under the hypothesis Y₀ᵀS₀ ≻ 0 of Theorem 2, every d_k is positive (the
well-definedness step of the proof, `ExpConeIPM.Secant.psi_posDef`).
-/

/-- The unit vector e_j of ℝ^p (0-based index `j`; the paper's e_{j+1}). -/
noncomputable def unitVec {p : ℕ} (j : Fin p) : Fin p → ℝ := Pi.single j 1

/-- The inner product ⟨Y e_j, S e_j⟩ of the `j`-th columns of `Y` and `S` (= (YᵀS)_{jj}). -/
noncomputable def colInner {n p : ℕ} (Y S : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : ℝ :=
  (Y *ᵥ unitVec j) ⬝ᵥ (S *ᵥ unitVec j)

/-- One step of (25)–(26) on column `j`: with d := ⟨Y e_j, S e_j⟩, v := Y e_j / d^{1/2} and
u := S e_j / d^{1/2}, return (Y − v vᵀ S, S − u uᵀ Y). Both updates use the *previous* pair. -/
noncomputable def step {n p : ℕ} (j : Fin p) (Y S : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin p) ℝ × Matrix (Fin n) (Fin p) ℝ :=
  let v : Fin n → ℝ := (Real.sqrt (colInner Y S j))⁻¹ • (Y *ᵥ unitVec j)
  let u : Fin n → ℝ := (Real.sqrt (colInner Y S j))⁻¹ • (S *ᵥ unitVec j)
  (Y - vecMulVec v v * S, S - vecMulVec u u * Y)

/-- The pair (Y_k, S_k) after `k` steps of (25)–(26), started at (Y₀, S₀). Step k + 1 uses the
column `⟨k, hk⟩` (the paper's e_{k+1}) for k < p; for k ≥ p the pair is left unchanged (the paper
only runs k = 1, …, p). -/
noncomputable def pair {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) :
    ℕ → Matrix (Fin n) (Fin p) ℝ × Matrix (Fin n) (Fin p) ℝ
  | 0 => (Y₀, S₀)
  | k + 1 =>
    if hk : k < p then step ⟨k, hk⟩ (pair Y₀ S₀ k).1 (pair Y₀ S₀ k).2 else pair Y₀ S₀ k

/-- The paper's Y_k. -/
noncomputable def Ys {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin p) ℝ :=
  (pair Y₀ S₀ k).1

/-- The paper's S_k. -/
noncomputable def Ss {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin p) ℝ :=
  (pair Y₀ S₀ k).2

/-- `d Y₀ S₀ j` is the paper's d_{j+1} = ⟨Y_j e_{j+1}, S_j e_{j+1}⟩ (0-based column `j`). -/
noncomputable def d {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : ℝ :=
  colInner (Ys Y₀ S₀ j) (Ss Y₀ S₀ j) j

/-- V := (v₁ ⋯ v_p): column `j` is v_{j+1} = Y_j e_{j+1} / d_{j+1}^{1/2}. -/
noncomputable def V {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  Matrix.of fun i j => ((Real.sqrt (d Y₀ S₀ j))⁻¹ • (Ys Y₀ S₀ j *ᵥ unitVec j)) i

/-- U := (u₁ ⋯ u_p): column `j` is u_{j+1} = S_j e_{j+1} / d_{j+1}^{1/2}. -/
noncomputable def U {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  Matrix.of fun i j => ((Real.sqrt (d Y₀ S₀ j))⁻¹ • (Ss Y₀ S₀ j *ᵥ unitVec j)) i

/-- The p × p matrix L of the proof of Theorem 2: column `j` is
Y_jᵀ S_j e_{j+1} / ⟨Y_j e_{j+1}, S_j e_{j+1}⟩^{1/2}. -/
noncomputable def L {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j =>
    ((Real.sqrt (d Y₀ S₀ j))⁻¹ • (((Ys Y₀ S₀ j)ᵀ * Ss Y₀ S₀ j) *ᵥ unitVec j)) i

/-- Ψ_k: the principal submatrix of Y_kᵀS_k on the last p − k rows and columns, i.e. on the
0-based indices j with k ≤ j. -/
noncomputable def Ψ {n p : ℕ} (Y₀ S₀ : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    Matrix {j : Fin p // k ≤ j.val} {j : Fin p // k ≤ j.val} ℝ :=
  ((Ys Y₀ S₀ k)ᵀ * Ss Y₀ S₀ k).submatrix Subtype.val Subtype.val

end ExpConeIPM.Secant


