-- Prove2me | Definitions.Def_RobustLS_Structured_Core
-- name    : RobustLS_Structured_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:32:59.898888+00:00
-- url     : https://prove2.me/theorems/7b4b0161-f0d1-464d-9f24-85d87d00295c
-- title:
--   Structured worst-case residual $r_S(\mathbf A,\mathbf b,\rho,x)$ of eq. (3), the data $M(x)$, $F,g,h$ of (26)–(27), the matrices of (28), (29), (32), and the quadratic functions of Lemma 2.1
-- statement:
--   This module fixes the objects of El Ghaoui and Lebret's **structured robust least-squares (SRLS)** problem.
--
--   Vectors carry the **Euclidean norm** $\|v\| = \sqrt{\sum_i v_i^2}$. Let $A_0, A_1, \dots, A_p \in \mathbb{R}^{n\times m}$ and $b_0, b_1, \dots, b_p \in \mathbb{R}^n$ be given. For every parameter $\delta \in \mathbb{R}^p$ put
--
--   $$
--   \mathbf A(\delta) = A_0 + \sum_{i=1}^p \delta_i A_i, \qquad \mathbf b(\delta) = b_0 + \sum_{i=1}^p \delta_i b_i .
--   $$
--
--   For $\rho \ge 0$ and $x \in \mathbb{R}^m$ the **structured worst-case residual** is
--
--   $$
--   r_S(\mathbf A,\mathbf b,\rho,x) = \max_{\|\delta\| \le \rho} \|\mathbf A(\delta)x - \mathbf b(\delta)\|,
--   $$
--
--   and $x$ is an **SRLS solution** if it minimizes $r_S(\mathbf A,\mathbf b,\rho,\cdot)$ over $\mathbb{R}^m$.
--
--   For fixed $x$, $M(x) = [A_1x - b_1 \ \cdots \ A_px - b_p] \in \mathbb{R}^{n\times p}$, and
--
--   $$
--   F = M(x)^T M(x), \qquad g = M(x)^T (A_0x - b_0), \qquad h = \|A_0x - b_0\|^2 .
--   $$
--
--   The module also defines the vector $[1;\delta] \in \mathbb{R}^{1+p}$, the symmetric matrices
--
--   $$
--   \begin{bmatrix} h & g^T \\ g & F \end{bmatrix}, \qquad \mathcal F(\lambda,\tau) = \begin{bmatrix} \lambda - \tau - h & -g^T \\ -g & \tau I - F \end{bmatrix},
--   $$
--
--   the $(1+p+n)\times(1+p+n)$ matrix of the semidefinite program (32),
--
--   $$
--   \begin{bmatrix} \lambda - \tau & 0 & (A_0x - b_0)^T \\ 0 & \tau I & M(x)^T \\ A_0x - b_0 & M(x) & I \end{bmatrix},
--   $$
--
--   feasibility of $(\lambda,\tau,x)$ in (32) (that matrix is positive semidefinite), and **optimality** of $(\lambda,\tau,x)$ for "minimize $\lambda$ subject to (32)" (feasible, and $\lambda \le \lambda'$ for every feasible $(\lambda',\tau',x')$). Finally, for Lemma 2.1 it defines the quadratic function $F(\zeta) = \zeta^T T\zeta + 2u^T\zeta + v$ of $\zeta \in \mathbb{R}^m$ and its block matrix $\begin{bmatrix} T & u \\ u^T & v\end{bmatrix}$.
--
--   These are the objects of §4 of the paper: Theorem 4.1 computes $r_S$ for fixed $x$ by a two-variable SDP in $\mathcal F(\lambda,\tau)$, and Theorem 4.2 minimizes it over $x$ through the SDP (32).
--
--   **Formalization Note** The family $A_1,\dots,A_p$ is a map `A : Fin p → Matrix` with `A i` the paper's $A_{i+1}$ (0-based), and likewise for $b$; $A_0$, $b_0$ are separate arguments. The maximum in (3) is encoded as `sSup` of the set of attained residuals; for $\rho \ge 0$ the set is nonempty and bounded (the ball is compact and the residual continuous), so `sSup` is the true maximum. Block matrices are `Matrix.fromBlocks` with the scalar block first (index `Unit ⊕ Fin p`, and `(Unit ⊕ Fin p) ⊕ Fin n` for (32)), in the printed order; Lemma 2.1's block puts $\zeta$ first (`Fin m ⊕ Unit`) as printed. $\lambda$ is written `lam`.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1035, Notation; p. 1036, Eqs. (2)–(3); p. 1038, Lemma 2.1; p. 1044, Eqs. (26)–(28); p. 1045, Eq. (29), Theorem 4.2, (32)

import Mathlib

namespace RobustLS.Structured

open Matrix

/-- The Euclidean norm `‖v‖ = √(∑ᵢ vᵢ²)` of a real vector indexed by a finite type.
El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Notation, p. 1035 (PDF p. 1): vectors carry the
Euclidean norm. (Written out because `‖v‖` on `ι → ℝ` in Mathlib is the sup norm.) -/
noncomputable def eucNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The structured matrix `A(δ) = A₀ + ∑_{i=1}^p δᵢ Aᵢ` of El Ghaoui & Lebret (1997), §1,
Eq. (2), p. 1036 (PDF p. 2). The paper's family `A₀, A₁, …, A_p` is passed as the nominal
matrix `A0 = A₀` and the map `A : Fin p → Matrix`, where `A i` is the paper's `A_{i+1}`
(0-based index). -/
def structMatrix {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (δ : Fin p → ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  A0 + ∑ i, δ i • A i

/-- The structured vector `b(δ) = b₀ + ∑_{i=1}^p δᵢ bᵢ` of El Ghaoui & Lebret (1997), §1,
Eq. (2), p. 1036 (PDF p. 2); `b i` is the paper's `b_{i+1}`. -/
def structVector {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) (δ : Fin p → ℝ) :
    Fin n → ℝ :=
  b0 + ∑ i, δ i • b i

/-- The residual `‖A(δ)x − b(δ)‖` of the perturbed system at the parameter `δ ∈ ℝ^p`
(El Ghaoui & Lebret (1997), §1, Eq. (3), p. 1036, the quantity inside the max). -/
noncomputable def structuredResidual {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (δ : Fin p → ℝ) : ℝ :=
  eucNorm (structMatrix A0 A δ *ᵥ x - structVector b0 b δ)

/-- The structured worst-case residual of El Ghaoui & Lebret (1997), §1, Eq. (3), p. 1036
(PDF p. 2): `r_S(A, b, ρ, x) = max_{‖δ‖ ≤ ρ} ‖A(δ)x − b(δ)‖`, `‖δ‖` Euclidean on `ℝ^p`.
Encoded as the supremum of the set of attained residuals. For `ρ ≥ 0` (the paper's standing
assumption) this set is nonempty (it contains the value at `δ = 0`) and bounded above (the
residual is continuous in `δ` and the ball is compact), so `sSup` is the true supremum and the
maximum is attained. -/
noncomputable def rS {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (ρ : ℝ) (x : Fin m → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ ρ ∧ r = structuredResidual A0 A b0 b x δ}

/-- `x` is an SRLS solution: it minimizes the structured worst-case residual `r_S(A, b, ρ, ·)`
over `ℝ^m`. El Ghaoui & Lebret (1997), §1, p. 1036 (PDF p. 2): "We say that x is an SRLS
solution if x minimizes the worst-case residual r_S(A, b, ρ, x)." -/
def IsSRLSSolution {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (ρ : ℝ) (x : Fin m → ℝ) : Prop :=
  ∀ x' : Fin m → ℝ, rS A0 A b0 b ρ x ≤ rS A0 A b0 b ρ x'

/-- The `n × p` matrix `M(x) = [A₁x − b₁ … A_px − b_p]` of El Ghaoui & Lebret (1997), §4,
Eq. (26), p. 1044 (PDF p. 10): its column `i` is `A i *ᵥ x − b i` (paper's `A_{i+1}x − b_{i+1}`). -/
def Mx {n m p : ℕ} (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  Matrix.of fun k i => (A i *ᵥ x - b i) k

/-- `F = M(x)ᵀ M(x)` (`p × p`), El Ghaoui & Lebret (1997), §4.1, Eq. (27), p. 1044. -/
def Fmat {n m p : ℕ} (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (Mx A b x)ᵀ * Mx A b x

/-- `g = M(x)ᵀ (A₀x − b₀)` (in `ℝ^p`), El Ghaoui & Lebret (1997), §4.1, Eq. (27), p. 1044. -/
def gvec {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ) (A : Fin p → Matrix (Fin n) (Fin m) ℝ)
    (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) (x : Fin m → ℝ) : Fin p → ℝ :=
  (Mx A b x)ᵀ *ᵥ (A0 *ᵥ x - b0)

/-- `h = ‖A₀x − b₀‖²`, El Ghaoui & Lebret (1997), §4.1, Eq. (27), p. 1044. -/
noncomputable def hval {n m : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ)
    (x : Fin m → ℝ) : ℝ :=
  eucNorm (A0 *ᵥ x - b0) ^ 2

/-- The stacked vector `[1; δ] ∈ ℝ^{1+p}`, indexed by `Unit ⊕ Fin p` (the scalar coordinate
first, as in the paper's Eq. (28), p. 1044). -/
def oneStack {p : ℕ} (δ : Fin p → ℝ) : Unit ⊕ Fin p → ℝ :=
  Sum.elim (fun _ => 1) δ

/-- The symmetric `(1+p) × (1+p)` matrix `[h gᵀ; g F]` of El Ghaoui & Lebret (1997), §4.1,
Eq. (28), p. 1044 (PDF p. 10), built from `x` via (27); index `Unit ⊕ Fin p`, the scalar
block first as printed. -/
noncomputable def hgFBlock {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) : Matrix (Unit ⊕ Fin p) (Unit ⊕ Fin p) ℝ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => hval A0 b0 x)
    (Matrix.of fun _ j => gvec A0 A b0 b x j)
    (Matrix.of fun i _ => gvec A0 A b0 b x i) (Fmat A b x)

/-- The matrix `𝓕(λ, τ) = [λ − τ − h, −gᵀ; −g, τI − F]` of El Ghaoui & Lebret (1997), §4.1,
Eq. (29), p. 1045 (PDF p. 11), built from `x` via (27); index `Unit ⊕ Fin p`, scalar block
first as printed. Condition (29) is `(calF … lam τ).PosSemidef`. -/
noncomputable def calF {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (lam τ : ℝ) : Matrix (Unit ⊕ Fin p) (Unit ⊕ Fin p) ℝ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => lam - τ - hval A0 b0 x)
    (Matrix.of fun _ j => -gvec A0 A b0 b x j)
    (Matrix.of fun i _ => -gvec A0 A b0 b x i) (τ • (1 : Matrix (Fin p) (Fin p) ℝ) - Fmat A b x)

/-- The `(1 + p + n) × (1 + p + n)` matrix of the SDP (32) of El Ghaoui & Lebret (1997),
Theorem 4.2, p. 1045 (PDF p. 11):
`[λ − τ, 0, (A₀x − b₀)ᵀ; 0, τI, M(x)ᵀ; A₀x − b₀, M(x), I]`.
Rows/columns are indexed by `(Unit ⊕ Fin p) ⊕ Fin n`: the scalar block, then the `p` block,
then the `n` block, in the printed order. -/
def sdp32Matrix {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (lam τ : ℝ) (x : Fin m → ℝ) :
    Matrix ((Unit ⊕ Fin p) ⊕ Fin n) ((Unit ⊕ Fin p) ⊕ Fin n) ℝ :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (Matrix.of fun _ _ => lam - τ) 0 0 (τ • (1 : Matrix (Fin p) (Fin p) ℝ)))
    (Matrix.of fun i k => Sum.elim (fun _ => (A0 *ᵥ x - b0) k) (fun j => Mx A b x k j) i)
    (Matrix.of fun k i => Sum.elim (fun _ => (A0 *ᵥ x - b0) k) (fun j => Mx A b x k j) i)
    (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Feasibility of `(λ, τ, x)` in the SDP (32): the matrix `sdp32Matrix` is positive
semidefinite. El Ghaoui & Lebret (1997), Theorem 4.2, p. 1045 (PDF p. 11). -/
def SDP32Feasible {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (lam τ : ℝ) (x : Fin m → ℝ) : Prop :=
  (sdp32Matrix A0 A b0 b lam τ x).PosSemidef

/-- `(λ, τ, x)` is an optimal solution of the SDP (32) "minimize λ subject to (32)": it is
feasible and `λ ≤ λ'` for every feasible `(λ', τ', x')`. El Ghaoui & Lebret (1997),
Theorem 4.2, p. 1045 (PDF p. 11). -/
def SDP32Optimal {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (lam τ : ℝ) (x : Fin m → ℝ) : Prop :=
  SDP32Feasible A0 A b0 b lam τ x ∧
    ∀ (lam' τ' : ℝ) (x' : Fin m → ℝ), SDP32Feasible A0 A b0 b lam' τ' x' → lam ≤ lam'

/-- The quadratic function `F(ζ) = ζᵀTζ + 2uᵀζ + v` of the variable `ζ ∈ ℝ^m`,
El Ghaoui & Lebret (1997), §2.2, Lemma 2.1, p. 1038 (PDF p. 4). -/
def quadFn {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) (v : ℝ)
    (ζ : Fin m → ℝ) : ℝ :=
  ζ ⬝ᵥ (T *ᵥ ζ) + 2 * (u ⬝ᵥ ζ) + v

/-- The `(m+1) × (m+1)` block matrix `[T u; uᵀ v]` of El Ghaoui & Lebret (1997), §2.2,
Lemma 2.1, p. 1038 (PDF p. 4); index `Fin m ⊕ Unit`, the `ζ` block first as printed. -/
def quadBlockMat {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) (v : ℝ) :
    Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) ℝ :=
  Matrix.fromBlocks T (Matrix.of fun i _ => u i) (Matrix.of fun _ j => u j)
    (Matrix.of fun _ _ => v)

end RobustLS.Structured


