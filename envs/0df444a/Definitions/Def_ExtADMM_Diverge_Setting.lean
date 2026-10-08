-- Prove2me | Definitions.Def_ExtADMM_Diverge_Setting
-- name    : ExtADMM_Diverge_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:18.32137+00:00
-- url     : https://prove2.me/theorems/7b53288b-8e57-4dbc-abc1-e1003abc3a89
-- title:
--   (1.1), (1.5), (1.6), (3.1), (3.6)–(3.10), pp. 1–2, 10–12 — the three-block problem, the extended ADMM, the linear example (3.10) and its matrices L, R, M
-- statement:
--   This file fixes the objects of the paper's divergence example.
--
--   **Problem (1.1).** Given matrices $A_i\in\mathbb R^{p\times n_i}$ $(i=1,2,3)$, a vector $b\in\mathbb R^p$, sets $\mathcal X_i\subseteq\mathbb R^{n_i}$ and functions $\theta_i:\mathbb R^{n_i}\to\mathbb R$, consider
--
--   $$\min\ \theta_1(x_1)+\theta_2(x_2)+\theta_3(x_3)\quad\text{s.t.}\quad A_1x_1+A_2x_2+A_3x_3=b,\ \ x_i\in\mathcal X_i .$$
--
--   The *standing assumptions* are: each $\mathcal X_i$ is closed and convex, each $\theta_i$ is convex, and the problem has an optimal solution.
--
--   **Augmented Lagrangian (1.6).** For a penalty $\beta$ and a multiplier $\lambda\in\mathbb R^p$,
--
--   $$\mathcal L_{\mathcal A}(x_1,x_2,x_3,\lambda)=\sum_{i=1}^3\theta_i(x_i)-\lambda^T(A_1x_1+A_2x_2+A_3x_3-b)+\frac{\beta}{2}\|A_1x_1+A_2x_2+A_3x_3-b\|^2 .$$
--
--   **Direct extension of ADMM (1.5).** Sequences $(x_1^k,x_2^k,x_3^k,\lambda^k)_{k\ge0}$ form a *run* if, for every $k$, $x_1^{k+1}$ minimises $\mathcal L_{\mathcal A}(\cdot,x_2^k,x_3^k,\lambda^k)$ over $\mathcal X_1$, then $x_2^{k+1}$ minimises $\mathcal L_{\mathcal A}(x_1^{k+1},\cdot,x_3^k,\lambda^k)$ over $\mathcal X_2$, then $x_3^{k+1}$ minimises $\mathcal L_{\mathcal A}(x_1^{k+1},x_2^{k+1},\cdot,\lambda^k)$ over $\mathcal X_3$, and $\lambda^{k+1}=\lambda^k-\beta(A_1x_1^{k+1}+A_2x_2^{k+1}+A_3x_3^{k+1}-b)$. The starting point is $(x_2^0,x_3^0,\lambda^0)$.
--
--   **The linear system (3.1).** For column vectors $a_1,a_2,a_3\in\mathbb R^3$, the problem $A_1x_1+A_2x_2+A_3x_3=0$ with $A_i=a_i$, scalar unknowns $x_i\in\mathbb R$, null objective, $b=0$ and $\mathcal X_i=\mathbb R$. The example of §3.2 takes
--
--   $$A=(A_1,A_2,A_3)=\begin{pmatrix}1&1&1\\1&1&2\\1&2&2\end{pmatrix}\qquad(3.10).$$
--
--   **State and matrices.** With $\mu=\lambda/\beta$, the state is $(x_2,x_3,\mu_1,\mu_2,\mu_3)\in\mathbb R^5$. The $5\times5$ matrices of (3.6) and (3.7) are
--
--   $$L=\begin{pmatrix}A_2^TA_2&0&0_{1\times3}\\A_3^TA_2&A_3^TA_3&0_{1\times3}\\A_2&A_3&I_{3\times3}\end{pmatrix},\qquad R=\begin{pmatrix}0&-A_2^TA_3&A_2^T\\0&0&A_3^T\\0_{3\times1}&0_{3\times1}&I_{3\times3}\end{pmatrix}-\frac{1}{A_1^TA_1}\begin{pmatrix}A_2^TA_1\\A_3^TA_1\\A_1\end{pmatrix}\bigl(-A_1^TA_2,\,-A_1^TA_3,\,A_1^T\bigr),$$
--
--   and $M=L^{-1}R$ (3.9). The file also records the matrices printed on p. 12 for the data (3.10):
--
--   $$L=\begin{pmatrix}6&0&0&0&0\\7&9&0&0&0\\1&1&1&0&0\\1&2&0&1&0\\2&2&0&0&1\end{pmatrix},\quad R=\frac13\begin{pmatrix}16&-1&-1&-1&2\\20&25&-2&1&1\\4&5&2&-1&-1\\4&5&-1&2&-1\\4&5&-1&-1&2\end{pmatrix},\quad M=\frac1{162}\begin{pmatrix}144&-9&-9&-9&18\\8&157&-5&13&-8\\64&122&122&-58&-64\\56&-35&-35&91&-56\\-88&-26&-26&-62&88\end{pmatrix}.$$
--
--   These definitions are the common vocabulary of the mission: every theorem about the divergence example is stated in terms of them.
--
--   **Formalization Note.** Vectors are `Fin n → ℝ`, and $\|r\|^2$ is the dot product $r\cdot r$ (not Mathlib's sup norm). The paper's "closed convex" $\theta_i$ is real-valued convex on all of $\mathbb R^{n_i}$, which is automatically continuous, so only convexity is stated. "Argmin" is read as "is a minimiser"; the run predicate does not choose a minimiser. $x_1^0$ is never used by (1.5). The multiplier is called `lam` and its components are indexed $0,1,2$ (the paper's $\mu_1,\mu_2,\mu_3$). The nonsingularity of $[A_1,A_2,A_3]$ assumed for (3.1) is a hypothesis of the theorems, not part of the definition. `M = L⁻¹R` uses Mathlib's matrix inverse, which is the true inverse whenever $\det L=(A_2^TA_2)(A_3^TA_3)\neq0$, in particular when $[A_1,A_2,A_3]$ is nonsingular.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), pp. 1–2, (1.1), (1.5), (1.6); pp. 10–12, (3.1), (3.6), (3.7), (3.9), (3.10) and the matrices L, R, M of p. 12

import Mathlib

namespace ExtADMM.Diverge

open Matrix

/-- Problem (1.1), p. 1: minimize `θ₁(x₁) + θ₂(x₂) + θ₃(x₃)` subject to
`A₁x₁ + A₂x₂ + A₃x₃ = b`, `xᵢ ∈ 𝒳ᵢ`, with `Aᵢ ∈ ℝ^{p×nᵢ}`, `b ∈ ℝ^p`, `𝒳ᵢ ⊆ ℝ^{nᵢ}` and
`θᵢ : ℝ^{nᵢ} → ℝ`. The standing assumptions of p. 1 are `Problem.Standing`. -/
structure Problem (n1 n2 n3 p : ℕ) where
  A1 : Matrix (Fin p) (Fin n1) ℝ
  A2 : Matrix (Fin p) (Fin n2) ℝ
  A3 : Matrix (Fin p) (Fin n3) ℝ
  b  : Fin p → ℝ
  θ1 : (Fin n1 → ℝ) → ℝ
  θ2 : (Fin n2 → ℝ) → ℝ
  θ3 : (Fin n3 → ℝ) → ℝ
  X1 : Set (Fin n1 → ℝ)
  X2 : Set (Fin n2 → ℝ)
  X3 : Set (Fin n3 → ℝ)

namespace Problem

variable {n1 n2 n3 p : ℕ}

/-- The constraint residual `A₁x₁ + A₂x₂ + A₃x₃ − b` of (1.1). -/
def residual (P : Problem n1 n2 n3 p) (x1 : Fin n1 → ℝ) (x2 : Fin n2 → ℝ)
    (x3 : Fin n3 → ℝ) : Fin p → ℝ :=
  P.A1 *ᵥ x1 + P.A2 *ᵥ x2 + P.A3 *ᵥ x3 - P.b

/-- The objective `θ₁(x₁) + θ₂(x₂) + θ₃(x₃)` of (1.1). -/
def objective (P : Problem n1 n2 n3 p) (x1 : Fin n1 → ℝ) (x2 : Fin n2 → ℝ)
    (x3 : Fin n3 → ℝ) : ℝ :=
  P.θ1 x1 + P.θ2 x2 + P.θ3 x3

/-- The standing assumptions of (1.1), p. 1: each `𝒳ᵢ` is closed and convex, each `θᵢ` is
convex (real-valued on all of `ℝ^{nᵢ}`, hence continuous, so "closed" adds nothing), and the
solution set of (1.1) is nonempty. -/
def Standing (P : Problem n1 n2 n3 p) : Prop :=
  Convex ℝ P.X1 ∧ IsClosed P.X1 ∧ Convex ℝ P.X2 ∧ IsClosed P.X2 ∧
  Convex ℝ P.X3 ∧ IsClosed P.X3 ∧
  ConvexOn ℝ Set.univ P.θ1 ∧ ConvexOn ℝ Set.univ P.θ2 ∧ ConvexOn ℝ Set.univ P.θ3 ∧
  ∃ x1 ∈ P.X1, ∃ x2 ∈ P.X2, ∃ x3 ∈ P.X3, P.residual x1 x2 x3 = 0 ∧
    ∀ y1 ∈ P.X1, ∀ y2 ∈ P.X2, ∀ y3 ∈ P.X3, P.residual y1 y2 y3 = 0 →
      P.objective x1 x2 x3 ≤ P.objective y1 y2 y3

/-- The augmented Lagrangian (1.6), p. 2:
`𝓛_𝒜(x₁,x₂,x₃,λ) = Σ θᵢ(xᵢ) − λᵀ(A₁x₁+A₂x₂+A₃x₃−b) + (β/2)‖A₁x₁+A₂x₂+A₃x₃−b‖²`,
with `‖r‖² = r ⬝ᵥ r` (Euclidean). -/
noncomputable def augLag (P : Problem n1 n2 n3 p) (β : ℝ) (x1 : Fin n1 → ℝ) (x2 : Fin n2 → ℝ)
    (x3 : Fin n3 → ℝ) (lam : Fin p → ℝ) : ℝ :=
  P.objective x1 x2 x3 - lam ⬝ᵥ P.residual x1 x2 x3 +
    β / 2 * (P.residual x1 x2 x3 ⬝ᵥ P.residual x1 x2 x3)

/-- A run of the direct extension of ADMM (1.5), p. 2, with penalty `β`: for every `k`,
`x₁^{k+1}`, `x₂^{k+1}`, `x₃^{k+1}` are minimisers of the augmented Lagrangian (1.6) over
`𝒳₁`, `𝒳₂`, `𝒳₃` in Gauss–Seidel order (1.5a)–(1.5c), and
`λ^{k+1} = λᵏ − β(A₁x₁^{k+1} + A₂x₂^{k+1} + A₃x₃^{k+1} − b)` (1.5d).
The starting point is `(x2 0, x3 0, lam 0)`; `x1 0` is never read. -/
def IsRun15 (P : Problem n1 n2 n3 p) (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ) : Prop :=
  ∀ k,
    (x1 (k+1) ∈ P.X1 ∧ ∀ y ∈ P.X1,
      P.augLag β (x1 (k+1)) (x2 k) (x3 k) (lam k) ≤ P.augLag β y (x2 k) (x3 k) (lam k)) ∧
    (x2 (k+1) ∈ P.X2 ∧ ∀ y ∈ P.X2,
      P.augLag β (x1 (k+1)) (x2 (k+1)) (x3 k) (lam k) ≤
        P.augLag β (x1 (k+1)) y (x3 k) (lam k)) ∧
    (x3 (k+1) ∈ P.X3 ∧ ∀ y ∈ P.X3,
      P.augLag β (x1 (k+1)) (x2 (k+1)) (x3 (k+1)) (lam k) ≤
        P.augLag β (x1 (k+1)) (x2 (k+1)) y (lam k)) ∧
    lam (k+1) = lam k - β • P.residual (x1 (k+1)) (x2 (k+1)) (x3 (k+1))

end Problem

/-- A column vector `a ∈ ℝ³` as a `3 × 1` matrix. -/
def col (a : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun i _ => a i

/-- The `3 × 3` matrix `[A₁, A₂, A₃]` whose columns are `a₁, a₂, a₃`. -/
def colMat (a1 a2 a3 : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => ![a1, a2, a3] j i

/-- The linear system (3.1), p. 10, `A₁x₁ + A₂x₂ + A₃x₃ = 0` with column vectors
`Aᵢ ∈ ℝ³` and scalars `xᵢ ∈ ℝ`, as the special case of (1.1) with null objective,
`b = 0` and `𝒳ᵢ = ℝ`. (The paper also assumes `[A₁, A₂, A₃]` nonsingular; that is a
hypothesis of the theorems, `(colMat a1 a2 a3).det ≠ 0`.) -/
def instance31 (a1 a2 a3 : Fin 3 → ℝ) : Problem 1 1 1 3 where
  A1 := col a1
  A2 := col a2
  A3 := col a3
  b := 0
  θ1 := fun _ => 0
  θ2 := fun _ => 0
  θ3 := fun _ => 0
  X1 := Set.univ
  X2 := Set.univ
  X3 := Set.univ

/-- The columns of the matrix `A` of (3.10), p. 12: `A₁ = (1,1,1)ᵀ`, `A₂ = (1,1,2)ᵀ`,
`A₃ = (1,2,2)ᵀ`. -/
def a310_1 : Fin 3 → ℝ := ![1, 1, 1]
/-- Second column of (3.10). -/
def a310_2 : Fin 3 → ℝ := ![1, 1, 2]
/-- Third column of (3.10). -/
def a310_3 : Fin 3 → ℝ := ![1, 2, 2]

/-- The example of §3.2: system (3.1) with `A = (A₁, A₂, A₃) = [[1,1,1],[1,1,2],[1,2,2]]`
of (3.10), p. 12. -/
def example310 : Problem 1 1 1 3 := instance31 a310_1 a310_2 a310_3

/-- The state `(x₂, x₃, μ₁, μ₂, μ₃)` of (3.5)/(3.8), with `μ = λ/β` (p. 11). Components are
0-based: `μ₁, μ₂, μ₃` are `lam 0 / β, lam 1 / β, lam 2 / β`. -/
noncomputable def stateVec (β : ℝ) (x2 x3 : Fin 1 → ℝ) (lam : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![x2 0, x3 0, lam 0 / β, lam 1 / β, lam 2 / β]

/-- The matrix `L` of (3.6), p. 11:
`L = [[A₂ᵀA₂, 0, 0_{1×3}], [A₃ᵀA₂, A₃ᵀA₃, 0_{1×3}], [A₂, A₃, I_{3×3}]]`.
It does not involve `A₁`. -/
def Lmat (a2 a3 : Fin 3 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![a2 ⬝ᵥ a2, 0, 0, 0, 0;
     a3 ⬝ᵥ a2, a3 ⬝ᵥ a3, 0, 0, 0;
     a2 0, a3 0, 1, 0, 0;
     a2 1, a3 1, 0, 1, 0;
     a2 2, a3 2, 0, 0, 1]

/-- The matrix `R` of (3.7), p. 11:
`R = [[0, −A₂ᵀA₃, A₂ᵀ], [0, 0, A₃ᵀ], [0_{3×1}, 0_{3×1}, I_{3×3}]]
  − (1/(A₁ᵀA₁)) (A₂ᵀA₁; A₃ᵀA₁; A₁)(−A₁ᵀA₂, −A₁ᵀA₃, A₁ᵀ)`. -/
noncomputable def Rmat (a1 a2 a3 : Fin 3 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, -(a2 ⬝ᵥ a3), a2 0, a2 1, a2 2;
     0, 0, a3 0, a3 1, a3 2;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1] -
  (1 / (a1 ⬝ᵥ a1)) • Matrix.vecMulVec
    ![a2 ⬝ᵥ a1, a3 ⬝ᵥ a1, a1 0, a1 1, a1 2]
    ![-(a1 ⬝ᵥ a2), -(a1 ⬝ᵥ a3), a1 0, a1 1, a1 2]

/-- The matrix `M = L⁻¹R` of (3.9), p. 11. (`L` is lower triangular with determinant
`(A₂ᵀA₂)(A₃ᵀA₃)`, nonzero when `[A₁, A₂, A₃]` is nonsingular, so `⁻¹` is the true inverse
there.) -/
noncomputable def Mmat (a1 a2 a3 : Fin 3 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (Lmat a2 a3)⁻¹ * Rmat a1 a2 a3

/-- `L` of p. 12, the matrix (3.6) at the data (3.10). -/
def L310 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![6, 0, 0, 0, 0;
     7, 9, 0, 0, 0;
     1, 1, 1, 0, 0;
     1, 2, 0, 1, 0;
     2, 2, 0, 0, 1]

/-- `R` of p. 12, the matrix (3.7) at the data (3.10). -/
noncomputable def R310 : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 / 3 : ℝ) •
  !![16, -1, -1, -1, 2;
     20, 25, -2, 1, 1;
     4, 5, 2, -1, -1;
     4, 5, -1, 2, -1;
     4, 5, -1, -1, 2]

/-- `M = L⁻¹R` of p. 12 at the data (3.10). -/
noncomputable def M310 : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 / 162 : ℝ) •
  !![144, -9, -9, -9, 18;
     8, 157, -5, 13, -8;
     64, 122, 122, -58, -64;
     56, -35, -35, 91, -56;
     -88, -26, -26, -62, 88]

end ExtADMM.Diverge


