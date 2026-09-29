-- Prove2me | Definitions.Def_RobustLS_LinFrac_Core
-- name    : RobustLS_LinFrac_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:37:26.686398+00:00
-- url     : https://prove2.me/theorems/d1aac503-4ef4-47fc-ae9f-afc17d16aa8d
-- title:
--   Linear-fractional perturbation model of §5.2: $A(\Delta)$, $b(\Delta)$, the event $\lambda > r_{\mathcal D}(A,b,x)$, the commutants (37) and the LMIs (9), (10), (38), (39)
-- statement:
--   This module fixes the objects of §§2.2 and 5 of El Ghaoui and Lebret's paper on robust least squares.
--
--   **Norms.** Vectors carry the **Euclidean norm** $\|v\| = \sqrt{\sum_i v_i^2}$. For a (possibly rectangular) real matrix $X$, $\|X\|$ is its **largest singular value**, i.e. the operator norm $\|X\| = \sup_{v \neq 0} \|Xv\|/\|v\|$.
--
--   **Linear-fractional perturbations (§5.2).** Let $\mathcal D$ be a linear subspace of $\mathbb R^{N\times N}$, and let $A \in \mathbb R^{n\times m}$, $b \in \mathbb R^n$, $L \in \mathbb R^{n\times N}$, $R_A \in \mathbb R^{N\times m}$, $R_b \in \mathbb R^N$, $D \in \mathbb R^{N\times N}$. For $\Delta \in \mathcal D$ with $\det(I - D\Delta) \neq 0$,
--
--   $$
--   A(\Delta) = A + L\Delta(I - D\Delta)^{-1}R_A, \qquad b(\Delta) = b + L\Delta(I - D\Delta)^{-1}R_b .
--   $$
--
--   For $x \in \mathbb R^m$ the **worst-case residual** (35), with $\rho = 1$, is $r_{\mathcal D}(A,b,x) = \max_{\Delta \in \mathcal D,\ \|\Delta\| \le 1} \|A(\Delta)x - b(\Delta)\|$ when $\det(I - D\Delta) \neq 0$ for every such $\Delta$, and $+\infty$ otherwise. The predicate $\mathrm{ResidualBelow}(\lambda, x)$ states $\lambda > r_{\mathcal D}(A,b,x)$: for every $\Delta \in \mathcal D$ with $\|\Delta\| \le 1$, $\det(I - D\Delta) \neq 0$ and $\|A(\Delta)x - b(\Delta)\| < \lambda$.
--
--   **Commutants (37).** $\mathcal B = \{B \in \mathbb R^{N\times N} : B\Delta = \Delta B \text{ for every } \Delta \in \mathcal D\}$, $\mathcal S = \{S \in \mathcal B : S = S^T\}$ and $\mathcal G = \{G \in \mathcal B : G = -G^T\}$.
--
--   **The matrix inequalities.** For $T_1 = T_1^T$, $T_2$, $T_3$, $T_4$ of compatible sizes, Lemma 2.2's function is $T(\Delta) = T_1 + T_2\Delta(I - T_4\Delta)^{-1}T_3 + T_3^T(I - T_4\Delta)^{-T}\Delta^T T_2^T$ (9); its block matrix (10) is
--
--   $$
--   \begin{bmatrix} T_1 - \tau T_2T_2^T & T_3^T - \tau T_2T_4^T \\ T_3 - \tau T_4T_2^T & \tau(I - T_4T_4^T) \end{bmatrix},
--   $$
--
--   and Lemma 2.3's block matrix is $\begin{bmatrix} T_1 - T_2ST_2^T & T_3^T - T_2ST_4^T + T_2G \\ T_3 - T_4ST_2^T - GT_2^T & S - GT_4^T + T_4G - T_4ST_4^T \end{bmatrix}$. The matrix of the §5.4 characterization is
--
--   $$
--   \begin{bmatrix} \lambda I & Ax - b \\ (Ax-b)^T & \lambda \end{bmatrix} + \begin{bmatrix} L \\ 0 \end{bmatrix}\Delta(I - D\Delta)^{-1}\begin{bmatrix} 0 & R_Ax - R_b \end{bmatrix} + \begin{bmatrix} 0 \\ (R_Ax - R_b)^T \end{bmatrix}(I - D\Delta)^{-T}\Delta^T\begin{bmatrix} L^T & 0 \end{bmatrix},
--   $$
--
--   and the SDP constraint (38)–(39) is
--
--   $$
--   \mathcal F(\lambda, S, G, x) = \begin{bmatrix} \Theta & \begin{matrix} Ax - b \\ R_Ax - R_b \end{matrix} \\ \begin{matrix} (Ax-b)^T & (R_Ax - R_b)^T \end{matrix} & \lambda \end{bmatrix}, \quad \Theta = \begin{bmatrix} \lambda I - LSL^T & -LSD^T + LG \\ -DSL^T + G^TL^T & S + DG - GD^T - DSD^T \end{bmatrix}.
--   $$
--
--   These are the objects of Theorem 5.2: minimizing $\lambda$ subject to $S \in \mathcal S$, $G \in \mathcal G$ and $\mathcal F(\lambda,S,G,x) \succ 0$ bounds the worst-case residual from above.
--
--   **Formalization Note** The Euclidean norm is written out as a square root of a sum of squares, because Mathlib's `‖·‖` on `Fin n → ℝ` is the sup norm; the largest singular value is the operator norm of `Matrix.toEuclideanLin X`, the same value as Mathlib's scoped `Matrix.Norms.L2Operator` norm. $\lambda > r_{\mathcal D}$ is encoded directly by the predicate `ResidualBelow`, never through a real supremum, so the value $+\infty$ of (35) is represented exactly (the predicate is false for every $\lambda$). Inverses are Mathlib's `Matrix.inv`, which returns $0$ on a singular matrix, so every statement using $A(\Delta)$, $b(\Delta)$ or $T(\Delta)$ carries $\det(I - D\Delta) \neq 0$ (resp. $\det(I - T_4\Delta) \ne 0$). Block matrices use `Matrix.fromBlocks`; the (38) matrix is indexed by `(Fin n ⊕ Fin N) ⊕ Unit` (the blocks $n$, $N$, $1$ of the page), Θ by `Fin n ⊕ Fin N`, the §5.4 matrix by `Fin n ⊕ Unit`.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1035, Notation; pp. 1038–1039, Lemmas 2.2–2.3, Eqs. (9)–(10); p. 1046, §5.2, Eq. (35); p. 1047, §5.4, Eq. (37); p. 1048, Eqs. (38)–(39)

import Mathlib

namespace RobustLS.LinFrac

open Matrix

/-- The Euclidean norm `‖v‖ = √(∑ᵢ vᵢ²)` of a real vector indexed by a finite type.
El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Notation, p. 1035 (PDF p. 1): vectors carry the
Euclidean norm. (Written out because `‖v‖` on `ι → ℝ` in Mathlib is the sup norm.) -/
noncomputable def eucNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The largest singular value `‖X‖` of a real (possibly rectangular) matrix: the operator norm
of `v ↦ X v` from Euclidean space to Euclidean space (the same value as Mathlib's scoped
`Matrix.Norms.L2Operator` norm, see `Matrix.l2_opNorm_def`).
El Ghaoui & Lebret (1997), Notation, p. 1035 (PDF p. 1): "For a matrix X, ‖X‖ denotes the
largest singular value". -/
noncomputable def specNorm {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (X : Matrix ι κ ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)‖

/-- The commutant `ℬ = {B ∈ ℝ^{N×N} | BΔ = ΔB for every Δ ∈ 𝒟}` of a subspace `𝒟` of
`ℝ^{N×N}`. El Ghaoui & Lebret (1997), §5.4, Eq. (37), p. 1047 (PDF p. 13). -/
def commutant {N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ)) :
    Set (Matrix (Fin N) (Fin N) ℝ) :=
  {B | ∀ Δ ∈ 𝒟, B * Δ = Δ * B}

/-- `𝒮 = {S ∈ ℬ | S = Sᵀ}`: the symmetric matrices commuting with every element of `𝒟`.
El Ghaoui & Lebret (1997), §5.4, Eq. (37), p. 1047 (PDF p. 13); also Lemma 2.3, p. 1039. -/
def symCommutant {N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ)) :
    Set (Matrix (Fin N) (Fin N) ℝ) :=
  {S | S ∈ commutant 𝒟 ∧ S = Sᵀ}

/-- `𝒢 = {G ∈ ℬ | G = −Gᵀ}`: the skew-symmetric matrices commuting with every element of `𝒟`.
El Ghaoui & Lebret (1997), §5.4, Eq. (37), p. 1047 (PDF p. 13); also Lemma 2.3, p. 1039. -/
def skewCommutant {N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ)) :
    Set (Matrix (Fin N) (Fin N) ℝ) :=
  {G | G ∈ commutant 𝒟 ∧ G = -Gᵀ}

/-- The linear-fractional matrix function of Lemma 2.2, Eq. (9):
`T(Δ) = T₁ + T₂Δ(I − T₄Δ)⁻¹T₃ + T₃ᵀ(I − T₄Δ)⁻ᵀΔᵀT₂ᵀ`, with `T₁ ∈ ℝ^{d×d}`, `T₂ ∈ ℝ^{d×k}`,
`T₃ ∈ ℝ^{l×d}`, `T₄ ∈ ℝ^{l×k}` and `Δ ∈ ℝ^{k×l}`. `(·)⁻¹` is Mathlib's `Matrix.inv`, which
returns `0` on a singular matrix; every statement using `T(Δ)` carries `det(I − T₄Δ) ≠ 0`.
El Ghaoui & Lebret (1997), §2.2, Lemma 2.2, Eq. (9), p. 1038 (PDF p. 4). -/
noncomputable def lftT {d k l : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ)
    (T₂ : Matrix (Fin d) (Fin k) ℝ) (T₃ : Matrix (Fin l) (Fin d) ℝ)
    (T₄ : Matrix (Fin l) (Fin k) ℝ) (Δ : Matrix (Fin k) (Fin l) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  T₁ + T₂ * Δ * (1 - T₄ * Δ)⁻¹ * T₃ + T₃ᵀ * ((1 - T₄ * Δ)⁻¹)ᵀ * Δᵀ * T₂ᵀ

/-- The block matrix of Lemma 2.2, Eq. (10), with rows/columns indexed by `Fin d ⊕ Fin l`:
`[[T₁ − τT₂T₂ᵀ, T₃ᵀ − τT₂T₄ᵀ], [T₃ − τT₄T₂ᵀ, τ(I − T₄T₄ᵀ)]]`.
El Ghaoui & Lebret (1997), §2.2, Lemma 2.2, Eq. (10), p. 1038 (PDF p. 4). -/
def lemma22Block {d k l : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ)
    (T₂ : Matrix (Fin d) (Fin k) ℝ) (T₃ : Matrix (Fin l) (Fin d) ℝ)
    (T₄ : Matrix (Fin l) (Fin k) ℝ) (τ : ℝ) :
    Matrix (Fin d ⊕ Fin l) (Fin d ⊕ Fin l) ℝ :=
  Matrix.fromBlocks (T₁ - τ • (T₂ * T₂ᵀ)) (T₃ᵀ - τ • (T₂ * T₄ᵀ))
    (T₃ - τ • (T₄ * T₂ᵀ)) (τ • (1 - T₄ * T₄ᵀ))

/-- The block matrix of Lemma 2.3 (square perturbations, `k = l = N`), rows/columns indexed by
`Fin d ⊕ Fin N`:
`[[T₁ − T₂ST₂ᵀ, T₃ᵀ − T₂ST₄ᵀ + T₂G], [T₃ − T₄ST₂ᵀ − GT₂ᵀ, S − GT₄ᵀ + T₄G − T₄ST₄ᵀ]]`.
El Ghaoui & Lebret (1997), §2.2, Lemma 2.3, p. 1039 (PDF p. 5). -/
def lemma23Block {d N : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ)
    (T₂ : Matrix (Fin d) (Fin N) ℝ) (T₃ : Matrix (Fin N) (Fin d) ℝ)
    (T₄ S G : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin d ⊕ Fin N) (Fin d ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (T₁ - T₂ * S * T₂ᵀ) (T₃ᵀ - T₂ * S * T₄ᵀ + T₂ * G)
    (T₃ - T₄ * S * T₂ᵀ - G * T₂ᵀ) (S - G * T₄ᵀ + T₄ * G - T₄ * S * T₄ᵀ)

/-- The perturbed matrix `A(Δ) = A + LΔ(I − DΔ)⁻¹R_A` of §5.2, with `A ∈ ℝ^{n×m}`,
`L ∈ ℝ^{n×N}`, `R_A ∈ ℝ^{N×m}`, `D, Δ ∈ ℝ^{N×N}`. Meaningful only when `det(I − DΔ) ≠ 0`
(Lean's `Matrix.inv` returns `0` otherwise; every statement using it carries that condition).
El Ghaoui & Lebret (1997), §5.2, p. 1046 (PDF p. 12). -/
noncomputable def pertA {n m N : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (L : Matrix (Fin n) (Fin N) ℝ) (RA : Matrix (Fin N) (Fin m) ℝ)
    (D Δ : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  A + L * Δ * (1 - D * Δ)⁻¹ * RA

/-- The perturbed vector `b(Δ) = b + LΔ(I − DΔ)⁻¹R_b` of §5.2, with `b ∈ ℝ^n`, `R_b ∈ ℝ^N`.
Meaningful only when `det(I − DΔ) ≠ 0`.
El Ghaoui & Lebret (1997), §5.2, p. 1046 (PDF p. 12). -/
noncomputable def pertB {n N : ℕ} (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (Rb : Fin N → ℝ) (D Δ : Matrix (Fin N) (Fin N) ℝ) : Fin n → ℝ :=
  b + (L * Δ * (1 - D * Δ)⁻¹) *ᵥ Rb

/-- `ResidualBelow 𝒟 A b L RA Rb D x lam` is the statement `lam > r_𝒟(A, b, x)` for the
worst-case residual (35) with `ρ = 1`: for every `Δ ∈ 𝒟` with `‖Δ‖ ≤ 1` (largest singular
value), `det(I − DΔ) ≠ 0` and `‖A(Δ)x − b(Δ)‖ < lam`. If some admissible `Δ` makes `I − DΔ`
singular, (35) sets `r_𝒟 = ∞` and the predicate is false for every `lam`, as it should be.
(Since `{Δ ∈ 𝒟 | ‖Δ‖ ≤ 1}` is compact and the residual is continuous on it when no determinant
vanishes, the maximum in (35) is attained, so the pointwise strict bound is exactly
`lam > max`.)
El Ghaoui & Lebret (1997), §5.2, Eq. (35), p. 1046 (PDF p. 12). -/
def ResidualBelow {n m N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) : Prop :=
  ∀ Δ ∈ 𝒟, specNorm Δ ≤ 1 →
    (1 - D * Δ).det ≠ 0 ∧ eucNorm (pertA A L RA D Δ *ᵥ x - pertB b L Rb D Δ) < lam

/-- The matrix of the §5.4 characterization (p. 1047), rows/columns indexed by `Fin n ⊕ Unit`:
`[[λI, Ax − b], [(Ax − b)ᵀ, λ]] + [L; 0] Δ(I − DΔ)⁻¹ [0  R_Ax − R_b]
   + [0; (R_Ax − R_b)ᵀ] (I − DΔ)⁻ᵀΔᵀ [Lᵀ  0]`.
El Ghaoui & Lebret (1997), §5.4, p. 1047 (PDF p. 13). -/
noncomputable def residualLMI {n m N : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (L : Matrix (Fin n) (Fin N) ℝ) (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ)
    (D : Matrix (Fin N) (Fin N) ℝ) (x : Fin m → ℝ) (lam : ℝ)
    (Δ : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks (lam • (1 : Matrix (Fin n) (Fin n) ℝ)) (replicateCol Unit (A *ᵥ x - b))
      (replicateRow Unit (A *ᵥ x - b)) (lam • (1 : Matrix Unit Unit ℝ))
    + Matrix.fromRows L (0 : Matrix Unit (Fin N) ℝ) * Δ * (1 - D * Δ)⁻¹
        * Matrix.fromCols (0 : Matrix (Fin N) (Fin n) ℝ) (replicateCol Unit (RA *ᵥ x - Rb))
    + Matrix.fromRows (0 : Matrix (Fin n) (Fin N) ℝ) (replicateRow Unit (RA *ᵥ x - Rb))
        * ((1 - D * Δ)⁻¹)ᵀ * Δᵀ * Matrix.fromCols Lᵀ (0 : Matrix (Fin N) Unit ℝ)

/-- The matrix `Θ` of Eq. (39), rows/columns indexed by `Fin n ⊕ Fin N`:
`Θ = [[λI − LSLᵀ, −LSDᵀ + LG], [−DSLᵀ + GᵀLᵀ, S + DG − GDᵀ − DSDᵀ]]`.
El Ghaoui & Lebret (1997), §5.4, Eq. (39), p. 1048 (PDF p. 14). -/
def theta {n N : ℕ} (L : Matrix (Fin n) (Fin N) ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (lam : ℝ) (S G : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin n ⊕ Fin N) (Fin n ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (lam • (1 : Matrix (Fin n) (Fin n) ℝ) - L * S * Lᵀ) (-(L * S * Dᵀ) + L * G)
    (-(D * S * Lᵀ) + Gᵀ * Lᵀ) (S + D * G - G * Dᵀ - D * S * Dᵀ)

/-- The matrix `𝓕(λ, S, G, x)` of Eq. (38), rows/columns indexed by `(Fin n ⊕ Fin N) ⊕ Unit`
(the blocks `n`, `N`, `1` of the page, in that order):
`𝓕 = [[Θ, (Ax − b; R_Ax − R_b)], [((Ax − b)ᵀ, (R_Ax − R_b)ᵀ), λ]]`.
El Ghaoui & Lebret (1997), §5.4, Eq. (38), p. 1048 (PDF p. 14). -/
noncomputable def lmiF {n m N : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (L : Matrix (Fin n) (Fin N) ℝ) (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ)
    (D : Matrix (Fin N) (Fin N) ℝ) (x : Fin m → ℝ) (lam : ℝ) (S G : Matrix (Fin N) (Fin N) ℝ) :
    Matrix ((Fin n ⊕ Fin N) ⊕ Unit) ((Fin n ⊕ Fin N) ⊕ Unit) ℝ :=
  Matrix.fromBlocks (theta L D lam S G)
    (replicateCol Unit (Sum.elim (A *ᵥ x - b) (RA *ᵥ x - Rb)))
    (replicateRow Unit (Sum.elim (A *ᵥ x - b) (RA *ᵥ x - Rb)))
    (lam • (1 : Matrix Unit Unit ℝ))

end RobustLS.LinFrac


