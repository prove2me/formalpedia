-- Prove2me | Definitions.Def_RobustOpt2009_SDPApproximation_Model
-- name    : RobustOpt2009_SDPApproximation_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:11.251548+00:00
-- url     : https://prove2.me/theorems/1bf28c1a-c0e4-4b7e-b9e7-6e2922e57359
-- title:
--   Structured robust LMIs and their finite SDP certificate
-- statement:
--   Let $m$ be the matrix size, $s$ the number of scalar blocks and $f$ the number of full matrix blocks. For each full block $j$, choose positive dimensions $p_j,q_j$. A mixed matrix cube has symmetric real matrices $A^n,A_i$ and real matrices $L_j\in\mathbb R^{p_j\times m}$ and $R_j\in\mathbb R^{q_j\times m}$. Its uncertain body is
--   $$A^n+\sum_{i=1}^s z_i A_i+\sum_{j=1}^f(L_j^TZ_jR_j+R_j^TZ_j^TL_j).$$
--   The predicate $\mathcal A(\rho)$ requires this matrix to be positive semidefinite for every $|z_i|\le\rho$ and every $\|Z_j\|_{2,2}\le\rho$. The independent domination predicate $\mathcal B(\rho)$ asks for symmetric $U_i,V_j$ such that $U_i\succeq\pm A_i$, each $V_j$ dominates $L_j^TZR_j+R_j^TZ^TL_j$ for every $\|Z\|_{2,2}\le1$, and $A^n-\rho\sum_iU_i-\rho\sum_jV_j\succeq0$.
--
--   The finite certificate $\mathcal C(\rho)$ instead asks for symmetric $U_i,V_j$ and real $\lambda_j$ satisfying
--   $$U_i\succeq\pm A_i,\qquad
--   \begin{bmatrix}\lambda_j I_{p_j}&L_j\\L_j^T&V_j-\lambda_jR_j^TR_j\end{bmatrix}\succeq0,\qquad
--   A^n-\rho\Bigl(\sum_i U_i+\sum_jV_j\Bigr)\succeq0.$$
--   A structured uncertain LMI makes $A^n,A_i,L_j$ affine in a design vector $y\in\mathbb R^n$, with fixed nonzero $R_j$. Evaluation at $y$ gives the mixed cube above. The least uniform rank index is the least integer $\mu\ge2$ bounding $\operatorname{rank}A_i(y)$ for every scalar index and every design vector.
--
--   These definitions keep robust feasibility, block domination and the finite certificate logically independent.
--
--   **Formalization Note** The two block classes use separate finite index sets; their union has $s+f$ elements. Matrix operator norms use the L2 operator instance. Positive semidefiniteness includes symmetry. The least rank is expressed by an `IsLeast` predicate on a nonempty set of natural numbers; $\max(2,m)$ always bounds it. Definition 9.1.1 is realized by affine maps, not arbitrary functions or assumed equivalences.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Definition 9.1.1 and (9.1.1)–(9.1.4), printed pp. 225–226 (PDF pp. 251–252); Theorem 7.1.3 predicates, printed p. 183 (PDF p. 209)

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustOpt2009.SDPApproximation

/-- Data for the mixed real matrix cube in Theorem 7.1.3. Scalar and full
blocks are enumerated separately; their original ordering is immaterial. -/
structure CubeData (m s f : ℕ) where
  p : Fin f → ℕ
  q : Fin f → ℕ
  p_pos : ∀ j, 0 < p j
  q_pos : ∀ j, 0 < q j
  nominal : Matrix (Fin m) (Fin m) ℝ
  scalar : Fin s → Matrix (Fin m) (Fin m) ℝ
  left : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ
  right : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ
  nominal_symm : nominal.IsHermitian
  scalar_symm : ∀ i, (scalar i).IsHermitian

/-- The uncertain body, with unscaled perturbations. -/
noncomputable def cubeBody {m s f : ℕ} (D : CubeData m s f)
    (z : Fin s → ℝ) (Z : (j : Fin f) → Matrix (Fin (D.p j)) (Fin (D.q j)) ℝ) :=
  D.nominal + (∑ i, z i • D.scalar i) +
    ∑ j, ((D.left j)ᵀ * Z j * D.right j + (D.right j)ᵀ * (Z j)ᵀ * D.left j)

/-- Predicate A(rho) in Theorem 7.1.3. The matrix norm is the Euclidean
operator norm, not Mathlib's default entrywise matrix norm. -/
def Robust {m s f : ℕ} (D : CubeData m s f) (ρ : ℝ) : Prop :=
  ∀ z Z, (∀ i, |z i| ≤ ρ) → (∀ j, ‖Z j‖ ≤ ρ) → (cubeBody D z Z).PosSemidef

/-- Predicate B(rho), defined by actual blockwise domination, independently
of any finite LMI certificate. -/
def Dominating {m s f : ℕ} (D : CubeData m s f) (ρ : ℝ) : Prop :=
  ∃ (U : Fin s → Matrix (Fin m) (Fin m) ℝ)
      (V : Fin f → Matrix (Fin m) (Fin m) ℝ),
    (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
    (∀ i, (U i - D.scalar i).PosSemidef ∧ (U i + D.scalar i).PosSemidef) ∧
    (∀ j, ∀ Z : Matrix (Fin (D.p j)) (Fin (D.q j)) ℝ, ‖Z‖ ≤ 1 →
      (V j - ((D.left j)ᵀ * Z * D.right j +
        (D.right j)ᵀ * Zᵀ * D.left j)).PosSemidef) ∧
    (D.nominal - ρ • (∑ i, U i) - ρ • (∑ j, V j)).PosSemidef

/-- The explicit finite system (9.1.3), existentially projected onto the
fixed data. The real multipliers have no separately imposed sign constraint. -/
def Certificate {m s f : ℕ} (D : CubeData m s f) (ρ : ℝ) : Prop :=
  ∃ (U : Fin s → Matrix (Fin m) (Fin m) ℝ)
    (V : Fin f → Matrix (Fin m) (Fin m) ℝ) (lam : Fin f → ℝ),
    (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
    (∀ i, (U i - D.scalar i).PosSemidef ∧ (U i + D.scalar i).PosSemidef) ∧
    (∀ j, (Matrix.fromBlocks (lam j • (1 : Matrix (Fin (D.p j)) (Fin (D.p j)) ℝ))
      (D.left j) (D.left j)ᵀ
      (V j - lam j • ((D.right j)ᵀ * D.right j))).PosSemidef) ∧
    (D.nominal - ρ • ((∑ i, U i) + ∑ j, V j)).PosSemidef

/-- Definition 9.1.1: affine nominal and scalar matrices, affine left factors,
fixed nonzero right factors, and positive matrix dimensions. -/
structure StructuredData (n m s f : ℕ) where
  p : Fin f → ℕ
  q : Fin f → ℕ
  p_pos : ∀ j, 0 < p j
  q_pos : ∀ j, 0 < q j
  nominal : (Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ
  scalar : Fin s → ((Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ)
  left : (j : Fin f) → ((Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin (p j)) (Fin m) ℝ)
  right : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ
  nominal_symm : ∀ y, (nominal y).IsHermitian
  scalar_symm : ∀ i y, (scalar i y).IsHermitian
  right_ne_zero : ∀ j, right j ≠ 0

/-- Evaluate affine data at the design vector, retaining the original
uncertainty dimensions and coefficients. -/
noncomputable def StructuredData.atDesign {n m s f : ℕ} (D : StructuredData n m s f) (y : Fin n → ℝ) :
    CubeData m s f where
  p := D.p
  q := D.q
  p_pos := D.p_pos
  q_pos := D.q_pos
  nominal := D.nominal y
  scalar := fun i => D.scalar i y
  left := fun j => D.left j y
  right := D.right
  nominal_symm := D.nominal_symm y
  scalar_symm := fun i => D.scalar_symm i y

/-- The book's smallest integer at least two bounding every scalar rank
uniformly over all design vectors. This set is nonempty: max 2 m belongs to it. -/
def LeastUniformRank {n m s f : ℕ} (D : StructuredData n m s f) (μ : ℕ) : Prop :=
  IsLeast {k : ℕ | 2 ≤ k ∧ ∀ i y, (D.scalar i y).rank ≤ k} μ

end RobustOpt2009.SDPApproximation


