-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
-- name    : OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:53:43.221864+00:00
-- url     : https://prove2.me/theorems/e604d47e-17ef-4597-aa5f-2c8e0dab8e67
-- title:
--   Arrays over $\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$, the real tensor criterion and rank-one test arrays
-- statement:
--   This file introduces the real-coefficient form of the tensor criterion for finite point configurations, together with the rank-one arrays, affine evaluations and isometry rows used to build solutions of it.
--
--   Throughout, $s$ and $d$ are natural numbers and $a=(a_1,\dots,a_s)$ is a family of points of the Euclidean space $\mathbb{R}^d$, with coordinates $a_i=(a_{i1},\dots,a_{id})$. Write $T=\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$ for the tensor product of $\mathbb{R}$ with itself over $\mathbb{Q}$ (a commutative ring) and $m:T\to\mathbb{R}$ for the multiplication map $x\otimes y\mapsto xy$. Arrays are indexed by the augmented index set $\{0,1,\dots,d\}$, in which $0$ is an extra index for the constant term.
--
--   1. **Real arrays.** A *real array* is a matrix $P=(P_{\alpha\beta})_{\alpha,\beta\in\{0,\dots,d\}}$ with entries in $T$.
--   2. **Augmented points.** For each $i$, $\tilde a_i:\{0,\dots,d\}\to\mathbb{R}$ is given by $\tilde a_i(0)=1$ and $\tilde a_i(j)=a_{ij}$ for $1\le j\le d$.
--   3. **Array evaluation.** For each $i$, $E_i$ is the $\mathbb{Q}$-linear map from real arrays to $T$ defined by
--   $$E_i(P)=\sum_{\alpha=0}^{d}\sum_{\beta=0}^{d}\bigl(\tilde a_i(\alpha)\otimes1\bigr)\,P_{\alpha\beta}\,\bigl(1\otimes\tilde a_i(\beta)\bigr).$$
--   4. **Spatial multiplication.** $S$ is the $\mathbb{Q}$-linear map from real arrays to real $d\times d$ matrices with $S(P)_{\alpha\beta}=m(P_{\alpha\beta})$ for $1\le\alpha,\beta\le d$; the row and the column with index $0$ are discarded.
--   5. **Real criterion.** The configuration $a$ satisfies the *real criterion* if there is a real array $P$ with
--   $$E_i(P)=0\quad\text{for all }1\le i\le s\qquad\text{and}\qquad S(P)=I_d ,$$
--   where $I_d$ is the $d\times d$ identity matrix.
--   6. **Diagonal arrays.** For $v\in\mathbb{R}$ and $u\in\mathbb{R}^d$ let $w=(w_0,w_1,\dots,w_d)=(v,u_1,\dots,u_d)$. The diagonal array $\mathcal D(v,u)$ has entries $\mathcal D(v,u)_{\alpha\beta}=w_\alpha\otimes w_\beta$.
--   7. **Rank-one matrices.** For $u\in\mathbb{R}^d$, $uu^{\mathsf T}$ is the real $d\times d$ matrix with entries $u_\alpha u_\beta$.
--   8. **Affine evaluation.** For $v\in\mathbb{R}$, $u\in\mathbb{R}^d$ and an index $i$, $\ell_i(v,u)=v+\sum_{j=1}^{d}a_{ij}u_j$.
--   9. **Rows of an isometry.** For a linear isometry $Q:\mathbb{R}^d\to\mathbb{R}^D$ and $1\le j\le D$, $q_j\in\mathbb{R}^d$ is the vector with entries $(q_j)_\alpha=(Qe_\alpha)_j$, where $e_1,\dots,e_d$ are the standard basis vectors; thus $q_j$ is the $j$-th row of the matrix of $Q$.
--
--   The real criterion is the field criterion of the classification of Euclidean Ramsey configurations with the coordinate field (the subfield of $\mathbb{R}$ generated over $\mathbb{Q}$ by all $a_{ij}$) replaced by $\mathbb{R}$; in this development the two criteria are shown to be equivalent. The test data match the maps: directly from the definitions, $E_i(\mathcal D(v,u))=\ell_i(v,u)\otimes\ell_i(v,u)$ and $S(\mathcal D(v,u))=uu^{\mathsf T}$; for an isometry $Q$ and $z\in\mathbb{R}^D$, $\ell_i(z_j,q_j)$ is the $j$-th coordinate of $z+Qa_i$; and $\sum_{j=1}^{D}q_jq_j^{\mathsf T}=I_d$ because $Q$ preserves inner products. Hence for a congruent copy $(z+Qa_i)_{i}$ of the configuration in $\mathbb{R}^D$ and any point $c\in\mathbb{R}^D$, the array $\sum_{j=1}^{D}\bigl(\mathcal D(z_j,q_j)-\mathcal D(c_j,0)\bigr)$ has spatial multiplication $I_d$ and evaluations $E_i=\sum_{j}\bigl((z+Qa_i)_j\otimes(z+Qa_i)_j-c_j\otimes c_j\bigr)$. When $a$ is congruent to part of a finite configuration $y$ whose distance-preserving permutations act transitively, and the points of $a$ affinely span $\mathbb{R}^d$, every such permutation yields a congruent copy of this form; averaging the corresponding arrays over the group, with $c$ the copy of a fixed base point, makes all evaluations vanish by transitivity and therefore produces a solution of the real criterion.
--
--   **Formalization Note** `RealTensor` is `ℝ ⊗[ℚ] ℝ` and `RealArray d` is `Matrix (Option (Fin d)) (Option (Fin d)) RealTensor`, where `none` plays the role of the index $0$ and Lean's coordinates run over `Fin d`; points live in `Space d = EuclideanSpace ℝ (Fin d)`. The maps are `realAugmented`, `arrayEvaluation` and `spatialMultiply` (built from `Algebra.TensorProduct.lmul'`), the criterion is `RealCriterion` (with `spatialMultiply P = 1`), and the test data are `diagonalArray`, `gradientRankOne`, `affineEvaluation` and `isometryRows`, the last defined as `WithLp.toLp 2 (fun α => Q (EuclideanSpace.single α 1) j)`. The identities quoted above are proved separately, not in this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyTransitive mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model

namespace OAI

universe uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

abbrev RealTensor := ℝ ⊗[ℚ] ℝ
abbrev RealArray (d : ℕ) := Matrix (Option (Fin d)) (Option (Fin d)) RealTensor
def realAugmented {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : Option (Fin d) → ℝ
  | none => 1
  | some j => a i j

def arrayEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s) :
    RealArray d →ₗ[ℚ] RealTensor where
  toFun P := ∑ α, ∑ β, ((realAugmented a i α) ⊗ₜ[ℚ] (1 : ℝ)) * P α β *
    ((1 : ℝ) ⊗ₜ[ℚ] (realAugmented a i β))
  map_add' P Q := by
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' q P := by
    simp only [Matrix.smul_apply, RingHom.id_apply, mul_smul_comm, smul_mul_assoc,
      Finset.smul_sum]

def spatialMultiply {d : ℕ} : RealArray d →ₗ[ℚ] Matrix (Fin d) (Fin d) ℝ where
  toFun P := fun α β => Algebra.TensorProduct.lmul' ℚ (P (some α) (some β))
  map_add' P Q := by
    ext α β
    exact map_add (Algebra.TensorProduct.lmul' ℚ) _ _
  map_smul' q P := by
    ext α β
    exact (Algebra.TensorProduct.lmul' ℚ).toLinearMap.map_smul q _

def RealCriterion {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∃ P : RealArray d, (∀ i, arrayEvaluation a i P = 0) ∧ spatialMultiply P = 1

def diagonalArray {d : ℕ} (v : ℝ) (u : Space d) : RealArray d :=
  let w : Option (Fin d) → ℝ := fun α => α.elim v (u ·)
  fun α β => w α ⊗ₜ[ℚ] w β

def gradientRankOne {d : ℕ} (u : Space d) : Matrix (Fin d) (Fin d) ℝ :=
  fun α β => u α * u β

def affineEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (v : ℝ) (u : Space d) : ℝ := v + ∑ j, a i j * u j

def isometryRows {d D : ℕ} (Q : Space d →ₗᵢ[ℝ] Space D) (j : Fin D) : Space d :=
  WithLp.toLp 2 (fun α => Q (EuclideanSpace.single α 1) j)

end EuclideanRamsey

end

end OAI


