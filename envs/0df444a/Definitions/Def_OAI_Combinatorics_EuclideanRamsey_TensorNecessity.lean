-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
-- name    : OAI_Combinatorics_EuclideanRamsey_TensorNecessity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:17:14.622519+00:00
-- url     : https://prove2.me/theorems/dca92790-ac9a-4a4b-8302-1d478d3105cc
-- title:
--   Arrays over $\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$, augmented evaluation maps and the real tensor criterion
-- statement:
--   This file introduces the real-coefficient form of the tensor criterion for finite point configurations, together with the special arrays, matrices and vectors used to test it.
--
--   Throughout, $s$ and $d$ are natural numbers and $a=(a_1,\dots,a_s)$ is a family of points of the Euclidean space $\mathbb{R}^d$, with coordinates $a_i=(a_{i1},\dots,a_{id})$. Write $T=\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$ for the tensor product of $\mathbb{R}$ with itself over $\mathbb{Q}$ (a commutative ring), and $m:T\to\mathbb{R}$ for the multiplication map $x\otimes y\mapsto xy$. Arrays are indexed by the augmented index set $\{0,1,\dots,d\}$, in which $0$ is an extra index for the constant term.
--
--   1. **Arrays and the separation space.** A *real array* is a matrix $P=(P_{\alpha\beta})_{\alpha,\beta\in\{0,\dots,d\}}$ with entries in $T$. The *separation space* is $T^s\times M_d(\mathbb{R})$, consisting of an $s$-tuple of elements of $T$ together with a real $d\times d$ matrix.
--   2. **Augmented points.** For each $i$, $\tilde a_i\in\mathbb{R}^{1+d}$ is the vector with $\tilde a_i(0)=1$ and $\tilde a_i(j)=a_{ij}$ for $1\le j\le d$.
--   3. **Array evaluation at a point.** For each $i$, $E_i$ is the $\mathbb{Q}$-linear map from real arrays to $T$ given by
--   $$E_i(P)=\sum_{\alpha=0}^{d}\sum_{\beta=0}^{d}\bigl(\tilde a_i(\alpha)\otimes1\bigr)\,P_{\alpha\beta}\,\bigl(1\otimes\tilde a_i(\beta)\bigr).$$
--   4. **Spatial multiplication.** $S$ is the $\mathbb{Q}$-linear map from real arrays to $M_d(\mathbb{R})$ with $S(P)_{\alpha\beta}=m(P_{\alpha\beta})$ for $1\le\alpha,\beta\le d$; the row and the column with index $0$ are discarded.
--   5. **Array map.** $A_a(P)=\bigl((E_1(P),\dots,E_s(P)),\,S(P)\bigr)$, a $\mathbb{Q}$-linear map from real arrays to the separation space.
--   6. **Real criterion.** The configuration $a$ satisfies the *real criterion* if there is a real array $P$ with
--   $$E_i(P)=0\quad\text{for all }1\le i\le s\qquad\text{and}\qquad S(P)=I_d ,$$
--   that is, if $(0,I_d)$ lies in the image of $A_a$.
--   7. **Rank-one test data.** For $v\in\mathbb{R}$ and $u\in\mathbb{R}^d$ put $w=(v,u_1,\dots,u_d)\in\mathbb{R}^{1+d}$. The *diagonal array* $\mathcal D(v,u)$ has entries $\mathcal D(v,u)_{\alpha\beta}=w_\alpha\otimes w_\beta$; the real $d\times d$ matrix $uu^{\mathsf T}$ has entries $u_\alpha u_\beta$; and the *affine evaluation* at the $i$-th point is $\ell_i(v,u)=v+\sum_{j=1}^{d}a_{ij}u_j$.
--   8. **Rows of an isometry.** For a linear isometry $Q:\mathbb{R}^d\to\mathbb{R}^D$ and $1\le j\le D$, $q_j\in\mathbb{R}^d$ is the vector with entries $(q_j)_\alpha=(Qe_\alpha)_j$, i.e. the $j$-th row of the matrix of $Q$ in the standard bases.
--
--   A configuration is *Ramsey* if for every number $r\ge2$ of colours there is a dimension $D\ge1$ such that every colouring of $\mathbb{R}^D$ with $r$ colours contains a monochromatic congruent copy of it. The real criterion is the field criterion of the Euclidean Ramsey classification with the coordinate field $K$ (the subfield of $\mathbb{R}$ generated over $\mathbb{Q}$ by all coordinates $a_{ij}$) replaced by $\mathbb{R}$ itself, and it serves as the intermediate condition between being Ramsey and satisfying the field criterion. The test data are matched to the maps above: expanding the definitions gives $E_i(\mathcal D(v,u))=\ell_i(v,u)\otimes\ell_i(v,u)$ and $S(\mathcal D(v,u))=uu^{\mathsf T}$, and the rows of an isometry satisfy $\sum_j q_jq_j^{\mathsf T}=I_d$. This is what allows a $\mathbb{Q}$-linear functional separating $(0,I_d)$ from the image of $A_a$ to be converted into real-valued functions that every congruent copy of $a$ must violate.
--
--   **Formalization Note** `RealTensor` is `ℝ ⊗[ℚ] ℝ`, `RealArray d` is `Matrix (Option (Fin d)) (Option (Fin d)) RealTensor` (the index `none` plays the role of $0$ and `some j` that of the coordinate $j$; Lean's coordinates run over `Fin d`), and `SeparationSpace s d` is `(Fin s → RealTensor) × Matrix (Fin d) (Fin d) ℝ`. The points live in `Space d = EuclideanSpace ℝ (Fin d)`. The maps are `realAugmented`, `arrayEvaluation`, `spatialMultiply` (built from `Algebra.TensorProduct.lmul'`) and `arrayMap`, the criterion is `RealCriterion`, and the test data are `diagonalArray`, `gradientRankOne`, `affineEvaluation` and `isometryRows`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamsey mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamsey

namespace OAI

universe uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

abbrev RealTensor := ℝ ⊗[ℚ] ℝ
abbrev RealArray (d : ℕ) := Matrix (Option (Fin d)) (Option (Fin d)) RealTensor
abbrev SeparationSpace (s d : ℕ) := (Fin s → RealTensor) × Matrix (Fin d) (Fin d) ℝ

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

def arrayMap {s d : ℕ} (a : Fin s → Space d) :
    RealArray d →ₗ[ℚ] SeparationSpace s d :=
  (LinearMap.pi (arrayEvaluation a)).prod spatialMultiply

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


