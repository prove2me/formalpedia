-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyCircle
-- name    : OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyCircle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:34:39.661506+00:00
-- url     : https://prove2.me/theorems/d6ff050e-9b80-41ea-99b9-08ca4a2293d2
-- title:
--   The real tensor criterion for point configurations
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $T=\mathbb R\otimes_{\mathbb Q}\mathbb R$ and $m:T\to\mathbb R$ the multiplication map. Arrays are indexed by $\{0,1,\dots,d\}$, where $0$ is an extra index for the constant term.
--
--   1. **Real arrays.** Matrices $P=(P_{\alpha\beta})_{\alpha,\beta\in\{0,\dots,d\}}$ with entries in $T$. The separation space is $T^s\times\mathbb R^{d\times d}$.
--   2. **Augmented points and evaluation.** $\tilde a_i(0)=1$ and $\tilde a_i(j)=a_{ij}$. The $\mathbb Q$-linear map $E_i(P)=\sum_{\alpha,\beta}(\tilde a_i(\alpha)\otimes1)\,P_{\alpha\beta}\,(1\otimes\tilde a_i(\beta))$.
--   3. **Spatial multiplication.** $S(P)_{jk}=m(P_{jk})$ for $1\le j,k\le d$. The array map is $P\mapsto\bigl((E_i(P))_i,S(P)\bigr)$.
--   4. **Real criterion.** There is a real array $P$ with $E_i(P)=0$ for all $i$ and $S(P)=I$.
--   5. **Test arrays and helpers.** The rank-one array $w\otimes w$ with $w=(v,u)$ for $v\in\mathbb R$ and $u\in\mathbb R^d$; the rank-one matrix $uu^{\mathsf T}$; the affine evaluation $v+\langle a_i,u\rangle$; and the rows of a linear isometry $\mathbb R^d\to\mathbb R^D$, viewed as vectors of $\mathbb R^d$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension

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


