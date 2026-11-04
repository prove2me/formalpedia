-- Prove2me | Definitions.Def_FreeGroupFactorProof13
-- name    : FreeGroupFactorProof13
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T02:08:36.622798+00:00
-- url     : https://prove2.me/theorems/6ef5a776-82cb-49b9-8678-b853f67432d5
-- title:
--   Free group factors: supporting development, part 13
-- statement:
--   Part 13 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof12

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

theorem vertex_mul_vertex (r s : Bool) : (vertex r : Operator ι)*vertex s=if r=s then vertex r else 0 := by
  cases r <;> cases s <;> simp only [vertex_false,vertex_true,Bool.false_eq_true,Bool.true_eq_false,
    ite_true,ite_false,mul_sub,sub_mul,one_mul,mul_one,projection_P.isIdempotentElem.eq]
  all_goals abel

theorem vertex_commute_empty (u v : ℝ) (r : Bool) (T : oldAlgebra u v (∅ : Set ι)) :
    Commute (vertex r : Operator ι) (T:Operator ι) := by
  have hp : P∈StarSubalgebra.centralizer ℂ (insert (P : Operator ι) (S u v '' (∅ : Set ι))) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | ⟨_,h,_⟩
    · exact ⟨rfl,by rw [projection_P.isSelfAdjoint.star_eq]⟩
    · exact False.elim h
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property P hp).1
  cases r
  · exact (Commute.one_left _).sub_left hc
  · exact hc

theorem vertex_empty_vertex (u v : ℝ) (r s : Bool) (T : oldAlgebra u v (∅ : Set ι)) :
    (vertex r : Operator ι)*(T:Operator ι)*vertex s=if r=s then (T:Operator ι)*vertex r else 0 := by
  rw [(vertex_commute_empty u v r T).eq,mul_assoc,vertex_mul_vertex]
  split_ifs <;> simp only [mul_zero]

def ambientRect (u v : ℝ) (i : ι) (r s : Bool) : Operator ι := vertex r*C u v i*vertex s

theorem ambientRect_covariance (u v : ℝ) (i j : ι) (r s t q : Bool)
    (T : oldAlgebra u v (∅ : Set ι)) :
    star (ambientRect u v i r s)*(T:Operator ι)*ambientRect u v j t q=
      if i=j ∧ r=t ∧ s=q then vacuumTrace u v ((T:Operator ι)*vertex r) • vertex s else 0 := by
  have hc := fresh_C_contraction u v ∅ i j (by simp) (by simp)
    (vertexOld u v r*T*vertexOld u v t)
  change star (C u v i)*(vertex r*(T:Operator ι)*vertex t)*C u v j=_ at hc
  have hh : star (ambientRect u v i r s)*(T:Operator ι)*ambientRect u v j t q=
      if i=j then vacuumTrace u v (vertex r*(T:Operator ι)*vertex t) • (vertex s*vertex q) else 0 := by
    calc
      _ = vertex s*(star (C u v i)*(vertex r*(T:Operator ι)*vertex t)*C u v j)*vertex q := by
        simp only [ambientRect,star_mul,vertex_star,mul_assoc]
      _ = _ := by
        rw [hc]
        split_ifs <;> simp only [mul_smul_comm,smul_mul_assoc,mul_one,mul_zero,zero_mul]
        rfl
  rw [vertex_empty_vertex,vertex_mul_vertex] at hh
  rw [hh]
  have hz : vacuumTrace u v (0:Operator ι)=0 := by simp only [vacuumTrace,zero_apply,inner_zero_right]
  by_cases hij : i=j <;> by_cases hrt : r=t <;> by_cases hsq : s=q <;>
    simp [hij,hrt,hsq,hz,smul_zero (M := ℂ) (A := Operator ι),zero_smul ℂ (A := Operator ι)]

theorem ambientRect_annihilate (u v : ℝ) (i : ι) (r s : Bool)
    (T : oldAlgebra u v (∅ : Set ι)) :
    star (ambientRect u v i r s) ((T:Operator ι) (vacuum u v))=0 := by
  have hh := fresh_C_annihilates_old_vacuum u v ∅ i (by simp) (vertexOld u v r*T)
  simp only [ambientRect,star_mul,vertex_star,mul_apply_eq_comp]
  change star (C u v i) (vertex r ((T:Operator ι) (vacuum u v)))=0 at hh
  rw [hh,map_zero]

variable (u v : ℝ) (i : ι)
def diagonalCreate : Operator ι := ambientRect u v i true true+ambientRect u v i false false

def diagonalCovariance (T : oldAlgebra u v (∅ : Set ι)) : oldAlgebra u v (∅ : Set ι) :=
  vacuumTrace u v ((T:Operator ι)*vertex true) • vertexOld u v true+
    vacuumTrace u v ((T:Operator ι)*vertex false) • vertexOld u v false

theorem diagonalCreate_covariance (T : oldAlgebra u v (∅ : Set ι)) :
    star (diagonalCreate u v i)*(T:Operator ι)*diagonalCreate u v i=
      (diagonalCovariance u v T : Operator ι) := by
  simp only [diagonalCreate,star_add (R := Operator ι),add_mul,mul_add,ambientRect_covariance,
    Bool.true_eq_false,Bool.false_eq_true,and_self,and_false,ite_true,ite_false,add_zero,zero_add]
  rfl

theorem diagonalCreate_annihilate (T : oldAlgebra u v (∅ : Set ι)) :
    star (diagonalCreate u v i) ((T:Operator ι) (vacuum u v))=0 := by
  simp only [diagonalCreate,star_add (R := Operator ι),add_apply,ambientRect_annihilate,add_zero]

theorem ambientRect_diagonal_orthogonal (r : Bool) (T : oldAlgebra u v (∅ : Set ι)) :
    star (ambientRect u v i r (!r))*(T:Operator ι)*diagonalCreate u v i=0 := by
  cases r <;> simp only [diagonalCreate,mul_add,ambientRect_covariance,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,Bool.true_eq_false,and_false,and_true,ite_false,add_zero]

def diagonalBase : StarSubalgebra ℂ (Operator ι) :=
  Bicommutant.algebra (insert (diagonalCreate u v i+star (diagonalCreate u v i))
    (oldAlgebra u v (∅ : Set ι) : Set (Operator ι)))

theorem diagonal_base_annihilate (r : Bool) (T : diagonalBase u v i) :
    star (ambientRect u v i r (!r)) ((T:Operator ι) (vacuum u v))=0 :=
  GaussianExtension.annihilation_extension (oldAlgebra u v ∅) (diagonalCreate u v i)
    (diagonalCovariance u v) (diagonalCreate_covariance u v i)
    (ambientRect u v i r (!r)) (vacuum u v) (diagonalCreate_annihilate u v i)
    (fun a => ambientRect_annihilate u v i r (!r) a)
    (ambientRect_diagonal_orthogonal u v i r) T T.property

theorem diagonal_vertex_annihilate (r : Bool) (T : oldAlgebra u v (∅ : Set ι)) :
    star (diagonalCreate u v i) ((T:Operator ι) (vertex r (vacuum u v)))=0 := by
  have hh := diagonalCreate_annihilate u v i (T*vertexOld u v r)
  change star (diagonalCreate u v i) (((T:Operator ι)*vertex r : Operator ι) (vacuum u v))=0 at hh
  exact hh

theorem diagonal_residual_covariance (r : Bool) (T : diagonalBase u v i) :
    star (ambientRect u v i r (!r))*(T:Operator ι)*ambientRect u v i r (!r)=
      inner ℂ (vertex r (vacuum u v)) ((T:Operator ι) (vertex r (vacuum u v))) • vertex (!r) := by
  apply GaussianExtension.covariance_extension (oldAlgebra u v ∅) (diagonalCreate u v i)
    (diagonalCovariance u v) (diagonalCreate_covariance u v i)
    (ambientRect u v i r (!r)) (ambientRect u v i r (!r)) (vertex (!r))
    (vertex r (vacuum u v)) (vertex r (vacuum u v))
    (diagonal_vertex_annihilate u v i r) (diagonal_vertex_annihilate u v i r)
    (ambientRect_diagonal_orthogonal u v i r)
    (GaussianOrthogonal.symm (ambientRect_diagonal_orthogonal u v i r)) ?_ T T.property
  intro a
  rw [ambientRect_covariance,ite_eq_left ⟨rfl,rfl,rfl⟩]
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_right (vertex r)]
  change inner ℂ (vacuum u v) (((a:Operator ι)*vertex r : Operator ι) (vacuum u v))=
    inner ℂ (vacuum u v) ((star (vertex r)*((a:Operator ι)*vertex r) : Operator ι) (vacuum u v))
  rw [vertex_star,← mul_assoc,vertex_empty_vertex,ite_eq_left rfl]
end

section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

end

section
open FreeFock GaussianOrthogonal
variable {ι : Type u_3} [DecidableEq ι]

end

open FreeFock WeightedCornerIndex

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


