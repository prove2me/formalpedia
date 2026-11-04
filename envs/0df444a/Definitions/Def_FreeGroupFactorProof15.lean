-- Prove2me | Definitions.Def_FreeGroupFactorProof15
-- name    : FreeGroupFactorProof15
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T02:35:14.143316+00:00
-- url     : https://prove2.me/theorems/23e4cf11-2fdc-4166-bdec-81010e17a3f0
-- title:
--   Free group factors: supporting development, part 15
-- statement:
--   Part 15 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof14

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

variable (u v : ℝ) (i : ι)

end

section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

end

section
open FreeFock GaussianOrthogonal
variable {ι : Type u_3} [DecidableEq ι]

theorem diagonal_residual_trace (u v : ℝ) (i : ι) (r : Bool) (T : diagonalBase u v i) :
    star (ambientRect u v i r (!r))*(T:Operator ι)*ambientRect u v i r (!r)=
      vacuumTrace u v ((T:Operator ι)*vertex r) • vertex (!r) := by
  rw [diagonal_residual_covariance]
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_right (vertex r : Operator ι)]
  change inner ℂ (vacuum u v) ((star (vertex r)*((T:Operator ι)*vertex r) : Operator ι) (vacuum u v))=_
  rw [vertex_star,← mul_assoc,(diagonalBase_vertex_commute u v i r T).eq,mul_assoc,
    vertex_mul_vertex,ite_eq_left rfl]
  rfl

theorem diagonal_residual_orthogonal (u v : ℝ) (i : ι) (r s : Bool) (hrs : r≠s)
    (T : diagonalBase u v i) :
    star (ambientRect u v i r (!r))*(T:Operator ι)*ambientRect u v i s (!s)=0 := by
  apply GaussianExtension.orthogonality_extension (oldAlgebra u v ∅) (diagonalCreate u v i)
    (diagonalCovariance u v) (diagonalCreate_covariance u v i)
    (ambientRect u v i r (!r)) (ambientRect u v i s (!s))
    (ambientRect_diagonal_orthogonal u v i r)
    (GaussianOrthogonal.symm (ambientRect_diagonal_orthogonal u v i s)) ?_ T T.property
  intro a
  rw [ambientRect_covariance,ite_eq_right (by simp only [hrs,and_false,false_and,not_false_eq_true])]

theorem rect_paired_eq (u v : ℝ) (i : ι) (r s : Bool) :
    ambientRect u v i r s+star (ambientRect u v i s r)=vertex r*S u v i*vertex s := by
  change _=vertex r*(C u v i+star (C u v i))*vertex s
  simp only [ambientRect,star_mul,vertex_star,mul_add,add_mul,mul_assoc]

theorem vertex_mem_old (u v : ℝ) (J : Set ι) (r : Bool) : (vertex r : Operator ι)∈oldAlgebra u v J := by
  cases r
  · exact sub_mem (one_mem _) (P_mem_old u v J)
  · exact P_mem_old u v J

theorem oldAlgebra_mono (u v : ℝ) {J K : Set ι} (h : J⊆K) : oldAlgebra u v J≤oldAlgebra u v K := by
  apply StarSubalgebra.centralizer_le
  apply StarSubalgebra.centralizer_le
  exact Set.insert_subset_insert (Set.image_mono h)

theorem diagonalBase_le_singleton (u v : ℝ) (i : ι) : diagonalBase u v i≤oldAlgebra u v {i} := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · rw [← diagonalSelf_eq,diagonalSelf,diagonalLeg,diagonalLeg,rect_paired_eq,rect_paired_eq]
    exact add_mem (mul_mem (mul_mem (vertex_mem_old u v _ _) (S_mem_old u v _ i rfl)) (vertex_mem_old u v _ _))
      (mul_mem (mul_mem (vertex_mem_old u v _ _) (S_mem_old u v _ i rfl)) (vertex_mem_old u v _ _))
  · exact oldAlgebra_mono u v (Set.empty_subset {i}) hT

theorem diagonalBase_le_ambient (u v : ℝ) (i : ι) : diagonalBase u v i≤ambientAlgebra u v :=
  (diagonalBase_le_singleton u v i).trans (by
    apply StarSubalgebra.centralizer_le
    apply StarSubalgebra.centralizer_le
    exact Set.insert_subset_insert (by rintro _ ⟨j,_,rfl⟩;exact Set.mem_range_self j))

theorem ambient_C_rect_empty (u v : ℝ) (i n : ι) (hn : n≠i) (r s : Bool)
    (T : oldAlgebra u v (∅:Set ι)) : star (C u v n)*(T:Operator ι)*ambientRect u v i r s=0 := by
  have hh := fresh_C_contraction u v ∅ n i (by simp) (by simp) (T*vertexOld u v r)
  rw [ite_eq_right hn] at hh
  change star (C u v n)*((T:Operator ι)*vertex r)*C u v i=0 at hh
  calc
    _ = (star (C u v n)*((T:Operator ι)*vertex r)*C u v i)*vertex s := by simp only [ambientRect,mul_assoc]
    _ = 0 := by rw [hh,zero_mul]

theorem ambient_C_diagonal_empty (u v : ℝ) (i n : ι) (hn : n≠i)
    (T : oldAlgebra u v (∅:Set ι)) : star (C u v n)*(T:Operator ι)*diagonalCreate u v i=0 := by
  rw [diagonalCreate,mul_add,ambient_C_rect_empty u v i n hn,ambient_C_rect_empty u v i n hn,add_zero]

theorem ambient_C_residual (u v : ℝ) (i n : ι) (hn : n≠i) (r : Bool)
    (T : diagonalBase u v i) : star (C u v n)*(T:Operator ι)*ambientRect u v i r (!r)=0 := by
  exact GaussianExtension.orthogonality_extension (oldAlgebra u v ∅) (diagonalCreate u v i)
    (diagonalCovariance u v) (diagonalCreate_covariance u v i) (C u v n) (ambientRect u v i r (!r))
    (ambient_C_diagonal_empty u v i n hn)
    (GaussianOrthogonal.symm (ambientRect_diagonal_orthogonal u v i r))
    (ambient_C_rect_empty u v i n hn r (!r)) T T.property
end

open FreeFock WeightedCornerIndex

def residualIndex (b : Bool) : WeightedCornerIndex.Index := .inr (.inl 0,b)
def residualSlot : WeightedCornerIndex.Index → Option Bool
  | .inr (.inl 0,b) => some b
  | _ => none

theorem residualSlot_some (i : WeightedCornerIndex.Index) (b : Bool) : residualSlot i=some b ↔ i=residualIndex b := by
  rcases i with i|⟨(n|k),c⟩
  · simp [residualSlot,residualIndex]
  · cases n <;> simp [residualSlot,residualIndex]
  · simp [residualSlot,residualIndex]

theorem residualSlot_flip (i : WeightedCornerIndex.Index) :
    residualSlot (CircularRotation.flip i)=(residualSlot i).map Bool.not := by
  rcases i with i|⟨(n|k),c⟩
  · rfl
  · cases n <;> rfl
  · rfl

def diagonalVertex (u v : ℝ) (b : Bool) : diagonalBase u v (0:ℕ) :=
  ⟨vertex b,by cases b;exact sub_mem (one_mem _) (P_mem_diagonalBase u v 0);exact P_mem_diagonalBase u v 0⟩

def ambientLeft (u v : ℝ) (i : WeightedCornerIndex.Index) : diagonalBase u v (0:ℕ) :=
  (residualSlot i).elim 0 (diagonalVertex u v)
def ambientRight (u v : ℝ) (i : WeightedCornerIndex.Index) : diagonalBase u v (0:ℕ) :=
  (residualSlot i).elim 0 (fun b => diagonalVertex u v (!b))
def ambientExtra (u v : ℝ) (i : WeightedCornerIndex.Index) : Operator ℕ :=
  (residualSlot i).elim 0 (fun b => ambientRect u v 0 b (!b))

theorem diagonalVertex_projection (u v : ℝ) (b : Bool) : IsStarProjection (diagonalVertex u v b) := by
  constructor
  · apply Subtype.ext;exact (vertex_projection b).isIdempotentElem.eq
  · apply Subtype.ext;exact vertex_star b

theorem ambientLeft_projection (u v : ℝ) (i : WeightedCornerIndex.Index) : IsStarProjection (ambientLeft u v i) := by
  unfold ambientLeft
  cases residualSlot i
  · exact IsStarProjection.zero _
  · exact diagonalVertex_projection u v _

theorem ambientRight_projection (u v : ℝ) (i : WeightedCornerIndex.Index) : IsStarProjection (ambientRight u v i) := by
  unfold ambientRight
  cases residualSlot i
  · exact IsStarProjection.zero _
  · exact diagonalVertex_projection u v _

theorem ambientLeft_flip (u v : ℝ) (i : WeightedCornerIndex.Index) :
    ambientLeft u v (CircularRotation.flip i)=ambientRight u v i := by
  simp only [ambientLeft,ambientRight,residualSlot_flip]
  cases residualSlot i <;> rfl

theorem ambientRight_flip (u v : ℝ) (i : WeightedCornerIndex.Index) :
    ambientRight u v (CircularRotation.flip i)=ambientLeft u v i := by
  simp only [ambientLeft,ambientRight,residualSlot_flip]
  cases residualSlot i with
  | none => rfl
  | some b => cases b <;> rfl

theorem ambientExtra_supported (u v : ℝ) (i : WeightedCornerIndex.Index) :
    (ambientLeft u v i:Operator ℕ)*ambientExtra u v i*(ambientRight u v i:Operator ℕ)=ambientExtra u v i := by
  unfold ambientLeft ambientRight ambientExtra
  cases residualSlot i with
  | none => simp
  | some b =>
    change vertex b*ambientRect u v 0 b (!b)*vertex (!b)=_
    rw [ambientRect_left,ambientRect_right]
    rfl

def diagonalTrace (u v : ℝ) : diagonalBase u v (0:ℕ) →ₗ[ℂ] ℂ where
  toFun a := vacuumTrace u v (a:Operator ℕ)
  map_add' a b := by simp only [vacuumTrace,AddMemClass.coe_add,add_apply,inner_add_right]
  map_smul' c a := by simp only [vacuumTrace,SetLike.val_smul,smul_apply,inner_smul_right,RingHom.id_apply,smul_eq_mul]

theorem diagonalTrace_tracial (u v : ℝ) (hu : u≠0) (hv : v≠0) (a b : diagonalBase u v (0:ℕ)) :
    diagonalTrace u v (a*b)=diagonalTrace u v (b*a) :=
  ambient_trace_mul u v hu hv ⟨(a:Operator ℕ),diagonalBase_le_ambient u v 0 a.property⟩ ⟨(b:Operator ℕ),diagonalBase_le_ambient u v 0 b.property⟩

theorem ambientExtra_covariance (u v : ℝ) (i j : WeightedCornerIndex.Index) (a : diagonalBase u v (0:ℕ)) :
    star (ambientExtra u v i)*(a:Operator ℕ)*ambientExtra u v j=
      if i=j then diagonalTrace u v (a*ambientLeft u v i) • (ambientRight u v i:Operator ℕ) else 0 := by
  cases hi : residualSlot i with
  | none => simp [ambientExtra,ambientLeft,ambientRight,hi,star_zero (R := Operator ℕ),
      zero_smul ℂ (A := Operator ℕ)]
  | some b =>
    cases hj : residualSlot j with
    | none =>
      have hij : i≠j := by intro h;subst j;rw [hi] at hj;cases hj
      simp [ambientExtra,hj,hij]
    | some c =>
      have hei := (residualSlot_some i b).mp hi
      have hej := (residualSlot_some j c).mp hj
      have he : i=j ↔ b=c := by rw [hei,hej];simp [residualIndex]
      simp only [ambientExtra,ambientLeft,ambientRight,hi,hj,Option.elim_some,he]
      by_cases hbc : b=c
      · subst c
        rw [ite_eq_left rfl,diagonal_residual_trace]
        rfl
      · rw [ite_eq_right hbc]
        exact diagonal_residual_orthogonal u v 0 b c hbc a

def ambientRaw (u v : ℝ) (i : WeightedCornerIndex.Index) (n : ℕ) : Operator ℕ := C u v (reservoirCode (i,n)+1)

theorem ambientRaw_covariance (u v : ℝ) (i j : WeightedCornerIndex.Index) (n m : ℕ)
    (a : diagonalBase u v (0:ℕ)) :
    star (ambientRaw u v i n)*(a:Operator ℕ)*ambientRaw u v j m=
      if i=j ∧ n=m then diagonalTrace u v a • (1:Operator ℕ) else 0 := by
  have hh := fresh_C_contraction u v {0} (reservoirCode (i,n)+1) (reservoirCode (j,m)+1)
    (by simp) (by simp) ⟨a,diagonalBase_le_singleton u v 0 a.property⟩
  change star (C u v (reservoirCode (i,n)+1))*(a:Operator ℕ)*C u v (reservoirCode (j,m)+1)=
    if i=j ∧ n=m then vacuumTrace u v (a:Operator ℕ) • (1:Operator ℕ) else 0
  simpa only [Nat.add_right_cancel_iff,reservoirCode.injective.eq_iff,Prod.mk.injEq] using hh

theorem ambientRaw_extra (u v : ℝ) (i j : WeightedCornerIndex.Index) (n : ℕ)
    (a : diagonalBase u v (0:ℕ)) : star (ambientRaw u v i n)*(a:Operator ℕ)*ambientExtra u v j=0 := by
  unfold ambientExtra
  cases residualSlot j with
  | none => exact mul_zero _
  | some b => exact ambient_C_residual u v 0 _ (by omega) b a

def ambientAbsorption (u v : ℝ) (hu : u≠0) (hv : v≠0) :
    PairedAbsorption.Input (diagonalBase u v (0:ℕ)) SelfIndex PairIndex where
  τ := diagonalTrace u v
  tracial := diagonalTrace_tracial u v hu hv
  p := ambientLeft u v
  q := ambientRight u v
  projection := ambientLeft_projection u v
  projectionq := ambientRight_projection u v
  pq := ambientLeft_flip u v
  qp := ambientRight_flip u v
  raw := ambientRaw u v
  extra := ambientExtra u v
  supported := ambientExtra_supported u v
  raw_cov := ambientRaw_covariance u v
  extra_cov := ambientExtra_covariance u v
  raw_extra := ambientRaw_extra u v
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock MeasureTheory CyclicSpectral
variable {ι : Type u_1} [DecidableEq ι]

theorem vacuum_norm_one (u v : ℝ) (hunit : u^2+v^2=1) : ‖(vacuum u v:H ι)‖=1 := by
  have hh := vacuumTrace_one (ι := ι) u v
  rw [hunit,Complex.ofReal_one] at hh
  change inner ℂ (vacuum u v:H ι) (vacuum u v)=1 at hh
  have hr := congrArg Complex.re hh
  rw [inner_self_eq_norm_sq_to_K] at hr
  have hr : ‖(vacuum u v:H ι)‖^2=1 := by exact_mod_cast hr
  nlinarith [norm_nonneg (vacuum u v:H ι)]

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

section
open FreeFock WeightedCornerIndex GaussianRecognition CyclicSpectral

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

section
open FreeFock CyclicSpectral GaussianRecognition Filter Topology
open scoped ENNReal
variable {ι : Type u_2} [DecidableEq ι]

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

section
open FreeFock WeightedCornerIndex GaussianRecognition
variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

open FreeFock GaussianRecognition CyclicSpectral
variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


