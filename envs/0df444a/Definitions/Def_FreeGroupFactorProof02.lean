-- Prove2me | Definitions.Def_FreeGroupFactorProof02
-- name    : FreeGroupFactorProof02
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T00:32:24.133812+00:00
-- url     : https://prove2.me/theorems/6d55c181-5368-480e-ae2b-11ab0255bd59
-- title:
--   Free group factors: supporting development, part 2 of 12
-- statement:
--   Part 2 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof01

set_option linter.all false

section
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15

noncomputable section
namespace FreeGroupFactorMain.FreeFock
open scoped ENNReal

variable {α : Type u_2} {β : Type u_3} [DecidableEq α] [DecidableEq β]

end FreeGroupFactorMain.FreeFock
namespace FreeGroupFactorMain.CoordinateProjection

variable {α : Type u_6} [DecidableEq α]
open scoped Classical

end FreeGroupFactorMain.CoordinateProjection

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_11} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_12}

variable [DecidableEq ι]

def vacuum (u v : ℝ) : H ι := (u:ℂ) • lp.single 2 ([],true) 1 +
  (v:ℂ) • lp.single 2 ([],false) 1

@[simp] theorem reverse_vacuum (u v : ℝ) : reverseOperator (vacuum u v : H ι)=vacuum u v := by
  simp only [vacuum,map_add,map_smul,reverseOperator_single,reverse_nil]

 theorem right_creation_commute (i j : ι) (r s : Bool) :
    Commute (creation i r) (rightCreation j s) := by
  change _*_=_*_
  apply operator_basis_ext
  intro w
  simp only [mul_apply_eq_comp,creation_single,rightCreation_single,appendPath]
  rfl

 theorem P_commute_rightCreation (i : ι) (r : Bool) :
    Commute (P : Operator ι) (rightCreation i r) := by
  apply CoordinateProjection.commute_embedding
  intro w
  change start (appendPath w i r)=true ↔ start w=true
  rw [start_appendPath]

 theorem rightP_commute_creation (i : ι) (r : Bool) :
    Commute (rightP : Operator ι) (creation i r) := by
  apply CoordinateProjection.commute_embedding
  intro w
  rfl

end

section
open FreeFock
variable {ι : Type u_13} [DecidableEq ι]

def vacuumMatrix (r s : Bool) : Operator ι :=
  InnerProductSpace.rankOne ℂ (lp.single 2 ([],s) 1) (lp.single 2 ([],r) 1)

@[simp] theorem vacuumMatrix_nil (r s e : Bool) (z : ℂ) :
    (vacuumMatrix r s : Operator ι) (lp.single 2 ([],e) z)=
      if r=e then lp.single 2 ([],s) z else 0 := by
  classical
  by_cases hr : r=e
  · subst e
    ext w
    simp [vacuumMatrix,InnerProductSpace.rankOne_apply,lp.inner_single_left,
      lp.single_apply,Pi.single_apply]
  · simp [vacuumMatrix,InnerProductSpace.rankOne_apply,lp.inner_single_left,
      lp.single_apply,hr]

@[simp] theorem vacuumMatrix_cons (r s e : Bool) (i : ι) (t : Bool)
    (w : List (ι×Bool)) (z : ℂ) :
    (vacuumMatrix r s : Operator ι) (lp.single 2 ((i,t)::w,e) z)=0 := by
  simp [vacuumMatrix,InnerProductSpace.rankOne_apply,lp.inner_single_left,lp.single_apply]

@[simp] theorem star_vacuumMatrix (r s : Bool) :
    star (vacuumMatrix r s : Operator ι)=vacuumMatrix s r := by
  simp only [vacuumMatrix,ContinuousLinearMap.star_eq_adjoint,InnerProductSpace.adjoint_rankOne]

 theorem annihilation_rightCreation (i j : ι) (r s : Bool) :
    star (creation i r)*rightCreation j s=
      rightCreation j s*star (creation i r)+(if i=j then vacuumMatrix r s else 0) := by
  apply operator_basis_ext
  rintro ⟨w,e⟩
  cases w with
  | nil =>
    simp only [mul_apply_eq_comp,add_apply,rightCreation_single,appendPath,List.nil_append,
      annihilation_single_cons,annihilation_single_nil,map_zero,zero_add]
    by_cases hij : i=j
    · subst j
      simp [vacuumMatrix_nil]
    · simp only [Prod.mk.injEq,hij,false_and,ite_false]
      rfl
  | cons a w =>
    rcases a with ⟨k,t⟩
    simp only [mul_apply_eq_comp,add_apply,rightCreation_single,appendPath,List.cons_append,
      annihilation_single_cons]
    have hm : (if i=j then (vacuumMatrix r s : Operator ι) else 0)
        (lp.single 2 ((k,t)::w,e) 1)=0 := by
      split_ifs <;> simp
    rw [hm,add_zero]
    by_cases h : (i,r)=(k,t)
    · simp only [h,ite_true,rightCreation_single,appendPath]
    · simp only [h,ite_false,map_zero]

def C (u v : ℝ) (i : ι) : Operator ι :=
  (u:ℂ) • creation i true+(v:ℂ) • creation i false

def rightC (u v : ℝ) (i : ι) : Operator ι :=
  (u:ℂ) • rightCreation i true+(v:ℂ) • rightCreation i false

theorem reverseConj_C (u v : ℝ) (i : ι) : reverseConj (C u v i)=rightC u v i := by
  simp only [C,rightC,map_add,map_smul,reverseConj_creation]

theorem S_eq (u v : ℝ) (i : ι) : S u v i=C u v i+star (C u v i) := rfl

def rightS (u v : ℝ) (i : ι) : Operator ι := rightC u v i+star (rightC u v i)

theorem reverseConj_S (u v : ℝ) (i : ι) : reverseConj (S u v i)=rightS u v i := by
  have hs : reverseConj (star (C u v i)) = star (reverseConj (C u v i)) :=
    reverseConj.map_star' (C u v i)
  simp only [S_eq,map_add,hs,reverseConj_C,rightS]

def vacuumCorrection (u v : ℝ) : Operator ι :=
  ((u:ℂ)^2) • vacuumMatrix true true +
  ((u:ℂ)*(v:ℂ)) • vacuumMatrix true false +
  ((u:ℂ)*(v:ℂ)) • vacuumMatrix false true +
  ((v:ℂ)^2) • vacuumMatrix false false

theorem vacuumCorrection_selfAdjoint (u v : ℝ) :
    IsSelfAdjoint (vacuumCorrection u v : Operator ι) := by
  change star (vacuumCorrection u v)=vacuumCorrection u v
  simp only [vacuumCorrection,star_add (R := Operator ι),star_smul,star_vacuumMatrix,Complex.star_def,
    map_pow,map_mul,Complex.conj_ofReal]
  abel

theorem C_commute_rightC (u v : ℝ) (i j : ι) : Commute (C u v i) (rightC u v j) := by
  unfold C rightC
  exact (((right_creation_commute i j true true).smul_left _).smul_right _ |>.add_right
    (((right_creation_commute i j true false).smul_left _).smul_right _)).add_left
      ((((right_creation_commute i j false true).smul_left _).smul_right _ |>.add_right
        (((right_creation_commute i j false false).smul_left _).smul_right _)))

theorem C_annihilation_rightC (u v : ℝ) (i j : ι) :
    star (C u v i)*rightC u v j=rightC u v j*star (C u v i)+
      (if i=j then vacuumCorrection u v else 0) := by
  simp only [C,rightC,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,
    add_mul,mul_add,smul_mul_assoc,mul_smul_comm,annihilation_rightCreation,smul_add,
    smul_smul]
  by_cases hij : i=j
  · simp only [hij,ite_true,vacuumCorrection]
    module
  · simp only [hij,ite_false,add_zero]
    module

 omit [DecidableEq ι] in
theorem add_star_commute_of_correction {A B D : Operator ι}
    (hAB : A*B=B*A) (h : star A*B=B*star A+D) (hD : star D=D) :
    Commute (A+star A) (B+star B) := by
  have habs : star A*star B=star B*star A := by
    have he := congrArg star hAB
    simpa only [star_mul] using he.symm
  have has : A*star B=star B*A-D := by
    have he := congrArg star h
    simp only [star_mul,star_star,star_add (R := Operator ι),hD] at he
    exact eq_sub_iff_add_eq.mpr he.symm
  change _*_=_*_
  rw [add_mul,mul_add,mul_add,hAB,has,h,habs]
  simp only [mul_add,add_mul]
  abel

 theorem S_commute_rightS (u v : ℝ) (i j : ι) :
    Commute (S u v i) (rightS u v j) := by
  rw [S_eq,rightS]
  apply add_star_commute_of_correction (C_commute_rightC u v i j).eq
    (C_annihilation_rightC u v i j)
  split_ifs
  · exact (vacuumCorrection_selfAdjoint u v).star_eq
  · exact star_zero (Operator ι)

 theorem rightP_projection : IsStarProjection (rightP : Operator ι) := CoordinateProjection.projection _

 theorem P_commute_rightS (u v : ℝ) (i : ι) : Commute (P : Operator ι) (rightS u v i) := by
  have hc : Commute (P : Operator ι) (rightC u v i) :=
    ((P_commute_rightCreation i true).smul_right _).add_right
      ((P_commute_rightCreation i false).smul_right _)
  have hs := hc.star_star
  rw [projection_P.isSelfAdjoint.star_eq] at hs
  exact hc.add_right hs

 theorem rightP_commute_S (u v : ℝ) (i : ι) : Commute (rightP : Operator ι) (S u v i) := by
  have hc : Commute (rightP : Operator ι) (C u v i) :=
    ((rightP_commute_creation i true).smul_right _).add_right
      ((rightP_commute_creation i false).smul_right _)
  have hs := hc.star_star
  rw [rightP_projection.isSelfAdjoint.star_eq] at hs
  exact hc.add_right hs

end

section
open FreeFock
open scoped ComplexConjugate
variable {ι : Type u_14} [DecidableEq ι]

def ambientCommutant (u v : ℝ) : StarSubalgebra ℂ (Operator ι) :=
  StarSubalgebra.centralizer ℂ (insert P (Set.range (S u v : ι → Operator ι)))

def Good (u v : ℝ) (A : Operator ι) : Prop :=
  A ∈ ambientAlgebra u v ∧ reverseConj A ∈ ambientCommutant u v ∧
    reverseConj A (vacuum u v)=star A (vacuum u v)

theorem good_one (u v : ℝ) : Good u v (1 : Operator ι) := by
  refine ⟨(ambientAlgebra u v).one_mem,?_,?_⟩
  · rw [map_one]; exact (ambientCommutant u v).one_mem
  · simp only [map_one,star_one]

theorem good_zero (u v : ℝ) : Good u v (0 : Operator ι) := by
  refine ⟨(ambientAlgebra u v).zero_mem,?_,?_⟩
  · rw [map_zero]; exact (ambientCommutant u v).zero_mem
  · simp only [map_zero,star_zero (Operator ι)]

theorem good_sub {u v : ℝ} {A B : Operator ι} (hA : Good u v A) (hB : Good u v B) :
    Good u v (A-B) := by
  refine ⟨(ambientAlgebra u v).sub_mem hA.1 hB.1,?_,?_⟩
  · rw [map_sub]; exact (ambientCommutant u v).sub_mem hA.2.1 hB.2.1
  · simp only [map_sub,sub_apply,star_sub (R := Operator ι),hA.2.2,hB.2.2]

theorem good_smul {u v : ℝ} {A : Operator ι} (c : ℝ) (hA : Good u v A) :
    Good u v ((c:ℂ) • A) := by
  refine ⟨(ambientAlgebra u v).smul_mem hA.1 _,?_,?_⟩
  · rw [map_smul]; exact (ambientCommutant u v).smul_mem hA.2.1 _
  · simp only [map_smul,_root_.smul_apply,star_smul,Complex.star_def,
      Complex.conj_ofReal,hA.2.2]

theorem good_mul {u v : ℝ} {A B : Operator ι} (hA : Good u v A) (hB : Good u v B) :
    Good u v (A*B) := by
  refine ⟨(ambientAlgebra u v).mul_mem hA.1 hB.1,?_,?_⟩
  · rw [map_mul]; exact (ambientCommutant u v).mul_mem hA.2.1 hB.2.1
  · have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp
      (star_mem hB.1) _ hA.2.1).1
    rw [map_mul,mul_apply_eq_comp,hB.2.2,← mul_apply_eq_comp,hc,
      mul_apply_eq_comp,hA.2.2,star_mul,mul_apply_eq_comp]

theorem reverseConj_vacuum (A : Operator ι) (u v : ℝ) :
    reverseConj A (vacuum u v)=reverseOperator (A (vacuum u v)) := by
  rw [reverseConj_apply,reverse_vacuum]

theorem rightP_mem_commutant (u v : ℝ) : (rightP : Operator ι) ∈ ambientCommutant u v := by
  rw [ambientCommutant,StarSubalgebra.mem_centralizer_iff]
  intro A hA
  rcases Set.mem_insert_iff.mp hA with hA | ⟨i,rfl⟩
  · subst A
    refine ⟨(CoordinateProjection.commute _ _).eq,?_⟩
    rw [projection_P.isSelfAdjoint.star_eq]
    exact (CoordinateProjection.commute _ _).eq
  · refine ⟨(rightP_commute_S u v i).eq.symm,?_⟩
    rw [(S_selfAdjoint u v i).star_eq]
    exact (rightP_commute_S u v i).eq.symm

theorem rightS_mem_commutant (u v : ℝ) (j : ι) : rightS u v j ∈ ambientCommutant u v := by
  rw [ambientCommutant,StarSubalgebra.mem_centralizer_iff]
  intro A hA
  rcases Set.mem_insert_iff.mp hA with hA | ⟨i,rfl⟩
  · subst A
    refine ⟨(P_commute_rightS u v j).eq,?_⟩
    rw [projection_P.isSelfAdjoint.star_eq]
    exact (P_commute_rightS u v j).eq
  · refine ⟨(S_commute_rightS u v i j).eq,?_⟩
    rw [(S_selfAdjoint u v i).star_eq]
    exact (S_commute_rightS u v i j).eq

theorem good_P (u v : ℝ) : Good u v (P : Operator ι) := by
  refine ⟨P_mem_ambient u v,?_,?_⟩
  · rw [reverseConj_P]; exact rightP_mem_commutant u v
  · rw [reverseConj_vacuum,projection_P.isSelfAdjoint.star_eq]
    simp only [vacuum,map_add,map_smul,P_nil_true,P_nil_false,smul_zero,add_zero,
      reverseOperator_single,reverse_nil]

theorem good_S (u v : ℝ) (i : ι) : Good u v (S u v i) := by
  refine ⟨S_mem_ambient u v i,?_,?_⟩
  · rw [reverseConj_S]; exact rightS_mem_commutant u v i
  · rw [reverseConj_vacuum,(S_selfAdjoint u v i).star_eq]
    simp only [vacuum,map_add,map_smul,S_nil,reverseOperator_single,reverse_cons,
      reverse_nil,appendPath,List.nil_append,smul_add,smul_smul]
    module

def vertex (r : Bool) : Operator ι := if r then P else 1-P

def weight (u v : ℝ) (r : Bool) : ℝ := if r then u else v

theorem good_vertex (u v : ℝ) (r : Bool) : Good u v (vertex r : Operator ι) := by
  cases r
  · exact good_sub (good_one u v) (good_P u v)
  · exact good_P u v

theorem weight_ne_zero {u v : ℝ} (hu : u≠0) (hv : v≠0) (r : Bool) : weight u v r ≠ 0 := by
  cases r <;> assumption

@[simp] theorem vertex_single (r : Bool) (w : Path ι) (z : ℂ) :
    (vertex r : Operator ι) (lp.single 2 w z)=if start w=r then lp.single 2 w z else 0 := by
  cases r <;> cases h : start w <;> simp [vertex,P_single,h]

 theorem vertex_S_nil (u v : ℝ) (i : ι) (r e : Bool) :
    (vertex r : Operator ι) (S u v i (lp.single 2 ([],e) 1))=
      ((weight u v r):ℂ) • lp.single 2 ([(i,r)],e) 1 := by
  rw [S_nil]
  simp only [map_add,map_smul]
  cases r <;> simp only [vertex_single,start,weight,Bool.false_eq_true,Bool.true_eq_false,
    ite_true,ite_false,smul_zero,zero_add,add_zero]

 theorem S_cons (u v : ℝ) (i j : ι) (s e : Bool) (w : List (ι×Bool)) :
    S u v i (lp.single 2 ((j,s)::w,e) 1)=
      (u:ℂ) • lp.single 2 ((i,true)::(j,s)::w,e) 1+
      (v:ℂ) • lp.single 2 ((i,false)::(j,s)::w,e) 1+
      (if i=j then ((weight u v s):ℂ) • lp.single 2 (w,e) 1 else 0) := by
  simp only [S,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,add_apply,
    _root_.smul_apply,creation_single,annihilation_single_cons,Prod.mk.injEq]
  cases s <;> by_cases hij : i=j <;> simp [hij,weight]

 theorem vertex_S_cons (u v : ℝ) (i j : ι) (r s e : Bool) (w : List (ι×Bool)) :
    (vertex r : Operator ι) (S u v i (lp.single 2 ((j,s)::w,e) 1))=
      ((weight u v r):ℂ) • lp.single 2 ((i,r)::(j,s)::w,e) 1+
      (if i=j then ((weight u v s):ℂ) • (vertex r : Operator ι) (lp.single 2 (w,e) 1) else 0) := by
  rw [S_cons,map_add,map_add]
  cases r <;> cases s <;> by_cases hij : i=j <;>
    simp only [hij,ite_true,ite_false,map_smul,map_zero,vertex_single,start,weight,
      Bool.false_eq_true,Bool.true_eq_false,smul_zero,zero_add,add_zero]

 theorem vertex_vacuum (u v : ℝ) (r : Bool) :
    (vertex r : Operator ι) (vacuum u v)=((weight u v r):ℂ) • lp.single 2 ([],r) 1 := by
  simp only [vacuum,map_add,map_smul]
  cases r <;> simp only [vertex_single,start,weight,Bool.false_eq_true,Bool.true_eq_false,
    ite_true,ite_false,smul_zero,zero_add,add_zero]

 theorem good_basis (u v : ℝ) (hu : u≠0) (hv : v≠0) (w : Path ι) :
    ∃ A : Operator ι, Good u v A ∧ A (vacuum u v)=lp.single 2 w 1 := by
  have h : ∀ l : List (ι×Bool),
      (∀ e, ∃ A : Operator ι, Good u v A ∧ A (vacuum u v)=lp.single 2 (l,e) 1) ∧
      (∀ i r e, ∃ A : Operator ι, Good u v A ∧ A (vacuum u v)=lp.single 2 ((i,r)::l,e) 1) := by
    intro l
    induction l with
    | nil =>
      have root (e : Bool) : ∃ A : Operator ι, Good u v A ∧
          A (vacuum u v)=lp.single 2 ([],e) 1 := by
        refine ⟨(((weight u v e)⁻¹:ℝ):ℂ) • vertex e,good_smul _ (good_vertex u v e),?_⟩
        rw [_root_.smul_apply,vertex_vacuum,smul_smul]
        simp only [Complex.ofReal_inv,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
          (weight_ne_zero hu hv e)),one_smul]
      refine ⟨root,?_⟩
      intro i r e
      obtain ⟨A,hA,he⟩ := root e
      refine ⟨(((weight u v r)⁻¹:ℝ):ℂ) • (vertex r*S u v i*A),
        good_smul _ (good_mul (good_mul (good_vertex u v r) (good_S u v i)) hA),?_⟩
      simp only [_root_.smul_apply,mul_apply_eq_comp,he,vertex_S_nil,smul_smul,
        Complex.ofReal_inv,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
          (weight_ne_zero hu hv r)),one_smul]
    | cons b l ih =>
      rcases b with ⟨j,s⟩
      refine ⟨ih.2 j s,?_⟩
      intro i r e
      obtain ⟨A,hA,heA⟩ := ih.2 j s e
      obtain ⟨B,hB,heB⟩ := ih.1 e
      let D : Operator ι := if i=j then ((weight u v s):ℂ) • (vertex r*B) else 0
      have hD : Good u v D := by
        dsimp [D]
        split_ifs
        · exact good_smul _ (good_mul (good_vertex u v r) hB)
        · exact good_zero u v
      have heD : D (vacuum u v)=if i=j then ((weight u v s):ℂ) •
          (vertex r : Operator ι) (lp.single 2 (l,e) 1) else 0 := by
        dsimp [D]
        split_ifs
        · change ((weight u v s):ℂ) • ((vertex r : Operator ι) (B (vacuum u v)))=_
          rw [heB]
          ext x
          simp only [lp.coeFn_smul,Pi.smul_apply]
          rfl
        · rfl
      refine ⟨(((weight u v r)⁻¹:ℝ):ℂ) • (vertex r*S u v i*A-D),
        good_smul _ (good_sub (good_mul (good_mul (good_vertex u v r) (good_S u v i)) hA) hD),?_⟩
      simp only [_root_.smul_apply,sub_apply,mul_apply_eq_comp,heA,vertex_S_cons,
        heD,add_sub_cancel_right,smul_smul,Complex.ofReal_inv,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_ne_zero hu hv r)),one_smul]
  exact (h w.1).1 w.2

end

open FreeFock
open scoped ComplexConjugate
variable {ι : Type u_15} [DecidableEq ι]

 theorem good_star {u v : ℝ} {A : Operator ι} (hA : Good u v A) :
    Good u v (star A) := by
  refine ⟨star_mem hA.1,?_,?_⟩
  · have hs : reverseConj (star A) = star (reverseConj A) := reverseConj.map_star' A
    rw [hs]; exact star_mem hA.2.1
  · rw [reverseConj_vacuum,star_star,← hA.2.2,reverseConj_vacuum,
      reverseOperator_involutive]

 theorem good_right_basis (u v : ℝ) (hu : u≠0) (hv : v≠0) (w : Path ι) :
    ∃ B : Operator ι, B ∈ ambientCommutant u v ∧
      B (vacuum u v)=lp.single 2 w 1 ∧ star B (vacuum u v)=lp.single 2 (reversePath w) 1 := by
  obtain ⟨A,hA,heA⟩ := good_basis u v hu hv (reversePath w)
  refine ⟨reverseConj A,hA.2.1,?_,?_⟩
  · rw [reverseConj_vacuum,heA,reverseOperator_single,reversePath_reverse]
  · have hs : reverseConj (star A) = star (reverseConj A) := reverseConj.map_star' A
    rw [← hs,(good_star hA).2.2,star_star,heA]

 theorem ambient_star_vector (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (T : ambientAlgebra (ι := ι) u v) (w : Path ι) :
    ((star (T : Operator ι)) (vacuum u v)) w=
      conj (((T : Operator ι) (vacuum u v)) (reversePath w)) := by
  obtain ⟨B,hB,heB,hesB⟩ := good_right_basis u v hu hv w
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ hB).1
  have hec := DFunLike.congr_fun hc (vacuum u v)
  simp only [mul_apply_eq_comp,heB] at hec
  have he : inner ℂ (lp.single 2 w 1) ((star (T : Operator ι)) (vacuum u v))=
      inner ℂ ((T : Operator ι) (vacuum u v)) (lp.single 2 (reversePath w) 1) := by
    calc
      _ = inner ℂ ((T : Operator ι) (lp.single 2 w 1)) (vacuum u v) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = inner ℂ (B ((T : Operator ι) (vacuum u v))) (vacuum u v) := by rw [hec]
      _ = inner ℂ ((T : Operator ι) (vacuum u v)) ((star B) (vacuum u v)) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = _ := by rw [hesB]
  simpa [lp.inner_single_left,lp.inner_single_right,RCLike.inner_apply] using he

 def vacuumTrace (u v : ℝ) (T : Operator ι) : ℂ := inner ℂ (vacuum u v) (T (vacuum u v))

 theorem ambient_trace_mul (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (S T : ambientAlgebra (ι := ι) u v) :
    vacuumTrace u v ((S : Operator ι)*(T : Operator ι))=
      vacuumTrace u v ((T : Operator ι)*(S : Operator ι)) := by
  have hf (A B : ambientAlgebra (ι := ι) u v) :
      vacuumTrace u v ((A : Operator ι)*(B : Operator ι))=
        ∑' w : Path ι, ((A : Operator ι) (vacuum u v)) (reversePath w)*
          ((B : Operator ι) (vacuum u v)) w := by
    unfold vacuumTrace
    rw [mul_apply_eq_comp,← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ ((star (A : Operator ι)) (vacuum u v)) ((B : Operator ι) (vacuum u v))=_
    rw [lp.inner_eq_tsum]
    congr 1
    funext w
    rw [ambient_star_vector u v hu hv]
    simp [RCLike.inner_apply,mul_comm]
  rw [hf,hf]
  let e : Path ι ≃ Path ι := ⟨reversePath,reversePath,
    reversePath_involutive,reversePath_involutive⟩
  have hs := e.tsum_eq (fun w : Path ι => ((T : Operator ι) (vacuum u v)) (reversePath w)*
    ((S : Operator ι) (vacuum u v)) w)
  change (∑' w : Path ι, ((T : Operator ι) (vacuum u v)) (reversePath (reversePath w))*
    ((S : Operator ι) (vacuum u v)) (reversePath w))=_ at hs
  simpa only [reversePath_reverse,mul_comm] using hs

 theorem vacuumTrace_one (u v : ℝ) : vacuumTrace u v (1 : Operator ι)=((u^2+v^2:ℝ):ℂ) := by
  simp only [vacuumTrace,one_apply_eq_self,vacuum,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,lp.inner_single_left]
  simp [lp.single_apply,RCLike.inner_apply,pow_two]

 theorem vacuumTrace_P (u v : ℝ) : vacuumTrace u v (P : Operator ι)=((u^2:ℝ):ℂ) := by
  simp only [vacuumTrace,vacuum,map_add,map_smul,P_nil_true,P_nil_false,smul_zero,
    add_zero,inner_add_left,inner_smul_left,inner_smul_right,lp.inner_single_left]
  simp [lp.single_apply,RCLike.inner_apply,pow_two]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.Amplification.Polar

section

variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev Operator (E : Type u_2) [NormedAddCommGroup E] [InnerProductSpace ℂ E] := E →L[ℂ] E

def modulus (T : Operator E) : Operator E := CFC.sqrt (star T*T)

theorem modulus_star (T : Operator E) : star (modulus T) = modulus T :=
  (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq

theorem modulus_sq (T : Operator E) : modulus T*modulus T = star T*T :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T)

theorem modulus_norm (T : Operator E) (x : E) : ‖modulus T x‖ = ‖T x‖ := by
  have hinner : inner ℂ (modulus T x) (modulus T x) = inner ℂ (T x) (T x) := by
    calc
      _ = inner ℂ ((star (modulus T)*modulus T) x) x := by
        exact (ContinuousLinearMap.adjoint_inner_left (modulus T) x (modulus T x)).symm
      _ = inner ℂ ((star T*T) x) x := by rw [modulus_star,modulus_sq]
      _ = _ := ContinuousLinearMap.adjoint_inner_left T x (T x)
  have hs : ‖modulus T x‖^2 = ‖T x‖^2 := by
    simpa only [inner_self_eq_norm_sq] using congrArg (RCLike.re : ℂ → ℝ) hinner
  nlinarith [norm_nonneg (modulus T x),norm_nonneg (T x)]

def closedRange (T : Operator E) : Submodule ℂ E := T.toLinearMap.range.topologicalClosure

instance closedRange_complete (T : Operator E) : CompleteSpace (closedRange T) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def intoClosedRange (T : Operator E) : E →L[ℂ] closedRange T :=
  T.codRestrict (closedRange T) (fun x => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))

omit [CompleteSpace E] in
theorem intoClosedRange_dense (T : Operator E) : DenseRange (intoClosedRange T) := by
  rw [DenseRange,Subtype.dense_iff,← Set.range_comp]
  change (closedRange T : Set E) ⊆ closure (Set.range (fun x : E => T x))
  rw [closedRange,Submodule.topologicalClosure_coe]
  exact Set.Subset.rfl

def polarSpatial (T : Operator E) : closedRange (modulus T) ≃ₗᵢ[ℂ] closedRange T :=
  (LinearEquiv.refl ℂ E).extendOfIsometry (intoClosedRange (modulus T)).toLinearMap
    (intoClosedRange T).toLinearMap (intoClosedRange_dense _) (intoClosedRange_dense _)
    (fun x => (modulus_norm T x).symm)

theorem polarSpatial_modulus (T : Operator E) (x : E) :
    polarSpatial T (intoClosedRange (modulus T) x) = intoClosedRange T x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

def partialIsometry (T : Operator E) : Operator E :=
  (closedRange T).subtypeL.comp ((polarSpatial T).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (closedRange (modulus T)).orthogonalProjectionOnto)

theorem partialIsometry_factorization (T : Operator E) : partialIsometry T * modulus T = T := by
  apply ContinuousLinearMap.ext
  intro x
  change ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto (modulus T x)) : E) = T x
  have he : (closedRange (modulus T)).orthogonalProjectionOnto (modulus T x) = intoClosedRange (modulus T) x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (intoClosedRange (modulus T) x)
  rw [he,polarSpatial_modulus]
  rfl

theorem partialIsometry_on_range (T : Operator E) (x : closedRange (modulus T)) :
    partialIsometry T x = (polarSpatial T x : E) := by
  change ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto x) : E) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem partialIsometry_inner (T : Operator E) (x y : E) :
    inner ℂ (partialIsometry T x) (partialIsometry T y) =
      inner ℂ ((closedRange (modulus T)).starProjection x) y := by
  change inner ℂ (polarSpatial T ((closedRange (modulus T)).orthogonalProjectionOnto x))
      (polarSpatial T ((closedRange (modulus T)).orthogonalProjectionOnto y)) = _
  rw [(polarSpatial T).inner_map_map]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

theorem partialIsometry_initial (T : Operator E) :
    star (partialIsometry T)*partialIsometry T = (closedRange (modulus T)).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left,partialIsometry_inner]

theorem partialIsometry_adjoint (T : Operator E) (x : E) :
    star (partialIsometry T) x =
      ((polarSpatial T).symm ((closedRange T).orthogonalProjectionOnto x) : E) := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ x ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto y) : E) = _
  rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto y)) x]
  rw [← (polarSpatial T).symm.inner_map_map,(polarSpatial T).symm_apply_apply]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

theorem partialIsometry_final (T : Operator E) :
    partialIsometry T*star (partialIsometry T) = (closedRange T).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp,partialIsometry_adjoint,partialIsometry_on_range,
    (polarSpatial T).apply_symm_apply]
  rfl

end
section
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem modulus_commute {T S : Operator E} (h : Commute T S) (hstar : Commute (star T) S) :
    Commute (modulus T) S :=
  (hstar.mul_left h).cfcₙ_nnreal NNReal.sqrt

omit [CompleteSpace E] in
 theorem closedRange_invariant {T S : Operator E} (h : Commute T S) :
    ∀ x ∈ closedRange T, S x ∈ closedRange T := by
  have hi : T.toLinearMap.range ∈ Module.End.invtSubmodule S := by
    rw [Module.End.mem_invtSubmodule_iff_map_le]
    rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    refine ⟨S x,?_⟩
    exact DFunLike.congr_fun h.eq x
  exact Submodule.topologicalClosure_mem_invtSubmodule hi

 theorem orthogonal_invariant (K : Submodule ℂ E) (S : Operator E)
    (h : ∀ x ∈ K, star S x ∈ K) : ∀ x ∈ Kᗮ, S x ∈ Kᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hx (star S y) (h y hy)

 theorem starProjection_commute (K : Submodule ℂ E) [K.HasOrthogonalProjection] (S : Operator E)
    (h : ∀ x ∈ K, S x ∈ K) (hstar : ∀ x ∈ K, star S x ∈ K) :
    Commute K.starProjection S := by
  apply ContinuousLinearMap.ext
  intro x
  change K.starProjection (S x) = S (K.starProjection x)
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact h _ (K.orthogonalProjectionOnto x).property
  · rw [← map_sub]
    exact orthogonal_invariant K S hstar _ (K.sub_starProjection_mem_orthogonal x)

 theorem partialIsometry_projection (T : Operator E) :
    partialIsometry T * (closedRange (modulus T)).starProjection = partialIsometry T := by
  apply ContinuousLinearMap.ext
  intro x
  change ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto
    ((closedRange (modulus T)).orthogonalProjectionOnto x)) : E) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

 theorem partialIsometry_commute {T S : Operator E}
    (h : Commute T S) (hstar : Commute (star T) S)
    (hs : Commute T (star S)) (hstars : Commute (star T) (star S)) :
    Commute (partialIsometry T) S := by
  have hm := modulus_commute h hstar
  have hms := modulus_commute hs hstars
  have hp := starProjection_commute (closedRange (modulus T)) S
    (closedRange_invariant hm) (closedRange_invariant hms)
  have he : Set.EqOn (partialIsometry T * S) (S * partialIsometry T)
      (closedRange (modulus T) : Set E) := by
    apply Set.EqOn.closure _ (partialIsometry T * S).continuous (S * partialIsometry T).continuous
    rintro _ ⟨x,rfl⟩
    change partialIsometry T (S (modulus T x)) = S (partialIsometry T (modulus T x))
    have hmx : modulus T (S x) = S (modulus T x) := DFunLike.congr_fun hm.eq x
    rw [← hmx]
    change (partialIsometry T * modulus T) (S x) = S ((partialIsometry T * modulus T) x)
    rw [partialIsometry_factorization]
    exact DFunLike.congr_fun h.eq x
  apply ContinuousLinearMap.ext
  intro x
  have hx := he ((closedRange (modulus T)).orthogonalProjectionOnto x).property
  change (partialIsometry T * S) x = (S * partialIsometry T) x
  calc
    _ = (partialIsometry T * (closedRange (modulus T)).starProjection * S) x := by
      rw [partialIsometry_projection]
    _ = (partialIsometry T * S * (closedRange (modulus T)).starProjection) x := by
      rw [mul_assoc,hp.eq,← mul_assoc]
    _ = (S * partialIsometry T * (closedRange (modulus T)).starProjection) x := hx
    _ = _ := by rw [mul_assoc,partialIsometry_projection]

end
section
variable {E : Type u_4} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem partialIsometry_mem_centralizer (s : Set (Operator E)) {T : Operator E}
    (hT : T ∈ StarSubalgebra.centralizer ℂ s) :
    partialIsometry T ∈ StarSubalgebra.centralizer ℂ s := by
  have ht := (StarSubalgebra.mem_centralizer_iff ℂ).mp hT
  have hts := (StarSubalgebra.mem_centralizer_iff ℂ).mp
    (star_mem hT)
  rw [StarSubalgebra.mem_centralizer_iff]
  intro S hS
  have h₁ : Commute T S := (ht S hS).1.symm
  have h₂ : Commute (star T) S := (hts S hS).1.symm
  have h₃ : Commute T (star S) := (ht S hS).2.symm
  have h₄ : Commute (star T) (star S) := (hts S hS).2.symm
  exact ⟨(partialIsometry_commute h₁ h₂ h₃ h₄).eq.symm,
    (partialIsometry_commute h₃ h₄ (by simpa using h₁) (by simpa using h₂)).eq.symm⟩

 theorem closedRange_eq_orthogonal_ker (T : Operator E) :
    closedRange T = (star T).kerᗮ := by
  simpa only [closedRange,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint]
    using (ContinuousLinearMap.orthogonal_ker (star T)).symm

 theorem modulus_ker (T : Operator E) : (modulus T).ker = T.ker := by
  ext x
  change modulus T x = 0 ↔ T x = 0
  calc
    _ ↔ ‖modulus T x‖ = 0 := norm_eq_zero.symm
    _ ↔ ‖T x‖ = 0 := by rw [modulus_norm]
    _ ↔ _ := norm_eq_zero

 theorem modulus_closedRange (T : Operator E) : closedRange (modulus T) = T.kerᗮ := by
  rw [closedRange_eq_orthogonal_ker,modulus_star,modulus_ker]

end
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
 theorem fixed_on_closedRange {q T : Operator E} (h : q*T=T) (x : closedRange T) : q x=x := by
  have he : Set.EqOn q id (Set.range T) := by
    rintro _ ⟨y,rfl⟩
    exact DFunLike.congr_fun h y
  have hc := he.closure q.continuous continuous_id
  apply hc
  have hx := x.property
  change (x : E) ∈ (↑(T.toLinearMap.range.topologicalClosure) : Set E) at hx
  rw [Submodule.topologicalClosure_coe] at hx
  exact hx

 theorem partialIsometry_left_support {q T : Operator E} (h : q*T=T) :
    q*partialIsometry T=partialIsometry T := by
  apply ContinuousLinearMap.ext
  intro x
  exact fixed_on_closedRange h ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto x))

 theorem modulus_right_support {p T : Operator E} (h : T*p=T) : modulus T*p=modulus T := by
  apply ContinuousLinearMap.ext
  intro x
  have hz : T (p x-x)=0 := by rw [map_sub]; exact sub_eq_zero.mpr (DFunLike.congr_fun h x)
  have hn : ‖modulus T (p x-x)‖=0 := by rw [modulus_norm,hz,norm_zero]
  change modulus T (p x)=modulus T x
  simpa only [map_sub,sub_eq_zero] using norm_eq_zero.mp hn

 theorem partialIsometry_right_support {p T : Operator E} (hp : IsSelfAdjoint p) (h : T*p=T) :
    partialIsometry T*p=partialIsometry T := by
  have hm := congrArg star (modulus_right_support h)
  simp only [star_mul,hp.star_eq,modulus_star] at hm
  have ha : p*star (partialIsometry T)=star (partialIsometry T) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [mul_apply_eq_comp,partialIsometry_adjoint]
    exact fixed_on_closedRange hm ((polarSpatial T).symm ((closedRange T).orthogonalProjectionOnto x))
  have he := congrArg star ha
  simpa only [star_mul,star_star,hp.star_eq] using he

 theorem partialIsometry_partial (T : Operator E) :
    partialIsometry T*star (partialIsometry T)*partialIsometry T=partialIsometry T := by
  rw [partialIsometry_final]
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto x)).property

end FreeGroupFactorMain.Amplification.Polar

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
open Amplification.Polar
variable {ι : Type u_6} [DecidableEq ι]

 theorem weighted_creation_norm (i : ι) (r : Bool) (ξ : H ι) :
    ‖creation i r ξ‖=‖ξ‖ := (hilbertEmbedding (prepend i r)).norm_map ξ

 theorem weighted_creation_opNorm_le (i : ι) (r : Bool) : ‖creation i r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ξ
  rw [weighted_creation_norm,one_mul]

 theorem P_creation_true (i : ι) : (P : Operator ι)*creation i true=creation i true := by
  apply operator_basis_ext
  rintro ⟨w,e⟩
  simp only [mul_apply_eq_comp,creation_single,P_cons,ite_true]

 def offDiagonal (u v : ℝ) (i : ι) : Operator ι := P*S u v i*(1-P)

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.Amplification.Polar
variable {E : Type u_7} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.Polar
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
open Amplification.Polar
variable {ι : Type u_8} [DecidableEq ι]

end
open FreeFock
open scoped ENNReal
open Amplification.Polar
variable {ι : Type u_9} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


