-- Prove2me | Definitions.Def_FreeGroupFactorProof03
-- name    : FreeGroupFactorProof03
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T00:35:05.344244+00:00
-- url     : https://prove2.me/theorems/478e7deb-ae00-461f-910b-38a07b10db60
-- title:
--   Free group factors: supporting development, part 3 of 12
-- statement:
--   Part 3 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof02

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.Amplification.Polar

section

variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end
section
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end
section
variable {E : Type u_4} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.Polar

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
open Amplification.Polar
variable {ι : Type u_6} [DecidableEq ι]

 theorem offDiagonal_formula (u v : ℝ) (i : ι) :
    offDiagonal u v i=(u:ℂ) • (creation i true*(1-P)) +
      (v:ℂ) • (P*star (creation i false)) := by
  have ht : star (creation i true)*(1-P : Operator ι)=0 := by
    have hh := congrArg star (P_creation_true i)
    simp only [star_mul,projection_P.isSelfAdjoint.star_eq] at hh
    rw [mul_sub,mul_one,hh,sub_self]
  have hf : star (creation i false)*(1-P : Operator ι)=star (creation i false) := by
    have hh := congrArg star (P_creation_false i)
    simp only [star_mul,projection_P.isSelfAdjoint.star_eq,star_zero (Operator ι)] at hh
    rw [mul_sub,mul_one,hh,sub_zero]
  simp only [offDiagonal,S,mul_add,add_mul,star_add (R := Operator ι),star_smul,Complex.star_def,
    Complex.conj_ofReal,mul_smul_comm,smul_mul_assoc,P_creation_true,P_creation_false,
    mul_assoc,ht,hf,mul_zero,zero_mul,smul_zero,add_zero,zero_add]

 theorem offDiagonal_right (u v : ℝ) (i : ι) :
    offDiagonal u v i*(1-P)=offDiagonal u v i := by
  unfold offDiagonal
  simp only [mul_assoc,projection_P.one_sub.isIdempotentElem.eq]

 theorem offDiagonal_left (u v : ℝ) (i : ι) :
    P*offDiagonal u v i=offDiagonal u v i := by
  rw [offDiagonal,← mul_assoc,← mul_assoc,projection_P.isIdempotentElem.eq]

 theorem offDiagonal_lower_bound (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (i : ι) (ξ : H ι) (hξ : (1-P : Operator ι) ξ=ξ) :
    (u-v)*‖ξ‖ ≤ ‖offDiagonal u v i ξ‖ := by
  have hP : ‖(P : Operator ι)‖ ≤ 1 := CoordinateProjection.norm_proj_le _
  have hc : ‖star (creation i false) ξ‖ ≤ ‖ξ‖ := by
    calc
      _ ≤ ‖star (creation i false)‖*‖ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1*‖ξ‖ := mul_le_mul_of_nonneg_right (by simpa only [ContinuousLinearMap.star_eq_adjoint,LinearIsometryEquiv.norm_map] using weighted_creation_opNorm_le i false) (norm_nonneg _)
      _ = _ := one_mul _
  have hpc : ‖P (star (creation i false) ξ)‖ ≤ ‖ξ‖ := by
    calc
      _ ≤ ‖(P : Operator ι)‖*‖star (creation i false) ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1*‖star (creation i false) ξ‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ ‖ξ‖ := by simpa only [one_mul] using hc
  rw [offDiagonal_formula]
  change (u-v)*‖ξ‖ ≤ ‖(u:ℂ) • creation i true ((1-P : Operator ι) ξ)+
    (v:ℂ) • P (star (creation i false) ξ)‖
  rw [hξ]
  have hb := norm_sub_norm_le ((u:ℂ) • creation i true ξ)
    (-((v:ℂ) • P (star (creation i false) ξ)))
  simp only [norm_neg,sub_neg_eq_add,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hu,abs_of_nonneg hv,weighted_creation_norm] at hb
  have hpv := mul_le_mul_of_nonneg_left hpc hv
  nlinarith

 theorem offDiagonal_ker (u v : ℝ) (hv : 0 ≤ v) (hvu : v<u) (i : ι) :
    (offDiagonal u v i).ker = (1-P : Operator ι).ker := by
  ext ξ
  change offDiagonal u v i ξ=0 ↔ (1-P : Operator ι) ξ=0
  constructor
  · intro hξ
    have hproj : (1-P : Operator ι) ((1-P : Operator ι) ξ)=(1-P : Operator ι) ξ :=
      DFunLike.congr_fun projection_P.one_sub.isIdempotentElem.eq ξ
    have hb := offDiagonal_lower_bound u v (hv.trans hvu.le) hv i ((1-P : Operator ι) ξ) hproj
    have hx : offDiagonal u v i ((1-P : Operator ι) ξ)=0 := by
      have he : offDiagonal u v i ((1-P : Operator ι) ξ)=offDiagonal u v i ξ :=
        DFunLike.congr_fun (offDiagonal_right u v i) ξ
      exact he.trans hξ
    rw [hx,norm_zero] at hb
    have hn : ‖(1-P : Operator ι) ξ‖=0 := by nlinarith [norm_nonneg ((1-P : Operator ι) ξ)]
    exact norm_eq_zero.mp hn
  · intro hξ
    have he := DFunLike.congr_fun (offDiagonal_right u v i) ξ
    simpa only [mul_apply_eq_comp,hξ,map_zero] using he.symm

 theorem offDiagonal_mem_ambient (u v : ℝ) (i : ι) :
    offDiagonal u v i ∈ ambientAlgebra u v :=
  mul_mem (mul_mem (P_mem_ambient u v) (S_mem_ambient u v i))
    (sub_mem (one_mem _) (P_mem_ambient u v))

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.Amplification.Polar
variable {E : Type u_7} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem kernel_orthogonal_projection {q : Operator E} (hq : IsStarProjection q) :
    q.kerᗮ.starProjection=q := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [Submodule.mem_orthogonal]
    intro y hy
    have hyq : q y=0 := hy
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (star q y) x=0
    rw [hq.isSelfAdjoint.star_eq,hyq,inner_zero_left]
  · rw [Submodule.orthogonal_orthogonal]
    change q (x-q x)=0
    rw [map_sub]
    have he : q (q x)=q x := DFunLike.congr_fun hq.isIdempotentElem.eq x
    rw [he,sub_self]

end FreeGroupFactorMain.Amplification.Polar
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
open Amplification.Polar
variable {ι : Type u_8} [DecidableEq ι]

 def edgePolar (u v : ℝ) (i : ι) : Operator ι := partialIsometry (offDiagonal u v i)

 theorem edgePolar_mem_ambient (u v : ℝ) (i : ι) :
    edgePolar u v i ∈ ambientAlgebra u v :=
  partialIsometry_mem_centralizer _ (offDiagonal_mem_ambient u v i)

 theorem edgePolar_initial (u v : ℝ) (hv : 0 ≤ v) (hvu : v<u) (i : ι) :
    star (edgePolar u v i)*edgePolar u v i=1-P := by
  simp only [edgePolar,partialIsometry_initial,modulus_closedRange,
    offDiagonal_ker u v hv hvu,kernel_orthogonal_projection projection_P.one_sub]

 theorem edgePolar_left (u v : ℝ) (i : ι) : P*edgePolar u v i=edgePolar u v i :=
  partialIsometry_left_support (offDiagonal_left u v i)

 theorem edgePolar_right (u v : ℝ) (i : ι) : edgePolar u v i*(1-P)=edgePolar u v i :=
  partialIsometry_right_support projection_P.one_sub.isSelfAdjoint (offDiagonal_right u v i)

 def edgeRange (u v : ℝ) (i : ι) : Operator ι := edgePolar u v i*star (edgePolar u v i)

 theorem edgeRange_projection (u v : ℝ) (i : ι) : IsStarProjection (edgeRange u v i) := by
  rw [edgeRange,edgePolar,partialIsometry_final]
  exact isStarProjection_starProjection

 theorem edgeRange_le_P (u v : ℝ) (i : ι) : P*edgeRange u v i=edgeRange u v i := by
  rw [edgeRange,← mul_assoc,edgePolar_left]

 theorem edgePolar_trace (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) :
    vacuumTrace u v (edgeRange u v i)=(v^2:ℝ) := by
  have ht := ambient_trace_mul u v (ne_of_gt (hv.trans hvu)) hv.ne'
    ⟨edgePolar u v i,edgePolar_mem_ambient u v i⟩
    ⟨star (edgePolar u v i),star_mem (edgePolar_mem_ambient u v i)⟩
  change vacuumTrace u v (edgePolar u v i*star (edgePolar u v i))=
    vacuumTrace u v (star (edgePolar u v i)*edgePolar u v i) at ht
  rw [edgePolar_initial u v hv.le hvu] at ht
  rw [edgeRange,ht]
  simp only [vacuumTrace,sub_apply,one_apply_eq_self,
    inner_sub_right]
  change vacuumTrace u v 1-vacuumTrace u v P=(v^2:ℝ)
  rw [vacuumTrace_one,vacuumTrace_P]
  push_cast
  ring

end
open FreeFock
open scoped ENNReal
open Amplification.Polar
variable {ι : Type u_9} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.CornerRerouting

section
variable {A : Type u_1} [Ring A] [StarRing A]

omit [StarRing A] in
 theorem right_zero {p v : A} (h : v*(1-p)=v) : v*p=0 := by
  have hh : v-v*p=v := by simpa only [mul_sub,mul_one] using h
  exact sub_eq_self.mp hh

 theorem star_left_zero {p v : A} (hp : IsSelfAdjoint p) (h : v*p=0) : p*star v=0 := by
  have hh := congrArg star h
  simpa only [star_mul,hp.star_eq,star_zero] using hh

end
section
variable {A : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {ι : Type u_3}

end
variable {A : Type u_4} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

end FreeGroupFactorMain.CornerRerouting
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification.Polar
variable {ι : Type u_5} [DecidableEq ι]

def edgeAlgebra (u v : ℝ) (i : ι) : StarSubalgebra ℂ (Operator ι) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ
      (insert P {offDiagonal u v i+star (offDiagonal u v i)}) : Set (Operator ι))

theorem edge_left_modulus_selfAdjoint (u v : ℝ) (i : ι) :
    IsSelfAdjoint (offDiagonal u v i*star (edgePolar u v i)) := by
  have hf := partialIsometry_factorization (offDiagonal u v i)
  change edgePolar u v i*modulus (offDiagonal u v i)=offDiagonal u v i at hf
  rw [← hf]
  change star ((edgePolar u v i*modulus (offDiagonal u v i))*star (edgePolar u v i))=_
  simp only [star_mul,star_star,modulus_star,mul_assoc]

end
section
open FreeFock
variable {ι : Type u_6} [DecidableEq ι]

def rightInsertEmbedding (j : ι) (w : Path ι) : Path ι ↪ Path ι :=
  ⟨fun x => (x.1 ++ [(j,x.2)] ++ w.1,w.2), by
    rintro ⟨a,r⟩ ⟨b,s⟩ h
    have h₁ := List.append_cancel_right (Prod.mk.inj h).1
    have h₂ := List.append_singleton_inj.mp h₁
    exact Prod.ext h₂.1 (Prod.mk.inj h₂.2).2⟩

def rightInsert (j : ι) (w : Path ι) : Operator ι :=
  (hilbertEmbedding (rightInsertEmbedding j w)).toContinuousLinearMap

@[simp] theorem rightInsert_single (j : ι) (w x : Path ι) (z : ℂ) :
    rightInsert j w (lp.single 2 x z)=
      lp.single 2 (x.1++[(j,x.2)]++w.1,w.2) z :=
  hilbertEmbedding_single (rightInsertEmbedding j w) x z

theorem P_commute_rightInsert (j : ι) (w : Path ι) :
    Commute (P : Operator ι) (rightInsert j w) := by
  apply CoordinateProjection.commute_embedding
  rintro ⟨a,r⟩
  cases a with
  | nil => rfl
  | cons k a => cases k; rfl

theorem creation_commute_rightInsert (i j : ι) (r : Bool) (w : Path ι) :
    Commute (creation i r) (rightInsert j w) := by
  change _*_=_*_
  apply operator_basis_ext
  intro x
  simp only [mul_apply_eq_comp,rightInsert_single,creation_single,List.cons_append]

def vacuumTo (w : Path ι) (r : Bool) : Operator ι :=
  InnerProductSpace.rankOne ℂ (lp.single 2 w 1) (lp.single 2 ([],r) 1)

@[simp] theorem vacuumTo_nil (w : Path ι) (r s : Bool) (z : ℂ) :
    vacuumTo w r (lp.single 2 ([],s) z)=if r=s then lp.single 2 w z else 0 := by
  classical
  by_cases h : r=s
  · subst s
    ext x
    simp [vacuumTo,InnerProductSpace.rankOne_apply,lp.inner_single_left,
      lp.single_apply,Pi.single_apply]
  · simp [vacuumTo,InnerProductSpace.rankOne_apply,lp.inner_single_left,
      lp.single_apply,h]

@[simp] theorem vacuumTo_cons (w : Path ι) (r s e : Bool) (i : ι)
    (a : List (ι×Bool)) (z : ℂ) :
    vacuumTo w r (lp.single 2 ((i,s)::a,e) z)=0 := by
  simp [vacuumTo,InnerProductSpace.rankOne_apply,lp.inner_single_left,lp.single_apply]

theorem annihilation_rightInsert (i j : ι) (r : Bool) (w : Path ι) :
    star (creation i r)*rightInsert j w=rightInsert j w*star (creation i r)+
      if i=j then vacuumTo w r else 0 := by
  apply operator_basis_ext
  rintro ⟨a,e⟩
  cases a with
  | nil =>
    simp only [mul_apply_eq_comp,add_apply,rightInsert_single,List.nil_append,
      List.singleton_append,annihilation_single_cons,annihilation_single_nil,map_zero,zero_add]
    by_cases h : i=j
    · subst j
      simp [vacuumTo_nil]
    · simp only [Prod.mk.injEq,h,false_and,ite_false]
      rfl
  | cons k a =>
    rcases k with ⟨k,s⟩
    simp only [mul_apply_eq_comp,add_apply,rightInsert_single,List.cons_append,
      annihilation_single_cons]
    have hm : (if i=j then vacuumTo w r else 0) (lp.single 2 ((k,s)::a,e) 1)=0 := by
      split_ifs <;> simp
    rw [hm,add_zero]
    by_cases h : (i,r)=(k,s)
    · simp only [h,ite_true,rightInsert_single]
    · simp only [h,ite_false,map_zero]

theorem S_commute_rightInsert (u v : ℝ) (i j : ι) (hij : i≠j) (w : Path ι) :
    Commute (S u v i) (rightInsert j w) := by
  have ha (r : Bool) : Commute (star (creation i r)) (rightInsert j w) := by
    change _*_=_*_
    simpa only [hij,ite_false,add_zero] using annihilation_rightInsert i j r w
  simp only [S,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal]
  exact (((creation_commute_rightInsert i j true w).smul_left _).add_left
    ((creation_commute_rightInsert i j false w).smul_left _)).add_left
      (((ha true).smul_left _).add_left ((ha false).smul_left _))

def oldPaths (J : Set ι) : Set (Path ι) := {w | ∀ x∈w.1, x.1∈J}
def oldProjection (J : Set ι) : Operator ι := CoordinateProjection.proj (oldPaths J)
def oldAlgebra (u v : ℝ) (J : Set ι) : StarSubalgebra ℂ (Operator ι) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
    (insert P ((S u v) '' J)) : Set (Operator ι))

theorem oldProjection_commute_creation (J : Set ι) (i : ι) (hi : i∈J) (r : Bool) :
    Commute (oldProjection J) (creation i r) := by
  apply CoordinateProjection.commute_embedding
  intro w
  change (∀ x∈(i,r)::w.1, x.1∈J) ↔ (∀ x∈w.1, x.1∈J)
  simp [hi]

theorem oldProjection_commute_S (u v : ℝ) (J : Set ι) (i : ι) (hi : i∈J) :
    Commute (oldProjection J) (S u v i) := by
  have ha (r : Bool) := (oldProjection_commute_creation J i hi r).star_star
  have hp : star (oldProjection J)=oldProjection J := CoordinateProjection.star_proj _
  simp only [hp] at ha
  simp only [S,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal]
  exact (((oldProjection_commute_creation J i hi true).smul_right _).add_right
    ((oldProjection_commute_creation J i hi false).smul_right _)).add_right
      (((ha true).smul_right _).add_right ((ha false).smul_right _))

theorem oldProjection_mem_commutant (u v : ℝ) (J : Set ι) :
    oldProjection J ∈ StarSubalgebra.centralizer ℂ (insert P ((S u v) '' J)) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  rcases hT with hT | ⟨i,hi,rfl⟩
  · subst T
    have hc : Commute (oldProjection J) P := CoordinateProjection.commute _ _
    exact ⟨hc.eq.symm, by rw [projection_P.isSelfAdjoint.star_eq]; exact hc.eq.symm⟩
  · have hc := oldProjection_commute_S u v J i hi
    exact ⟨hc.eq.symm, by rw [(S_selfAdjoint u v i).star_eq]; exact hc.eq.symm⟩

theorem rightInsert_mem_oldCommutant (u v : ℝ) (J : Set ι)
    (j : ι) (hj : j∉J) (w : Path ι) :
    rightInsert j w ∈ StarSubalgebra.centralizer ℂ (insert P ((S u v) '' J)) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  rcases hT with hT | ⟨i,hi,rfl⟩
  · subst T
    have hc := P_commute_rightInsert j w
    exact ⟨hc.eq,by rw [projection_P.isSelfAdjoint.star_eq]; exact hc.eq⟩
  · have hij : i≠j := by rintro rfl; exact hj hi
    have hc := S_commute_rightInsert u v i j hij w
    exact ⟨hc.eq,by rw [(S_selfAdjoint u v i).star_eq]; exact hc.eq⟩

theorem annihilation_oldProjection (J : Set ι) (i : ι) (hi : i∉J) (r : Bool) :
    star (creation i r)*oldProjection J=0 := by
  apply operator_basis_ext
  rintro ⟨a,e⟩
  cases a with
  | nil => simp [mul_apply_eq_comp,oldProjection,CoordinateProjection.proj_single,
      oldPaths,annihilation_single_nil]
  | cons k a =>
    rcases k with ⟨j,s⟩
    by_cases h : ((j,s)::a,e)∈oldPaths J
    · have hj : j∈J := h (j,s) (List.mem_cons_self ..)
      have hij : i≠j := by rintro rfl; exact hi hj
      simp [mul_apply_eq_comp,oldProjection,CoordinateProjection.proj_single,h,
        annihilation_single_cons,Prod.mk.injEq,hij]
    · simp [mul_apply_eq_comp,oldProjection,CoordinateProjection.proj_single,h]

theorem old_root_fixed (u v : ℝ) (J : Set ι) (T : oldAlgebra u v J) (s : Bool) :
    oldProjection J ((T : Operator ι) (lp.single 2 ([],s) 1))=
      (T : Operator ι) (lp.single 2 ([],s) 1) := by
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
    (oldProjection_mem_commutant u v J)).1
  have ht := DFunLike.congr_fun hc (lp.single 2 ([],s) 1)
  simpa only [mul_apply_eq_comp,oldProjection,CoordinateProjection.proj_single,
    oldPaths,Set.mem_ofPred_eq,List.not_mem_nil,forall_const,false_implies,
    implies_true,ite_true] using ht

theorem annihilation_old_root (u v : ℝ) (J : Set ι) (i : ι) (hi : i∉J)
    (T : oldAlgebra u v J) (r s : Bool) :
    star (creation i r) ((T : Operator ι) (lp.single 2 ([],s) 1))=0 := by
  have ht := DFunLike.congr_fun (annihilation_oldProjection J i hi r)
    ((T : Operator ι) (lp.single 2 ([],s) 1))
  simpa only [mul_apply_eq_comp,old_root_fixed,zero_apply] using ht

@[simp] theorem vacuumTo_apply (w : Path ι) (r : Bool) (ξ : H ι) :
    vacuumTo w r ξ=ξ ([],r) • lp.single 2 w 1 := by
  simp [vacuumTo,InnerProductSpace.rankOne_apply,lp.inner_single_left,RCLike.inner_apply]

theorem fresh_creation_contraction (u v : ℝ) (J : Set ι)
    (i j : ι) (hi : i∉J) (hj : j∉J) (T : oldAlgebra u v J) (r s : Bool) :
    star (creation i r)*(T : Operator ι)*creation j s=
      if i=j then (((T : Operator ι) (lp.single 2 ([],s) 1)) ([],r)) • 1 else 0 := by
  apply operator_basis_ext
  intro w
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
    (rightInsert_mem_oldCommutant u v J j hj w)).1
  have ht := DFunLike.congr_fun hc (lp.single 2 ([],s) 1)
  simp only [mul_apply_eq_comp,rightInsert_single,List.nil_append,List.singleton_append] at ht
  have ha := DFunLike.congr_fun (annihilation_rightInsert i j r w)
    ((T : Operator ι) (lp.single 2 ([],s) 1))
  simp only [mul_apply_eq_comp,add_apply,annihilation_old_root u v J i hi T,
    map_zero,zero_add] at ha
  simp only [mul_apply_eq_comp,creation_single,← ht,ha]
  by_cases hij : i=j
  · simp only [hij,ite_true,vacuumTo_apply,_root_.smul_apply,one_apply_eq_self]
  · simp only [hij,ite_false,zero_apply]

theorem vacuumTrace_root_expansion (u v : ℝ) (T : Operator ι) :
    vacuumTrace u v T =
      (u:ℂ)*(u:ℂ)*(T (lp.single 2 ([],true) 1)) ([],true) +
      (u:ℂ)*(v:ℂ)*(T (lp.single 2 ([],false) 1)) ([],true) +
      (v:ℂ)*(u:ℂ)*(T (lp.single 2 ([],true) 1)) ([],false) +
      (v:ℂ)*(v:ℂ)*(T (lp.single 2 ([],false) 1)) ([],false) := by
  simp only [vacuumTrace,vacuum,map_add,map_smul,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,lp.inner_single_left,RCLike.inner_apply,
    map_one,Complex.conj_ofReal]
  ring

theorem fresh_C_contraction (u v : ℝ) (J : Set ι)
    (i j : ι) (hi : i∉J) (hj : j∉J) (T : oldAlgebra u v J) :
    star (C u v i)*(T : Operator ι)*C u v j=
      if i=j then vacuumTrace u v (T : Operator ι) • 1 else 0 := by
  simp only [C,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,
    add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    fresh_creation_contraction u v J i j hi hj T]
  by_cases h : i=j
  · simp only [h,ite_true,smul_smul,
      ← add_smul (R := ℂ) (M := Operator ι)]
    rw [vacuumTrace_root_expansion]
    congr 1
    ring
  · simp only [h,ite_false,smul_zero (M := ℂ) (A := Operator ι),add_zero]

theorem fresh_C_annihilates_old_vacuum (u v : ℝ) (J : Set ι)
    (i : ι) (hi : i∉J) (T : oldAlgebra u v J) :
    star (C u v i) ((T : Operator ι) (vacuum u v))=0 := by
  simp only [vacuum,C,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,
    map_add,map_smul,add_apply,_root_.smul_apply,
    annihilation_old_root u v J i hi T,smul_zero,add_zero]

end

section
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

def terminalVertex (r : Bool) : Operator ι := CoordinateProjection.proj {w | w.2=r}
def edgeCreation (i : ι) (r s : Bool) : Operator ι := creation i r*vertex s

theorem vertex_eq_proj (r : Bool) : (vertex r : Operator ι)=
    CoordinateProjection.proj {w | start w=r} := by
  classical
  apply operator_basis_ext
  intro w
  by_cases h : start w=r <;> simp [vertex_single,CoordinateProjection.proj_single,h]

@[simp] theorem vertex_star (r : Bool) : star (vertex r : Operator ι)=vertex r := by
  rw [vertex_eq_proj,CoordinateProjection.star_proj]
omit [DecidableEq ι] in
@[simp] theorem terminalVertex_star (r : Bool) : star (terminalVertex r : Operator ι)=terminalVertex r :=
  CoordinateProjection.star_proj _
@[simp] theorem terminalVertex_single (r : Bool) (w : Path ι) (z : ℂ) :
    terminalVertex r (lp.single 2 w z)=if w.2=r then lp.single 2 w z else 0 := by
  classical
  by_cases h : w.2=r <;> simp [terminalVertex,CoordinateProjection.proj_single,h]

@[simp] theorem edgeCreation_single (i : ι) (r s : Bool) (w : Path ι) (z : ℂ) :
    edgeCreation i r s (lp.single 2 w z)=
      if start w=s then lp.single 2 ((i,r)::w.1,w.2) z else 0 := by
  simp only [edgeCreation,mul_apply_eq_comp,vertex_single]
  split_ifs <;> simp only [creation_single,map_zero]

@[simp] theorem edgeAnnihilation_nil (i : ι) (r s e : Bool) (z : ℂ) :
    star (edgeCreation i r s) (lp.single 2 ([],e) z)=0 := by
  simp only [edgeCreation,star_mul,vertex_star,mul_apply_eq_comp,annihilation_single_nil,map_zero]

@[simp] theorem edgeAnnihilation_cons (i j : ι) (r s t e : Bool)
    (w : List (ι×Bool)) (z : ℂ) :
    star (edgeCreation i r s) (lp.single 2 ((j,t)::w,e) z)=
      if (i,r)=(j,t) ∧ start (w,e)=s then lp.single 2 (w,e) z else 0 := by
  simp only [edgeCreation,star_mul,vertex_star,mul_apply_eq_comp,annihilation_single_cons]
  by_cases h : (i,r)=(j,t) <;> simp [h]

 theorem vertex_commute_rightInsert (r : Bool) (j : ι) (w : Path ι) :
    Commute (vertex r : Operator ι) (rightInsert j w) := by
  rw [vertex_eq_proj]
  apply CoordinateProjection.commute_embedding
  rintro ⟨a,e⟩
  cases a with
  | nil => rfl
  | cons k a => cases k; rfl

 theorem terminalVertex_commute_creation (e : Bool) (i : ι) (r : Bool) :
    Commute (terminalVertex e : Operator ι) (creation i r) := by
  apply CoordinateProjection.commute_embedding
  intro w
  rfl

 theorem terminalVertex_commute_edgeCreation (e : Bool) (i : ι) (r s : Bool) :
    Commute (terminalVertex e : Operator ι) (edgeCreation i r s) :=
  (terminalVertex_commute_creation e i r).mul_right (by
    rw [vertex_eq_proj];exact CoordinateProjection.commute _ _)

 theorem edgeCreation_commute_rightInsert (i j : ι) (r s : Bool) (w : Path ι) :
    Commute (edgeCreation i r s) (rightInsert j w) :=
  (creation_commute_rightInsert i j r w).mul_left (vertex_commute_rightInsert s j w)

 def diagonalInsert (j : ι) (w : Path ι) : Operator ι :=
   rightInsert j w*terminalVertex (start w)

 theorem vertex_commute_diagonalInsert (r : Bool) (j : ι) (w : Path ι) :
    Commute (vertex r : Operator ι) (diagonalInsert j w) :=
  (vertex_commute_rightInsert r j w).mul_right (by
    rw [vertex_eq_proj];exact CoordinateProjection.commute _ _)

 theorem edgeCreation_commute_diagonalInsert (i j : ι) (r s : Bool) (w : Path ι) :
    Commute (edgeCreation i r s) (diagonalInsert j w) :=
  (edgeCreation_commute_rightInsert i j r s w).mul_right
    (terminalVertex_commute_edgeCreation (start w) i r s).symm

 theorem vacuumTo_terminal (w : Path ι) (r s : Bool) :
    vacuumTo w r*terminalVertex s=if r=s then vacuumTo w r else 0 := by
  apply operator_basis_ext
  rintro ⟨a,e⟩
  cases a with
  | nil =>
    cases r <;> cases s <;> cases e <;>
      simp [mul_apply_eq_comp,terminalVertex_single]
  | cons k a =>
    rcases k with ⟨i,t⟩
    simp only [mul_apply_eq_comp,terminalVertex_single]
    split_ifs <;> simp only [vacuumTo_cons,map_zero,zero_apply]

 theorem vertex_vacuumTo (w : Path ι) (r s : Bool) :
    vertex s*vacuumTo w r=if start w=s then vacuumTo w r else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [mul_apply_eq_comp,vacuumTo_apply,map_smul,vertex_single]
  split_ifs <;> simp only [vacuumTo_apply,smul_zero,zero_apply]

 theorem crossAnnihilation_commute_diagonalInsert (i j : ι) (r s : Bool)
    (hrs : r≠s) (w : Path ι) :
    Commute (star (edgeCreation i r s)) (diagonalInsert j w) := by
  have hbase := annihilation_rightInsert i j r w
  have hterm := (terminalVertex_commute_creation (start w) i r).star_star
  simp only [terminalVertex_star] at hterm
  have hvertex := vertex_commute_rightInsert s j w
  have hvt : Commute (vertex s : Operator ι) (terminalVertex (start w)) := by
    rw [vertex_eq_proj];exact CoordinateProjection.commute _ _
  change _*_=_*_
  simp only [edgeCreation,star_mul,vertex_star,diagonalInsert]
  calc
    (vertex s*star (creation i r))*(rightInsert j w*terminalVertex (start w)) =
        vertex s*(star (creation i r)*rightInsert j w)*terminalVertex (start w) := by
          simp only [mul_assoc]
    _ = (rightInsert j w*terminalVertex (start w))*(vertex s*star (creation i r)) +
        vertex s*(if i=j then vacuumTo w r else 0)*terminalVertex (start w) := by
      rw [hbase,mul_add,add_mul]
      congr 1
      calc
        vertex s*(rightInsert j w*star (creation i r))*terminalVertex (start w) =
            rightInsert j w*(vertex s*star (creation i r)*terminalVertex (start w)) := by
              rw [← mul_assoc, hvertex.eq]; simp only [mul_assoc]
        _ = _ := by
          rw [mul_assoc (vertex s),← hterm.eq,← mul_assoc (vertex s),hvt.eq]
          simp only [mul_assoc]
    _ = _ := by
      have hz : vertex s*(if i=j then vacuumTo w r else 0)*terminalVertex (start w)=0 := by
        by_cases hij : i=j
        · rw [ite_eq_left hij,mul_assoc,vacuumTo_terminal]
          by_cases hr : r=start w
          · rw [ite_eq_left hr,vertex_vacuumTo,ite_eq_right (by simpa only [← hr] using hrs)]
          · rw [ite_eq_right hr,mul_zero]
        · rw [ite_eq_right hij,mul_zero,zero_mul]
      rw [hz,add_zero]

end

section
open FreeFock
variable {ι : Type u_8} [DecidableEq ι]

omit [DecidableEq ι] in
@[simp] theorem vertex_true : (vertex true : Operator ι)=P := rfl
omit [DecidableEq ι] in
@[simp] theorem vertex_false : (vertex false : Operator ι)=1-P := rfl

 theorem offDiagonal_edges (u v : ℝ) (i : ι) :
    offDiagonal u v i=(u:ℂ) • edgeCreation i true false+
      (v:ℂ) • star (edgeCreation i false true) := by
  rw [offDiagonal_formula]
  simp only [edgeCreation,star_mul,vertex_true,vertex_false,projection_P.isSelfAdjoint.star_eq]

 theorem offDiagonal_commute_diagonalInsert (u v : ℝ) (i j : ι) (w : Path ι) :
    Commute (offDiagonal u v i) (diagonalInsert j w) := by
  rw [offDiagonal_edges]
  exact ((edgeCreation_commute_diagonalInsert i j true false w).smul_left _).add_left
    ((crossAnnihilation_commute_diagonalInsert i j false true Bool.false_ne_true w).smul_left _)

 theorem offDiagonalStar_commute_diagonalInsert (u v : ℝ) (i j : ι) (w : Path ι) :
    Commute (star (offDiagonal u v i)) (diagonalInsert j w) := by
  rw [offDiagonal_edges]
  simp only [star_add (R := Operator ι),star_smul,star_star]
  exact ((crossAnnihilation_commute_diagonalInsert i j true false (by decide) w).smul_left _).add_left
    ((edgeCreation_commute_diagonalInsert i j false true w).smul_left _)

 theorem diagonalInsert_mem_edgeCommutant (u v : ℝ) (i j : ι) (w : Path ι) :
    diagonalInsert j w ∈ StarSubalgebra.centralizer ℂ
      (insert P {offDiagonal u v i+star (offDiagonal u v i)}) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  rcases hT with hT | hT
  · subst T
    have hc := vertex_commute_diagonalInsert true j w
    rw [vertex_true] at hc
    exact ⟨hc.eq,by rw [projection_P.isSelfAdjoint.star_eq];exact hc.eq⟩
  · have hT' : T=offDiagonal u v i+star (offDiagonal u v i) := hT
    subst T
    have hc := (offDiagonal_commute_diagonalInsert u v i j w).add_left
      (offDiagonalStar_commute_diagonalInsert u v i j w)
    exact ⟨hc.eq,by rw [(IsSelfAdjoint.add_star_self (R := Operator ι) _).star_eq];exact hc.eq⟩

 def alternatingList (e : Bool) : List (ι×Bool) → Prop
   | [] => True
   | (_,r)::a => r≠start (a,e) ∧ alternatingList e a
 def alternatingProjection : Operator ι :=
   CoordinateProjection.proj {w | alternatingList w.2 w.1}

 theorem alternatingProjection_pos (w : Path ι) (z : ℂ)
    (h : alternatingList w.2 w.1) :
    alternatingProjection (lp.single 2 w z)=lp.single 2 w z := by
  classical
  unfold alternatingProjection
  rw [CoordinateProjection.proj_single]
  apply ite_eq_left
  exact h

 theorem alternatingProjection_neg (w : Path ι) (z : ℂ)
    (h : ¬alternatingList w.2 w.1) :
    alternatingProjection (lp.single 2 w z)=0 := by
  classical
  unfold alternatingProjection
  rw [CoordinateProjection.proj_single]
  apply ite_eq_right
  exact h

 theorem alternating_commute_edgeCreation (i : ι) (r s : Bool) (hrs : r≠s) :
    Commute (alternatingProjection : Operator ι) (edgeCreation i r s) := by
  classical
  change _*_=_*_
  apply operator_basis_ext
  intro w
  simp only [mul_apply_eq_comp]
  by_cases hs : start w=s
  · have hneq : r≠start w := by simpa only [hs] using hrs
    by_cases ha : alternatingList w.2 w.1
    · have hn : alternatingList w.2 ((i,r)::w.1) := ⟨hneq,ha⟩
      rw [edgeCreation_single,ite_eq_left hs,alternatingProjection_pos _ _ hn,
        alternatingProjection_pos _ _ ha,edgeCreation_single,ite_eq_left hs]
    · have hn : ¬alternatingList w.2 ((i,r)::w.1) := fun h => ha h.2
      rw [edgeCreation_single,ite_eq_left hs,alternatingProjection_neg _ _ hn,
        alternatingProjection_neg _ _ ha,map_zero]
  · rw [edgeCreation_single,ite_eq_right hs,map_zero]
    by_cases ha : alternatingList w.2 w.1
    · rw [alternatingProjection_pos _ _ ha,edgeCreation_single,ite_eq_right hs]
    · rw [alternatingProjection_neg _ _ ha,map_zero]

 theorem alternating_commute_edgeAnnihilation (i : ι) (r s : Bool) (hrs : r≠s) :
    Commute (alternatingProjection : Operator ι) (star (edgeCreation i r s)) := by
  have h := (alternating_commute_edgeCreation i r s hrs).star_star
  simpa only [alternatingProjection,CoordinateProjection.star_proj] using h

 theorem alternating_mem_edgeCommutant (u v : ℝ) (i : ι) :
    (alternatingProjection : Operator ι) ∈ StarSubalgebra.centralizer ℂ
      (insert P {offDiagonal u v i+star (offDiagonal u v i)}) := by
  have hc : Commute (alternatingProjection : Operator ι) (offDiagonal u v i) := by
    rw [offDiagonal_edges]
    exact ((alternating_commute_edgeCreation i true false (by decide)).smul_right _).add_right
      ((alternating_commute_edgeAnnihilation i false true Bool.false_ne_true).smul_right _)
  have hcs := hc.star_star
  simp only [alternatingProjection,CoordinateProjection.star_proj] at hcs
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  rcases hT with hT | hT
  · subst T
    have hh : Commute (alternatingProjection : Operator ι) P := CoordinateProjection.commute _ _
    exact ⟨hh.eq.symm,by rw [projection_P.isSelfAdjoint.star_eq];exact hh.eq.symm⟩
  · have hT' : T=offDiagonal u v i+star (offDiagonal u v i) := hT
    subst T
    have hh := hc.add_right hcs
    exact ⟨hh.eq.symm,by rw [(IsSelfAdjoint.add_star_self (R := Operator ι) _).star_eq];exact hh.eq.symm⟩

 theorem diagonal_annihilation_alternating (i : ι) (r : Bool) :
    star (edgeCreation i r r)*alternatingProjection=0 := by
  classical
  apply operator_basis_ext
  rintro ⟨a,e⟩
  simp only [mul_apply_eq_comp,zero_apply]
  cases a with
  | nil =>
    rw [alternatingProjection_pos _ _ (show alternatingList e [] from trivial),
      edgeAnnihilation_nil]
  | cons k a =>
    rcases k with ⟨j,s⟩
    by_cases ha : alternatingList e ((j,s)::a)
    · rw [alternatingProjection_pos _ _ ha,edgeAnnihilation_cons]
      apply ite_eq_right
      rintro ⟨heq,hs⟩
      exact ha.1 ((Prod.mk.inj heq).2.symm.trans hs.symm)
    · rw [alternatingProjection_neg _ _ ha,map_zero]

 theorem alternating_edge_root (u v : ℝ) (i : ι) (T : edgeAlgebra u v i) (s : Bool) :
    alternatingProjection ((T : Operator ι) (lp.single 2 ([],s) 1))=
      (T : Operator ι) (lp.single 2 ([],s) 1) := by
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
    (alternating_mem_edgeCommutant u v i)).1
  have ht := DFunLike.congr_fun hc (lp.single 2 ([],s) 1)
  simpa only [mul_apply_eq_comp,alternatingProjection_pos ([],s) 1
    (show alternatingList s [] from trivial)] using ht

 theorem diagonal_annihilation_edge_root (u v : ℝ) (i j : ι)
    (T : edgeAlgebra u v i) (r s : Bool) :
    star (edgeCreation j r r) ((T : Operator ι) (lp.single 2 ([],s) 1))=0 := by
  have ht := DFunLike.congr_fun (diagonal_annihilation_alternating j r)
    ((T : Operator ι) (lp.single 2 ([],s) 1))
  simpa only [mul_apply_eq_comp,alternating_edge_root,zero_apply] using ht

end
open FreeFock
variable {ι : Type u_9} [DecidableEq ι]

 theorem edgeAnnihilation_diagonalInsert_formula (i j : ι) (r s : Bool) (w : Path ι) :
    star (edgeCreation i r s)*diagonalInsert j w=
      diagonalInsert j w*star (edgeCreation i r s)+
        vertex s*(if i=j then vacuumTo w r else 0)*terminalVertex (start w) := by
  have hbase := annihilation_rightInsert i j r w
  have hterm := (terminalVertex_commute_creation (start w) i r).star_star
  simp only [terminalVertex_star] at hterm
  have hvertex := vertex_commute_rightInsert s j w
  have hvt : Commute (vertex s : Operator ι) (terminalVertex (start w)) := by
    rw [vertex_eq_proj];exact CoordinateProjection.commute _ _
  simp only [edgeCreation,star_mul,vertex_star,diagonalInsert]
  calc
    (vertex s*star (creation i r))*(rightInsert j w*terminalVertex (start w)) =
        vertex s*(star (creation i r)*rightInsert j w)*terminalVertex (start w) := by
          simp only [mul_assoc]
    _ = _ := by
      rw [hbase,mul_add,add_mul]
      congr 1
      calc
        vertex s*(rightInsert j w*star (creation i r))*terminalVertex (start w) =
            rightInsert j w*(vertex s*star (creation i r)*terminalVertex (start w)) := by
              rw [← mul_assoc, hvertex.eq]; simp only [mul_assoc]
        _ = _ := by
          rw [mul_assoc (vertex s),← hterm.eq,← mul_assoc (vertex s),hvt.eq]
          simp only [mul_assoc]

 theorem diagonalAnnihilation_diagonalInsert (i j : ι) (r : Bool) (w : Path ι) :
    star (edgeCreation i r r)*diagonalInsert j w=
      diagonalInsert j w*star (edgeCreation i r r)+
        if i=j ∧ start w=r then vacuumTo w r else 0 := by
  rw [edgeAnnihilation_diagonalInsert_formula]
  congr 1
  by_cases hij : i=j
  · rw [ite_eq_left hij,mul_assoc,vacuumTo_terminal]
    by_cases hr : start w=r
    · simp only [hr,ite_true,vertex_vacuumTo,hij,true_and]
    · simp only [ite_eq_right (Ne.symm hr),mul_zero,hij,true_and,hr,ite_false]
  · simp only [hij,ite_false,mul_zero,zero_mul,false_and]

 theorem diagonalInsert_nil (j : ι) (w : Path ι) (s : Bool) :
    diagonalInsert j w (lp.single 2 ([],s) 1)=
      if s=start w then lp.single 2 ((j,s)::w.1,w.2) 1 else 0 := by
  simp only [diagonalInsert,mul_apply_eq_comp,terminalVertex_single]
  split_ifs <;> simp only [rightInsert_single,List.nil_append,List.singleton_append,map_zero]

 theorem diagonal_edge_contraction (u v : ℝ) (i j k : ι)
    (T : edgeAlgebra u v i) (r s : Bool) :
    star (edgeCreation j r r)*(T : Operator ι)*edgeCreation k s s=
      if j=k ∧ r=s then
        (((T : Operator ι) (lp.single 2 ([],s) 1)) ([],r)) • vertex s else 0 := by
  apply operator_basis_ext
  intro w
  by_cases hs : start w=s
  · have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
      (diagonalInsert_mem_edgeCommutant u v i k w)).1
    have ht := DFunLike.congr_fun hc (lp.single 2 ([],s) 1)
    simp only [mul_apply_eq_comp,diagonalInsert_nil,hs,ite_true] at ht
    have ha := DFunLike.congr_fun (diagonalAnnihilation_diagonalInsert j k r w)
      ((T : Operator ι) (lp.single 2 ([],s) 1))
    simp only [mul_apply_eq_comp,add_apply,diagonal_annihilation_edge_root u v i j T,
      map_zero,zero_add,hs] at ha
    simp only [mul_apply_eq_comp,edgeCreation_single,hs,ite_true,← ht,ha]
    by_cases hjk : j=k
    · by_cases hrs : r=s
      · simp [hjk,hrs,vacuumTo_apply,_root_.smul_apply,vertex_single,hs]
      · simp only [hjk,true_and,Ne.symm hrs,hrs,ite_false,zero_apply]
    · simp only [hjk,false_and,ite_false,zero_apply]
  · simp only [mul_apply_eq_comp,edgeCreation_single,hs,ite_false,map_zero]
    split_ifs <;> simp only [_root_.smul_apply,vertex_single,hs,ite_false,smul_zero,zero_apply]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

open Filter Topology
namespace FreeGroupFactorMain.JacobiNonatom

def invariant (a c : ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  a*((x n)^2+(x (n+1))^2)-c*x n*x (n+1)

 theorem invariant_step (a c : ℂ) (ha : a≠0) (x : ℕ → ℂ)
    (h : ∀ n,a*x (n+2)=c*x (n+1)-a*x n) (n : ℕ) :
    invariant a c x (n+1)=invariant a c x n := by
  apply mul_left_cancel₀ ha
  calc
    a*invariant a c x (n+1)=a*invariant a c x n+
      (a*x (n+2)-a*x n)*(a*x (n+2)+a*x n-c*x (n+1)) := by
      simp only [invariant,Nat.add_assoc]
      ring
    _ = a*invariant a c x n := by rw [h];ring

 theorem invariant_constant (a c : ℂ) (ha : a≠0) (x : ℕ → ℂ)
    (h : ∀ n,a*x (n+2)=c*x (n+1)-a*x n) (n : ℕ) :
    invariant a c x n=invariant a c x 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [invariant_step a c ha x h,ih]

 theorem invariant_zero (a c : ℂ) (ha : a≠0) (x : ℕ → ℂ)
    (h : ∀ n,a*x (n+2)=c*x (n+1)-a*x n)
    (hx : Tendsto x atTop (𝓝 0)) : invariant a c x 0=0 := by
  have hx' := hx.comp (tendsto_add_atTop_nat 1)
  have hl : Tendsto (invariant a c x) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n => a*((x n)^2+(x (n+1))^2)) atTop
        (𝓝 (a*((0:ℂ)^2+0^2))) :=
      tendsto_const_nhds.mul ((hx.pow 2).add (hx'.pow 2))
    have h₂ : Tendsto (fun n => c*x n*x (n+1)) atTop (𝓝 (c*0*0)) :=
      (tendsto_const_nhds.mul hx).mul hx'
    change Tendsto (fun n => a*((x n)^2+(x (n+1))^2)-c*x n*x (n+1)) atTop (𝓝 0)
    simpa only [zero_pow (by decide : (2:ℕ)≠0),zero_add,mul_zero,sub_zero]
      using h₁.sub h₂
  have he : invariant a c x=(fun _ : ℕ => invariant a c x 0) :=
    funext (invariant_constant a c ha x h)
  rw [he] at hl
  exact tendsto_nhds_unique tendsto_const_nhds hl

 theorem nonzero_eigenvector_zero (u v z : ℂ) (hu : u≠0) (hv : v≠0) (hz : z≠0)
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 0))
    (hfirst : (u*v)*x 1=(z-u^2)*x 0)
    (hstep : ∀ n,(u*v)*x (n+2)=(z-u^2-v^2)*x (n+1)-(u*v)*x n) :
    ∀ n,x n=0 := by
  have hi := invariant_zero (u*v) (z-u^2-v^2) (mul_ne_zero hu hv) x hstep hx
  have hb : (u*v)*invariant (u*v) (z-u^2-v^2) x 0=z*v^2*(x 0)^2 := by
    calc
      _ = (u*v)^2*(x 0)^2+((u*v)*x 1)^2-
        (z-u^2-v^2)*x 0*((u*v)*x 1) := by simp only [invariant];ring
      _ = _ := by rw [hfirst];ring
  rw [hi,mul_zero] at hb
  have h0 : x 0=0 := by
    have hz : (x 0)^2=0 := (mul_eq_zero.mp hb.symm).resolve_left
      (mul_ne_zero hz (pow_ne_zero 2 hv))
    exact (sq_eq_zero_iff).mp hz
  have h1 : x 1=0 := by
    rw [h0,mul_zero] at hfirst
    exact (mul_eq_zero.mp hfirst).resolve_left (mul_ne_zero hu hv)
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n hn hn1 =>
    have h := hstep n
    rw [hn,hn1,mul_zero,mul_zero,sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hu hv)

end FreeGroupFactorMain.JacobiNonatom
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Filter Topology
open scoped ENNReal
variable {ι : Type u_1} [DecidableEq ι]

def jacobiList (i : ι) : ℕ → List (ι × Bool)
  | 0 => []
  | n+1 => (i,false)::(i,true)::jacobiList i n

def jacobiPath (i : ι) (n : ℕ) : Path ι := (jacobiList i n,false)
def oddJacobiPath (i : ι) (n : ℕ) : Path ι := ((i,true)::jacobiList i n,false)
def jacobiBasis (i : ι) (n : ℕ) : H ι := lp.single 2 (jacobiPath i n) 1
def oddJacobiBasis (i : ι) (n : ℕ) : H ι := lp.single 2 (oddJacobiPath i n) 1

omit [DecidableEq ι] in
@[simp] theorem jacobiList_length (i : ι) (n : ℕ) : (jacobiList i n).length=2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [jacobiList,List.length_cons,ih];omega

omit [DecidableEq ι] in
 theorem jacobiPath_injective (i : ι) : Function.Injective (jacobiPath i) := by
  intro n m h
  have hh := congrArg (fun w : Path ι => w.1.length) h
  simp only [jacobiPath,jacobiList_length] at hh
  omega

omit [DecidableEq ι] in
@[simp] theorem jacobiPath_start (i : ι) (n : ℕ) : start (jacobiPath i n)=false := by
  cases n <;> rfl
omit [DecidableEq ι] in
@[simp] theorem oddJacobiPath_start (i : ι) (n : ℕ) : start (oddJacobiPath i n)=true := rfl

 theorem offDiagonal_jacobi_zero (u v : ℝ) (i : ι) :
    offDiagonal u v i (jacobiBasis i 0)=(u:ℂ) • oddJacobiBasis i 0 := by
  simp only [offDiagonal_edges,jacobiBasis,jacobiPath,jacobiList,oddJacobiBasis,
    oddJacobiPath,_root_.smul_apply,add_apply,edgeCreation_single,edgeAnnihilation_nil,
    smul_zero,add_zero]
  rfl

 theorem offDiagonal_jacobi_succ (u v : ℝ) (i : ι) (n : ℕ) :
    offDiagonal u v i (jacobiBasis i (n+1))=
      (u:ℂ) • oddJacobiBasis i (n+1)+(v:ℂ) • oddJacobiBasis i n := by
  simp only [offDiagonal_edges,jacobiBasis,jacobiPath,jacobiList,oddJacobiBasis,
    oddJacobiPath,_root_.smul_apply,add_apply,edgeCreation_single,edgeAnnihilation_cons,
    start,ite_true,eq_self,true_and]

 theorem offDiagonalStar_oddJacobi (u v : ℝ) (i : ι) (n : ℕ) :
    star (offDiagonal u v i) (oddJacobiBasis i n)=
      (u:ℂ) • jacobiBasis i n+(v:ℂ) • jacobiBasis i (n+1) := by
  cases n <;>
    simp only [offDiagonal_edges,star_add (R := Operator ι),star_smul,star_star,Complex.star_def,
      Complex.conj_ofReal,jacobiBasis,jacobiPath,jacobiList,oddJacobiBasis,oddJacobiPath,
      _root_.smul_apply,add_apply,edgeCreation_single,edgeAnnihilation_cons,
      start,ite_true,eq_self,true_and]

 def edgeSquare (u v : ℝ) (i : ι) : Operator ι := star (offDiagonal u v i)*offDiagonal u v i

 theorem edgeSquare_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (edgeSquare u v i) := by
  simp [IsSelfAdjoint,edgeSquare,star_mul]

 theorem edgeSquare_jacobi_zero (u v : ℝ) (i : ι) :
    edgeSquare u v i (jacobiBasis i 0)=
      ((u:ℂ)^2) • jacobiBasis i 0+((u:ℂ)*v) • jacobiBasis i 1 := by
  rw [edgeSquare,mul_apply_eq_comp,offDiagonal_jacobi_zero,map_smul,offDiagonalStar_oddJacobi]
  simp only [smul_add,smul_smul,pow_two]

 theorem edgeSquare_jacobi_succ (u v : ℝ) (i : ι) (n : ℕ) :
    edgeSquare u v i (jacobiBasis i (n+1))=
      ((u:ℂ)*v) • jacobiBasis i n+
        ((u:ℂ)^2+(v:ℂ)^2) • jacobiBasis i (n+1)+
          ((u:ℂ)*v) • jacobiBasis i (n+2) := by
  rw [edgeSquare,mul_apply_eq_comp,offDiagonal_jacobi_succ,map_add,map_smul,
    map_smul,offDiagonalStar_oddJacobi,offDiagonalStar_oddJacobi]
  simp only [smul_add,smul_smul,pow_two,add_smul,Nat.add_assoc]
  module

omit [DecidableEq ι] in
 theorem jacobi_coordinates_decay (i : ι) (ξ : H ι) :
    Tendsto (fun n => ξ (jacobiPath i n)) atTop (𝓝 0) := by
  have hs : Summable (fun w : Path ι => ‖ξ w‖^2) := by
    simpa using (lp.memℓp ξ).summable (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
  have ht := (hs.comp_injective (jacobiPath_injective i)).tendsto_atTop_zero
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have hn : Tendsto (fun n => ‖ξ (jacobiPath i n)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

 theorem edgeSquare_eigen_coordinates (u v : ℝ) (i : ι) (z : ℂ) (ξ : H ι)
    (hξ : edgeSquare u v i ξ=z • ξ) :
    ((u:ℂ)*v)*ξ (jacobiPath i 1)=(z-(u:ℂ)^2)*ξ (jacobiPath i 0) ∧
      ∀ n,((u:ℂ)*v)*ξ (jacobiPath i (n+2))=
        (z-(u:ℂ)^2-(v:ℂ)^2)*ξ (jacobiPath i (n+1))-
          ((u:ℂ)*v)*ξ (jacobiPath i n) := by
  have he (n : ℕ) : inner ℂ (edgeSquare u v i (jacobiBasis i n)) ξ=
      z*ξ (jacobiPath i n) := by
    rw [← (edgeSquare_selfAdjoint u v i).star_eq,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left,hξ,inner_smul_right]
    simp [jacobiBasis,lp.inner_single_left,RCLike.inner_apply]
  constructor
  · have h := he 0
    rw [edgeSquare_jacobi_zero] at h
    simp [jacobiBasis,lp.inner_single_left,
      RCLike.inner_apply] at h
    linear_combination h
  · intro n
    have h := he (n+1)
    rw [edgeSquare_jacobi_succ] at h
    simp [jacobiBasis,lp.inner_single_left,
      RCLike.inner_apply] at h
    linear_combination h

 theorem edgeSquare_eigen_root_zero (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (z : ℂ) (hz : z≠0) (ξ : H ι) (hξ : edgeSquare u v i ξ=z • ξ) :
    ξ ([],false)=0 := by
  have h := edgeSquare_eigen_coordinates u v i z ξ hξ
  exact JacobiNonatom.nonzero_eigenvector_zero (u:ℂ) (v:ℂ) z
    (Complex.ofReal_ne_zero.mpr hu) (Complex.ofReal_ne_zero.mpr hv) hz
    (fun n => ξ (jacobiPath i n)) (jacobi_coordinates_decay i ξ) h.1 h.2 0

end

section
open FreeFock
variable {ι : Type u_2}

def flipPath : Path ι ≃ Path ι where
  toFun w := (w.1.map (fun a => (a.1,!a.2)),!w.2)
  invFun w := (w.1.map (fun a => (a.1,!a.2)),!w.2)
  left_inv w := by
    rcases w with ⟨l,b⟩
    simp only [List.map_map,Function.comp_def,Bool.not_not]
    simp
  right_inv w := by
    rcases w with ⟨l,b⟩
    simp only [List.map_map,Function.comp_def,Bool.not_not]
    simp

@[simp] theorem flipPath_apply (w : Path ι) : flipPath w=(w.1.map (fun a => (a.1,!a.2)),!w.2) := rfl

@[simp] theorem flipPath_involutive (w : Path ι) : flipPath (flipPath w)=w := by
  rcases w with ⟨l,b⟩
  simp only [flipPath_apply,List.map_map,Function.comp_def,Bool.not_not]
  simp

@[simp] theorem flipPath_symm (w : Path ι) : flipPath.symm w=flipPath w := by
  apply flipPath.injective
  rw [Equiv.apply_symm_apply,flipPath_involutive]

@[simp] theorem start_flipPath (w : Path ι) : start (flipPath w)=!(start w) := by
  rcases w with ⟨l,b⟩
  cases l <;> rfl

def flipSpatial : H ι ≃ₗᵢ[ℂ] H ι := hilbertReindex flipPath

@[simp] theorem flipSpatial_apply (ξ : H ι) (w : Path ι) : flipSpatial ξ w=ξ (flipPath w) := by
  simp only [flipSpatial,hilbertReindex_apply,flipPath_symm]

variable [DecidableEq ι]

theorem flipSpatial_single (w : Path ι) (z : ℂ) :
    flipSpatial (lp.single 2 w z)=lp.single 2 (flipPath w) z := by
  ext a
  simp only [flipSpatial_apply,lp.single_apply,Pi.single_apply]
  by_cases h : flipPath w=a
  · subst a
    simp only [flipPath_involutive,ite_true]
  · have hh : w≠flipPath a := by
      intro he
      apply h
      rw [he,flipPath_involutive]
    simp_all [eq_comm]

theorem flipSpatial_vertex_intertwines (r : Bool) (ξ : H ι) :
    flipSpatial (vertex r ξ)=vertex (!r) (flipSpatial ξ) := by
  have he : flipSpatial.toContinuousLinearEquiv.toContinuousLinearMap*(vertex r : Operator ι)=
      vertex (!r)*flipSpatial.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply operator_basis_ext
    intro w
    simp only [mul_apply_eq_comp,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,vertex_single,flipSpatial_single,start_flipPath]
    split_ifs with h h' h' <;> simp_all [flipSpatial_single]
  exact DFunLike.congr_fun he ξ

theorem flipSpatial_conjugates_vertex (r : Bool) :
    flipSpatial.conjStarAlgEquiv (vertex r : Operator ι)=vertex (!r) := by
  ext ξ
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [flipSpatial_vertex_intertwines,LinearIsometryEquiv.apply_symm_apply]

theorem flipSpatial_creation_intertwines (i : ι) (r : Bool) (ξ : H ι) :
    flipSpatial (creation i r ξ)=creation i (!r) (flipSpatial ξ) := by
  have he : flipSpatial.toContinuousLinearEquiv.toContinuousLinearMap*creation i r=
      creation i (!r)*flipSpatial.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply operator_basis_ext
    intro w
    simp only [mul_apply_eq_comp,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,creation_single,flipSpatial_single,flipPath_apply,List.map_cons]
  exact DFunLike.congr_fun he ξ

theorem flipSpatial_conjugates_creation (i : ι) (r : Bool) :
    flipSpatial.conjStarAlgEquiv (creation i r)=creation i (!r) := by
  ext ξ
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [flipSpatial_creation_intertwines,LinearIsometryEquiv.apply_symm_apply]

theorem flipSpatial_conjugates_edgeCreation (i : ι) (r s : Bool) :
    flipSpatial.conjStarAlgEquiv (edgeCreation i r s)=edgeCreation i (!r) (!s) := by
  rw [edgeCreation,map_mul,flipSpatial_conjugates_creation,flipSpatial_conjugates_vertex]
  rfl

theorem flipSpatial_conjugates_offDiagonal (u v : ℝ) (i : ι) :
    flipSpatial.conjStarAlgEquiv (offDiagonal u v i)=star (offDiagonal v u i) := by
  simp only [offDiagonal_edges,map_add,map_smul,map_star,flipSpatial_conjugates_edgeCreation,
    Bool.not_true,Bool.not_false,star_add (R := Operator ι),star_smul,star_star,Complex.star_def,Complex.conj_ofReal]
  exact add_comm _ _

theorem flipSpatial_conjugates_edgeSquare (u v : ℝ) (i : ι) :
    flipSpatial.conjStarAlgEquiv (edgeSquare u v i)=offDiagonal v u i*star (offDiagonal v u i) := by
  rw [edgeSquare,map_mul,map_star,flipSpatial_conjugates_offDiagonal,star_star]

end
open FreeFock Amplification.Polar
variable {ι : Type u_3} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


