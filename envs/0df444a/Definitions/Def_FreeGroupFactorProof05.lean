-- Prove2me | Definitions.Def_FreeGroupFactorProof05
-- name    : FreeGroupFactorProof05
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T00:47:10.031193+00:00
-- url     : https://prove2.me/theorems/f99b201e-f819-43d1-9aeb-6b1b068f4583
-- title:
--   Free group factors: supporting development, part 5 of 12
-- statement:
--   Part 5 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof04

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

theorem fresh_C_filled_contraction (u v : ℝ) (i j n m : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (hmi : m≠i) (hmj : m≠j) (T : filledEdgeAlgebra u v i j) :
    star (C u v n)*(T : Operator ι)*C u v m=
      if n=m then vacuumTrace u v (T : Operator ι) • 1 else 0 := by
  have hD := weightedDefect_annihilates_edge u v i j hji
  have hR (a : edgeAlgebra u v i) : star (weightedDefectCreation u v i j)*(a : Operator ι)*C u v m=0 := by
    have hh := congrArg star (fresh_C_weightedDefect u v i j m hji hmi hmj (star a))
    simpa only [star_mul,star_star,StarMemClass.coe_star,star_zero (Operator ι),mul_assoc] using hh
  have hb (a : edgeAlgebra u v i) : star (C u v n)*(a : Operator ι)*C u v m=
      (inner ℂ (vacuum u v) ((a : Operator ι) (vacuum u v))) • (if n=m then (1 : Operator ι) else 0) := by
    have hh := fresh_C_contraction u v {i} n m hni hmi
      ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩
    split_ifs with h <;> simpa only [vacuumTrace,h,ite_true,ite_false,
      smul_zero (M := ℂ) (A := Operator ι)] using hh
  have hh := GaussianExtension.covariance_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji)
    (C u v n) (C u v m) (if n=m then (1 : Operator ι) else 0) (vacuum u v) (vacuum u v)
    hD hD (fresh_C_weightedDefect u v i j n hji hni hnj) hR hb (T : Operator ι) T.property
  split_ifs with h <;> simpa only [vacuumTrace,h,ite_true,ite_false,
    smul_zero (M := ℂ) (A := Operator ι)] using hh

theorem fresh_C_filled_annihilation (u v : ℝ) (i j n : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (T : filledEdgeAlgebra u v i j) : star (C u v n) ((T : Operator ι) (vacuum u v))=0 := by
  apply GaussianExtension.annihilation_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji)
    (C u v n) (vacuum u v) (weightedDefect_annihilates_edge u v i j hji)
    _ (fresh_C_weightedDefect u v i j n hji hni hnj) (T : Operator ι) T.property
  intro a
  exact fresh_C_annihilates_old_vacuum u v {i} n hni
    ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩
end
section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem edgeAlgebra_le_ambient (u v : ℝ) (i : ι) : edgeAlgebra u v i≤ambientAlgebra u v := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · exact P_mem_ambient u v
  · have he : T=offDiagonal u v i+star (offDiagonal u v i) := hT
    rw [he]
    exact add_mem (offDiagonal_mem_ambient u v i) (star_mem (offDiagonal_mem_ambient u v i))

theorem edgeAlgebra_le_filled (u v : ℝ) (i j : ι) : edgeAlgebra u v i≤filledEdgeAlgebra u v i j :=
  fun _ h => Bicommutant.subset _ (Set.mem_insert_of_mem _ h)

theorem weightedDefect_semicircle_mem_filled (u v : ℝ) (i j : ι) :
    weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)∈filledEdgeAlgebra u v i j :=
  Bicommutant.subset _ (Set.mem_insert _ _)

theorem filledEdgeAlgebra_le_ambient (u v : ℝ) (i j : ι) : filledEdgeAlgebra u v i j≤ambientAlgebra u v := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · have he : weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)=
        edgeDefect u v i*S u v j*edgeDefect u v i := by
      simp only [weightedDefectCreation,S_eq,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
        mul_add,add_mul,mul_assoc]
    rw [he]
    have hd := edgeAlgebra_le_ambient u v i (edgeDefect_mem_edge u v i)
    exact mul_mem (mul_mem hd (S_mem_ambient u v j)) hd
  · exact edgeAlgebra_le_ambient u v i hT

theorem weightedDefectCreation_eq (u v : ℝ) (i j : ι) :
    weightedDefectCreation u v i j=(u:ℂ) • defectCreation u v i j := by
  have he : P*C u v j*P=(u:ℂ) • edgeCreation j true true := by
    simp only [C,mul_add,mul_smul_comm,smul_mul_assoc,P_creation_true,P_creation_false,
      smul_zero (M := ℂ) (A := Operator ι),add_zero,edgeCreation,vertex_true]
  calc
    _ = edgeDefect u v i*(P*C u v j*P)*edgeDefect u v i := by
      simp only [weightedDefectCreation,mul_assoc,P_mul_edgeDefect]
      rw [← mul_assoc (edgeDefect u v i) P,edgeDefect_mul_P]
    _ = _ := by rw [he,mul_smul_comm,smul_mul_assoc]; rfl

theorem defectSemicircle_mem_filled (u v : ℝ) (hu : u≠0) (i j : ι) :
    defectSemicircle u v i j∈filledEdgeAlgebra u v i j := by
  have he : weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)=
      (u:ℂ) • defectSemicircle u v i j := by
    simp only [weightedDefectCreation_eq,star_smul,Complex.star_def,Complex.conj_ofReal,
      defectSemicircle,smul_add]
  have hh := (filledEdgeAlgebra u v i j).smul_mem (weightedDefect_semicircle_mem_filled u v i j) (u:ℂ)⁻¹
  rw [he,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hu),one_smul] at hh
  exact hh

theorem diffuseBase_le_filled (u v : ℝ) (hu : u≠0) (i j : ι) :
    diffuseBase u v i j≤filledEdgeAlgebra u v i j := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · exact edgeAlgebra_le_filled u v i j (P_mem_edge u v i)
  · have he : T=oldBaseGenerator u v i j := hT
    rw [he,oldBaseGenerator]
    apply add_mem
    · apply add_mem
      · exact edgeAlgebra_le_filled u v i j
          (mul_mem (offDiagonal_mem_edge u v i) (star_mem (edgePolar_mem_edge u v i)))
      · exact defectSemicircle_mem_filled u v hu i j
    · exact (filledEdgeAlgebra u v i j).smul_mem
        (edgeAlgebra_le_filled u v i j (edgeRange_mem_edge u v i)) _
end

open FreeFock
variable {ι : Type u_3} [DecidableEq ι]

theorem edgePolar_mul_P (u v : ℝ) (i : ι) : edgePolar u v i*P=0 :=
  CornerRerouting.right_zero (edgePolar_right u v i)

theorem P_mul_star_edgePolar (u v : ℝ) (i : ι) : P*star (edgePolar u v i)=0 :=
  CornerRerouting.star_left_zero projection_P.isSelfAdjoint (edgePolar_mul_P u v i)

def supportedLeg (u v : ℝ) (i₀ : ι) (r : Bool) : Operator ι :=
  if r then edgePolar u v i₀ else P

def legSupport (u v : ℝ) (i₀ : ι) (r : Bool) : Operator ι :=
  if r then edgeRange u v i₀ else P

theorem supportedLeg_mem_edge (u v : ℝ) (i : ι) (r : Bool) :
    supportedLeg u v i r∈edgeAlgebra u v i := by
  cases r
  · exact P_mem_edge u v i
  · exact edgePolar_mem_edge u v i

theorem supportedLeg_mem_ambient (u v : ℝ) (i : ι) (r : Bool) :
    supportedLeg u v i r∈ambientAlgebra u v :=
  edgeAlgebra_le_ambient u v i (supportedLeg_mem_edge u v i r)

theorem supportedLeg_mul_star (u v : ℝ) (i : ι) (r s : Bool) :
    supportedLeg u v i r*star (supportedLeg u v i s)=
      if r=s then legSupport u v i r else 0 := by
  cases r <;> cases s <;>
    simp only [supportedLeg,legSupport,Bool.false_eq_true,ite_false,ite_true,
      projection_P.isSelfAdjoint.star_eq,projection_P.isIdempotentElem.eq,
      P_mul_star_edgePolar,edgePolar_mul_P,Bool.true_eq_false,edgeRange]

theorem supportedLeg_trace_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (r s : Bool) (T : ambientAlgebra (ι := ι) u v) :
    vacuumTrace u v (star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i s)=
      if r=s then vacuumTrace u v ((T : Operator ι)*legSupport u v i r) else 0 := by
  have ht := ambient_trace_mul u v hu hv
    ⟨star (supportedLeg u v i r),star_mem (supportedLeg_mem_ambient u v i r)⟩
    (T*⟨supportedLeg u v i s,supportedLeg_mem_ambient u v i s⟩)
  change vacuumTrace u v (star (supportedLeg u v i r)*((T : Operator ι)*supportedLeg u v i s))=
    vacuumTrace u v (((T : Operator ι)*supportedLeg u v i s)*star (supportedLeg u v i r)) at ht
  rw [mul_assoc,ht,mul_assoc,supportedLeg_mul_star]
  by_cases h : r=s
  · subst s
    simp only [ite_true]
  · simp only [h,Ne.symm h,ite_false,mul_zero,vacuumTrace,zero_apply,inner_zero_right]

def supportedCreation (u v : ℝ) (i₀ i : ι) (r s : Bool) : Operator ι :=
  supportedLeg u v i₀ r*C u v i*star (supportedLeg u v i₀ s)

theorem supportedCreation_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j n m : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j) (hmi : m≠i) (hmj : m≠j)
    (r s r' s' : Bool) (T : filledEdgeAlgebra u v i j) :
    star (supportedCreation u v i n r s)*(T : Operator ι)*supportedCreation u v i m r' s'=
      if n=m ∧ r=r' ∧ s=s' then
        vacuumTrace u v ((T : Operator ι)*legSupport u v i r) • legSupport u v i s else 0 := by
  let a (b : Bool) : filledEdgeAlgebra u v i j :=
    ⟨supportedLeg u v i b,edgeAlgebra_le_filled u v i j (supportedLeg_mem_edge u v i b)⟩
  have hc := fresh_C_filled_contraction u v i j n m hji hni hnj hmi hmj (star (a r)*T*a r')
  change star (C u v n)*(star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r')*C u v m=_ at hc
  calc
    _ = supportedLeg u v i s*(star (C u v n)*
        (star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r')*C u v m)*
        star (supportedLeg u v i s') := by simp only [supportedCreation,star_mul,star_star,mul_assoc]
    _ = _ := by
      rw [hc]
      change (supportedLeg u v i s*(if n=m then
        vacuumTrace u v (star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r') • 1 else 0)*
        star (supportedLeg u v i s'))=_
      rw [supportedLeg_trace_covariance u v hu hv i r r'
        ⟨T,filledEdgeAlgebra_le_ambient u v i j T.property⟩]
      by_cases hnm : n=m
      · rw [ite_eq_left hnm,mul_smul_comm,smul_mul_assoc,mul_one,supportedLeg_mul_star]
        by_cases hr : r=r' <;> by_cases hs : s=s' <;>
          simp only [hnm,hr,hs,ite_true,ite_false,zero_smul ℂ (A := Operator ι),
            smul_zero (M := ℂ) (A := Operator ι),true_and,false_and,and_false]
      · simp only [hnm,ite_false,mul_zero,zero_mul,false_and]

theorem supportedCreation_filled_annihilation (u v : ℝ)
    (i j n : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (supportedCreation u v i n r s) ((T : Operator ι) (vacuum u v))=0 := by
  let a : filledEdgeAlgebra u v i j :=
    ⟨star (supportedLeg u v i r),star_mem
      (edgeAlgebra_le_filled u v i j (supportedLeg_mem_edge u v i r))⟩*T
  have hh := fresh_C_filled_annihilation u v i j n hji hni hnj a
  simp only [supportedCreation,star_mul,star_star,mul_apply_eq_comp]
  change supportedLeg u v i s (star (C u v n) ((a : Operator ι) (vacuum u v)))=0
  rw [hh,map_zero]

def pVacuumTrace (u v : ℝ) (T : Operator ι) : ℂ := (u:ℂ)⁻¹*(u:ℂ)⁻¹*vacuumTrace u v T

def normalizedCreation (u v : ℝ) (i n : ι) (r s : Bool) : Operator ι :=
  (u:ℂ)⁻¹ • supportedCreation u v i n r s

theorem normalizedCreation_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j n m : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j) (hmi : m≠i) (hmj : m≠j)
    (r s r' s' : Bool) (T : filledEdgeAlgebra u v i j) :
    star (normalizedCreation u v i n r s)*(T : Operator ι)*normalizedCreation u v i m r' s'=
      if n=m ∧ r=r' ∧ s=s' then
        pVacuumTrace u v ((T : Operator ι)*legSupport u v i r) • legSupport u v i s else 0 := by
  simp only [normalizedCreation,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm]
  rw [supportedCreation_filled_covariance u v hu hv i j n m hji hni hnj hmi hmj]
  split_ifs <;> simp only [smul_zero (M := ℂ) (A := Operator ι),smul_smul,pVacuumTrace,mul_assoc]

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
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

theorem annihilation_commute_diagonalInsert (n j : ι) (hnj : n≠j) (r : Bool) (w : Path ι) :
    Commute (star (creation n r)) (diagonalInsert j w) := by
  have hA : Commute (star (creation n r)) (rightInsert j w) := by
    have hh := annihilation_rightInsert n j r w
    exact (show Commute _ _ from by
      change _ * _ = _ * _
      simpa only [hnj,ite_false,add_zero] using hh)
  have ht := (terminalVertex_commute_creation (start w) n r).star_star
  simp only [terminalVertex_star] at ht
  exact hA.mul_right ht.symm

theorem Cstar_commute_diagonalInsert (u v : ℝ) (n j : ι) (hnj : n≠j) (w : Path ι) :
    Commute (star (C u v n)) (diagonalInsert j w) := by
  have hh := ((annihilation_commute_diagonalInsert n j hnj true w).smul_left (u:ℂ)).add_left
    ((annihilation_commute_diagonalInsert n j hnj false w).smul_left (v:ℂ))
  simpa only [C,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal] using hh

theorem fresh_C_edge_root (u v : ℝ) (i n : ι) (hni : n≠i) (T : edgeAlgebra u v i) (s : Bool) :
    star (C u v n) ((T : Operator ι) (lp.single 2 ([],s) 1))=0 := by
  let a : oldAlgebra u v {i} := ⟨T,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) T.property⟩
  have hh (r) : star (creation n r) ((T : Operator ι) (lp.single 2 ([],s) 1))=0 :=
    annihilation_old_root u v {i} n hni a r s
  simp only [C,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,add_apply,_root_.smul_apply,
    hh,smul_zero,add_zero]

theorem fresh_C_diagonal_edge (u v : ℝ) (i n j : ι) (hni : n≠i) (hnj : n≠j)
    (T : edgeAlgebra u v i) (r : Bool) :
    star (C u v n)*(T : Operator ι)*edgeCreation j r r=0 := by
  apply operator_basis_ext
  intro w
  by_cases hs : start w=r
  · have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _
      (diagonalInsert_mem_edgeCommutant u v i j w)).1
    have ht := DFunLike.congr_fun hc (lp.single 2 ([],r) 1)
    simp only [mul_apply_eq_comp,diagonalInsert_nil,hs,ite_true] at ht
    have ha := DFunLike.congr_fun (Cstar_commute_diagonalInsert u v n j hnj w).eq
      ((T : Operator ι) (lp.single 2 ([],r) 1))
    simp only [mul_apply_eq_comp,fresh_C_edge_root u v i n hni T,map_zero] at ha
    simpa only [mul_apply_eq_comp,edgeCreation_single,hs,ite_true,ht,zero_apply] using ha
  · simp only [mul_apply_eq_comp,edgeCreation_single,hs,ite_false,map_zero,zero_apply]

theorem diagonal_weightedDefect (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (T : edgeAlgebra u v i) (r : Bool) :
    star (edgeCreation k r r)*(T : Operator ι)*weightedDefectCreation u v i j=0 := by
  let a : edgeAlgebra u v i := T*⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩
  have hh := congrArg star (fresh_C_diagonal_edge u v i j k hji hjk (star a) r)
  simp only [star_mul,star_star,star_zero (Operator ι),StarMemClass.coe_star] at hh
  change star (edgeCreation k r r)*((T : Operator ι)*edgeDefect u v i)*C u v j=0 at hh
  calc
    _ = (star (edgeCreation k r r)*((T : Operator ι)*edgeDefect u v i)*C u v j)*edgeDefect u v i := by
      simp only [weightedDefectCreation,mul_assoc]
    _ = 0 := by rw [hh,zero_mul]

theorem weightedDefect_edge_root (u v : ℝ) (i j : ι) (hji : j≠i)
    (T : edgeAlgebra u v i) (r : Bool) :
    star (weightedDefectCreation u v i j) ((T : Operator ι) (lp.single 2 ([],r) 1))=0 := by
  let a : edgeAlgebra u v i := ⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩*T
  have hh := fresh_C_edge_root u v i j hji a r
  simp only [weightedDefectCreation,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
    mul_apply_eq_comp]
  change star (C u v j) (edgeDefect u v i ((T : Operator ι) (lp.single 2 ([],r) 1)))=0 at hh
  rw [hh,map_zero]

theorem diagonal_filled_contraction (u v : ℝ) (i j k l : ι) (hji : j≠i) (hjk : j≠k) (hjl : j≠l)
    (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (edgeCreation k r r)*(T : Operator ι)*edgeCreation l s s=
      (inner ℂ (lp.single 2 ([],r) 1) ((T : Operator ι) (lp.single 2 ([],s) 1))) •
        (if k=l ∧ r=s then vertex s else 0) := by
  apply GaussianExtension.covariance_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji)
    (edgeCreation k r r) (edgeCreation l s s) _ (lp.single 2 ([],r) 1) (lp.single 2 ([],s) 1)
    (fun a => weightedDefect_edge_root u v i j hji a r)
    (fun a => weightedDefect_edge_root u v i j hji a s)
    (fun a => diagonal_weightedDefect u v i j k hji hjk a r) _ _ (T : Operator ι) T.property
  · intro a
    have hh := congrArg star (diagonal_weightedDefect u v i j l hji hjl (star a) s)
    simpa only [star_mul,star_star,star_zero (Operator ι),StarMemClass.coe_star,mul_assoc] using hh
  · intro a
    have hh := diagonal_edge_contraction u v i k l a r s
    split_ifs with h
    · simpa [h,lp.inner_single_left] using hh
    · simpa only [h,ite_false,smul_zero] using hh

theorem diagonal_filled_annihilation (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (r : Bool) (T : filledEdgeAlgebra u v i j) :
    star (edgeCreation k r r) ((T : Operator ι) (vacuum u v))=0 := by
  apply GaussianExtension.annihilation_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji)
    (edgeCreation k r r) (vacuum u v) (weightedDefect_annihilates_edge u v i j hji) _
    (fun a => diagonal_weightedDefect u v i j k hji hjk a r) T T.property
  intro a
  simp only [vacuum,map_add,map_smul,diagonal_annihilation_edge_root u v i k a,
    smul_zero,add_zero]
end

open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem vertex_trace_inner (u v : ℝ) (r : Bool) (T : Operator ι) :
    vacuumTrace u v (vertex r*T*vertex r)=
      (weight u v r : ℂ)^2*inner ℂ (lp.single 2 ([],r) 1) (T (lp.single 2 ([],r) 1)) := by
  unfold vacuumTrace
  simp only [mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (vertex r) (vacuum u v)) (T (vertex r (vacuum u v)))=_
  rw [vertex_star,vertex_vacuum]
  simp only [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal,pow_two,mul_assoc]

theorem supportedLeg_vertex (u v : ℝ) (i : ι) (r : Bool) :
    supportedLeg u v i r*vertex (!r)=supportedLeg u v i r := by
  cases r
  · exact projection_P.isIdempotentElem.eq
  · exact edgePolar_right u v i

theorem vertex_star_supportedLeg (u v : ℝ) (i : ι) (r : Bool) :
    vertex (!r)*star (supportedLeg u v i r)=star (supportedLeg u v i r) := by
  simpa only [star_mul,vertex_star] using congrArg star (supportedLeg_vertex u v i r)

theorem supportedLeg_root_trace (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (r : Bool) (T : ambientAlgebra (ι := ι) u v) :
    (weight u v (!r) : ℂ)^2*inner ℂ (lp.single 2 ([],!r) 1)
        ((star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r) (lp.single 2 ([],!r) 1))=
      vacuumTrace u v ((T : Operator ι)*legSupport u v i r) := by
  rw [← vertex_trace_inner]
  rw [← mul_assoc,← mul_assoc,vertex_star_supportedLeg,mul_assoc _ _ (vertex (!r)),supportedLeg_vertex]
  simpa only [ite_true] using supportedLeg_trace_covariance u v hu hv i r r T

def transportedDiagonal (u v : ℝ) (i k : ι) (r : Bool) : Operator ι :=
  supportedLeg u v i r*edgeCreation k (!r) (!r)*star (supportedLeg u v i r)

def normalizedDiagonal (u v : ℝ) (i k : ι) (r : Bool) : Operator ι :=
  ((weight u v (!r) : ℂ)/(u:ℂ)) • transportedDiagonal u v i k r

theorem transportedDiagonal_filled_contraction (u v : ℝ) (i j k l : ι)
    (hji : j≠i) (hjk : j≠k) (hjl : j≠l) (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (transportedDiagonal u v i k r)*(T : Operator ι)*transportedDiagonal u v i l s=
      if k=l ∧ r=s then (inner ℂ (lp.single 2 ([],!r) 1)
        ((star (supportedLeg u v i r)*(T : Operator ι)*supportedLeg u v i r) (lp.single 2 ([],!r) 1))) •
          legSupport u v i r else 0 := by
  let a (b : Bool) : filledEdgeAlgebra u v i j :=
    ⟨supportedLeg u v i b,edgeAlgebra_le_filled u v i j (supportedLeg_mem_edge u v i b)⟩
  have h := diagonal_filled_contraction u v i j k l hji hjk hjl (!r) (!s) (star (a r)*T*a s)
  calc
    _ = supportedLeg u v i r*(star (edgeCreation k (!r) (!r))*
        ((star (a r)*T*a s : filledEdgeAlgebra u v i j) : Operator ι)*edgeCreation l (!s) (!s))*
        star (supportedLeg u v i s) := by
      simp only [transportedDiagonal,StarMemClass.coe_star,MulMemClass.coe_mul,star_mul,star_star,mul_assoc]
      rfl
    _ = _ := by
      rw [h]
      by_cases hr : r=s
      · subst s
        by_cases hk : k=l
        · simp only [hk,ite_true,true_and,mul_smul_comm,smul_mul_assoc,supportedLeg_vertex,
            supportedLeg_mul_star]
          rfl
        · simp only [hk,false_and,ite_false,smul_zero (M := ℂ) (A := Operator ι),mul_zero,zero_mul]
      · have hr' : (!r)≠(!s) := by cases r <;> cases s <;> simp_all
        simp only [hr,hr',and_false,ite_false,smul_zero (M := ℂ) (A := Operator ι),mul_zero,zero_mul]

theorem normalizedDiagonal_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j k l : ι) (hji : j≠i) (hjk : j≠k) (hjl : j≠l)
    (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (normalizedDiagonal u v i k r)*(T : Operator ι)*normalizedDiagonal u v i l s=
      if k=l ∧ r=s then pVacuumTrace u v ((T : Operator ι)*legSupport u v i r) • legSupport u v i r else 0 := by
  simp only [normalizedDiagonal,star_smul,Complex.star_def,map_div₀,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm]
  rw [transportedDiagonal_filled_contraction u v i j k l hji hjk hjl]
  by_cases h : k=l ∧ r=s
  · obtain ⟨hk,hrs⟩ := h
    subst l;subst s
    simp only [and_self,ite_true,smul_smul]
    congr 1
    unfold pVacuumTrace
    rw [← supportedLeg_root_trace u v hu hv i r ⟨T,filledEdgeAlgebra_le_ambient u v i j T.property⟩]
    ring
  · simp only [h,ite_false,smul_zero (M := ℂ) (A := Operator ι)]
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.GaussianSplit
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (C : E →L[ℂ] E) (Ω : E)
variable (hC : ∀ a : B,star C*(a : E →L[ℂ] E)*C=(inner ℂ Ω ((a : E →L[ℂ] E) Ω)) • 1)
variable (hΩ : ∀ a : B,star C ((a : E →L[ℂ] E) Ω)=0)
variable (d : B) (hd : IsStarProjection d) (hcentral : ∀ a : B,Commute d a)

def cut (r : Bool) : B := if r then d else 1-d

include hd in
theorem cut_star (r : Bool) : star (cut B d r)=cut B d r := by
  cases r <;> simp only [cut,Bool.false_eq_true,ite_false,ite_true,star_sub (R := B),star_one,hd.isSelfAdjoint.star_eq]

include hd in
theorem cut_d (r : Bool) : cut B d r*d=if r then d else 0 := by
  cases r <;> simp only [cut,Bool.false_eq_true,ite_false,ite_true,sub_mul,one_mul,hd.isIdempotentElem.eq,sub_self]

include hd hcentral in
theorem cut_false_a_d (a : B) : cut B d false*a*d=0 := by
  rw [mul_assoc,← (hcentral a).eq,← mul_assoc,cut_d B d hd]
  simp only [Bool.false_eq_true,ite_false,zero_mul]

def block (r s : Bool) : E →L[ℂ] E := (cut B d r : E →L[ℂ] E)*C*(cut B d s : E →L[ℂ] E)

def D : E →L[ℂ] E := (d : E →L[ℂ] E)*C*(d : E →L[ℂ] E)

def covariance (a : B) : B := (inner ℂ Ω (((d*a*d : B) : E →L[ℂ] E) Ω)) • d

include hC hd in
theorem D_contraction (a : B) : star (D B C d)*(a : E →L[ℂ] E)*D B C d=
    (covariance B Ω d a : E →L[ℂ] E) := by
  have he := hC (d*a*d)
  have hs : star (d : E →L[ℂ] E)=(d : E →L[ℂ] E) := congrArg Subtype.val hd.isSelfAdjoint.star_eq
  have hid : (d : E →L[ℂ] E)*(d : E →L[ℂ] E)=(d : E →L[ℂ] E) := congrArg Subtype.val hd.isIdempotentElem.eq
  change star C*((d : E →L[ℂ] E)*(a : E →L[ℂ] E)*(d : E →L[ℂ] E))*C=_ at he
  calc
    _ = (d : E →L[ℂ] E)*(star C*((d : E →L[ℂ] E)*(a : E →L[ℂ] E)*(d : E →L[ℂ] E))*C)*(d : E →L[ℂ] E) := by
      simp only [D,star_mul,hs,mul_assoc]
    _ = _ := by rw [he,mul_smul_comm,smul_mul_assoc,mul_one,hid];rfl

include hΩ hd in
theorem D_annihilation (a : B) : star (D B C d) ((a : E →L[ℂ] E) Ω)=0 := by
  have he := hΩ (d*a)
  have hs : star (d : E →L[ℂ] E)=(d : E →L[ℂ] E) := congrArg Subtype.val hd.isSelfAdjoint.star_eq
  simp only [D,star_mul,hs,mul_apply_eq_comp]
  change star C ((d : E →L[ℂ] E) ((a : E →L[ℂ] E) Ω))=0 at he
  rw [he,map_zero]

include hC hd in
theorem block_contraction (r s r' s' : Bool) (a : B) :
    star (block B C d r s)*(a : E →L[ℂ] E)*block B C d r' s'=
      (inner ℂ ((cut B d r : E →L[ℂ] E) Ω)
        ((a : E →L[ℂ] E) ((cut B d r' : E →L[ℂ] E) Ω))) •
        ((cut B d s : E →L[ℂ] E)*(cut B d s' : E →L[ℂ] E)) := by
  have hs (r) : star (cut B d r : E →L[ℂ] E)=(cut B d r : E →L[ℂ] E) :=
    congrArg Subtype.val (cut_star B d hd r)
  have he := hC (cut B d r*a*cut B d r')
  change star C*((cut B d r : E →L[ℂ] E)*(a : E →L[ℂ] E)*(cut B d r' : E →L[ℂ] E))*C=_ at he
  calc
    _ = (cut B d s : E →L[ℂ] E)*
        (star C*((cut B d r : E →L[ℂ] E)*(a : E →L[ℂ] E)*(cut B d r' : E →L[ℂ] E))*C)*
        (cut B d s' : E →L[ℂ] E) := by simp only [block,star_mul,hs,mul_assoc]
    _ = _ := by
      rw [he,mul_smul_comm,smul_mul_assoc,mul_one]
      congr 1
      change inner ℂ Ω ((cut B d r : E →L[ℂ] E) ((a : E →L[ℂ] E) ((cut B d r' : E →L[ℂ] E) Ω)))=_
      rw [← ContinuousLinearMap.adjoint_inner_left]
      change inner ℂ ((star (cut B d r : E →L[ℂ] E)) Ω) _=_
      rw [hs r]

include hΩ hd in
theorem block_annihilation (r s : Bool) (a : B) : star (block B C d r s) ((a : E →L[ℂ] E) Ω)=0 := by
  have he := hΩ (cut B d r*a)
  have hs (r) : star (cut B d r : E →L[ℂ] E)=(cut B d r : E →L[ℂ] E) :=
    congrArg Subtype.val (cut_star B d hd r)
  simp only [block,star_mul,hs,mul_apply_eq_comp]
  change star C ((cut B d r : E →L[ℂ] E) ((a : E →L[ℂ] E) Ω))=0 at he
  rw [he,map_zero]

include hC hd hcentral in
theorem block_D (r s : Bool) (hrs : ¬(r=true ∧ s=true)) (a : B) :
    star (block B C d r s)*(a : E →L[ℂ] E)*D B C d=0 := by
  have he := block_contraction B C Ω hC d hd r s true true a
  change star (block B C d r s)*(a : E →L[ℂ] E)*D B C d=
    (inner ℂ ((cut B d r : E →L[ℂ] E) Ω)
      ((a : E →L[ℂ] E) ((d : E →L[ℂ] E) Ω))) •
      ((cut B d s : E →L[ℂ] E)*(d : E →L[ℂ] E)) at he
  rw [he]
  cases s with
  | false =>
    have hz : (cut B d false : E →L[ℂ] E)*(d : E →L[ℂ] E)=0 :=
      congrArg Subtype.val (cut_d B d hd false)
    rw [hz,smul_zero (M := ℂ) (A := E →L[ℂ] E)]
  | true =>
    have hr : r=false := by cases r <;> simp_all
    subst r
    have hz := congrArg Subtype.val (cut_false_a_d B d hd hcentral a)
    change (cut B d false : E →L[ℂ] E)*(a : E →L[ℂ] E)*(d : E →L[ℂ] E)=0 at hz
    have hs : star (cut B d false : E →L[ℂ] E)=(cut B d false : E →L[ℂ] E) :=
      congrArg Subtype.val (cut_star B d hd false)
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ Ω ((star (cut B d false : E →L[ℂ] E)*(a : E →L[ℂ] E)*(d : E →L[ℂ] E)) Ω) • _=0
    rw [hs,hz,zero_apply,inner_zero_right,zero_smul ℂ (A := E →L[ℂ] E)]

def filled : StarSubalgebra ℂ (E →L[ℂ] E) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
    (insert (D B C d+star (D B C d)) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))

include hC hΩ hd hcentral in

theorem residual_covariance (r s r' s' : Bool) (hrs : ¬(r=true ∧ s=true))
    (hrs' : ¬(r'=true ∧ s'=true)) (T : filled B C d) :
    star (block B C d r s)*(T : E →L[ℂ] E)*block B C d r' s'=
      (inner ℂ ((cut B d r : E →L[ℂ] E) Ω)
        ((T : E →L[ℂ] E) ((cut B d r' : E →L[ℂ] E) Ω))) •
        ((cut B d s : E →L[ℂ] E)*(cut B d s' : E →L[ℂ] E)) := by
  apply GaussianExtension.covariance_extension B (D B C d) (covariance B Ω d)
    (D_contraction B C Ω hC d hd) (block B C d r s) (block B C d r' s') _
    ((cut B d r : E →L[ℂ] E) Ω) ((cut B d r' : E →L[ℂ] E) Ω)
    (fun a => D_annihilation B C Ω hΩ d hd (a*cut B d r))
    (fun a => D_annihilation B C Ω hΩ d hd (a*cut B d r'))
    (block_D B C Ω hC d hd hcentral r s hrs) _
    (block_contraction B C Ω hC d hd r s r' s') (T : E →L[ℂ] E) T.property
  intro a
  have he := congrArg star (block_D B C Ω hC d hd hcentral r' s' hrs' (star a))
  simpa only [star_mul,star_star,star_zero (E →L[ℂ] E),StarMemClass.coe_star,mul_assoc] using he

include hC hΩ hd hcentral in
theorem residual_annihilation (r s : Bool) (hrs : ¬(r=true ∧ s=true)) (T : filled B C d) :
    star (block B C d r s) ((T : E →L[ℂ] E) Ω)=0 :=
  GaussianExtension.annihilation_extension B (D B C d) (covariance B Ω d)
    (D_contraction B C Ω hC d hd) (block B C d r s) Ω
    (D_annihilation B C Ω hΩ d hd) (block_annihilation B C Ω hΩ d hd r s)
    (block_D B C Ω hC d hd hcentral r s hrs) T T.property
end FreeGroupFactorMain.GaussianSplit

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem edgeDefect_commute (u v : ℝ) (i : ι) (T : edgeAlgebra u v i) :
    Commute (edgeDefect u v i) (T : Operator ι) := by
  have hl (a : edgeAlgebra u v i) :
      edgeDefect u v i*(a : Operator ι)*edgeDefect u v i=(a : Operator ι)*edgeDefect u v i := by
    obtain ⟨c,hc⟩ := edge_algebra_scalar_on_defect u v i a
    rw [mul_assoc,hc,mul_smul_comm,(edgeDefect_projection u v i).isIdempotentElem.eq]
  have hr := congrArg star (hl (star T))
  simp only [star_mul,StarMemClass.coe_star,star_star,
    (edgeDefect_projection u v i).isSelfAdjoint.star_eq,← mul_assoc] at hr
  exact hr.symm.trans (hl T)

def defectAsEdge (u v : ℝ) (i : ι) : edgeAlgebra u v i :=
  ⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩

theorem defectAsEdge_projection (u v : ℝ) (i : ι) : IsStarProjection (defectAsEdge u v i) := by
  constructor
  · apply Subtype.ext
    exact (edgeDefect_projection u v i).isIdempotentElem.eq
  · apply Subtype.ext
    exact (edgeDefect_projection u v i).isSelfAdjoint.star_eq

theorem defectAsEdge_central (u v : ℝ) (i : ι) (a : edgeAlgebra u v i) :
    Commute (defectAsEdge u v i) a := Subtype.ext (edgeDefect_commute u v i a).eq

theorem fresh_C_edge_contraction (u v : ℝ) (i j : ι) (hji : j≠i) (a : edgeAlgebra u v i) :
    star (C u v j)*(a : Operator ι)*C u v j=
      (inner ℂ (vacuum u v) ((a : Operator ι) (vacuum u v))) • 1 := by
  have hh := fresh_C_contraction u v {i} j j hji hji
    ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩
  simpa only [ite_true,vacuumTrace] using hh

theorem fresh_C_edge_annihilation (u v : ℝ) (i j : ι) (hji : j≠i) (a : edgeAlgebra u v i) :
    star (C u v j) ((a : Operator ι) (vacuum u v))=0 :=
  fresh_C_annihilates_old_vacuum u v {i} j hji
    ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩

def splitCut (u v : ℝ) (i : ι) (b : Bool) : Operator ι :=
  GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) b

def splitBlock (u v : ℝ) (i j : ι) (r s : Bool) : Operator ι :=
  GaussianSplit.block (edgeAlgebra u v i) (C u v j) (defectAsEdge u v i) r s

theorem splitBlock_filled_covariance (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s r' s' : Bool) (hrs : ¬(r=true ∧ s=true)) (hrs' : ¬(r'=true ∧ s'=true))
    (T : filledEdgeAlgebra u v i j) :
    star (splitBlock u v i j r s)*(T : Operator ι)*splitBlock u v i j r' s'=
      (inner ℂ (splitCut u v i r (vacuum u v))
        ((T : Operator ι) (splitCut u v i r' (vacuum u v)))) •
        (splitCut u v i s*splitCut u v i s') :=
  GaussianSplit.residual_covariance (edgeAlgebra u v i) (C u v j) (vacuum u v)
    (fresh_C_edge_contraction u v i j hji) (fresh_C_edge_annihilation u v i j hji)
    (defectAsEdge u v i) (defectAsEdge_projection u v i) (defectAsEdge_central u v i)
    r s r' s' hrs hrs' T

theorem splitBlock_filled_annihilation (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s : Bool) (hrs : ¬(r=true ∧ s=true)) (T : filledEdgeAlgebra u v i j) :
    star (splitBlock u v i j r s) ((T : Operator ι) (vacuum u v))=0 :=
  GaussianSplit.residual_annihilation (edgeAlgebra u v i) (C u v j) (vacuum u v)
    (fresh_C_edge_contraction u v i j hji) (fresh_C_edge_annihilation u v i j hji)
    (defectAsEdge u v i) (defectAsEdge_projection u v i) (defectAsEdge_central u v i)
    r s hrs T

theorem splitCut_selfAdjoint (u v : ℝ) (i : ι) (b : Bool) : IsSelfAdjoint (splitCut u v i b) :=
  congrArg Subtype.val (GaussianSplit.cut_star (edgeAlgebra u v i) (defectAsEdge u v i)
    (defectAsEdge_projection u v i) b)

end

open FreeFock
variable {ι : Type u_3} [DecidableEq ι]

def residualLeg (u v : ℝ) (i : ι) : Option Bool → Operator ι
  | none => edgeDefect u v i
  | some false => edgeRange u v i
  | some true => edgePolar u v i

def residualSupport (u v : ℝ) (i : ι) : Option Bool → Operator ι
  | none => edgeDefect u v i
  | some _ => edgeRange u v i

def residualCut : Option Bool → Bool
  | none => true
  | some _ => false

theorem residualLeg_mem_edge (u v : ℝ) (i : ι) (r : Option Bool) :
    residualLeg u v i r∈edgeAlgebra u v i := by
  cases r with
  | none => exact edgeDefect_mem_edge u v i
  | some r => cases r
              · exact edgeRange_mem_edge u v i
              · exact edgePolar_mem_edge u v i

theorem P_mul_residualLeg (u v : ℝ) (i : ι) (r : Option Bool) :
    P*residualLeg u v i r=residualLeg u v i r := by
  cases r with
  | none => exact P_mul_edgeDefect u v i
  | some r => cases r
              · exact edgeRange_le_P u v i
              · exact edgePolar_left u v i

theorem edgePolar_mul_defect (u v : ℝ) (i : ι) : edgePolar u v i*edgeDefect u v i=0 := by
  rw [← P_mul_edgeDefect u v i,← mul_assoc,edgePolar_mul_P,zero_mul]

theorem edgePolar_mul_range (u v : ℝ) (i : ι) : edgePolar u v i*edgeRange u v i=0 := by
  rw [← edgeRange_le_P u v i,← mul_assoc,edgePolar_mul_P,zero_mul]

theorem defect_mul_star_edgePolar (u v : ℝ) (i : ι) :
    edgeDefect u v i*star (edgePolar u v i)=0 := by
  simpa only [star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,star_zero (Operator ι)]
    using congrArg star (edgePolar_mul_defect u v i)

theorem range_mul_star_edgePolar (u v : ℝ) (i : ι) :
    edgeRange u v i*star (edgePolar u v i)=0 := by
  simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq,star_zero (Operator ι)]
    using congrArg star (edgePolar_mul_range u v i)

theorem residualLeg_mul_star (u v : ℝ) (i : ι) (r s : Option Bool) :
    residualLeg u v i r*star (residualLeg u v i s)=
      if r=s then residualSupport u v i r else 0 := by
  rcases r with _ | (_ | _) <;> rcases s with _ | (_ | _)
  all_goals simp only [residualLeg,residualSupport,Option.some.injEq,Option.some_ne_none,
      reduceCtorEq,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
  · rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq]
    exact (edgeDefect_projection u v i).isIdempotentElem.eq
  · rw [(edgeRange_projection u v i).isSelfAdjoint.star_eq,defect_mul_edgeRange]
  · exact defect_mul_star_edgePolar u v i
  · rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq,edgeRange_mul_defect]
  · rw [(edgeRange_projection u v i).isSelfAdjoint.star_eq]
    exact (edgeRange_projection u v i).isIdempotentElem.eq
  · exact range_mul_star_edgePolar u v i
  · rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq,edgePolar_mul_defect]
  · rw [(edgeRange_projection u v i).isSelfAdjoint.star_eq,edgePolar_mul_range]
  · rfl

theorem residualLeg_cut (u v : ℝ) (i : ι) (r : Option Bool) :
    residualLeg u v i r*splitCut u v i (residualCut r)=residualLeg u v i r := by
  rcases r with _ | (_ | _)
  · exact (edgeDefect_projection u v i).isIdempotentElem.eq
  · change edgeRange u v i*(1-edgeDefect u v i)=edgeRange u v i
    rw [mul_sub,mul_one,edgeRange_mul_defect,sub_zero]
  · change edgePolar u v i*(1-edgeDefect u v i)=edgePolar u v i
    rw [mul_sub,mul_one,edgePolar_mul_defect,sub_zero]

theorem cut_star_residualLeg (u v : ℝ) (i : ι) (r : Option Bool) :
    splitCut u v i (residualCut r)*star (residualLeg u v i r)=star (residualLeg u v i r) := by
  simpa only [star_mul,(splitCut_selfAdjoint u v i (residualCut r)).star_eq]
    using congrArg star (residualLeg_cut u v i r)

theorem residualLeg_trace_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (r s : Option Bool) (T : ambientAlgebra (ι := ι) u v) :
    vacuumTrace u v (star (residualLeg u v i r)*(T : Operator ι)*residualLeg u v i s)=
      if r=s then vacuumTrace u v ((T : Operator ι)*residualSupport u v i r) else 0 := by
  have ht := ambient_trace_mul u v hu hv
    ⟨star (residualLeg u v i r),star_mem (edgeAlgebra_le_ambient u v i (residualLeg_mem_edge u v i r))⟩
    (T*⟨residualLeg u v i s,edgeAlgebra_le_ambient u v i (residualLeg_mem_edge u v i s)⟩)
  change vacuumTrace u v (star (residualLeg u v i r)*((T : Operator ι)*residualLeg u v i s))=
    vacuumTrace u v (((T : Operator ι)*residualLeg u v i s)*star (residualLeg u v i r)) at ht
  rw [mul_assoc,ht,mul_assoc,residualLeg_mul_star]
  by_cases h : r=s
  · subst s; simp only [ite_true]
  · simp only [h,Ne.symm h,ite_false,mul_zero,vacuumTrace,zero_apply,inner_zero_right]

def residualCreation (u v : ℝ) (i j : ι) (r s : Option Bool) : Operator ι :=
  residualLeg u v i r*C u v j*star (residualLeg u v i s)

theorem residualCreation_split (u v : ℝ) (i j : ι) (r s : Option Bool) :
    residualCreation u v i j r s=
      residualLeg u v i r*splitBlock u v i j (residualCut r) (residualCut s)*star (residualLeg u v i s) := by
  change _=residualLeg u v i r*(splitCut u v i (residualCut r)*C u v j*
    splitCut u v i (residualCut s))*star (residualLeg u v i s)
  simp only [mul_assoc]
  rw [cut_star_residualLeg]
  rw [← mul_assoc, residualLeg_cut]
  rfl

theorem residual_allowed (r s : Option Bool) (h : ¬(r=none ∧ s=none)) :
    ¬(residualCut r=true ∧ residualCut s=true) := by
  rcases r with _ | (_ | _) <;> rcases s with _ | (_ | _) <;> simp_all [residualCut]

theorem residualCreation_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j : ι) (hji : j≠i) (r s r' s' : Option Bool)
    (hrs : ¬(r=none ∧ s=none)) (hrs' : ¬(r'=none ∧ s'=none))
    (T : filledEdgeAlgebra u v i j) :
    star (residualCreation u v i j r s)*(T : Operator ι)*residualCreation u v i j r' s'=
      if r=r' ∧ s=s' then
        vacuumTrace u v ((T : Operator ι)*residualSupport u v i r) • residualSupport u v i s else 0 := by
  let a (t : Option Bool) : filledEdgeAlgebra u v i j :=
    ⟨residualLeg u v i t,edgeAlgebra_le_filled u v i j (residualLeg_mem_edge u v i t)⟩
  have hc := splitBlock_filled_covariance u v i j hji (residualCut r) (residualCut s)
    (residualCut r') (residualCut s') (residual_allowed r s hrs) (residual_allowed r' s' hrs')
    (star (a r)*T*a r')
  have hi : inner ℂ (splitCut u v i (residualCut r) (vacuum u v))
      (((star (a r)*T*a r' : filledEdgeAlgebra u v i j) : Operator ι)
        (splitCut u v i (residualCut r') (vacuum u v)))=
      vacuumTrace u v (star (residualLeg u v i r)*(T : Operator ι)*residualLeg u v i r') := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (vacuum u v) ((star (splitCut u v i (residualCut r))*
      (star (residualLeg u v i r)*(T : Operator ι)*residualLeg u v i r')*
      splitCut u v i (residualCut r')) (vacuum u v))=_
    rw [(splitCut_selfAdjoint u v i (residualCut r)).star_eq]
    simp only [← mul_assoc,cut_star_residualLeg]
    rw [mul_assoc _ _ (splitCut u v i (residualCut r')),residualLeg_cut]
    rfl
  rw [hi] at hc
  calc
    _ = residualLeg u v i s*(star (splitBlock u v i j (residualCut r) (residualCut s))*
        (star (residualLeg u v i r)*(T : Operator ι)*residualLeg u v i r')*
        splitBlock u v i j (residualCut r') (residualCut s'))*star (residualLeg u v i s') := by
      rw [residualCreation_split,residualCreation_split]
      simp only [star_mul,star_star,mul_assoc]
    _ = _ := by
      change (residualLeg u v i s*(star (splitBlock u v i j (residualCut r) (residualCut s))*
        ((star (a r)*T*a r' : filledEdgeAlgebra u v i j) : Operator ι)*
        splitBlock u v i j (residualCut r') (residualCut s'))*star (residualLeg u v i s'))=_
      rw [hc,mul_smul_comm,smul_mul_assoc]
      rw [← mul_assoc,mul_assoc _ (splitCut u v i (residualCut s')),
        cut_star_residualLeg,residualLeg_cut,residualLeg_mul_star]
      rw [residualLeg_trace_covariance u v hu hv i r r'
        ⟨T,filledEdgeAlgebra_le_ambient u v i j T.property⟩]
      by_cases hr : r=r' <;> by_cases hs : s=s' <;>
        simp only [hr,hs,ite_true,ite_false,zero_smul ℂ (A := Operator ι),
          smul_zero (M := ℂ) (A := Operator ι),true_and,false_and,and_false]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

theorem residualCreation_filled_annihilation (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s : Option Bool) (hrs : ¬(r=none ∧ s=none)) (T : filledEdgeAlgebra u v i j) :
    star (residualCreation u v i j r s) ((T : Operator ι) (vacuum u v))=0 := by
  let a : filledEdgeAlgebra u v i j :=
    ⟨star (residualLeg u v i r),star_mem
      (edgeAlgebra_le_filled u v i j (residualLeg_mem_edge u v i r))⟩*T
  have hh := splitBlock_filled_annihilation u v i j hji (residualCut r) (residualCut s)
    (residual_allowed r s hrs) a
  rw [residualCreation_split]
  simp only [star_mul,star_star,mul_apply_eq_comp]
  change residualLeg u v i s (star (splitBlock u v i j (residualCut r) (residualCut s))
    ((a : Operator ι) (vacuum u v)))=0
  rw [hh,map_zero]

def normalizedResidual (u v : ℝ) (i j : ι) (r s : Option Bool) : Operator ι :=
  (u:ℂ)⁻¹ • residualCreation u v i j r s

end FreeGroupFactorMain.WeightedFock

section
namespace FreeGroupFactorMain.GaussianExtension
variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (D : E →L[ℂ] E)
variable (κ : B → B) (hκ : ∀ a : B,star D*(a : E →L[ℂ] E)*D=(κ a : E →L[ℂ] E))

end FreeGroupFactorMain.GaussianExtension

namespace FreeGroupFactorMain.GaussianOrthogonal
variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

variable {B : StarSubalgebra ℂ A} {L R : A}

end FreeGroupFactorMain.GaussianOrthogonal
namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianOrthogonal
variable {ι : Type u_4} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.GaussianOrthogonal
variable {A : Type u_5} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {B : StarSubalgebra ℂ A} {L R : A}

end FreeGroupFactorMain.GaussianOrthogonal

namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianOrthogonal
variable {ι : Type u_6} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


