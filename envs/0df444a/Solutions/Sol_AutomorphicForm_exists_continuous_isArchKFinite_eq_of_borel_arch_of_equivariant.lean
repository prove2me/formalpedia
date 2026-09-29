-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4d5fcdf0-b80b-5865-987f-1ecb1d730008

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm
open AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

noncomputable section

namespace SectConC1

section Local

variable {L : Type*} [NormedField L]

theorem norm_diag_eq_one_of_isRowIsometry (m : GL (Fin 2) L)
    (h10 : (m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hm : IsRowIsometry m) :
    ‖(m : Matrix (Fin 2) (Fin 2) L) 0 0‖ = 1 ∧ ‖(m : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
  obtain ⟨hdet, hrow⟩ := hm
  have h := hrow 0 1
  rw [zero_mul, one_mul, zero_add, zero_mul, one_mul, zero_add, norm_zero, norm_one, one_pow,
    zero_pow two_ne_zero, zero_add, h10, norm_zero, zero_pow two_ne_zero, zero_add] at h
  have h11 : ‖(m : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
    have h' := Real.sqrt_sq (norm_nonneg ((m : Matrix (Fin 2) (Fin 2) L) 1 1))
    rw [h, Real.sqrt_one] at h'
    exact h'.symm
  refine ⟨?_, h11⟩
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero, norm_mul, h11, mul_one] at hdet
  exact hdet

end Local

theorem gl2_ext {R : Type*} [CommRing R] {A B : GL (Fin 2) R}
    (h00 : (A : Matrix (Fin 2) (Fin 2) R) 0 0 = (B : Matrix (Fin 2) (Fin 2) R) 0 0)
    (h01 : (A : Matrix (Fin 2) (Fin 2) R) 0 1 = (B : Matrix (Fin 2) (Fin 2) R) 0 1)
    (h10 : (A : Matrix (Fin 2) (Fin 2) R) 1 0 = (B : Matrix (Fin 2) (Fin 2) R) 1 0)
    (h11 : (A : Matrix (Fin 2) (Fin 2) R) 1 1 = (B : Matrix (Fin 2) (Fin 2) R) 1 1) : A = B :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j
    exacts [h00, h01, h10, h11]

variable (K : Type) [Field K] [NumberField K]

section ArchPart

def archP : (AdelicGL2 (𝓞 K) K) →* (AdelicGL2 (𝓞 K) K) := (adelicArchGLIncl K).comp (glArch (𝓞 K) K)

theorem archP_def (g : (AdelicGL2 (𝓞 K) K)) : archP K g = adelicArchGLIncl K (glArch (𝓞 K) K g) := rfl

theorem glArch_archP (g : (AdelicGL2 (𝓞 K) K)) : glArch (𝓞 K) K (archP K g) = glArch (𝓞 K) K g :=
  glArch_adelicArchGLIncl K _

theorem glFin_archP (g : (AdelicGL2 (𝓞 K) K)) : glFin (𝓞 K) K (archP K g) = 1 := glFin_adelicArchGLIncl K _

theorem archP_apply_fst (g : (AdelicGL2 (𝓞 K) K)) (i j : Fin 2) :
    (((archP K g : (AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 = (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).1 :=
  congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing K) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j)
    (glArch_archP K g)

theorem archP_apply_snd (g : (AdelicGL2 (𝓞 K) K)) (i j : Fin 2) :
    (((archP K g : (AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :=
  congrArg (fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j)
    (glFin_archP K g)

theorem eq_of_glArch_eq_of_glFin_eq {g g' : (AdelicGL2 (𝓞 K) K)} (h1 : glArch (𝓞 K) K g = glArch (𝓞 K) K g')
    (h2 : glFin (𝓞 K) K g = glFin (𝓞 K) K g') : g = g' := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing K) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h1
  · exact congrArg (fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h2

theorem archP_eq_of_glArch_eq {g g' : (AdelicGL2 (𝓞 K) K)} (h : glArch (𝓞 K) K g = glArch (𝓞 K) K g') :
    archP K g = archP K g' := by
  rw [archP_def, archP_def, h]

theorem archP_of_glFin_eq_one {g : (AdelicGL2 (𝓞 K) K)} (hg : glFin (𝓞 K) K g = 1) : archP K g = g :=
  eq_of_glArch_eq_of_glFin_eq K (glArch_archP K g) (by rw [glFin_archP, hg])

theorem archP_archP (g : (AdelicGL2 (𝓞 K) K)) : archP K (archP K g) = archP K g :=
  archP_of_glFin_eq_one K (glFin_archP K g)

theorem archComponent_archP (w : InfinitePlace K) (g : (AdelicGL2 (𝓞 K) K)) :
    archComponent K w (glArch (𝓞 K) K (archP K g)) = archComponent K w (glArch (𝓞 K) K g) := by
  rw [glArch_archP]

theorem archP_mem_borel {b : (AdelicGL2 (𝓞 K) K)} (hb : b ∈ adelicBorel (𝓞 K) K) : archP K b ∈ adelicBorel (𝓞 K) K := by
  rw [mem_borelSubgroup_iff] at hb ⊢
  refine Prod.ext ?_ ?_
  · rw [archP_apply_fst, hb]
  · rw [archP_apply_snd, Matrix.one_apply_ne (by decide)]; rfl

theorem continuous_archP : Continuous (archP K) := by
  have hval : ∀ g : AdelicGL2 (𝓞 K) K, ∀ i j : Fin 2,
      ((archP K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
        = (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1,
            (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :=
    fun g i j => Prod.ext (archP_apply_fst K g i j) (archP_apply_snd K g i j)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact (((Units.continuous_val.matrix_elem i j).fst).prodMk continuous_const).congr
      fun g => (hval g i j).symm
  · refine continuous_matrix fun i j => ?_
    have e1 : (fun a : AdelicGL2 (𝓞 K) K =>
        (((archP K a)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)
        = fun a => ((archP K a⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j :=
      funext fun a => by rw [map_inv]
    rw [e1]
    exact (((Units.continuous_coe_inv.matrix_elem i j).fst).prodMk continuous_const).congr
      fun g => (hval g⁻¹ i j).symm

end ArchPart

section ArchUnit

def archProj : (AdeleRing (𝓞 K) K) →* (AdeleRing (𝓞 K) K) where
  toFun x := (x.1, 1)
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (mul_one 1).symm

def archUnit : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (archProj K)

theorem archUnit_val_fst (t : (AdeleRing (𝓞 K) K)ˣ) : ((archUnit K t : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)).1 = (t : (AdeleRing (𝓞 K) K)).1 := rfl
theorem archUnit_val_snd (t : (AdeleRing (𝓞 K) K)ˣ) : ((archUnit K t : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)).2 = 1 := rfl

theorem archUnit_eq_self_of_snd_eq_one {t : (AdeleRing (𝓞 K) K)ˣ} (ht : (t : (AdeleRing (𝓞 K) K)).2 = 1) : archUnit K t = t :=
  Units.ext (Prod.ext rfl ht.symm)

theorem continuous_archUnit : Continuous (archUnit K) :=
  Continuous.units_map _ ((continuous_fst.prodMk continuous_const : Continuous fun x : (AdeleRing (𝓞 K) K) => ((x.1, (1 : FiniteAdeleRing (𝓞 K) K)) : (AdeleRing (𝓞 K) K))))

theorem borelDiagFst_archP {b : (AdelicGL2 (𝓞 K) K)} (hb : b ∈ adelicBorel (𝓞 K) K) :
    borelDiagFst (⟨archP K b, archP_mem_borel K hb⟩ : ↥(adelicBorel (𝓞 K) K)) =
      archUnit K (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) := by
  apply Units.ext
  refine Prod.ext ?_ ?_
  · exact archP_apply_fst K b 0 0
  · rw [borelDiagFst_apply_val, archUnit_val_snd]
    exact (archP_apply_snd K b 0 0).trans (Matrix.one_apply_eq 0)

theorem borelDiagSnd_archP {b : (AdelicGL2 (𝓞 K) K)} (hb : b ∈ adelicBorel (𝓞 K) K) :
    borelDiagSnd (⟨archP K b, archP_mem_borel K hb⟩ : ↥(adelicBorel (𝓞 K) K)) =
      archUnit K (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) := by
  apply Units.ext
  refine Prod.ext ?_ ?_
  · exact archP_apply_fst K b 1 1
  · rw [borelDiagSnd_apply_val, archUnit_val_snd]
    exact (archP_apply_snd K b 1 1).trans (Matrix.one_apply_eq 1)

theorem finprod_norm_one_apply :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((1 : FiniteAdeleRing (𝓞 K) K)) v‖ = 1 :=
  finprod_eq_one_of_forall_eq_one fun v => by
    change ‖(1 : v.adicCompletion K)‖ = 1
    exact norm_one

theorem distribHaarChar_eq_one_of_norm_eq_one (u : (AdeleRing (𝓞 K) K)ˣ) (hu2 : (u : (AdeleRing (𝓞 K) K)).2 = 1)
    (hu1 : ∀ w : InfinitePlace K, ‖(u : (AdeleRing (𝓞 K) K)).1 w‖ = 1) :
    (distribHaarChar (AdeleRing (𝓞 K) K) u : ℝ) = 1 := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, hu2, finprod_norm_one_apply,
    mul_one]
  exact Finset.prod_eq_one fun w _ => by rw [hu1 w, one_pow]

end ArchUnit

section Eta

variable (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
  (hαv : ∀ t, ((α t : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 K) K) t : ℝ)) (s : ℂ) (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

def eta (b : ↥(adelicBorel (𝓞 K) K)) : ℂ :=
  ((etaFst 1 α hα s (archUnit K (borelDiagFst b)) : ℂˣ) : ℂ) *
    ((etaSnd ν α hα s (archUnit K (borelDiagSnd b)) : ℂˣ) : ℂ)

theorem eta_mul (b c : ↥(adelicBorel (𝓞 K) K)) : eta K α hα s ν (b * c) = eta K α hα s ν b * eta K α hα s ν c := by
  unfold eta
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul]
  ring

theorem eta_one : eta K α hα s ν 1 = 1 := by
  unfold eta
  rw [map_one, map_one, map_one, map_one, map_one, map_one, Units.val_one, one_mul]

theorem eta_archP {b : (AdelicGL2 (𝓞 K) K)} (hb : b ∈ adelicBorel (𝓞 K) K) :
    eta K α hα s ν ⟨archP K b, archP_mem_borel K hb⟩ = eta K α hα s ν ⟨b, hb⟩ := by
  unfold eta
  rw [borelDiagFst_archP, borelDiagSnd_archP, ← MonoidHom.comp_apply (archUnit K) (archUnit K),
    ← MonoidHom.comp_apply (archUnit K) (archUnit K)]
  rfl

include hαv in

theorem eta_eq_nu_of_isRowIsometry {m : (AdelicGL2 (𝓞 K) K)} (hm : m ∈ adelicBorel (𝓞 K) K)
    (hiso : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) :
    eta K α hα s ν ⟨m, hm⟩ = ((ν (archUnit K (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K)))) : ℂˣ) : ℂ) := by
  have h10' : (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hm
  have hdiag : ∀ w : InfinitePlace K,
      ‖(((m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0)).1 w‖ = 1 ∧
        ‖(((m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1)).1 w‖ = 1 := by
    intro w
    have h10 : ((archComponent K w (glArch (𝓞 K) K m) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
      rw [archComponent_apply, glArch_apply, h10']
      rfl
    exact norm_diag_eq_one_of_isRowIsometry _ h10 (hiso w)
  have hα1 : ((α (archUnit K (borelDiagFst (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K)))) : ℝˣ) : ℝ) = 1 := by
    rw [hαv]
    exact distribHaarChar_eq_one_of_norm_eq_one K _ (archUnit_val_snd K _) (fun w => (hdiag w).1)
  have hα2 : ((α (archUnit K (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K)))) : ℝˣ) : ℝ) = 1 := by
    rw [hαv]
    exact distribHaarChar_eq_one_of_norm_eq_one K _ (archUnit_val_snd K _) (fun w => (hdiag w).2)
  unfold eta
  rw [etaFst, etaSnd, MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul,
    MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val, cpowChar_apply_val, hα1, hα2,
    Complex.ofReal_one, Complex.one_cpow, Complex.one_cpow, one_mul, mul_one]

include hαv in

theorem alpha_archUnit_eq (t : (AdeleRing (𝓞 K) K)ˣ) :
    ((α (archUnit K t) : ℝˣ) : ℝ) =
      ∏ w : InfinitePlace K, ‖((t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult := by
  rw [hαv, NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, archUnit_val_snd,
    finprod_norm_one_apply, mul_one]
  rfl

include hαv in
theorem continuous_alpha_archUnit :
    Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => ((α (archUnit K t) : ℝˣ) : ℝ) := by
  simp_rw [alpha_archUnit_eq K α hαv]
  exact continuous_finsetProd _ fun w _ =>
    (((continuous_apply w).comp (continuous_fst.comp Units.continuous_val)).norm).pow _

include hαv in
theorem continuous_etaFst_archUnit :
    Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => ((etaFst 1 α hα s (archUnit K t) : ℂˣ) : ℂ) := by
  have e : (fun t : (AdeleRing (𝓞 K) K)ˣ => ((etaFst 1 α hα s (archUnit K t) : ℂˣ) : ℂ))
      = fun t => ((((α (archUnit K t) : ℝˣ) : ℝ)) : ℂ) ^ (s + 1 / 2) := by
    funext t
    rw [etaFst, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]
  rw [e]
  exact (Complex.continuous_ofReal.comp (continuous_alpha_archUnit K α hαv)).cpow continuous_const
    fun t => Complex.ofReal_mem_slitPlane.mpr (hα _)

include hαv in
theorem continuous_etaSnd_archUnit (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) :
    Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => ((etaSnd ν α hα s (archUnit K t) : ℂˣ) : ℂ) := by
  have e : (fun t : (AdeleRing (𝓞 K) K)ˣ => ((etaSnd ν α hα s (archUnit K t) : ℂˣ) : ℂ))
      = fun t => ((ν (archUnit K t) : ℂˣ) : ℂ) * ((((α (archUnit K t) : ℝˣ) : ℝ)) : ℂ) ^ (-(s + 1 / 2)) := by
    funext t
    rw [etaSnd, MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val]
  rw [e]
  exact (hνc.comp (continuous_archUnit K)).mul
    ((Complex.continuous_ofReal.comp (continuous_alpha_archUnit K α hαv)).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.mpr (hα _))

end Eta

section Choice

def Kset : Set (AdelicGL2 (𝓞 K) K) :=
  {k | glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
    ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))}

theorem mem_Kset_iff {k : (AdelicGL2 (𝓞 K) K)} : k ∈ Kset K ↔ glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
    ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k)) := Iff.rfl

theorem mul_mem_Kset {k k' : (AdelicGL2 (𝓞 K) K)} (hk : k ∈ Kset K) (hk' : k' ∈ Kset K) : k * k' ∈ Kset K :=
  ⟨by rw [map_mul]; exact mul_mem hk.1 hk'.1, fun w => by rw [map_mul, map_mul]; exact (hk.2 w).mul (hk'.2 w)⟩

theorem inv_mem_Kset {k : (AdelicGL2 (𝓞 K) K)} (hk : k ∈ Kset K) : k⁻¹ ∈ Kset K :=
  ⟨by rw [map_inv]; exact inv_mem hk.1, fun w => by rw [map_inv, map_inv]; exact (hk.2 w).inv⟩

theorem archP_mem_Kset {k : (AdelicGL2 (𝓞 K) K)} (hk : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) :
    archP K k ∈ Kset K :=
  ⟨by rw [glFin_archP]; exact one_mem _, fun w => by rw [archComponent_archP]; exact hk w⟩

theorem mem_Kset_of_glFin_eq_one {k : (AdelicGL2 (𝓞 K) K)} (hk1 : glFin (𝓞 K) K k = 1)
    (hk : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) : k ∈ Kset K :=
  ⟨by rw [hk1]; exact one_mem _, hk⟩

def bOf (x : (AdelicGL2 (𝓞 K) K)) : (AdelicGL2 (𝓞 K) K) := Classical.choose (AutomorphicForm.exists_mem_adelicBorel_mul_eq K x)

def kOf (x : (AdelicGL2 (𝓞 K) K)) : (AdelicGL2 (𝓞 K) K) := Classical.choose (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq K x))

theorem bOf_mem (x : (AdelicGL2 (𝓞 K) K)) : bOf K x ∈ adelicBorel (𝓞 K) K :=
  (Classical.choose_spec (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq K x))).1

theorem kOf_mem (x : (AdelicGL2 (𝓞 K) K)) : kOf K x ∈ Kset K :=
  ⟨(Classical.choose_spec (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq K x))).2.1,
   (Classical.choose_spec (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq K x))).2.2.1⟩

theorem bOf_mul_kOf (x : (AdelicGL2 (𝓞 K) K)) : bOf K x * kOf K x = x :=
  (Classical.choose_spec (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq K x))).2.2.2.symm

end Choice

section Ext

variable (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
  (hαv : ∀ t, ((α t : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 K) K) t : ℝ)) (s : ℂ) (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

def Equivariant (h : (AdelicGL2 (𝓞 K) K) → ℂ) : Prop :=
  ∀ (m k : (AdelicGL2 (𝓞 K) K)) (hm : m ∈ adelicBorel (𝓞 K) K),
    glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
    (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) →
    (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
      h (m * k) = ((ν (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * h k

private def _root_.SectConC1.ext (h : (AdelicGL2 (𝓞 K) K) → ℂ) (g : (AdelicGL2 (𝓞 K) K)) : ℂ :=
  eta K α hα s ν ⟨bOf K (archP K g), bOf_mem K _⟩ * h (archP K (kOf K (archP K g)))

p2m_export "SectConC1" "ext"
theorem ext_apply (h : (AdelicGL2 (𝓞 K) K) → ℂ) (g : (AdelicGL2 (𝓞 K) K)) :
    ext K α hα s ν h g = eta K α hα s ν ⟨bOf K (archP K g), bOf_mem K _⟩ * h (archP K (kOf K (archP K g))) := rfl

def extLin : ((AdelicGL2 (𝓞 K) K) → ℂ) →ₗ[ℂ] ((AdelicGL2 (𝓞 K) K) → ℂ) where
  toFun := ext K α hα s ν
  map_add' h h' := by funext g; simp only [ext_apply, Pi.add_apply]; ring
  map_smul' c h := by funext g; simp only [ext_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem extLin_apply (h : (AdelicGL2 (𝓞 K) K) → ℂ) : extLin K α hα s ν h = ext K α hα s ν h := rfl

theorem ext_eq_of_archP_eq (h : (AdelicGL2 (𝓞 K) K) → ℂ) {g g' : (AdelicGL2 (𝓞 K) K)} (hg : archP K g = archP K g') :
    ext K α hα s ν h g = ext K α hα s ν h g' := by
  rw [ext_apply, ext_apply, hg]

include hαv in

theorem ext_eq (h : (AdelicGL2 (𝓞 K) K) → ℂ) (hh : Equivariant K ν h) (g b k : (AdelicGL2 (𝓞 K) K)) (hb : b ∈ adelicBorel (𝓞 K) K)
    (hk : k ∈ Kset K) (e : archP K g = b * k) :
    ext K α hα s ν h g = eta K α hα s ν ⟨b, hb⟩ * h (archP K k) := by
  rw [ext_apply]
  set x := archP K g with hx
  have hb₀ : bOf K x ∈ adelicBorel (𝓞 K) K := bOf_mem K x
  have hk₀ : kOf K x ∈ Kset K := kOf_mem K x
  have e₀ : bOf K x * kOf K x = x := bOf_mul_kOf K x

  set m : (AdelicGL2 (𝓞 K) K) := b⁻¹ * bOf K x with hm
  have hmB : m ∈ adelicBorel (𝓞 K) K := mul_mem (inv_mem hb) hb₀
  have hmk : m = k * (kOf K x)⁻¹ := by
    rw [hm, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, e₀]
    exact e
  have hmK : m ∈ Kset K := by
    have h' := mul_mem_Kset K hk (inv_mem_Kset K hk₀)
    rwa [← hmk] at h'
  have hb₀m : bOf K x = b * m := by rw [hm, mul_inv_cancel_left]
  have hkm : k = m * kOf K x := by rw [hmk, inv_mul_cancel_right]

  have h1 : eta K α hα s ν ⟨bOf K x, hb₀⟩ = eta K α hα s ν ⟨b, hb⟩ * eta K α hα s ν ⟨m, hmB⟩ := by
    have h' : (⟨bOf K x, hb₀⟩ : ↥(adelicBorel (𝓞 K) K)) = ⟨b, hb⟩ * ⟨m, hmB⟩ := Subtype.ext hb₀m
    rw [h', eta_mul]

  have h2 : h (archP K k) =
      ((ν (borelDiagSnd (⟨archP K m, archP_mem_borel K hmB⟩ : ↥(adelicBorel (𝓞 K) K)))) : ℂ) *
        h (archP K (kOf K x)) := by
    rw [hkm, map_mul]
    exact hh (archP K m) (archP K (kOf K x)) (archP_mem_borel K hmB) (glFin_archP K m) (glFin_archP K _)
      (fun w => by rw [archComponent_archP]; exact hmK.2 w)
      (fun w => by rw [archComponent_archP]; exact hk₀.2 w)

  have h3 : eta K α hα s ν ⟨m, hmB⟩ =
      ((ν (borelDiagSnd (⟨archP K m, archP_mem_borel K hmB⟩ : ↥(adelicBorel (𝓞 K) K)))) : ℂ) := by
    rw [eta_eq_nu_of_isRowIsometry K α hα hαv s ν hmB hmK.2, borelDiagSnd_archP]
  rw [h1, h2, h3]
  ring

end Ext

end SectConC1

end

open SectConC1 in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (finf : AdelicGL2 (𝓞 K) K → ℂ) (_hfc : Continuous finf) (_hfK : IsArchKFinite K finf)
      (_hfeq : ∀ (m k : AdelicGL2 (𝓞 K) K) (hm : m ∈ adelicBorel (𝓞 K) K),
        glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          finf (m * k) = ((ν (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * finf k),
    ∃ Φ : AdelicGL2 (𝓞 K) K → ℂ,
      (∀ g g' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = glArch (𝓞 K) K g' → Φ g = Φ g') ∧
      (∀ (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K b = 1 →
          Φ (b * g) =
            ((etaFst 1 α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
              ((etaSnd ν α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * Φ g) ∧
      Continuous Φ ∧ IsArchKFinite K Φ ∧
      (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          Φ k = finf k) := by
  intro α hα s ν hνc finf hfc hfK hfeq
  have hαv : ∀ t, ((α t : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 K) K) t : ℝ) := fun t => rfl
  have hfeq' : Equivariant K ν finf := fun m k hm h1 h2 h3 h4 => hfeq m k hm h1 h2 h3 h4

  have hΦarch : ∀ g g' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = glArch (𝓞 K) K g' → (SectConC1.ext K α hα s ν finf) g = (SectConC1.ext K α hα s ν finf) g' :=
    fun g g' hg => ext_eq_of_archP_eq K α hα s ν finf (archP_eq_of_glArch_eq K hg)

  have hΦK : ∀ k : AdelicGL2 (𝓞 K) K,
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        (SectConC1.ext K α hα s ν finf) k = finf (archP K k) := by
    intro k hk
    have e : archP K k = 1 * archP K k := (one_mul _).symm
    have := ext_eq K α hα hαv s ν finf hfeq' k 1 (archP K k) (one_mem _) (archP_mem_Kset K hk) e
    rw [this, archP_archP]
    show eta K α hα s ν 1 * finf (archP K k) = finf (archP K k)
    rw [eta_one, one_mul]

  have hΦind : IsInducedSection (𝓞 K) K ((etaFst 1 α hα s).comp (archUnit K)) ((etaSnd ν α hα s).comp (archUnit K)) (SectConC1.ext K α hα s ν finf) := by
    intro b hb g
    show SectConC1.ext K α hα s ν finf (b * g) = _
    have e : archP K (b * g) = (archP K b * bOf K (archP K g)) * kOf K (archP K g) := by
      rw [map_mul, mul_assoc, bOf_mul_kOf]
    rw [ext_eq K α hα hαv s ν finf hfeq' (b * g) _ _ (mul_mem (archP_mem_borel K hb) (bOf_mem K _))
      (kOf_mem K _) e]
    have hsplit : (⟨archP K b * bOf K (archP K g), mul_mem (archP_mem_borel K hb) (bOf_mem K _)⟩ :
        ↥(adelicBorel (𝓞 K) K)) = ⟨archP K b, archP_mem_borel K hb⟩ * ⟨bOf K (archP K g), bOf_mem K _⟩ := rfl
    rw [hsplit, eta_mul, eta_archP K α hα s ν hb]
    simp only [eta, MonoidHom.comp_apply, ext_apply]
    ring

  have hΦbor : ∀ (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
      glFin (𝓞 K) K b = 1 →
        (SectConC1.ext K α hα s ν finf) (b * g) =
          ((etaFst 1 α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
            ((etaSnd ν α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * (SectConC1.ext K α hα s ν finf) g := by
    intro b hb g hb1
    have hfst : (((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0)).2 = 1 := by
      have h' := congrArg (fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 0 0) hb1
      beta_reduce at h'
      rw [glFin_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq] at h'
      exact h'
    have hsnd : (((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1)).2 = 1 := by
      have h' := congrArg (fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1) hb1
      beta_reduce at h'
      rw [glFin_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq] at h'
      exact h'
    rw [hΦind b hb g, MonoidHom.comp_apply, MonoidHom.comp_apply,
      archUnit_eq_self_of_snd_eq_one K (t := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) hfst,
      archUnit_eq_self_of_snd_eq_one K (t := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) hsnd]

  have hΦc : Continuous (SectConC1.ext K α hα s ν finf) := by
    have hχ₁c : Continuous fun t : (AdeleRing (𝓞 K) K)ˣ =>
        ((((etaFst 1 α hα s).comp (archUnit K)) t : ℂˣ) : ℂ) :=
      continuous_etaFst_archUnit K α hα hαv s
    have hχ₂c : Continuous fun t : (AdeleRing (𝓞 K) K)ˣ =>
        ((((etaSnd ν α hα s).comp (archUnit K)) t : ℂˣ) : ℂ) :=
      continuous_etaSnd_archUnit K α hα hαv s ν hνc
    have hKc : ContinuousOn (fun p : Unit × AdelicGL2 (𝓞 K) K => SectConC1.ext K α hα s ν finf p.2)
        (Set.univ ×ˢ {k | glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
          ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))}) := by
      refine (((hfc.comp (continuous_archP K)).comp continuous_snd).continuousOn).congr ?_
      rintro ⟨x, k⟩ ⟨-, hk⟩
      exact hΦK k hk.2
    have hc : ContinuousOn (fun p : Unit × AdelicGL2 (𝓞 K) K => SectConC1.ext K α hα s ν finf p.2)
        (Set.univ ×ˢ Set.univ) :=
      AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact K (X := Unit)
        Set.univ isOpen_univ
        (fun _ => (etaFst 1 α hα s).comp (archUnit K)) (fun _ => (etaSnd ν α hα s).comp (archUnit K))
        ((hχ₁c.comp continuous_snd).continuousOn) ((hχ₂c.comp continuous_snd).continuousOn)
        (fun _ => SectConC1.ext K α hα s ν finf) (fun _ _ => hΦind) hKc
    rw [Set.univ_prod_univ, continuousOn_univ] at hc
    have h2 : Continuous fun g : AdelicGL2 (𝓞 K) K => (((), g) : Unit × AdelicGL2 (𝓞 K) K) :=
      continuous_const.prodMk continuous_id
    have h3 := hc.comp h2
    exact h3

  have hΦfin : IsArchKFinite K (SectConC1.ext K α hα s ν finf) := by
    classical
    intro w
    obtain ⟨sw, hsw⟩ := hfK w
    refine ⟨sw.image (SectConC1.ext K α hα s ν), ?_⟩
    intro kk hkk
    obtain ⟨kw, hkw, rfl⟩ := Subgroup.mem_map.mp hkk
    have hkk1 : glFin (𝓞 K) K (adelicArchGLInclAt K w kw) = 1 := glFin_adelicArchGLIncl K _
    have hkkiso : ∀ v : InfinitePlace K,
        IsRowIsometry (archComponent K v (glArch (𝓞 K) K (adelicArchGLInclAt K w kw))) := by
      intro v
      change IsRowIsometry (archComponent K v (glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w kw))))
      rw [glArch_adelicArchGLIncl]
      by_cases hvw : v = w
      · subst hvw
        rw [archComponent_archGLIncl_self]
        exact hkw
      · rw [archComponent_archGLIncl_of_ne K hvw]
        exact isRowIsometry_one
    have hkkK : adelicArchGLInclAt K w kw ∈ Kset K := mem_Kset_of_glFin_eq_one K hkk1 hkkiso

    have key : (fun x => SectConC1.ext K α hα s ν finf (x * adelicArchGLInclAt K w kw))
        = SectConC1.ext K α hα s ν (fun x => finf (x * adelicArchGLInclAt K w kw)) := by
      funext x
      have e : archP K (x * adelicArchGLInclAt K w kw) =
          bOf K (archP K x) * (kOf K (archP K x) * adelicArchGLInclAt K w kw) := by
        rw [map_mul, archP_of_glFin_eq_one K hkk1, ← mul_assoc, bOf_mul_kOf]
      rw [ext_eq K α hα hαv s ν finf hfeq' _ _ _ (bOf_mem K _) (mul_mem_Kset K (kOf_mem K _) hkkK) e,
        ext_apply, map_mul, archP_of_glFin_eq_one K hkk1]
    rw [key, Finset.coe_image]
    change extLin K α hα s ν (fun x => finf (x * adelicArchGLInclAt K w kw)) ∈
      Submodule.span ℂ (extLin K α hα s ν '' (sw : Set (AdelicGL2 (𝓞 K) K → ℂ)))
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem (hsw _ hkk)
  refine ⟨(SectConC1.ext K α hα s ν finf), hΦarch, hΦbor, hΦc, hΦfin, fun k hk1 hk => ?_⟩
  rw [hΦK k hk, archP_of_glFin_eq_one K hk1]

end S_AutomorphicForm_exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_isArchKFinite_eq_of_borel_arch_of_equivariant (solution)
