-- Prove2me | solution 1 for AutomorphicForm.le_iSup_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7625bf6d-3fbd-5436-bcfe-822502366307

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
import Theorems.Thm_AutomorphicForm_exists_isHeckeCosetSystem_levelOne_and_principalLevel_heckeGen_of_not_dvd
import Definitions.Def_NumberField_PrincipalLevel
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_le_iSup_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

section Standardness

open NumberField IsDedekindDomain AutomorphicForm LocalGL2 AdelicDock NumberField.AdelicLevel

namespace PrincipalCosetStandardness

variable (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

private def piScalar (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    GL (Fin 2) (v.adicCompletion L) :=
  ⟨Matrix.diagonal fun _ => algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ,
    Matrix.diagonal fun _ => (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [mul_inv_cancel₀ hϖ0, Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal]; simp only [inv_mul_cancel₀ hϖ0, Matrix.diagonal_one]⟩

private def piUnit (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    (v.adicCompletion L)ˣ :=
  Units.mk0 _ hϖ0

private theorem weyl_diagPi_weyl_diagPi (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    (weylR : GL (Fin 2) (v.adicCompletion L)) * diagPi ϖ hϖ0 * weylR * diagPi ϖ hϖ0
      = piScalar L v ϖ hϖ0 := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagPi]
  show !![(0 : v.adicCompletion L), 1; 1, 0]
        * !![algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ, 0; 0, 1]
        * !![(0 : v.adicCompletion L), 1; 1, 0]
        * !![algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ, 0; 0, 1]
      = Matrix.diagonal fun _ => algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private theorem diagPi_inv_eq (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    (diagPi ϖ hϖ0)⁻¹
      = (piScalar L v ϖ hϖ0)⁻¹ * (weylR : GL (Fin 2) (v.adicCompletion L)) * diagPi ϖ hϖ0
          * weylR := by
  rw [← weyl_diagPi_weyl_diagPi L v ϖ hϖ0]
  group

private theorem finEmbed_localEmbed_piScalar (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v (piScalar L v ϖ hϖ0))
      = centralScalar (𝓞 L) L
          (Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v (piUnit L v ϖ hϖ0))) := by
  apply Units.ext
  rw [coe_finEmbed, coe_localEmbed]
  show finMat (𝓞 L) L (localMat (𝓞 L) L v (piScalar L v ϖ hϖ0 : Matrix (Fin 2) (Fin 2) _))
      = Matrix.scalar (Fin 2)
          (((Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v (piUnit L v ϖ hϖ0)) :
              (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L))
  rw [Matrix.scalar_apply, Units.coe_map]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 L) L ?_ ?_
  · rw [mapMatrix_arch_finMat, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
    simp only [adeleArch_apply, finIncl_apply_fst, Matrix.diagonal_one]
  · rw [mapMatrix_fin_finMat, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
    simp only [adeleFin_apply, finIncl_apply_snd]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 L) L fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
      show Matrix.diagonal (fun _ => algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) ϖ)
          = Matrix.diagonal fun _ => finAdeleEval (𝓞 L) L w
              ((localUnit (𝓞 L) L w (piUnit L w ϖ hϖ0) : (FiniteAdeleRing (𝓞 L) L)ˣ) :
                FiniteAdeleRing (𝓞 L) L)
      rw [finAdeleEval_apply, localUnit_apply_self]
      rfl
    · rw [mapMatrix_localMat_of_ne (𝓞 L) L v _ hw, RingHom.mapMatrix_apply,
        Matrix.diagonal_map (map_zero _)]
      simp only [finAdeleEval_apply, localUnit_apply_of_ne (𝓞 L) L v _ hw, Matrix.diagonal_one]

private theorem heckeGen_inv_eq_of_weyl_mem (U : Subgroup (AdelicGL2 (𝓞 L) L))
    (hU : finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR) ∈ U) :
    ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L), u₁ ∈ U ∧ u₂ ∈ U ∧
      (heckeGen (𝓞 L) L v)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L v * u₂ := by
  obtain ⟨ϖ, hϖ0, -, hgen, -⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen L v
  refine ⟨(Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v (piUnit L v ϖ hϖ0)))⁻¹,
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR), finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR),
    hU, hU, ?_⟩
  rw [← hgen, ← map_inv (finEmbed (𝓞 L) L), ← map_inv (localEmbed (𝓞 L) L v),
    diagPi_inv_eq L v ϖ hϖ0]
  simp only [map_mul, map_inv, finEmbed_localEmbed_piScalar]

private theorem isLocalLevelOne_of_integral (N : Ideal (𝓞 L)) (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N)
    (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers L) :
    IsLocalLevelOne (𝓞 L) L v N m := by
  have hb : idealBound (𝓞 L) N v = 1 := idealBound_eq_one_of_not_dvd (R := 𝓞 L) hN hv
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact hm 1 0
  · rw [hb]
    exact sub_mem (hm 1 1) (one_mem _)

private theorem finEmbed_localEmbed_mem_levelOne (N : Ideal (𝓞 L)) (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N)
    (m : GL (Fin 2) (v.adicCompletion L))
    (hm : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j ∈ v.adicCompletionIntegers L)
    (hmi : ∀ i j, ((m⁻¹ : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j
      ∈ v.adicCompletionIntegers L) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v m) ∈ levelOne (𝓞 L) L N := by
  rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_of_integral L v N hN hv _ hm, isLocalLevelOne_of_integral L v N hN hv _ hmi⟩

private theorem map_weylMatrix {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) :
    (!![(0 : A), 1; 1, 0] : Matrix (Fin 2) (Fin 2) A).map f = !![(0 : B), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem weylMatrix_mul_weylMatrix {A : Type*} [Semiring A] :
    (!![(0 : A), 1; 1, 0] : Matrix (Fin 2) (Fin 2) A) * !![(0 : A), 1; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem weyl_mul_finEmbed_localEmbed_mul_weyl_inv (m : GL (Fin 2) (v.adicCompletion L)) :
    weyl (𝓞 L) L * finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v m) * (weyl (𝓞 L) L)⁻¹
      = finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v ((weylR : GL (Fin 2) (v.adicCompletion L)) * m * weylR)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_finEmbed, coe_localEmbed, coe_finEmbed, coe_localEmbed, Units.val_mul,
    Units.val_mul]
  have hw : ((weyl (𝓞 L) L : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))
      = !![0, 1; 1, 0] := rfl
  have hwR : ((weylR : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L))
      = !![0, 1; 1, 0] := rfl
  rw [hw, hwR]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 L) L ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mul_one, one_mul]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat, mapMatrix_fin_finMat, RingHom.mapMatrix_apply, map_weylMatrix]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 L) L fun w => ?_
    rw [map_mul, map_mul, RingHom.mapMatrix_apply (M := !![(0 : FiniteAdeleRing (𝓞 L) L), 1; 1, 0]),
      map_weylMatrix]
    by_cases hw' : w = v
    · subst hw'
      rw [mapMatrix_localMat_self, mapMatrix_localMat_self, Matrix.mul_assoc _ _ !![(0 : w.adicCompletion L), 1; 1, 0],
        weylMatrix_mul_weylMatrix, Matrix.mul_one]
    · rw [mapMatrix_localMat_of_ne (𝓞 L) L v _ hw', mapMatrix_localMat_of_ne (𝓞 L) L v _ hw', mul_one, one_mul]

private theorem coe_weylR_mul_mul_weylR (m : GL (Fin 2) (v.adicCompletion L)) :
    ((((weylR : GL (Fin 2) (v.adicCompletion L)) * m * weylR : GL (Fin 2) (v.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion L)))
      = !![(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) 1 1, (m : Matrix (Fin 2) (Fin 2) _) 1 0;
           (m : Matrix (Fin 2) (Fin 2) _) 0 1, (m : Matrix (Fin 2) (Fin 2) _) 0 0] := by
  have hwR : ((weylR : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L))
      = !![0, 1; 1, 0] := rfl
  rw [Units.val_mul, Units.val_mul, hwR]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem weylR_mul_mul_weylR_apply_mem (m : GL (Fin 2) (v.adicCompletion L))
    (hm : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j ∈ v.adicCompletionIntegers L) :
    ∀ i j, (((weylR : GL (Fin 2) (v.adicCompletion L)) * m * weylR : GL (Fin 2) (v.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j ∈ v.adicCompletionIntegers L := by
  intro i j
  rw [coe_weylR_mul_mul_weylR]
  fin_cases i <;> fin_cases j
  · exact hm 1 1
  · exact hm 1 0
  · exact hm 0 1
  · exact hm 0 0

private theorem weylR_inv : ((weylR : GL (Fin 2) (v.adicCompletion L))⁻¹ : GL (Fin 2) (v.adicCompletion L)) = weylR :=
  Units.ext rfl

private theorem weylR_mul_weylR : (weylR : GL (Fin 2) (v.adicCompletion L)) * weylR = 1 := by
  nth_rewrite 1 [← weylR_inv L v]
  exact inv_mul_cancel _

private theorem finEmbed_localEmbed_mem_principalLevel (N : Ideal (𝓞 L)) (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N)
    (m : GL (Fin 2) (v.adicCompletion L))
    (hm : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j ∈ v.adicCompletionIntegers L)
    (hmi : ∀ i j, ((m⁻¹ : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j
      ∈ v.adicCompletionIntegers L) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v m) ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  refine Subgroup.mem_inf.mpr ⟨(mem_principalLevel_iff (𝓞 L) L N).mpr
    ⟨finEmbed_localEmbed_mem_levelOne L v N hN hv m hm hmi, ?_⟩, ?_⟩
  · refine Subgroup.mem_map.mpr ⟨finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v
      ((weylR : GL (Fin 2) (v.adicCompletion L)) * m * weylR)), ?_, ?_⟩
    · refine finEmbed_localEmbed_mem_levelOne L v N hN hv _ (weylR_mul_mul_weylR_apply_mem L v m hm) ?_
      rw [mul_inv_rev, mul_inv_rev, weylR_inv, ← mul_assoc]
      exact weylR_mul_mul_weylR_apply_mem L v m⁻¹ hmi
    · show weyl (𝓞 L) L * _ * (weyl (𝓞 L) L)⁻¹ = _
      rw [weyl_mul_finEmbed_localEmbed_mul_weyl_inv]
      congr 2
      rw [← mul_assoc, ← mul_assoc, weylR_mul_weylR, one_mul, mul_assoc, weylR_mul_weylR, mul_one]
  · rw [mem_finiteAdelicGL2Subgroup_iff, glArch_finEmbed]

private theorem finEmbed_localEmbed_weylR_mem_principalLevel (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (hv : ¬ v.asIdeal ∣ N) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR)
      ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  have hW : ∀ i j, ((weylR : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j
      ∈ v.adicCompletionIntegers L := by
    intro i j
    show (!![(0 : v.adicCompletion L), 1; 1, 0] : Matrix (Fin 2) (Fin 2) _) i j ∈ v.adicCompletionIntegers L
    fin_cases i <;> fin_cases j <;> simp
  refine finEmbed_localEmbed_mem_principalLevel L v N hN hv weylR hW ?_
  rw [weylR_inv]
  exact hW

private theorem finEmbed_localEmbed_unipotentInt_mem_principalLevel (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (hv : ¬ v.asIdeal ∣ N) (b : v.adicCompletionIntegers L) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v (unipotentInt (v.adicCompletion L) b))
      ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  have hU : ∀ c : v.adicCompletionIntegers L, ∀ i j,
      ((unipotentInt (v.adicCompletion L) c : GL (Fin 2) (v.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j ∈ v.adicCompletionIntegers L := by
    intro c i j
    rw [coe_unipotentInt]
    fin_cases i <;> fin_cases j <;> simp
  refine finEmbed_localEmbed_mem_principalLevel L v N hN hv _ (hU b) ?_
  rw [unipotentInt_inv]
  exact hU (-b)

private theorem hstd_principalLevel_heckeGen (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ S) :
    ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L),
        u₁ ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        u₂ ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        (heckeGen (𝓞 L) L w)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L w * u₂ :=
  fun w hw =>
    heckeGen_inv_eq_of_weyl_mem L w _
      (finEmbed_localEmbed_weylR_mem_principalLevel L w N hN fun hdvd => hw (hNS w hdvd))

private theorem localEmbed_mul_localEmbed_comm {w : HeightOneSpectrum (𝓞 L)} (hvw : v ≠ w)
    (g : GL (Fin 2) (v.adicCompletion L)) (h : GL (Fin 2) (w.adicCompletion L)) :
    localEmbed (𝓞 L) L v g * localEmbed (𝓞 L) L w h = localEmbed (𝓞 L) L w h * localEmbed (𝓞 L) L v g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_localEmbed, coe_localEmbed]
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 L) L fun u => ?_
  rw [map_mul, map_mul]
  by_cases hu : u = v
  · rw [hu, mapMatrix_localMat_self, mapMatrix_localMat_of_ne (𝓞 L) L w _ hvw, mul_one, one_mul]
  · rw [mapMatrix_localMat_of_ne (𝓞 L) L v _ hu, one_mul, mul_one]

private theorem weylInt_eq_weylR :
    (weylInt (v.adicCompletionIntegers L) (v.adicCompletion L) : GL (Fin 2) (v.adicCompletion L)) = weylR :=
  Units.ext (by rw [coe_weylInt]; rfl)

private theorem exists_fin_local_cosetSystem_principal (N : Ideal (𝓞 L)) (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 L) L,
      HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
        (heckeGen (𝓞 L) L v) reps ∧
      ∀ i, ∃ m : GL (Fin 2) (v.adicCompletion L), reps i = finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v m) := by
  obtain ⟨ϖ, hϖ0, -, hgen, sec, -, hsys⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen L v

  obtain ⟨F, hF_def⟩ : ∃ F : Option (𝓞 L ⧸ v.asIdeal) → AdelicGL2 (𝓞 L) L, F = fun i =>
      finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v (i.elim (localRepInf ϖ hϖ0)
        (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 L) (v.adicCompletionIntegers L) (sec c))))) := ⟨_, rfl⟩
  have hF₁ : HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L v) F := by
    rw [hF_def]
    exact hsys N hv
  have hFloc : ∀ o, ∃ m : GL (Fin 2) (v.adicCompletion L), F o = finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v m) :=
    fun o => by rw [hF_def]; exact ⟨_, rfl⟩

  obtain ⟨reps₀, -, h₀⟩ := exists_isHeckeCosetSystem_levelOne_and_principalLevel_heckeGen_of_not_dvd L N v hv
  have hKU : principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ≤ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
    inf_le_inf_right _ (principalLevel_le_levelOne (𝓞 L) L N)

  have hFmem : ∀ o, F o ∈ HeckePair.doubleCoset (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L v) := by
    intro o
    rw [hF_def]
    cases o with
    | none =>
      refine HeckePair.mem_doubleCoset_iff.mpr ⟨finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR),
        finEmbed_localEmbed_weylR_mem_principalLevel L v N hN hv, finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR),
        finEmbed_localEmbed_weylR_mem_principalLevel L v N hN hv, ?_⟩
      show _ = finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v (localRepInf ϖ hϖ0))
      rw [← hgen, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← weylInt_eq_weylR]
      rfl
    | some c =>
      refine HeckePair.mem_doubleCoset_iff.mpr ⟨finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v
          (unipotentInt (v.adicCompletion L) (algebraMap (𝓞 L) (v.adicCompletionIntegers L) (sec c)))),
        finEmbed_localEmbed_unipotentInt_mem_principalLevel L v N hN hv _, 1, one_mem _, ?_⟩
      show _ = finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v (localRepSome ϖ hϖ0 _))
      rw [mul_one, ← hgen, ← map_mul, ← map_mul]
      rfl

  have hFinj : Function.Injective fun o =>
      (QuotientGroup.mk (F o) : AdelicGL2 (𝓞 L) L ⧸ (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)) := by
    intro o o' hoo'
    apply hF₁.mk_injective
    exact QuotientGroup.eq.2 (hKU (QuotientGroup.eq.1 hoo'))

  have hcov : ∀ o, ∃ j, (QuotientGroup.mk (F o) :
      AdelicGL2 (𝓞 L) L ⧸ (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)) = QuotientGroup.mk (reps₀ j) :=
    fun o => h₀.covers (F o) (hFmem o)
  choose f hf using hcov
  haveI : Finite (𝓞 L ⧸ v.asIdeal) :=
    (Ideal.absNorm_ne_zero_iff v.asIdeal).1 (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  letI : Fintype (𝓞 L ⧸ v.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (Option (𝓞 L ⧸ v.asIdeal)) = Ideal.absNorm v.asIdeal + 1 := by
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfinj : Function.Injective f := by
    intro o o' hoo'
    apply hFinj
    simp only
    rw [hf o, hf o', hoo']
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard.trans (Fintype.card_fin _).symm⟩
  obtain ⟨e⟩ : Nonempty (Fin (Ideal.absNorm v.asIdeal + 1) ≃ Option (𝓞 L ⧸ v.asIdeal)) :=
    ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  refine ⟨fun i => F (e i), ⟨fun i => hFmem (e i), fun x hx => ?_, fun i j hij => e.injective (hFinj hij)⟩,
    fun i => hFloc (e i)⟩
  obtain ⟨j, hj⟩ := h₀.covers x hx
  obtain ⟨o, rfl⟩ := hfbij.2 j
  exact ⟨e.symm o, hj.trans ((hf o).symm.trans (by simp only [Equiv.apply_symm_apply]))⟩

end PrincipalCosetStandardness

end Standardness

section SlabDecomposition

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace PrincipalCosetSumIndependence

variable {K : Type} [Field K] [NumberField K]

open HeckeIntegralSeam

private theorem cosetSum_eq_of_isHeckeCosetSystem {U : Subgroup (AdelicGL2 (𝓞 K) K)} {gv : AdelicGL2 (𝓞 K) K}
    {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁] {reps₀ : ι₀ → AdelicGL2 (𝓞 K) K} {reps₁ : ι₁ → AdelicGL2 (𝓞 K) K}
    (h₀ : IsHeckeCosetSystem U gv reps₀) (h₁ : IsHeckeCosetSystem U gv reps₁) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g) (g : AdelicGL2 (𝓞 K) K) :
    ∑ i, φ (g * reps₀ i) = ∑ j, φ (g * reps₁ j) := by

  have hcov : ∀ i, ∃ j, (QuotientGroup.mk (reps₀ i) : AdelicGL2 (𝓞 K) K ⧸ U) = QuotientGroup.mk (reps₁ j) :=
    fun i => h₁.covers (reps₀ i) (h₀.mem_doubleCoset i)
  choose f hf using hcov
  have hinj : Function.Injective f := by
    intro i i' hii'
    apply h₀.mk_injective
    simp only
    rw [hf i, hf i', hii']
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := h₀.covers (reps₁ j) (h₁.mem_doubleCoset j)
    refine ⟨i, h₁.mk_injective ?_⟩
    simp only
    rw [← hf i, hi]
  refine Fintype.sum_bijective f ⟨hinj, hsurj⟩ _ _ fun i => ?_

  have hu : (reps₀ i)⁻¹ * reps₁ (f i) ∈ U := QuotientGroup.eq.1 (hf i)
  have e : reps₁ (f i) = reps₀ i * ((reps₀ i)⁻¹ * reps₁ (f i)) := by group
  rw [e, ← mul_assoc, hφU _ _ hu]

end PrincipalCosetSumIndependence

namespace PrincipalHeckeStableDecomposition

variable (K : Type) [Field K] [NumberField K]

private abbrev slabPins (Φ : Set (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

private def slabPairing (Φ : Set (AdelicGL2 (𝓞 K) K)) (a b : AdelicGL2 (𝓞 K) K → ℂ) : ℂ :=
  ∫ g in Φ, a g * conj (b g) ∂adelicGLHaar (Fin 2) (𝓞 K) K

variable {K}

open AutomorphicForm.CuspidalConstituent

variable {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 K) K)}

private theorem isSlabFundamentalDomain_of_binders (hα : 0 < α) (hαβ : α < β)
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    IsSlabFundamentalDomain K α β Φ := by
  exact ⟨hα, hαβ, hΦs, hΦ⟩

private theorem pairing_zero_eq_slabPairing (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    pairing K Φ 0 a b = slabPairing K Φ a b := by
  simp only [pairing, slabPairing, neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]

private theorem slabPairing_smul_left (c : ℂ) (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    slabPairing K Φ (c • a) b = c * slabPairing K Φ a b := by
  unfold slabPairing
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

private theorem slabPairing_smul_right (c : ℂ) (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    slabPairing K Φ a (c • b) = conj c * slabPairing K Φ a b := by
  unfold slabPairing
  simp_rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (conj c)]
  exact integral_const_mul _ _

private theorem memLp_two_of_mem {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {a : AdelicGL2 (𝓞 K) K → ℂ}
    (ha : a ∈ contMemberSubmodule K Φ ξ) : MemLp a 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
  ((mem_memberSubmodule_iff' K Φ ξ a).1 ha.1).2

private theorem integrable_mul_conj_of_mem {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {a b : AdelicGL2 (𝓞 K) K → ℂ} (ha : a ∈ contMemberSubmodule K Φ ξ) (hb : b ∈ contMemberSubmodule K Φ ξ) :
    Integrable (fun g => a g * conj (b g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
  (memLp_two_of_mem ha).integrable_mul (memLp_two_of_mem hb).star

private theorem slabPairing_sum_left (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) {n : ℕ}
    (a : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (ha : ∀ i, a i ∈ contMemberSubmodule K Φ ξ) (b : AdelicGL2 (𝓞 K) K → ℂ)
    (hb : b ∈ contMemberSubmodule K Φ ξ) :
    slabPairing K Φ (fun g => ∑ i, a i g) b = ∑ i, slabPairing K Φ (a i) b := by
  unfold slabPairing
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum Finset.univ fun i _ => integrable_mul_conj_of_mem (ha i) hb

private theorem slabPairing_sum_right (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (a : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : a ∈ contMemberSubmodule K Φ ξ) {n : ℕ} (b : Fin n → AdelicGL2 (𝓞 K) K → ℂ)
    (hb : ∀ i, b i ∈ contMemberSubmodule K Φ ξ) :
    slabPairing K Φ a (fun g => ∑ i, b i g) = ∑ i, slabPairing K Φ a (b i) := by
  unfold slabPairing
  simp_rw [map_sum, Finset.mul_sum]
  exact integral_finsetSum Finset.univ fun i _ => integrable_mul_conj_of_mem ha (hb i)

private theorem weightedMeasure_zero_eq : weightedMeasure K Φ 0 = (adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ := by
  rw [weightedMeasure_def]
  have hone : (fun x => ENNReal.ofReal (weight K 0 x)) = (1 : AdelicGL2 (𝓞 K) K → ENNReal) := by
    funext x
    simp [weight_def]
  rw [hone, withDensity_one]

private theorem eq_zero_of_slabPairing_self_eq_zero (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (a : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : a ∈ contMemberSubmodule K Φ ξ) (h : slabPairing K Φ a a = 0) : a = 0 := by
  have hsq : slabPairing K Φ a a = ((∫ g in Φ, ‖a g‖ ^ 2 ∂adelicGLHaar (Fin 2) (𝓞 K) K : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    unfold slabPairing
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [Complex.mul_conj', Complex.ofReal_pow]
  have hint : Integrable (fun g => ‖a g‖ ^ 2) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
    (memLp_two_of_mem ha).norm.integrable_sq
  have hzero : (fun g => ‖a g‖ ^ 2) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0 :=
    (integral_eq_zero_iff_of_nonneg (f := fun g => ‖a g‖ ^ 2) (fun g => sq_nonneg ‖a g‖) hint).1
      (Complex.ofReal_eq_zero.1 (hsq.symm.trans h))
  have hae : a =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0 := hzero.mono fun g hg => by simpa using hg
  refine eq_zero_of_toCarrier_eq_zero K hΦ₀ 0 ξ a ha ?_
  show (memLp_weightedMeasure_of_mem K hΦ₀ 0 ha.1).toLp a = 0
  rw [Lp.eq_zero_iff_ae_eq_zero]
  refine (MemLp.coeFn_toLp _).trans ?_
  rw [weightedMeasure_zero_eq]
  exact hae

private theorem exists_forall_slabPairing_rightTranslate_eq (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (r : AdelicGL2 (𝓞 K) K) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ a b : AdelicGL2 (𝓞 K) K → ℂ, a ∈ contMemberSubmodule K Φ ξ → b ∈ contMemberSubmodule K Φ ξ →
        rightTranslate K r a ∈ contMemberSubmodule K Φ ξ ∧
        rightTranslate K r⁻¹ b ∈ contMemberSubmodule K Φ ξ ∧
        slabPairing K Φ (rightTranslate K r a) b = (κ : ℂ) * slabPairing K Φ a (rightTranslate K r⁻¹ b) := by
  have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det r) :=
    NumberField.TateGlobal.ideleNorm_pos _

  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K
    (Real.sqrt (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det r))⁻¹)
    (Real.sqrt_pos.2 (inv_pos.2 hd))
  have hdet : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
    rw [show centralScalar (𝓞 K) K z = Matrix.GeneralLinearGroup.scalar (Fin 2) z from rfl,
      Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, sq]
  obtain ⟨y, hy_def⟩ : ∃ y : AdelicGL2 (𝓞 K) K, y = centralScalar (𝓞 K) K z * r := ⟨_, rfl⟩
  have hy : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) = 1 := by
    rw [hy_def, map_mul, hdet, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul, hz,
      Real.mul_self_sqrt (inv_nonneg.2 hd.le), inv_mul_cancel₀ hd.ne']
  obtain ⟨c, hc_def⟩ : ∃ c : ℂ, c = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc_def]
    exact (ξ ⟨z, Subgroup.mem_top z⟩).ne_zero
  refine ⟨‖c⁻¹‖ ^ 2, pow_pos (norm_pos_iff.2 (inv_ne_zero hc0)) 2, fun a b ha hb => ?_⟩
  obtain ⟨hya', hyb', hpair⟩ :=
    rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one K hΦ₀ 0 ξ a b ha hb y hy
  have hcen_a := ((mem_memberSubmodule_iff' K Φ ξ a).1 ha.1).1.central_transform
  have hcen_b := ((mem_memberSubmodule_iff' K Φ ξ b).1 hb.1).1.central_transform

  have hya : ∀ g : AdelicGL2 (𝓞 K) K, a (g * y) = c * a (g * r) := by
    intro g
    rw [hy_def, ← mul_assoc, AutomorphicForm.SiegelCovering.mul_centralScalar_comm, mul_assoc, hc_def]
    exact hcen_a ⟨z, Subgroup.mem_top z⟩ (g * r)
  have hyb : ∀ g : AdelicGL2 (𝓞 K) K, b (g * y⁻¹) = c⁻¹ * b (g * r⁻¹) := by
    intro g
    rw [hy_def, mul_inv_rev, ← map_inv (centralScalar (𝓞 K) K) z, ← mul_assoc,
      AutomorphicForm.SiegelCovering.mul_centralScalar_comm]
    have h := hcen_b (⟨z, Subgroup.mem_top z⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))⁻¹ (g * r⁻¹)
    rw [map_inv ξ, Units.val_inv_eq_inv_val, ← hc_def] at h
    exact h
  have hra : rightTranslate K r a = c⁻¹ • rightTranslate K y a := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
    rw [hya g, inv_mul_cancel_left₀ hc0]
  have hrb : rightTranslate K y⁻¹ b = c⁻¹ • rightTranslate K r⁻¹ b := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
    exact hyb g
  have hrb' : rightTranslate K r⁻¹ b = c • rightTranslate K y⁻¹ b := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
    rw [hyb g, mul_inv_cancel_left₀ hc0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hra]
    exact (contMemberSubmodule K Φ ξ).smul_mem _ hya'
  · rw [hrb']
    exact (contMemberSubmodule K Φ ξ).smul_mem _ hyb'
  · calc slabPairing K Φ (rightTranslate K r a) b
        _ = c⁻¹ * pairing K Φ 0 (rightTranslate K y a) b := by
          rw [hra, slabPairing_smul_left, pairing_zero_eq_slabPairing]
        _ = c⁻¹ * slabPairing K Φ a (rightTranslate K y⁻¹ b) := by rw [hpair, pairing_zero_eq_slabPairing]
        _ = ((‖c⁻¹‖ ^ 2 : ℝ) : ℂ) * slabPairing K Φ a (rightTranslate K r⁻¹ b) := by
          rw [hrb, slabPairing_smul_right, Complex.ofReal_pow, ← Complex.mul_conj', mul_assoc]

private theorem slabPairing_sub_left {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {a a' b : AdelicGL2 (𝓞 K) K → ℂ} (ha : a ∈ contMemberSubmodule K Φ ξ) (ha' : a' ∈ contMemberSubmodule K Φ ξ)
    (hb : b ∈ contMemberSubmodule K Φ ξ) :
    slabPairing K Φ (a - a') b = slabPairing K Φ a b - slabPairing K Φ a' b := by
  unfold slabPairing
  simp_rw [Pi.sub_apply, sub_mul]
  exact integral_sub (integrable_mul_conj_of_mem ha hb) (integrable_mul_conj_of_mem ha' hb)

private theorem exists_slabPairing_heckeCosetSum_eq (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (U : Subgroup (AdelicGL2 (𝓞 K) K)) (gv : AdelicGL2 (𝓞 K) K)
    (hstd : ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 K) K), u₁ ∈ U ∧ u₂ ∈ U ∧
      gv⁻¹ = centralScalar (𝓞 K) K z * u₁ * gv * u₂)
    {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K) (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (a b : AdelicGL2 (𝓞 K) K → ℂ),
      a ∈ contMemberSubmodule K Φ ξ → b ∈ contMemberSubmodule K Φ ξ →
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, a (g * u) = a g) → (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, b (g * u) = b g) →
      slabPairing K Φ (SmoothCusp.heckeCosetSum K reps a) b =
        c * slabPairing K Φ a (SmoothCusp.heckeCosetSum K reps b) := by
  obtain ⟨z, u₁, u₂, hu₁, hu₂, hgv⟩ := hstd
  choose κ hκpos hκ using fun x : AdelicGL2 (𝓞 K) K => exists_forall_slabPairing_rightTranslate_eq hΦ₀ ξ x
  obtain ⟨i₀, -⟩ := hsys.covers gv (HeckePair.self_mem_doubleCoset (U := U) gv)
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 i₀.pos.ne'
  obtain ⟨w, hw_def⟩ : ∃ w : ℂ, w = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := by
    rw [hw_def]
    exact (ξ ⟨z, Subgroup.mem_top z⟩).ne_zero
  have hcomm : ∀ X Y : AdelicGL2 (𝓞 K) K,
      X * (centralScalar (𝓞 K) K z * Y) = centralScalar (𝓞 K) K z * (X * Y) := fun X Y => by
    rw [← mul_assoc, AutomorphicForm.SiegelCovering.mul_centralScalar_comm, mul_assoc]
  have hκsum : (∑ i, (κ (reps i) : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_sum, Complex.ofReal_ne_zero]
    exact (Finset.sum_pos (fun i _ => hκpos (reps i)) ⟨i₀, Finset.mem_univ _⟩).ne'
  refine ⟨(∑ i, (κ (reps i) : ℂ)) * conj w * (n : ℂ)⁻¹,
    mul_ne_zero (mul_ne_zero hκsum ((map_ne_zero (starRingEnd ℂ)).2 hw0)) (inv_ne_zero hn),
    fun a b ha hb haU hbU => ?_⟩
  by_cases ha0 : a = 0
  · subst ha0
    simp [slabPairing, SmoothCusp.heckeCosetSum]
  have haa : slabPairing K Φ a a ≠ 0 := fun h => ha0 (eq_zero_of_slabPairing_self_eq_zero hΦ₀ ξ a ha h)
  have hfix : ∀ u ∈ U, rightTranslate K u a = a := fun u hu => funext fun g => by
    rw [rightTranslate_apply]
    exact haU g u hu

  have hcost : ∀ u ∈ U, (κ u : ℂ) = 1 := by
    intro u hu
    have h1 := (hκ u a a ha ha).2.2
    rw [hfix u hu, hfix u⁻¹ (inv_mem hu)] at h1
    exact mul_right_cancel₀ haa (h1.symm.trans (one_mul _).symm)

  have hfree : ∀ u ∈ U, ∀ ψ : AdelicGL2 (𝓞 K) K → ℂ, ψ ∈ contMemberSubmodule K Φ ξ →
      slabPairing K Φ a (rightTranslate K u ψ) = slabPairing K Φ a ψ := by
    intro u hu ψ hψ
    have h1 := (hκ u⁻¹ a ψ ha hψ).2.2
    rw [inv_inv, hcost u⁻¹ (inv_mem hu), one_mul, hfix u⁻¹ (inv_mem hu)] at h1
    exact h1.symm
  have hcen_b := ((mem_memberSubmodule_iff' K Φ ξ b).1 hb.1).1.central_transform
  have hgvb : rightTranslate K gv b ∈ contMemberSubmodule K Φ ξ := (hκ gv b b hb hb).1

  have hL : slabPairing K Φ (SmoothCusp.heckeCosetSum K reps a) b =
      (∑ i, (κ (reps i) : ℂ)) * (conj w * slabPairing K Φ a (rightTranslate K gv b)) := by
    have hsum := slabPairing_sum_left ξ (fun i => rightTranslate K (reps i) a)
      (fun i => (hκ (reps i) a b ha hb).1) b hb
    have hfun : SmoothCusp.heckeCosetSum K reps a = fun g => ∑ i, rightTranslate K (reps i) a g := by
      funext g
      simp only [SmoothCusp.heckeCosetSum, rightTranslate_apply]
    rw [hfun, hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨u, hu, u', hu', hrep⟩ := HeckePair.mem_doubleCoset_iff.1 (hsys.mem_doubleCoset i)
    have hinv : rightTranslate K (reps i)⁻¹ b = w • rightTranslate K (u'⁻¹ * u₁) (rightTranslate K gv b) := by
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
      have hg : g * (reps i)⁻¹ = centralScalar (𝓞 K) K z * (g * (u'⁻¹ * u₁) * gv) * (u₂ * u⁻¹) := by
        rw [← hrep, mul_inv_rev, mul_inv_rev, hgv]
        simp only [mul_assoc]
        rw [hcomm, hcomm]
      rw [hg, hbU _ _ (mul_mem hu₂ (inv_mem hu)), hw_def]
      exact hcen_b ⟨z, Subgroup.mem_top z⟩ _
    rw [(hκ (reps i) a b ha hb).2.2, hinv, slabPairing_smul_right, hfree _ (mul_mem (inv_mem hu') hu₁) _ hgvb]

  have hR : slabPairing K Φ a (SmoothCusp.heckeCosetSum K reps b) =
      (n : ℂ) * slabPairing K Φ a (rightTranslate K gv b) := by
    have hsum := slabPairing_sum_right ξ a ha (fun i => rightTranslate K (reps i) b)
      (fun i => (hκ (reps i) b b hb hb).1)
    have hfun : SmoothCusp.heckeCosetSum K reps b = fun g => ∑ i, rightTranslate K (reps i) b g := by
      funext g
      simp only [SmoothCusp.heckeCosetSum, rightTranslate_apply]
    rw [hfun, hsum]
    have hterm : ∀ i, slabPairing K Φ a (rightTranslate K (reps i) b) =
        slabPairing K Φ a (rightTranslate K gv b) := by
      intro i
      obtain ⟨u, hu, u', hu', hrep⟩ := HeckePair.mem_doubleCoset_iff.1 (hsys.mem_doubleCoset i)
      have hrt : rightTranslate K (reps i) b = rightTranslate K u (rightTranslate K gv b) := by
        funext g
        simp only [rightTranslate_apply]
        rw [← hrep, ← mul_assoc, ← mul_assoc, hbU _ _ hu']
      rw [hrt, hfree u hu _ hgvb]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hL, hR, ← mul_assoc, ← mul_assoc, mul_assoc _ (n : ℂ)⁻¹ (n : ℂ), inv_mul_cancel₀ hn, mul_one]

private def cosetEnd {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K) (X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hT : ∀ x ∈ X, SmoothCusp.heckeCosetSum K reps x ∈ X) : Module.End ℂ X where
  toFun x := ⟨SmoothCusp.heckeCosetSum K reps x, hT x x.2⟩
  map_add' x y := by
    apply Subtype.ext
    funext g
    show SmoothCusp.heckeCosetSum K reps ((x : AdelicGL2 (𝓞 K) K → ℂ) + y) g =
      SmoothCusp.heckeCosetSum K reps x g + SmoothCusp.heckeCosetSum K reps y g
    simp only [SmoothCusp.heckeCosetSum, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by
    apply Subtype.ext
    funext g
    show SmoothCusp.heckeCosetSum K reps (c • (x : AdelicGL2 (𝓞 K) K → ℂ)) g =
      c * SmoothCusp.heckeCosetSum K reps x g
    simp only [SmoothCusp.heckeCosetSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

private theorem heckeCosetSum_comm_of_forall_commute {m n : ℕ} {r : Fin m → AdelicGL2 (𝓞 K) K}
    {s : Fin n → AdelicGL2 (𝓞 K) K} (h : ∀ i j, r i * s j = s j * r i) (x : AdelicGL2 (𝓞 K) K → ℂ) :
    SmoothCusp.heckeCosetSum K r (SmoothCusp.heckeCosetSum K s x) =
      SmoothCusp.heckeCosetSum K s (SmoothCusp.heckeCosetSum K r x) := by
  funext g
  simp only [SmoothCusp.heckeCosetSum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, h i j, ← mul_assoc]

private theorem maxGenEigenspace_le_eigenspace (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hXm : ∀ x ∈ X, x ∈ contMemberSubmodule K Φ ξ) (T : Module.End ℂ X)
    (F : (AdelicGL2 (𝓞 K) K → ℂ) → AdelicGL2 (𝓞 K) K → ℂ)
    (hTF : ∀ x : X, ((T x : X) : AdelicGL2 (𝓞 K) K → ℂ) = F x) (c : ℂ)
    (hadj : ∀ a ∈ X, ∀ b ∈ X, slabPairing K Φ (F a) b = c * slabPairing K Φ a (F b)) (μ : ℂ) :
    T.maxGenEigenspace μ ≤ T.eigenspace μ := by
  have hFm : ∀ x : X, F x ∈ contMemberSubmodule K Φ ξ := fun x => by
    rw [← hTF x]
    exact hXm _ (T x).2

  have hker : ∀ y : X, (T - μ • 1) ((T - μ • 1) y) = 0 → (T - μ • 1) y = 0 := by
    intro y h
    obtain ⟨u, hu⟩ : ∃ u : X, (T - μ • 1) y = u := ⟨_, rfl⟩
    rw [hu] at h ⊢
    have hTu : F (u : AdelicGL2 (𝓞 K) K → ℂ) = μ • (u : AdelicGL2 (𝓞 K) K → ℂ) := by
      have h1 : T u = μ • u := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
        exact h
      rw [← hTF u]
      exact congrArg Subtype.val h1
    have hyu : F (y : AdelicGL2 (𝓞 K) K → ℂ) - μ • (y : AdelicGL2 (𝓞 K) K → ℂ) = (u : AdelicGL2 (𝓞 K) K → ℂ) := by
      have h1 := congrArg Subtype.val hu
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub, Submodule.coe_smul,
        hTF] at h1
      exact h1
    by_contra hu0
    have hu0' : (u : AdelicGL2 (𝓞 K) K → ℂ) ≠ 0 := fun h0 => hu0 (Submodule.coe_eq_zero.1 h0)
    have huu : slabPairing K Φ (u : AdelicGL2 (𝓞 K) K → ℂ) u ≠ 0 := fun h0 =>
      hu0' (eq_zero_of_slabPairing_self_eq_zero hΦ₀ ξ u (hXm u u.2) h0)

    have hμ : μ = c * conj μ := by
      have h1 := hadj u u.2 u u.2
      rw [hTu, slabPairing_smul_left, slabPairing_smul_right, ← mul_assoc] at h1
      exact mul_right_cancel₀ huu h1

    have hPu : slabPairing K Φ (u : AdelicGL2 (𝓞 K) K → ℂ) u = 0 := by
      have h1 := hadj y y.2 u u.2
      rw [hTu, slabPairing_smul_right] at h1
      have h2 := slabPairing_sub_left (hFm y) ((contMemberSubmodule K Φ ξ).smul_mem μ (hXm y y.2)) (hXm u u.2)
      rw [hyu, slabPairing_smul_left] at h2
      rw [h2, h1, ← mul_assoc, ← hμ, sub_self]
    exact huu hPu
  have hpow : ∀ (k : ℕ) (y : X), ((T - μ • 1) ^ (k + 1)) y = 0 → (T - μ • 1) y = 0 := by
    intro k
    induction k with
    | zero =>
      intro y hy
      simpa only [zero_add, pow_one] using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, Module.End.mul_apply] at hy
      exact hker y (ih ((T - μ • 1) y) hy)
  intro x hx
  rw [Module.End.mem_maxGenEigenspace] at hx
  obtain ⟨k, hk⟩ := hx
  rw [Module.End.mem_eigenspace_iff]
  cases k with
  | zero =>
    rw [pow_zero, Module.End.one_apply] at hk
    rw [hk, map_zero, smul_zero]
  | succ k =>
    have h1 := hpow k x hk
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h1
    exact h1

section Span

variable (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
  (S : Finset (HeightOneSpectrum (𝓞 K))) (tys : ArchTypeFamily K)

private abbrev IsCutSpace (X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) : Prop :=
  ∀ x ∈ X, IsSmoothCuspAutomorphicFnAt K (slabPins K Φ) ξ x ∧ Continuous x ∧
    (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x (g * u) = x g) ∧
    x ∈ archCutSubmodule K tys

private abbrev IsHeckeStable (X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
    HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v)
      reps → ∀ x ∈ X, SmoothCusp.heckeCosetSum K reps x ∈ X

private abbrev pieces : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
  ⨆ (π : HeckeEigensystem K ℂ) (_ : π ∈ cuspClasses K (slabPins K Φ) ξ N S),
    isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ⊓ archCutSubmodule K tys

variable {ξ N S tys}

private theorem le_pieces_of_scalar (hN : N ≠ ⊥) {X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hX : IsCutSpace (Φ := Φ) ξ N tys X)
    (reps : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K)
    (hsys : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S), HeckeIntegralSeam.IsHeckeCosetSystem
      (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v) (reps v hv))
    (hsc : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S), ∃ μ : ℂ, ∀ x ∈ X,
      SmoothCusp.heckeCosetSum K (reps v hv) x = μ • x) :
    X ≤ pieces (Φ := Φ) ξ N S tys := by
  classical
  by_cases hX0 : X = ⊥
  · rw [hX0]
    exact bot_le
  have hXm : ∀ x ∈ X, x ∈ contMemberSubmodule K Φ ξ := fun x hx =>
    ⟨(mem_memberSubmodule_iff K Φ ξ x).2 (hX x hx).1.1.1, (hX x hx).2.1⟩
  choose μ hμ using hsc

  obtain ⟨π, hlevel, hzero, ha, hb⟩ : ∃ π : HeckeEigensystem K ℂ, π.level = N ∧
      (∀ v ∈ S, π.a v = 0 ∧ π.b v = 0) ∧ (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S), π.a v = μ v hv) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → π.toRawCentral.b v =
        ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
    refine ⟨{ level := N
              level_ne_bot := hN
              a := fun v => if hv : v ∈ S then 0 else μ v hv
              b := fun v => if v ∈ S then 0 else HeckeEigensystem.cNorm v *
                ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) },
      rfl, fun v hv => ⟨dif_pos hv, if_pos hv⟩, fun v hv => dif_neg hv, fun v hv => ?_⟩
    rw [HeckeEigensystem.toRawCentral_b]
    show (HeckeEigensystem.cNorm v)⁻¹ * (if v ∈ S then 0 else HeckeEigensystem.cNorm v *
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) = _
    rw [if_neg hv, inv_mul_cancel_left₀ (HeckeEigensystem.cNorm_ne_zero v)]

  have hiso : ∀ x ∈ X, IsIsotypicCuspFormAt K (slabPins K Φ) ξ N S π x := fun x hx =>
    { smoothCusp := (hX x hx).1
      continuous := (hX x hx).2.1
      level_invariant := (hX x hx).2.2.1
      hecke_eigen := fun v hv => ⟨reps v hv, hsys v hv, fun g => by
        rw [ha v hv]
        exact congrFun (hμ v hv x hx) g⟩
      central_eigen := fun v hv g => by
        rw [hb v hv]
        exact ((mem_memberSubmodule_iff' K Φ ξ x).1 (hXm x hx).1).1.central_transform
          ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ g }

  have hπ : π ∈ cuspClasses K (slabPins K Φ) ξ N S := by
    refine ⟨hlevel, hzero, ?_⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff X).1 hX0
    exact (Submodule.ne_bot_iff _).2 ⟨x, (hiso x hx).mem_isotypicCuspSubmodule, hx0⟩
  intro x hx
  exact Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hπ
    (Submodule.mem_inf.2 ⟨(hiso x hx).mem_isotypicCuspSubmodule, (hX x hx).2.2.2⟩))

private theorem le_pieces_of_not_scalar (hΦ₀ : IsSlabFundamentalDomain K α β Φ) (hN : N ≠ ⊥)
    (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S) {X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hfin : FiniteDimensional ℂ X) (hX : IsCutSpace (Φ := Φ) ξ N tys X) (hstab : IsHeckeStable (K := K) N S X)
    (reps : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K)
    (hsys : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S), HeckeIntegralSeam.IsHeckeCosetSystem
      (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v) (reps v hv))
    (hloc : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (i : Fin (Ideal.absNorm v.asIdeal + 1)),
      ∃ m : GL (Fin 2) (v.adicCompletion K), reps v hv i = AdelicDock.finEmbed (𝓞 K) K
        (AdelicDock.localEmbed (𝓞 K) K v m))
    {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∉ S)
    (hns : ∀ μ : ℂ, ∃ x ∈ X, SmoothCusp.heckeCosetSum K (reps v₀ hv₀) x ≠ μ • x)
    (ih : ∀ Y : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ Y →
      Module.finrank ℂ Y < Module.finrank ℂ X → IsCutSpace (Φ := Φ) ξ N tys Y → IsHeckeStable (K := K) N S Y →
      Y ≤ pieces (Φ := Φ) ξ N S tys) :
    X ≤ pieces (Φ := Φ) ξ N S tys := by
  haveI := hfin
  have hXm : ∀ x ∈ X, x ∈ contMemberSubmodule K Φ ξ := fun x hx =>
    ⟨(mem_memberSubmodule_iff K Φ ξ x).2 (hX x hx).1.1.1, (hX x hx).2.1⟩
  have hXU : ∀ x ∈ X, ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      x (g * u) = x g := fun x hx => (hX x hx).2.2.1
  have hT : ∀ x ∈ X, SmoothCusp.heckeCosetSum K (reps v₀ hv₀) x ∈ X := hstab v₀ hv₀ (reps v₀ hv₀) (hsys v₀ hv₀)

  have hne : ∀ μ : ℂ, (cosetEnd (reps v₀ hv₀) X hT).eigenspace μ ≠ ⊤ := by
    intro μ htop
    obtain ⟨x, hx, hxμ⟩ := hns μ
    have hmem : (⟨x, hx⟩ : X) ∈ (cosetEnd (reps v₀ hv₀) X hT).eigenspace μ := by
      rw [htop]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hmem
    exact hxμ (congrArg Subtype.val hmem)

  obtain ⟨c, -, hc⟩ := exists_slabPairing_heckeCosetSum_eq hΦ₀ ξ (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (heckeGen (𝓞 K) K v₀) (PrincipalCosetStandardness.hstd_principalLevel_heckeGen K N hN S hNS v₀ hv₀) (reps v₀ hv₀)
    (hsys v₀ hv₀)
  have hgen : ∀ μ : ℂ, (cosetEnd (reps v₀ hv₀) X hT).maxGenEigenspace μ ≤
      (cosetEnd (reps v₀ hv₀) X hT).eigenspace μ :=
    maxGenEigenspace_le_eigenspace hΦ₀ ξ X hXm (cosetEnd (reps v₀ hv₀) X hT)
      (SmoothCusp.heckeCosetSum K (reps v₀ hv₀)) (fun _ => rfl) c
      (fun a ha b hb => hc a b (hXm a ha) (hXm b hb) (hXU a ha) (hXU b hb))

  have hcomm : ∀ (w : HeightOneSpectrum (𝓞 K)) (hw : w ∉ S)
      (s : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 K) K),
      HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K w)
        s →
      ∀ x ∈ X, SmoothCusp.heckeCosetSum K (reps v₀ hv₀) (SmoothCusp.heckeCosetSum K s x) =
        SmoothCusp.heckeCosetSum K s (SmoothCusp.heckeCosetSum K (reps v₀ hv₀) x) := by
    intro w hw s hs x hx
    have h1 : SmoothCusp.heckeCosetSum K s x = SmoothCusp.heckeCosetSum K (reps w hw) x :=
      funext fun g => PrincipalCosetSumIndependence.cosetSum_eq_of_isHeckeCosetSystem hs (hsys w hw) x (hXU x hx) g
    have h2 : SmoothCusp.heckeCosetSum K s (SmoothCusp.heckeCosetSum K (reps v₀ hv₀) x) =
        SmoothCusp.heckeCosetSum K (reps w hw) (SmoothCusp.heckeCosetSum K (reps v₀ hv₀) x) :=
      funext fun g =>
        PrincipalCosetSumIndependence.cosetSum_eq_of_isHeckeCosetSystem hs (hsys w hw) _ (hXU _ (hT x hx)) g
    rw [h1, h2]
    by_cases hvw : v₀ = w
    · subst hvw
      rfl
    · refine heckeCosetSum_comm_of_forall_commute (fun i j => ?_) x
      obtain ⟨mi, hmi⟩ := hloc v₀ hv₀ i
      obtain ⟨mj, hmj⟩ := hloc w hw j
      rw [hmi, hmj, ← map_mul (AdelicDock.finEmbed (𝓞 K) K), ← map_mul (AdelicDock.finEmbed (𝓞 K) K),
        PrincipalCosetStandardness.localEmbed_mul_localEmbed_comm K v₀ hvw]

  have hE : ∀ μ : ℂ, ((cosetEnd (reps v₀ hv₀) X hT).eigenspace μ).map X.subtype ≤ pieces (Φ := Φ) ξ N S tys := by
    intro μ
    refine ih _ inferInstance ?_ ?_ ?_
    · rw [Submodule.finrank_map_subtype_eq]
      exact Submodule.finrank_lt (hne μ)
    · intro y hy
      obtain ⟨z, -, rfl⟩ := Submodule.mem_map.1 hy
      exact hX z z.2
    · intro w hw s hs y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      have hzX : SmoothCusp.heckeCosetSum K s (z : AdelicGL2 (𝓞 K) K → ℂ) ∈ X := hstab w hw s hs z z.2
      have hmem : (⟨_, hzX⟩ : X) ∈ (cosetEnd (reps v₀ hv₀) X hT).eigenspace μ := by
        rw [Module.End.mem_eigenspace_iff] at hz ⊢
        apply Subtype.ext
        show SmoothCusp.heckeCosetSum K (reps v₀ hv₀) (SmoothCusp.heckeCosetSum K s z) =
          μ • SmoothCusp.heckeCosetSum K s z
        have hz' : SmoothCusp.heckeCosetSum K (reps v₀ hv₀) (z : AdelicGL2 (𝓞 K) K → ℂ) =
            μ • (z : AdelicGL2 (𝓞 K) K → ℂ) := congrArg Subtype.val hz
        rw [hcomm w hw s hs z z.2, hz']
        funext g
        simp only [SmoothCusp.heckeCosetSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Submodule.mem_map_of_mem hmem

  intro x hx
  have htop : (⟨x, hx⟩ : X) ∈ ⨆ μ : ℂ, (cosetEnd (reps v₀ hv₀) X hT).maxGenEigenspace μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _
    (motive := fun y : X => (y : AdelicGL2 (𝓞 K) K → ℂ) ∈ pieces (Φ := Φ) ξ N S tys) htop ?_ ?_ ?_
  · intro μ y hy
    exact hE μ (Submodule.mem_map_of_mem (hgen μ hy))
  · show ((0 : X) : AdelicGL2 (𝓞 K) K → ℂ) ∈ pieces (Φ := Φ) ξ N S tys
    rw [Submodule.coe_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    show ((y + z : X) : AdelicGL2 (𝓞 K) K → ℂ) ∈ pieces (Φ := Φ) ξ N S tys
    rw [Submodule.coe_add]
    exact Submodule.add_mem _ hy hz

private theorem le_pieces (hΦ₀ : IsSlabFundamentalDomain K α β Φ) (hN : N ≠ ⊥)
    (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S) (n : ℕ) :
    ∀ X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ X → Module.finrank ℂ X = n →
      IsCutSpace (Φ := Φ) ξ N tys X → IsHeckeStable (K := K) N S X → X ≤ pieces (Φ := Φ) ξ N S tys := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X hfin hXn hX hstab

    have hsysE : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
          HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (heckeGen (𝓞 K) K v) reps ∧
          ∀ i, ∃ m : GL (Fin 2) (v.adicCompletion K), reps i = AdelicDock.finEmbed (𝓞 K) K
            (AdelicDock.localEmbed (𝓞 K) K v m) :=
      fun v hv =>
        PrincipalCosetStandardness.exists_fin_local_cosetSystem_principal K v N hN fun hdvd => hv (hNS v hdvd)
    choose reps hsys hloc using hsysE
    by_cases hsc : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S), ∃ μ : ℂ, ∀ x ∈ X,
        SmoothCusp.heckeCosetSum K (reps v hv) x = μ • x
    · exact le_pieces_of_scalar hN hX reps hsys hsc
    · push Not at hsc
      obtain ⟨v₀, hv₀, hns⟩ := hsc
      exact le_pieces_of_not_scalar hΦ₀ hN hNS hfin hX hstab reps hsys hloc hv₀ hns
        fun Y hYfin hlt hY hYstab => ih _ (hlt.trans_eq hXn) Y hYfin rfl hY hYstab

end Span

end PrincipalHeckeStableDecomposition

end SlabDecomposition

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm PrincipalHeckeStableDecomposition

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (tys : ArchTypeFamily K) (X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hX : ∀ x ∈ X,
      IsSmoothCuspAutomorphicFnAt K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ x ∧
        Continuous x ∧
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
          (productionPinsOf K Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N,
          x (g * u) = x g) ∧
        x ∈ archCutSubmodule K tys)
    (hfin : FiniteDimensional ℂ X)
    (hstab : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
        HeckeIntegralSeam.IsHeckeCosetSystem
          ((productionPinsOf K Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N)
          ((productionPinsOf K Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).gen v) reps →
        ∀ x ∈ X, SmoothCusp.heckeCosetSum K reps x ∈ X) :
    X ≤ ⨆ (π : HeckeEigensystem K ℂ) (_ : π ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S),
        isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys := by
  exact le_pieces (isSlabFundamentalDomain_of_binders hα hαβ hΦs hΦ) hN hNS _ X hfin rfl hX hstab

end
end S_AutomorphicForm_le_iSup_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
end P2MW
export P2MW.S_AutomorphicForm_le_iSup_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem (solution)
