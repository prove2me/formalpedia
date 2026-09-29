-- Prove2me | solution 1 for AutomorphicForm.not_exists_isNormOf_centralScalar_mul_globalPoints_of_div_not_mem_range_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c1045820-f25b-50fa-bda9-dae023f033b8

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime
import Theorems.Thm_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
import Theorems.Thm_AutomorphicForm_normString_map_baseChangeEquiv_symm_centralScalar_eq_toTensorGL_centralScalar_idelicNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_not_exists_isNormOf_centralScalar_mul_globalPoints_of_div_not_mem_range_norm
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

namespace NNV9

open AutomorphicForm

section general

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem val_mul_apply (x y : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((x * y : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i 0 * (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 j +
        (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i 1 * (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaGL_apply (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      sigmaTensor K L A σ ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := rfl

theorem sigmaGL_iterate_apply (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (⇑(sigmaTensor K L A σ))^[n] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sigmaGL_apply, ih]

theorem toTensorGL_apply (g : GL (Fin 2) A) (i j : Fin 2) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ((g : Matrix (Fin 2) (Fin 2) A) i j) := rfl

theorem prod_iterate_diag (x : GL (Fin 2) (L ⊗[K] A))
    (h01 : (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) (h10 : (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0)
    (n : ℕ) :
    ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] x).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
        ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0)).prod ∧
    ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] x).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
        ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)).prod ∧
    ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] x).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
    ((((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] x).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h00, h11, h01', h10'⟩ := ih
    have e01 : (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
      rw [sigmaGL_iterate_apply, h01]; exact Function.iterate_fixed (map_zero _) n
    have e10 : (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
      rw [sigmaGL_iterate_apply, h10]; exact Function.iterate_fixed (map_zero _) n
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [val_mul_apply, h00, h01', zero_mul, add_zero, sigmaGL_iterate_apply]
    · rw [val_mul_apply, h11, h10', zero_mul, zero_add, sigmaGL_iterate_apply]
    · rw [val_mul_apply, h01', e01, mul_zero, zero_mul, add_zero]
    · rw [val_mul_apply, h10', e10, mul_zero, zero_mul, add_zero]

theorem normString_diag_apply (x : GL (Fin 2) (L ⊗[K] A))
    (h01 : (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) (h10 : (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) :
    ((normString K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
        ((List.range (Module.finrank K L)).map
          fun i => (⇑(sigmaTensor K L A σ))^[i] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0)).prod ∧
    ((normString K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
        ((List.range (Module.finrank K L)).map
          fun i => (⇑(sigmaTensor K L A σ))^[i] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)).prod := by
  obtain ⟨h00, h11, -, -⟩ := prod_iterate_diag K L A σ x h01 h10 (Module.finrank K L)
  exact ⟨h00, h11⟩

theorem offdiag_eq_zero_of_commute (T t : GL (Fin 2) (L ⊗[K] A))
    (hT01 : (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0)
    (hreg : IsUnit ((T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 - (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1))
    (hc : T * t = t * T) :
    (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
  have hv := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) hc
  have e01 := congrFun (congrFun hv 0) 1
  have e10 := congrFun (congrFun hv 1) 0
  rw [val_mul_apply, val_mul_apply, hT01, zero_mul, add_zero, mul_zero, zero_add] at e01
  rw [val_mul_apply, val_mul_apply, hT10, zero_mul, zero_add, mul_zero, add_zero] at e10

  constructor
  · have h : ((T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 - (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) *
        (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
      rw [sub_mul, e01, mul_comm, sub_self]
    exact (hreg.mul_right_eq_zero).mp h
  · have h : ((T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 - (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) *
        (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
      rw [sub_mul, e10, mul_comm, sub_self]
    exact (hreg.mul_right_eq_zero).mp h

end general

end NNV9

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (γ : GL (Fin 2) K) (hγ10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (hγ01 : (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (hnn : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∉
      Set.range (Algebra.norm K : L → K))
    (z : (AdeleRing (𝓞 K) K)ˣ) :
    ¬ ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ
        (AutomorphicForm.centralScalar (𝓞 K) K z * AutomorphicForm.globalPoints (𝓞 K) K γ) δ  := by
  classical
  rintro ⟨δ, hδ⟩
  set A := AdeleRing (𝓞 K) K with hA

  have hσ : σ ≠ 1 := by
    intro h1
    have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
      have := hgen τ
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
      exact this
    have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
    haveI : Subsingleton (L ≃ₐ[K] L) := ⟨fun a b => by rw [hall a, hall b]⟩
    have h1' : Nat.card (L ≃ₐ[K] L) = 1 := Nat.card_of_subsingleton (1 : L ≃ₐ[K] L)
    rw [h1'] at hcard
    exact hprime.one_lt.ne hcard

  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, fun τ => Subgroup.mem_zpowers_iff.mp (hgen τ)⟩⟩

  have hdetγ : (γ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [Matrix.det_fin_two, hγ10, mul_zero, sub_zero] at hdetγ
  obtain ⟨hγ00, hγ11⟩ := mul_ne_zero_iff.mp hdetγ
  have hne : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ (γ : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    intro heq
    apply hnn
    refine ⟨1, ?_⟩
    show Algebra.norm K (1 : L) = _
    rw [map_one, heq, div_self hγ11]

  set g : GL (Fin 2) A := centralScalar (𝓞 K) K z * globalPoints (𝓞 K) K γ with hg
  obtain ⟨t, x, ht, hN, -⟩ :=
    AutomorphicForm.exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime K L hprime σ hσ A g δ hδ
  set T : GL (Fin 2) (L ⊗[K] A) := toTensorGL K L A g with hT
  set iR : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight with hiR
  have hiRinj : Function.Injective iR := Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

  have hcs : ∀ i j : Fin 2, ((centralScalar (𝓞 K) K z : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      if i = j then (z : A) else 0 := by
    intro i j
    change Matrix.scalar (Fin 2) (z : A) i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  have hgp : ∀ i j : Fin 2, ((globalPoints (𝓞 K) K γ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      algebraMap K A ((γ : Matrix (Fin 2) (Fin 2) K) i j) := fun _ _ => rfl
  have hg00 : ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = (z : A) * algebraMap K A ((γ : Matrix (Fin 2) (Fin 2) K) 0 0) := by
    rw [hg, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hcs, hcs, hgp, hgp]; simp [hγ10]
  have hg11 : ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = (z : A) * algebraMap K A ((γ : Matrix (Fin 2) (Fin 2) K) 1 1) := by
    rw [hg, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hcs, hcs, hgp, hgp]; simp [hγ01]
  have hg01 : ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := by
    rw [hg, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hcs, hcs, hgp, hgp]; simp [hγ01]
  have hg10 : ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
    rw [hg, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hcs, hcs, hgp, hgp]; simp [hγ10]

  have hT01 : (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
    rw [hT, NNV9.toTensorGL_apply, hg01, map_zero]
  have hT10 : (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
    rw [hT, NNV9.toTensorGL_apply, hg10, map_zero]
  have hT00 : (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 = iR ((z : A) * algebraMap K A ((γ : Matrix (Fin 2) (Fin 2) K) 0 0)) := by
    rw [hT, NNV9.toTensorGL_apply, hg00]
  have hT11 : (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 = iR ((z : A) * algebraMap K A ((γ : Matrix (Fin 2) (Fin 2) K) 1 1)) := by
    rw [hT, NNV9.toTensorGL_apply, hg11]
  have hregK : IsUnit ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 - (γ : Matrix (Fin 2) (Fin 2) K) 1 1) :=
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hreg : IsUnit ((T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 - (T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := by
    rw [hT00, hT11, ← map_sub, ← mul_sub, ← map_sub]
    exact ((Units.isUnit z).mul (hregK.map (algebraMap K A))).map iR
  have hcomm : T * t = t * T := (Subgroup.mem_centralizer_iff.mp ht) T (Set.mem_singleton _)
  obtain ⟨ht01, ht10⟩ := NNV9.offdiag_eq_zero_of_commute K L A T t hT01 hT10 hreg hcomm

  set a : L ⊗[K] A := (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 with ha
  set b : L ⊗[K] A := (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 with hb
  have hdet : IsUnit (a * b) := by
    have h := (Matrix.isUnits_det_units t)
    rw [Matrix.det_fin_two, ht01, ht10] at h
    simpa [ha, hb] using h
  obtain ⟨hau, hbu⟩ := IsUnit.mul_iff.mp hdet

  set β := baseChangeEquiv K L with hβ
  set N := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hNdef
  have central : ∀ (u : L ⊗[K] A) (hu : IsUnit u),
      ((List.range (Module.finrank K L)).map fun i => (⇑(sigmaTensor K L A σ))^[i] u).prod =
        iR (((N (Units.map (β : L ⊗[K] A →* AdeleRing (𝓞 L) L) hu.unit)) : (AdeleRing (𝓞 K) K)ˣ) : A) := by
    intro u hu
    set w : (AdeleRing (𝓞 L) L)ˣ := Units.map (β : L ⊗[K] A →* AdeleRing (𝓞 L) L) hu.unit with hw
    have hsrv := AutomorphicForm.normString_map_baseChangeEquiv_symm_centralScalar_eq_toTensorGL_centralScalar_idelicNorm
      K L σ hgen w
    set cw : GL (Fin 2) (L ⊗[K] A) := Matrix.GeneralLinearGroup.map (baseChangeEquiv K L).symm.toRingHom
      (centralScalar (𝓞 L) L w) with hcw
    have hcwval : ∀ i j : Fin 2, ((cw : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
        if i = j then u else 0 := by
      intro i j
      change (baseChangeEquiv K L).symm.toRingHom (Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 L) L) i j) = _
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · rw [hw, Units.coe_map, IsUnit.unit_spec]
        change (baseChangeEquiv K L).symm (baseChangeEquiv K L u) = u
        exact (baseChangeEquiv K L).symm_apply_apply u
      · exact map_zero _
    have hcw01 : ((cw : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by rw [hcwval]; simp
    have hcw10 : ((cw : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by rw [hcwval]; simp
    have hcw00 : ((cw : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 = u := by rw [hcwval]; simp
    have h00 := (NNV9.normString_diag_apply K L A σ cw hcw01 hcw10).1
    rw [hcw00] at h00
    rw [← h00]
    have := congrArg (fun M : GL (Fin 2) (L ⊗[K] A) => (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) hsrv
    rw [hcw] at this ⊢
    rw [this, NNV9.toTensorGL_apply]
    congr 1
    all_goals simp [Matrix.scalar_apply]

  obtain ⟨hN00, hN11⟩ := NNV9.normString_diag_apply K L A σ t ht01 ht10
  have hNv := congrArg (fun M : GL (Fin 2) (L ⊗[K] A) => (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) hN
  have e00 := congrFun (congrFun hNv 0) 0
  have e11 := congrFun (congrFun hNv 1) 1
  rw [hN00, central a hau, hT00] at e00
  rw [hN11, central b hbu, hT11] at e11
  have f00 := hiRinj e00
  have f11 := hiRinj e11

  set wa : (AdeleRing (𝓞 L) L)ˣ := Units.map (β : L ⊗[K] A →* AdeleRing (𝓞 L) L) hau.unit with hwa
  set wb : (AdeleRing (𝓞 L) L)ˣ := Units.map (β : L ⊗[K] A →* AdeleRing (𝓞 L) L) hbu.unit with hwb
  set aK : Kˣ := Units.mk0 ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1)
    (div_ne_zero hγ00 hγ11) with haK
  have hunits : Units.map (algebraMap K A : K →* A) aK * N wb = N wa := by
    apply Units.ext
    rw [Units.val_mul, Units.coe_map, f00, f11, haK, Units.val_mk0, MonoidHom.coe_coe]
    rw [mul_left_comm, ← map_mul, div_mul_cancel₀ _ hγ11]
  have hrange : Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) aK ∈
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range := by
    refine ⟨wa * wb⁻¹, ?_⟩
    rw [map_mul, map_inv, ← hNdef, ← hunits, mul_inv_cancel_right]
  obtain ⟨bL, hbL⟩ := NumberField.exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic K L aK hrange
  exact hnn ⟨bL, by rw [hbL, haK, Units.val_mk0]⟩

end S_AutomorphicForm_not_exists_isNormOf_centralScalar_mul_globalPoints_of_div_not_mem_range_norm
end P2MW
export P2MW.S_AutomorphicForm_not_exists_isNormOf_centralScalar_mul_globalPoints_of_div_not_mem_range_norm (solution)
