-- Prove2me | solution 1 for AutomorphicForm.exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/90f83324-817f-5487-bfef-a6f91cacea3d

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
import Theorems.Thm_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport"
p2m_attr_erase "simp" "RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open FLT.SmoothVectors IsDedekindDomain
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace LevelAverageFinSol

variable {F : Type} [Field F] [NumberField F]

local notation "𝔾" => AdelicGL2 (𝓞 F) F

section RightTranslation

variable (F)

def rt (a : AdelicGL2 (𝓞 F) F) : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun f := fun y => f (y * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rtHom : AdelicGL2 (𝓞 F) F →* ((AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) where
  toFun := rt F
  map_one' := by
    apply LinearMap.ext; intro f; funext y
    show f (y * 1) = f y
    rw [mul_one]
  map_mul' a b := by
    apply LinearMap.ext; intro f; funext y
    show f (y * (a * b)) = f (y * a * b)
    rw [mul_assoc]

variable {F}

@[scoped simp] theorem rt_apply (a : 𝔾) (f : 𝔾 → ℂ) (y : 𝔾) : rt F a f y = f (y * a) := rfl

@[scoped simp] theorem rtHom_apply (a : 𝔾) : rtHom F a = rt F a := rfl

theorem rt_rt (a b : 𝔾) (f : 𝔾 → ℂ) : rt F a (rt F b f) = rt F (a * b) f := by
  funext y; simp [mul_assoc]

theorem rt_one (f : 𝔾 → ℂ) : rt F 1 f = f := by funext y; simp

theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 F) F) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (↑g⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

def finPart (x : 𝔾) : 𝔾 := AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F x)

def archPart (x : 𝔾) : 𝔾 := x * (finPart x)⁻¹

theorem finPart_mem (x : 𝔾) : finPart x ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact AdelicDock.glArch_finEmbed (𝓞 F) F _

theorem glFin_finPart (x : 𝔾) : glFin (𝓞 F) F (finPart x) = glFin (𝓞 F) F x :=
  AdelicDock.glFin_finEmbed (𝓞 F) F _

theorem glFin_archPart (x : 𝔾) : glFin (𝓞 F) F (archPart x) = 1 := by
  unfold archPart
  rw [map_mul, map_inv, glFin_finPart, mul_inv_cancel]

theorem archPart_mul_finPart (x : 𝔾) : archPart x * finPart x = x := by
  unfold archPart; rw [inv_mul_cancel_right]

theorem comm_of_glFin_eq_one {a k : 𝔾} (ha : glFin (𝓞 F) F a = 1)
    (hk : k ∈ finiteAdelicGL2Subgroup F) : k * a = a * k := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hk
  apply Units.ext
  have harch : ∀ g : 𝔾, (adeleArch (𝓞 F) F).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix _ _ _) := fun g => rfl
  have hfin : ∀ g : 𝔾, (adeleFin (𝓞 F) F).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _) := fun g => rfl
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [Units.val_mul, Units.val_mul, map_mul, map_mul, harch, harch, hk, Units.val_one, one_mul,
      mul_one]
  · rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hfin, hfin, ha, Units.val_one, one_mul,
      mul_one]

theorem archPart_comm {x k : 𝔾} (hk : k ∈ finiteAdelicGL2Subgroup F) :
    k * archPart x = archPart x * k :=
  comm_of_glFin_eq_one (glFin_archPart x) hk

end RightTranslation

section LevelAverage

variable (U : Subgroup (AdelicGL2 (𝓞 F) F))

def stabU (f : 𝔾 → ℂ) : Subgroup U :=
  MulAction.stabilizer U (RightTranslationFn.mk f : RightTranslationFn 𝔾 ℂ)

variable {U}

theorem mem_stabU_iff (f : 𝔾 → ℂ) (k : U) : k ∈ stabU U f ↔ ∀ y, f (y * (k : 𝔾)) = f y := by
  unfold stabU
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  constructor
  · intro h y
    have := congrArg (fun φ => RightTranslationFn.toFun φ y) h
    simpa using this
  · intro h
    exact RightTranslationFn.ext fun y => by simpa using h y

variable (U)

def avg (H : Subgroup U) (f : 𝔾 → ℂ) : 𝔾 → ℂ :=
  fun y => (Nat.card (U ⧸ H) : ℂ)⁻¹ * ∑ᶠ q : U ⧸ H, f (y * ((q.out : U) : 𝔾))

def levelAvg (f : 𝔾 → ℂ) : 𝔾 → ℂ := avg U (stabU U f) f

variable {U}

theorem avg_apply_of_finite (H : Subgroup U) [Fintype (U ⧸ H)] (f : 𝔾 → ℂ) (y : 𝔾) :
    avg U H f y = (Nat.card (U ⧸ H) : ℂ)⁻¹ * ∑ q : U ⧸ H, f (y * ((q.out : U) : 𝔾)) := by
  unfold avg
  rw [finsum_eq_sum_of_fintype]

theorem avg_eq_sum (H : Subgroup U) [Fintype (U ⧸ H)] (f : 𝔾 → ℂ) :
    avg U H f = (Nat.card (U ⧸ H) : ℂ)⁻¹ • ∑ q : U ⧸ H, rt F ((q.out : U) : 𝔾) f := by
  funext y
  rw [avg_apply_of_finite, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rfl

theorem apply_mul_out_eq {K : Subgroup U} {f : 𝔾 → ℂ} (hK : K ≤ stabU U f) (y : 𝔾) (a : U) :
    f (y * (((QuotientGroup.mk a : U ⧸ K).out : U) : 𝔾)) = f (y * (a : 𝔾)) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K a
  rw [hh, Subgroup.coe_mul, ← mul_assoc]
  exact (mem_stabU_iff f _).mp (hK h.2) _

theorem avg_eq_avg_of_le {H K : Subgroup U} [Fintype (U ⧸ H)] [Fintype (U ⧸ K)] (hHK : H ≤ K)
    {f : 𝔾 → ℂ} (hK : K ≤ stabU U f) : avg U H f = avg U K f := by
  classical
  set e := Subgroup.quotientEquivProdOfLE hHK with he
  haveI : Finite ((U ⧸ K) × (K ⧸ H.subgroupOf K)) := Finite.of_equiv _ e
  haveI : Finite (K ⧸ H.subgroupOf K) :=
    Finite.of_injective (fun r => ((QuotientGroup.mk 1 : U ⧸ K), r)) (Prod.mk_right_injective _)
  letI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  funext y
  rw [avg_apply_of_finite, avg_apply_of_finite]
  set g : U ⧸ K → ℂ := fun Q => f (y * ((Q.out : U) : 𝔾)) with hg

  have h1 : ∀ q : U ⧸ H, f (y * ((q.out : U) : 𝔾)) = g (Subgroup.quotientMapOfLE hHK q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [Subgroup.quotientMapOfLE_apply_mk, hg]
      dsimp only
      rw [apply_mul_out_eq (f := f) hK, apply_mul_out_eq (f := f) (hHK.trans hK)]

  have h2 : ∑ q : U ⧸ H, g (Subgroup.quotientMapOfLE hHK q)
      = ∑ p : (U ⧸ K) × (K ⧸ H.subgroupOf K), g p.1 := by
    refine Fintype.sum_equiv e _ _ fun q => ?_
    rfl
  set b : ℂ := (Fintype.card (K ⧸ H.subgroupOf K) : ℂ) with hb
  have h3 : ∑ p : (U ⧸ K) × (K ⧸ H.subgroupOf K), g p.1 = b * ∑ Q : U ⧸ K, g Q := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hcard : (Nat.card (U ⧸ H) : ℂ) = Nat.card (U ⧸ K) * b := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_congr e,
      Fintype.card_prod, Nat.cast_mul]
  have hne : b ≠ 0 := by
    rw [hb]; exact_mod_cast Fintype.card_ne_zero
  simp_rw [h1]
  rw [h2, h3, hcard, mul_inv, mul_assoc, ← mul_assoc b⁻¹, inv_mul_cancel₀ hne, one_mul]

theorem finite_quotient_of_le {H K : Subgroup U} [Finite (U ⧸ H)] (hHK : H ≤ K) :
    Finite (U ⧸ K) := by
  refine Finite.of_surjective (Subgroup.quotientMapOfLE hHK) fun Q => ?_
  induction Q using QuotientGroup.induction_on with
  | H a => exact ⟨QuotientGroup.mk a, Subgroup.quotientMapOfLE_apply_mk hHK a⟩

theorem levelAvg_eq_avg {H : Subgroup U} [Fintype (U ⧸ H)] {f : 𝔾 → ℂ} (hH : H ≤ stabU U f) :
    levelAvg U f = avg U H f := by
  haveI : Finite (U ⧸ stabU U f) := finite_quotient_of_le hH
  letI : Fintype (U ⧸ stabU U f) := Fintype.ofFinite _
  exact (avg_eq_avg_of_le hH le_rfl).symm

theorem levelAvg_eq_sum (f : 𝔾 → ℂ) [Fintype (U ⧸ stabU U f)] :
    levelAvg U f = (Nat.card (U ⧸ stabU U f) : ℂ)⁻¹ •
      ∑ q : U ⧸ stabU U f, rt F ((q.out : U) : 𝔾) f :=
  avg_eq_sum _ f

theorem levelAvg_of_invariant {f : 𝔾 → ℂ} (hf : ∀ y, ∀ k ∈ U, f (y * k) = f y) :
    levelAvg U f = f := by
  have htop : (⊤ : Subgroup U) ≤ stabU U f := fun k _ => (mem_stabU_iff f k).mpr fun y => hf y k k.2
  haveI : Subsingleton (U ⧸ (⊤ : Subgroup U)) := QuotientGroup.subsingleton_quotient_top
  letI : Fintype (U ⧸ (⊤ : Subgroup U)) := Fintype.ofFinite _
  rw [levelAvg_eq_avg htop]
  funext y
  rw [avg_apply_of_finite]
  have h1 : (Finset.univ : Finset (U ⧸ (⊤ : Subgroup U))) = {QuotientGroup.mk 1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨Finset.mem_univ _, fun q _ => Subsingleton.elim _ _⟩
  rw [h1, Finset.sum_singleton, Nat.card_eq_fintype_card, ← Finset.card_univ, h1,
    Finset.card_singleton, Nat.cast_one, inv_one, one_mul]
  exact hf y _ (Subtype.coe_prop _)

theorem levelAvg_invariant {f : 𝔾 → ℂ} [Fintype (U ⧸ stabU U f)] (y : 𝔾) (k : 𝔾) (hk : k ∈ U) :
    levelAvg U f (y * k) = levelAvg U f y := by
  letI : MulAction U (U ⧸ stabU U f) := MulAction.quotient U (stabU U f)
  unfold levelAvg
  rw [avg_apply_of_finite, avg_apply_of_finite]
  congr 1

  set kU : U := ⟨k, hk⟩ with hkU
  have hperm : ∀ q : U ⧸ stabU U f,
      f (y * k * ((q.out : U) : 𝔾)) = f (y * (((kU • q).out : U) : 𝔾)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [MulAction.Quotient.smul_mk, apply_mul_out_eq (f := f) le_rfl,
        apply_mul_out_eq (f := f) le_rfl, smul_eq_mul, Subgroup.coe_mul, ← mul_assoc]
  simp_rw [hperm]
  exact Fintype.sum_equiv (MulAction.toPerm kU) _ _ fun q => rfl

theorem levelAvg_lincomb (a b : ℂ) {f g : 𝔾 → ℂ} [Fintype (U ⧸ (stabU U f ⊓ stabU U g))] :
    levelAvg U (a • f + b • g) = a • levelAvg U f + b • levelAvg U g := by
  have hle : stabU U f ⊓ stabU U g ≤ stabU U (a • f + b • g) := by
    intro k hk
    rw [mem_stabU_iff]
    intro y
    have h1 := (mem_stabU_iff f k).mp hk.1 y
    have h2 := (mem_stabU_iff g k).mp hk.2 y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
  rw [levelAvg_eq_avg hle, levelAvg_eq_avg (inf_le_left : stabU U f ⊓ stabU U g ≤ _),
    levelAvg_eq_avg (inf_le_right : stabU U f ⊓ stabU U g ≤ _)]
  rw [avg_eq_sum, avg_eq_sum, avg_eq_sum]
  simp only [map_add, map_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  congr 1 <;> · refine Finset.sum_congr rfl fun q _ => ?_; rw [smul_comm]

theorem levelAvg_rt_comm {a : 𝔾} (ha : ∀ k ∈ U, k * a = a * k) {f : 𝔾 → ℂ}
    [Fintype (U ⧸ stabU U f)] : levelAvg U (rt F a f) = rt F a (levelAvg U f) := by
  have hle : stabU U f ≤ stabU U (rt F a f) := by
    intro k hk
    rw [mem_stabU_iff]
    intro y
    simp only [rt_apply]
    rw [mul_assoc, ha k k.2, ← mul_assoc]
    exact (mem_stabU_iff f k).mp hk _
  rw [levelAvg_eq_avg hle]
  unfold levelAvg
  funext y
  rw [avg_apply_of_finite, rt_apply, avg_apply_of_finite]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [rt_apply, mul_assoc, ha _ (Subtype.coe_prop _), ← mul_assoc]

variable (F)

def levelU (N : Ideal (𝓞 F)) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F

variable {F}

theorem levelU_le_fin (N : Ideal (𝓞 F)) : levelU F N ≤ finiteAdelicGL2Subgroup F := inf_le_right

theorem levelU_eq_image (N : Ideal (𝓞 F)) :
    (levelU F N : Set 𝔾) = AdelicDock.finEmbed (𝓞 F) F '' (finiteLevelOne (𝓞 F) F N) := by
  ext k
  constructor
  · intro hk
    have hk1 : k ∈ levelOne (𝓞 F) F N := hk.1
    have hk2 : k ∈ finiteAdelicGL2Subgroup F := hk.2
    refine ⟨glFin (𝓞 F) F k, (mem_levelOne_iff).mp hk1, ?_⟩
    rw [mem_finiteAdelicGL2Subgroup_iff] at hk2
    apply Units.ext
    have harch : ∀ g : 𝔾, (adeleArch (𝓞 F) F).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix _ _ _) := fun g => rfl
    have hfin : ∀ g : 𝔾, (adeleFin (𝓞 F) F).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _) := fun g => rfl
    refine (AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_).symm
    · rw [harch, harch, AdelicDock.glArch_finEmbed, hk2]
    · rw [hfin, hfin, AdelicDock.glFin_finEmbed]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(AdelicDock.finEmbed_mem_levelOne_iff (𝓞 F) F g).mpr hg, ?_⟩
    show AdelicDock.finEmbed (𝓞 F) F g ∈ finiteAdelicGL2Subgroup F
    rw [mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]

theorem isCompact_levelU (N : Ideal (𝓞 F)) : IsCompact (levelU F N : Set 𝔾) := by
  rw [levelU_eq_image]
  exact (isCompact_finiteLevelOne (R := 𝓞 F) (K := F) (N := N)).image continuous_finEmbed

scoped instance compactSpace_levelU (N : Ideal (𝓞 F)) : CompactSpace (levelU F N) :=
  isCompact_iff_compactSpace.mp (isCompact_levelU N)

theorem glFin_mem_integral_of_mem_levelU {N : Ideal (𝓞 F)} {k : 𝔾} (hk : k ∈ levelU F N) :
    glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F := by
  have hk1 : glFin (𝓞 F) F k ∈ finiteLevelOne (𝓞 F) F N := (mem_levelOne_iff).mp hk.1
  rw [mem_finiteIntegralGL2_iff]
  exact ⟨hk1.1.integral, hk1.2.integral⟩

theorem isOpen_stabU_of_isKfSmooth {N : Ideal (𝓞 F)} {f : 𝔾 → ℂ} (hf : IsKfSmooth F f) :
    IsOpen (stabU (levelU F N) f : Set (levelU F N)) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hf
  let incl : levelU F N → finiteAdelicGL2Subgroup F := fun k => ⟨k, levelU_le_fin N k.2⟩
  have hincl : Continuous incl := continuous_induced_rng.mpr continuous_subtype_val
  have hset : (stabU (levelU F N) f : Set (levelU F N))
      = incl ⁻¹' ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
          (RightTranslationFn.mk f : RightTranslationFn 𝔾 ℂ) : Subgroup _) : Set _) := by
    ext k
    simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    rfl
  rw [hset]
  exact hf.preimage hincl

theorem finite_quotient_of_isOpen {N : Ideal (𝓞 F)} (H : Subgroup (levelU F N))
    (hH : IsOpen (H : Set (levelU F N))) : Finite (levelU F N ⧸ H) :=
  Subgroup.quotient_finite_of_isOpen _ hH

end LevelAverage

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section GenericMeasure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lintegral_sq_lt_top_of_memLp {f : α → ℂ} (hf : MemLp f 2 μ) :
    ∫⁻ y, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂μ < ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hf.eLpNorm_lt_top
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact h

theorem memLp_of_lintegral_sq_lt_top {f : α → ℂ} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ y, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂μ < ⊤) : MemLp f 2 μ := by
  refine ⟨hf, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact h

theorem norm_toLp_sq {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = (∫⁻ y, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal := by
  rw [Lp.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, one_div]
  rw [← ENNReal.toReal_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  rfl

end GenericMeasure

section Context

variable (F)

structure Ctx where
  c : ℝ
  u : ℝ
  d₁ : ℝ
  d₂ : ℝ
  T : Finset (AdelicGL2 (𝓞 F) F)
  hc : 0 < c
  hd₁ : 0 < d₁
  hd : d₁ < d₂
  hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
  ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ
  ν : Measure (AdelicGL2 (𝓞 F) F)
  M : ℝ≥0∞
  χ : AdelicGL2 (𝓞 F) F → ℝ≥0∞
  hM : M ≠ ⊤
  hχ : ∀ x, χ x ≠ 0 ∧ χ x ≠ ⊤
  hχ1 : ∀ k ∈ finiteAdelicGL2Subgroup F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F → χ k = 1
  hB1 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
    ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤
      M * ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, (‖φ y‖₊ : ℝ≥0∞) ^ 2
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
  hB2 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
    ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, (‖φ y‖₊ : ℝ≥0∞) ^ 2
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤ M * ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν
  hB3 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ ξ φ → ∀ x,
    ∫⁻ y, (‖φ (y * x)‖₊ : ℝ≥0∞) ^ 2 ∂ν = χ x * ∫⁻ y, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂ν

variable {F} (C : Ctx F)

namespace Ctx

def D : Set 𝔾 := ⋃ x ∈ C.T, (· * x) '' centreCutSiegelSet F C.c C.u C.d₁ C.d₂

def dm (f : 𝔾 → ℂ) : ℝ≥0∞ := ∫⁻ y in C.D, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

def nm (f : 𝔾 → ℂ) : ℝ≥0∞ := ∫⁻ y, (‖f y‖₊ : ℝ≥0∞) ^ 2 ∂C.ν

theorem nm_le {f : 𝔾 → ℂ} (hf : Continuous f) (hξ : IsLsXiFunction (𝓞 F) F ⊤ C.ξ f) :
    C.nm f ≤ C.M * C.dm f := C.hB1 f hf hξ

theorem dm_le {f : 𝔾 → ℂ} (hf : Continuous f) (hξ : IsLsXiFunction (𝓞 F) F ⊤ C.ξ f) :
    C.dm f ≤ C.M * C.nm f := C.hB2 f hf hξ

theorem nm_rt {f : 𝔾 → ℂ} (hf : Continuous f) (hξ : IsLsXiFunction (𝓞 F) F ⊤ C.ξ f) (x : 𝔾) :
    C.nm (rt F x f) = C.χ x * C.nm f := C.hB3 f hf hξ x

theorem isLsXi_add {f g : 𝔾 → ℂ} (hf : IsLsXiFunction (𝓞 F) F ⊤ C.ξ f)
    (hg : IsLsXiFunction (𝓞 F) F ⊤ C.ξ g) : IsLsXiFunction (𝓞 F) F ⊤ C.ξ (f + g) :=
  ⟨fun γ y => by simp only [Pi.add_apply, hf.left_invariant, hg.left_invariant],
   fun z y => by simp only [Pi.add_apply, hf.central_transform, hg.central_transform, mul_add]⟩

theorem isLsXi_smul (a : ℂ) {f : 𝔾 → ℂ} (hf : IsLsXiFunction (𝓞 F) F ⊤ C.ξ f) :
    IsLsXiFunction (𝓞 F) F ⊤ C.ξ (a • f) :=
  ⟨fun γ y => by simp only [Pi.smul_apply, hf.left_invariant],
   fun z y => by simp only [Pi.smul_apply, hf.central_transform, smul_eq_mul]; ring⟩

theorem isLsXi_rt (x : 𝔾) {f : 𝔾 → ℂ} (hf : IsLsXiFunction (𝓞 F) F ⊤ C.ξ f) :
    IsLsXiFunction (𝓞 F) F ⊤ C.ξ (rt F x f) :=
  ⟨fun γ y => by simp only [rt_apply, mul_assoc, hf.left_invariant],
   fun z y => by simp only [rt_apply, mul_assoc, hf.central_transform]⟩

theorem isLsXi_zero : IsLsXiFunction (𝓞 F) F ⊤ C.ξ (0 : 𝔾 → ℂ) :=
  isLsXiFunction_zero (𝓞 F) F ⊤ C.ξ

theorem continuous_rt (x : 𝔾) {f : 𝔾 → ℂ} (hf : Continuous f) : Continuous (rt F x f) :=
  hf.comp (continuous_id.mul continuous_const)

def 𝓛 : Submodule ℂ (𝔾 → ℂ) where
  carrier := {f | Continuous f ∧ IsLsXiFunction (𝓞 F) F ⊤ C.ξ f ∧
    MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict C.D)}
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    exact ⟨hf1.add hg1, C.isLsXi_add hf2 hg2, hf3.add hg3⟩
  zero_mem' := ⟨continuous_const, C.isLsXi_zero, MemLp.zero'⟩
  smul_mem' := by
    rintro a f ⟨hf1, hf2, hf3⟩
    exact ⟨continuous_const.mul hf1, C.isLsXi_smul a hf2, hf3.const_smul a⟩

theorem continuous_of_mem {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) : Continuous f := hf.1

theorem isLsXi_of_mem {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) : IsLsXiFunction (𝓞 F) F ⊤ C.ξ f := hf.2.1

theorem memLp_of_mem {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) :
    MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict C.D) := hf.2.2

theorem dm_lt_top {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) : C.dm f < ⊤ :=
  lintegral_sq_lt_top_of_memLp (C.memLp_of_mem hf)

theorem nm_lt_top {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) : C.nm f < ⊤ :=
  lt_of_le_of_lt (C.nm_le hf.1 hf.2.1) (ENNReal.mul_lt_top C.hM.lt_top (C.dm_lt_top hf))

theorem mem_𝓛_of_dm_lt_top {f : 𝔾 → ℂ} (hf : Continuous f)
    (hξ : IsLsXiFunction (𝓞 F) F ⊤ C.ξ f) (hd : C.dm f < ⊤) : f ∈ C.𝓛 :=
  ⟨hf, hξ, memLp_of_lintegral_sq_lt_top hf.aestronglyMeasurable hd⟩

theorem rt_mem {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) (x : 𝔾) : rt F x f ∈ C.𝓛 := by
  refine C.mem_𝓛_of_dm_lt_top (continuous_rt x hf.1) (C.isLsXi_rt x hf.2.1) ?_
  have h1 := C.dm_le (continuous_rt x hf.1) (C.isLsXi_rt x hf.2.1)
  have h2 := C.nm_rt hf.1 hf.2.1 x
  calc C.dm (rt F x f) ≤ C.M * C.nm (rt F x f) := h1
    _ = C.M * (C.χ x * C.nm f) := by rw [h2]
    _ < ⊤ := ENNReal.mul_lt_top C.hM.lt_top
        (ENNReal.mul_lt_top (C.hχ x).2.lt_top (C.nm_lt_top hf))

theorem memLpν {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) : MemLp f 2 C.ν :=
  memLp_of_lintegral_sq_lt_top hf.1.aestronglyMeasurable (C.nm_lt_top hf)

def emb (f : 𝔾 → ℂ) : Lp ℂ 2 C.ν :=
  by classical exact if h : MemLp f 2 C.ν then h.toLp f else 0

theorem emb_eq {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) : C.emb f = (C.memLpν hf).toLp f := by
  unfold emb; rw [dif_pos (C.memLpν hf)]

theorem norm_emb_sq {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) : ‖C.emb f‖ ^ 2 = (C.nm f).toReal := by
  rw [C.emb_eq hf, norm_toLp_sq]; rfl

theorem emb_lincomb (a b : ℂ) {f g : 𝔾 → ℂ} (hf : f ∈ C.𝓛) (hg : g ∈ C.𝓛) :
    C.emb (a • f + b • g) = a • C.emb f + b • C.emb g := by
  have hfg : a • f + b • g ∈ C.𝓛 := C.𝓛.add_mem (C.𝓛.smul_mem a hf) (C.𝓛.smul_mem b hg)
  rw [C.emb_eq hfg, C.emb_eq hf, C.emb_eq hg, ← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul,
    ← MemLp.toLp_add]

theorem emb_add {f g : 𝔾 → ℂ} (hf : f ∈ C.𝓛) (hg : g ∈ C.𝓛) :
    C.emb (f + g) = C.emb f + C.emb g := by
  simpa using C.emb_lincomb 1 1 hf hg

theorem emb_smul (a : ℂ) {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) : C.emb (a • f) = a • C.emb f := by
  simpa using C.emb_lincomb a 0 hf hf

theorem emb_sub {f g : 𝔾 → ℂ} (hf : f ∈ C.𝓛) (hg : g ∈ C.𝓛) :
    C.emb (f - g) = C.emb f - C.emb g := by
  have h := C.emb_lincomb 1 (-1) hf hg
  simp only [one_smul, neg_smul] at h
  rw [sub_eq_add_neg, h, sub_eq_add_neg]

theorem emb_sum {ι : Type*} (s : Finset ι) {f : ι → 𝔾 → ℂ} (hf : ∀ i ∈ s, f i ∈ C.𝓛) :
    C.emb (∑ i ∈ s, f i) = ∑ i ∈ s, C.emb (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := C.emb_lincomb 0 0 C.𝓛.zero_mem C.𝓛.zero_mem
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      C.emb_add (hf i (Finset.mem_insert_self i s))
        (C.𝓛.sum_mem fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

def cχ (x : 𝔾) : ℝ := (C.χ x).toReal

theorem cχ_pos (x : 𝔾) : 0 < C.cχ x := ENNReal.toReal_pos (C.hχ x).1 (C.hχ x).2

theorem norm_emb_rt_sq (x : 𝔾) {f : 𝔾 → ℂ} (hf : f ∈ C.𝓛) :
    ‖C.emb (rt F x f)‖ ^ 2 = C.cχ x * ‖C.emb f‖ ^ 2 := by
  rw [C.norm_emb_sq (C.rt_mem hf x), C.norm_emb_sq hf, C.nm_rt hf.1 hf.2.1, ENNReal.toReal_mul]
  rfl

theorem inner_emb_rt (x : 𝔾) {f g : 𝔾 → ℂ} (hf : f ∈ C.𝓛) (hg : g ∈ C.𝓛) :
    ⟪C.emb (rt F x f), C.emb (rt F x g)⟫_ℂ = (C.cχ x : ℂ) * ⟪C.emb f, C.emb g⟫_ℂ := by
  have key : ∀ (a : ℂ), ‖C.emb (rt F x f) + a • C.emb (rt F x g)‖ ^ 2
      = C.cχ x * ‖C.emb f + a • C.emb g‖ ^ 2 := by
    intro a
    have hmem : f + a • g ∈ C.𝓛 := C.𝓛.add_mem hf (C.𝓛.smul_mem a hg)
    have h1 : C.emb (rt F x f) + a • C.emb (rt F x g) = C.emb (rt F x (f + a • g)) := by
      rw [map_add, map_smul, C.emb_add (C.rt_mem hf x) (C.𝓛.smul_mem a (C.rt_mem hg x)),
        C.emb_smul a (C.rt_mem hg x)]
    have h2 : C.emb f + a • C.emb g = C.emb (f + a • g) := by
      rw [C.emb_add hf (C.𝓛.smul_mem a hg), C.emb_smul a hg]
    rw [h1, h2, C.norm_emb_rt_sq x hmem]
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key (-RCLike.I)
  have k4 := key (RCLike.I)
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at k1 k2 k3 k4
  apply Complex.ext
  · have h1 := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ)
      (C.emb (rt F x f)) (C.emb (rt F x g))
    have h2 := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ)
      (C.emb f) (C.emb g)
    simp only [RCLike.re_to_complex] at h1 h2
    rw [Complex.re_ofReal_mul, h1, h2]
    linear_combination (k1 - k2) / 4
  · have h1 := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
      (𝕜 := ℂ) (C.emb (rt F x f)) (C.emb (rt F x g))
    have h2 := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
      (𝕜 := ℂ) (C.emb f) (C.emb g)
    simp only [RCLike.im_to_complex] at h1 h2
    rw [Complex.im_ofReal_mul, h1, h2]
    linear_combination (k3 - k4) / 4

theorem isKfSmooth_add {f g : 𝔾 → ℂ} (hf : IsKfSmooth F f) (hg : IsKfSmooth F g) :
    IsKfSmooth F (f + g) :=
  IsSmoothVector.add hf hg

theorem isKfSmooth_smul (a : ℂ) {f : 𝔾 → ℂ} (hf : IsKfSmooth F f) : IsKfSmooth F (a • f) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hf ⊢
  refine Subgroup.isOpen_mono (fun k hk => ?_) hf
  rw [MulAction.mem_stabilizer_iff] at hk ⊢
  refine RightTranslationFn.ext fun y => ?_
  have := congrArg (fun φ => RightTranslationFn.toFun φ y) hk
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at this ⊢
  simp only [Pi.smul_apply, this]

theorem isKfSmooth_zero' : IsKfSmooth F (0 : 𝔾 → ℂ) := isKfSmooth_zero F

theorem isKfSmooth_rt (x : 𝔾) {f : 𝔾 → ℂ} (hf : IsKfSmooth F f) : IsKfSmooth F (rt F x f) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hf ⊢

  have hconj : ∀ k : 𝔾, k ∈ finiteAdelicGL2Subgroup F → x⁻¹ * k * x ∈ finiteAdelicGL2Subgroup F := by
    intro k hk
    rw [mem_finiteAdelicGL2Subgroup_iff] at hk ⊢
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, inv_mul_cancel, map_one]
  let cj : finiteAdelicGL2Subgroup F → finiteAdelicGL2Subgroup F :=
    fun k => ⟨x⁻¹ * k * x, hconj k k.2⟩
  have hcont : Continuous cj := by
    refine continuous_induced_rng.mpr ?_
    show Continuous fun k : finiteAdelicGL2Subgroup F => x⁻¹ * (k : 𝔾) * x
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hset : ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
        (RightTranslationFn.mk (rt F x f) : RightTranslationFn 𝔾 ℂ) : Subgroup _) : Set _)
      = cj ⁻¹' ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
        (RightTranslationFn.mk f : RightTranslationFn 𝔾 ℂ) : Subgroup _) : Set _) := by
    ext k
    simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    constructor
    · intro h
      refine RightTranslationFn.ext fun y => ?_
      have := congrArg (fun φ => RightTranslationFn.toFun φ (y * x⁻¹)) h
      simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk, rt_apply] at this ⊢
      simpa [cj, mul_assoc] using this
    · intro h
      refine RightTranslationFn.ext fun y => ?_
      have := congrArg (fun φ => RightTranslationFn.toFun φ (y * x)) h
      simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk, rt_apply] at this ⊢
      simpa [cj, mul_assoc] using this
  rw [hset]
  exact hf.preimage hcont

def 𝓢 : Submodule ℂ (𝔾 → ℂ) where
  carrier := {f | f ∈ C.𝓛 ∧ IsKfSmooth F f}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨C.𝓛.add_mem hf1 hg1, isKfSmooth_add hf2 hg2⟩
  zero_mem' := ⟨C.𝓛.zero_mem, isKfSmooth_zero'⟩
  smul_mem' := by
    rintro a f ⟨hf1, hf2⟩
    exact ⟨C.𝓛.smul_mem a hf1, isKfSmooth_smul a hf2⟩

theorem 𝓢_le_𝓛 : C.𝓢 ≤ C.𝓛 := fun _ hf => hf.1

theorem rt_mem_𝓢 (x : 𝔾) {f : 𝔾 → ℂ} (hf : f ∈ C.𝓢) : rt F x f ∈ C.𝓢 :=
  ⟨C.rt_mem hf.1 x, isKfSmooth_rt x hf.2⟩

variable (N : Ideal (𝓞 F))

@[reducible] def fintypeQuot {f : 𝔾 → ℂ} (hf : IsKfSmooth F f) :
    Fintype (levelU F N ⧸ stabU (levelU F N) f) :=
  @Fintype.ofFinite _ (finite_quotient_of_isOpen _ (isOpen_stabU_of_isKfSmooth hf))

theorem inner_emb_levelAvg {f g : 𝔾 → ℂ} (hf : f ∈ C.𝓢) (hg : g ∈ C.𝓛)
    (hgU : ∀ y, ∀ k ∈ levelU F N, g (y * k) = g y) :
    ⟪C.emb (levelAvg (levelU F N) f), C.emb g⟫_ℂ = ⟪C.emb f, C.emb g⟫_ℂ := by
  letI := fintypeQuot N hf.2
  rw [levelAvg_eq_sum, C.emb_smul _ (C.𝓛.sum_mem fun q _ => C.rt_mem hf.1 _),
    C.emb_sum _ (fun q _ => C.rt_mem hf.1 _), inner_smul_left, sum_inner]
  have hterm : ∀ q : levelU F N ⧸ stabU (levelU F N) f,
      ⟪C.emb (rt F ((q.out : levelU F N) : 𝔾) f), C.emb g⟫_ℂ = ⟪C.emb f, C.emb g⟫_ℂ := by
    intro q
    set k : 𝔾 := ((q.out : levelU F N) : 𝔾) with hk
    have hkU : k ∈ levelU F N := Subtype.coe_prop _
    have hgk : rt F k g = g := funext fun y => hgU y k hkU
    have h1 : C.χ k = 1 := C.hχ1 k (levelU_le_fin N hkU) (glFin_mem_integral_of_mem_levelU hkU)
    conv_lhs => rw [← hgk]
    rw [C.inner_emb_rt k hf.1 hg]
    unfold cχ
    rw [h1, ENNReal.toReal_one, Complex.ofReal_one, one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, map_inv₀, Complex.conj_natCast, ← mul_assoc]
  have hne : (Nat.card (levelU F N ⧸ stabU (levelU F N) f) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hne, one_mul]

theorem levelAvg_mem_𝓢 {f : 𝔾 → ℂ} (hf : f ∈ C.𝓢) : levelAvg (levelU F N) f ∈ C.𝓢 := by
  letI := fintypeQuot N hf.2
  rw [levelAvg_eq_sum]
  exact C.𝓢.smul_mem _ (C.𝓢.sum_mem fun q _ => C.rt_mem_𝓢 _ hf)

theorem levelAvg_lincomb_𝓢 (a b : ℂ) {f g : 𝔾 → ℂ} (hf : f ∈ C.𝓢) (hg : g ∈ C.𝓢) :
    levelAvg (levelU F N) (a • f + b • g)
      = a • levelAvg (levelU F N) f + b • levelAvg (levelU F N) g := by
  haveI : Finite (levelU F N ⧸ (stabU (levelU F N) f ⊓ stabU (levelU F N) g)) := by
    refine finite_quotient_of_isOpen _ ?_
    rw [Subgroup.coe_inf]
    exact (isOpen_stabU_of_isKfSmooth hf.2).inter (isOpen_stabU_of_isKfSmooth hg.2)
  letI : Fintype (levelU F N ⧸ (stabU (levelU F N) f ⊓ stabU (levelU F N) g)) := Fintype.ofFinite _
  exact levelAvg_lincomb a b

theorem levelAvg_invariant_𝓢 {f : 𝔾 → ℂ} (hf : f ∈ C.𝓢) (y k : 𝔾) (hk : k ∈ levelU F N) :
    levelAvg (levelU F N) f (y * k) = levelAvg (levelU F N) f y := by
  letI := fintypeQuot N hf.2
  exact levelAvg_invariant y k hk

end Ctx

end Context

section SpanW

variable (N : Ideal (𝓞 F)) (φ' : AdelicGL2 (𝓞 F) F → ℂ)

def genE (b : 𝔾) : 𝔾 → ℂ := levelAvg (levelU F N) (rt F b φ')

def genSet : Set (𝔾 → ℂ) :=
  {w | ∃ a b : 𝔾, b ∈ finiteAdelicGL2Subgroup F ∧ w = rt F a (genE N φ' b)}

def W : Submodule ℂ (𝔾 → ℂ) := Submodule.span ℂ (genSet N φ')

variable {N φ'}

theorem gen_mem_W {a b : 𝔾} (hb : b ∈ finiteAdelicGL2Subgroup F) : rt F a (genE N φ' b) ∈ W N φ' :=
  Submodule.subset_span ⟨a, b, hb, rfl⟩

theorem rt_mem_W (x : 𝔾) {w : 𝔾 → ℂ} (hw : w ∈ W N φ') : rt F x w ∈ W N φ' := by
  induction hw using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, b, hb, rfl⟩ := hu
    rw [rt_rt]
    exact gen_mem_W hb
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u u' _ _ hu hu' => rw [map_add]; exact Submodule.add_mem _ hu hu'
  | smul a u _ hu => rw [map_smul]; exact Submodule.smul_mem _ a hu

variable (C : Ctx F)

theorem genE_mem_𝓢 (hφ' : φ' ∈ C.𝓢) (b : 𝔾) : genE N φ' b ∈ C.𝓢 :=
  C.levelAvg_mem_𝓢 N (C.rt_mem_𝓢 b hφ')

theorem W_le_𝓢 (hφ' : φ' ∈ C.𝓢) : W N φ' ≤ C.𝓢 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, b, hb, rfl⟩
  exact C.rt_mem_𝓢 a (genE_mem_𝓢 C hφ' b)

theorem W_le_orbit (hφ' : IsKfSmooth F φ') :
    W N φ' ≤ Submodule.span ℂ (Set.range fun x : 𝔾 => rtHom F x φ') := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, b, hb, rfl⟩
  letI := Ctx.fintypeQuot N (Ctx.isKfSmooth_rt b hφ')
  unfold genE
  rw [levelAvg_eq_sum, map_smul, map_sum]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
  rw [rt_rt, rt_rt]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem levelAvg_mem_W (hφ' : φ' ∈ C.𝓢) {w : 𝔾 → ℂ} (hw : w ∈ W N φ') :
    levelAvg (levelU F N) w ∈ W N φ' := by
  have hwS : w ∈ C.𝓢 := W_le_𝓢 C hφ' hw
  letI := Ctx.fintypeQuot N hwS.2
  rw [levelAvg_eq_sum]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => rt_mem_W _ hw)

theorem levelAvg_rt_mem_W (hφ' : IsKfSmooth F φ') (x : 𝔾) :
    levelAvg (levelU F N) (rt F x φ') ∈ W N φ' := by
  have hx : rt F x φ' = rt F (archPart x) (rt F (finPart x) φ') := by
    rw [rt_rt, archPart_mul_finPart]
  letI := Ctx.fintypeQuot N (Ctx.isKfSmooth_rt (finPart x) hφ')
  rw [hx, levelAvg_rt_comm (fun k hk => archPart_comm (levelU_le_fin N hk))]
  exact gen_mem_W (finPart_mem x)

variable (N φ') in

def Rep (w : 𝔾 → ℂ) : Prop :=
  ∃ (n : ℕ) (t : Fin n → Finset 𝔾) (l : Fin n → 𝔾 → ℂ) (x : Fin n → 𝔾),
    (∀ i, ∀ h ∈ t i, h ∈ finiteAdelicGL2Subgroup F) ∧
    (∀ i, ∀ g : 𝔾, ∀ k ∈ levelU F N,
      ∑ h ∈ t i, l i h * φ' (g * k * h) = ∑ h ∈ t i, l i h * φ' (g * h)) ∧
    w = fun y => ∑ i, ∑ h ∈ t i, l i h * φ' (y * x i * h)

theorem rep_zero : Rep N φ' 0 :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
    by funext y; simp⟩

theorem rep_add {w₁ w₂ : 𝔾 → ℂ} (h₁ : Rep N φ' w₁) (h₂ : Rep N φ' w₂) : Rep N φ' (w₁ + w₂) := by
  obtain ⟨n₁, t₁, l₁, x₁, hm₁, hi₁, rfl⟩ := h₁
  obtain ⟨n₂, t₂, l₂, x₂, hm₂, hi₂, rfl⟩ := h₂
  refine ⟨n₁ + n₂, Fin.append t₁ t₂, Fin.append l₁ l₂, Fin.append x₁ x₂, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hm₁ i
    · simpa only [Fin.append_right] using hm₂ i
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hi₁ i
    · simpa only [Fin.append_right] using hi₂ i
  · funext y
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.add_apply]

theorem rep_smul (a : ℂ) {w : 𝔾 → ℂ} (h : Rep N φ' w) : Rep N φ' (a • w) := by
  obtain ⟨n, t, l, x, hm, hi, rfl⟩ := h
  refine ⟨n, t, fun i h => a * l i h, x, hm, ?_, ?_⟩
  · intro i g k hk
    have := hi i g k hk
    simp only [mul_assoc] at this
    simp only [mul_assoc, ← Finset.mul_sum, this]
  · funext y
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem rep_rt (a : 𝔾) {w : 𝔾 → ℂ} (h : Rep N φ' w) : Rep N φ' (rt F a w) := by
  obtain ⟨n, t, l, x, hm, hi, rfl⟩ := h
  refine ⟨n, t, l, fun i => a * x i, hm, hi, ?_⟩
  funext y
  simp only [rt_apply, mul_assoc]

open scoped Classical in

theorem genE_apply (hφ' : IsKfSmooth F φ') {b : 𝔾} (hb : b ∈ finiteAdelicGL2Subgroup F) (z : 𝔾) :
    letI := Ctx.fintypeQuot N (Ctx.isKfSmooth_rt b hφ')
    genE N φ' b z =
      ∑ h ∈ Finset.univ.image
          (fun q : levelU F N ⧸ stabU (levelU F N) (rt F b φ') => ((q.out : levelU F N) : 𝔾) * b),
        (Nat.card (levelU F N ⧸ stabU (levelU F N) (rt F b φ')) : ℂ)⁻¹ * φ' (z * h) := by
  letI := Ctx.fintypeQuot N (Ctx.isKfSmooth_rt b hφ')
  have hinj : Function.Injective
      (fun q : levelU F N ⧸ stabU (levelU F N) (rt F b φ') => ((q.out : levelU F N) : 𝔾) * b) := by
    intro q q' hqq'
    have h1 : ((q.out : levelU F N) : 𝔾) = ((q'.out : levelU F N) : 𝔾) := mul_right_cancel hqq'
    exact Quotient.out_injective (Subtype.ext h1)
  rw [Finset.sum_image fun q _ q' _ h => hinj h]
  show levelAvg (levelU F N) (rt F b φ') z = _
  rw [levelAvg_eq_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [rt_apply, mul_assoc]

open scoped Classical in
theorem rep_genE (hφ' : IsKfSmooth F φ') {b : 𝔾} (hb : b ∈ finiteAdelicGL2Subgroup F) :
    Rep N φ' (genE N φ' b) := by
  letI := Ctx.fintypeQuot N (Ctx.isKfSmooth_rt b hφ')
  refine ⟨1, fun _ => Finset.univ.image
      (fun q : levelU F N ⧸ stabU (levelU F N) (rt F b φ') => ((q.out : levelU F N) : 𝔾) * b),
    fun _ _ => (Nat.card (levelU F N ⧸ stabU (levelU F N) (rt F b φ')) : ℂ)⁻¹, fun _ => 1,
    ?_, ?_, ?_⟩
  · intro i h hh
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hh
    exact Subgroup.mul_mem _ (levelU_le_fin N (Subtype.coe_prop _)) hb
  · intro i g k hk
    rw [← genE_apply hφ' hb, ← genE_apply hφ' hb]
    exact levelAvg_invariant _ _ hk
  · funext y
    rw [Fin.sum_univ_one, mul_one]
    exact genE_apply hφ' hb y

theorem rep_of_mem_W (hφ' : IsKfSmooth F φ') {w : 𝔾 → ℂ} (hw : w ∈ W N φ') : Rep N φ' w := by
  induction hw using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, b, hb, rfl⟩ := hu
    exact rep_rt a (rep_genE hφ' hb)
  | zero => exact rep_zero
  | add u u' _ _ hu hu' => exact rep_add hu hu'
  | smul a u _ hu => exact rep_smul a hu

end SpanW

section Assembly

namespace Ctx

variable (C : Ctx F)

theorem exists_eps_of_real (ε : ℝ) (hε : 0 < ε) :
    ∃ ε' : ℝ≥0∞, 0 < ε' ∧ ∀ A : ℝ≥0∞, A < ε' → C.M * A < ENNReal.ofReal (ε ^ 2) := by
  have hM1 : C.M + 1 ≠ 0 := by simp
  have hM1' : C.M + 1 ≠ ⊤ := by simp [C.hM]
  refine ⟨ENNReal.ofReal (ε ^ 2) / (C.M + 1), ?_, fun A hA => ?_⟩
  · exact ENNReal.div_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hM1'
  · calc C.M * A ≤ (C.M + 1) * A := mul_le_mul_left le_self_add A
      _ < (C.M + 1) * (ENNReal.ofReal (ε ^ 2) / (C.M + 1)) := ENNReal.mul_lt_mul_right hM1 hM1' hA
      _ = ENNReal.ofReal (ε ^ 2) := ENNReal.mul_div_cancel hM1 hM1'

theorem exists_real_of_eps (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ A : ℝ≥0∞, A ≠ ⊤ → A.toReal < ε₁ ^ 2 → C.M * A < ε := by
  have hM1 : C.M + 1 ≠ 0 := by simp
  have hM1' : C.M + 1 ≠ ⊤ := by simp [C.hM]
  by_cases htop : ε = ⊤
  · refine ⟨1, one_pos, fun A hA _ => ?_⟩
    rw [htop]
    exact ENNReal.mul_lt_top C.hM.lt_top hA.lt_top
  set δ : ℝ≥0∞ := ε / (C.M + 1) with hδ
  have hδtop : δ ≠ ⊤ := (ENNReal.div_lt_top htop hM1).ne
  have hδ0 : δ ≠ 0 := (ENNReal.div_pos_iff.mpr ⟨hε.ne', hM1'⟩).ne'
  have hδpos : 0 < δ.toReal := ENNReal.toReal_pos hδ0 hδtop
  refine ⟨Real.sqrt δ.toReal, Real.sqrt_pos.mpr hδpos, fun A hA hlt => ?_⟩
  rw [Real.sq_sqrt hδpos.le, ENNReal.toReal_lt_toReal hA hδtop] at hlt
  calc C.M * A ≤ (C.M + 1) * A := mul_le_mul_left le_self_add A
    _ < (C.M + 1) * δ := ENNReal.mul_lt_mul_right hM1 hM1' hlt
    _ = ε := ENNReal.mul_div_cancel hM1 hM1'

theorem norm_emb_sub_lt {f g : 𝔾 → ℂ} (hf : f ∈ C.𝓛) (hg : g ∈ C.𝓛) {ε : ℝ} (hε : 0 < ε)
    (h : C.M * C.dm (f - g) < ENNReal.ofReal (ε ^ 2)) : ‖C.emb f - C.emb g‖ < ε := by
  have hfg : f - g ∈ C.𝓛 := C.𝓛.sub_mem hf hg
  have h1 : ‖C.emb f - C.emb g‖ ^ 2 < ε ^ 2 := by
    rw [← C.emb_sub hf hg, C.norm_emb_sq hfg]
    refine ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt ?_ h)
    exact C.nm_le hfg.1 hfg.2.1
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp h1

theorem dm_sub_lt {f g : 𝔾 → ℂ} (hf : f ∈ C.𝓛) (hg : g ∈ C.𝓛) {ε : ℝ≥0∞} {ε₁ : ℝ}
    (hε₁ : ∀ A : ℝ≥0∞, A ≠ ⊤ → A.toReal < ε₁ ^ 2 → C.M * A < ε)
    (h : ‖C.emb f - C.emb g‖ < ε₁) : C.dm (f - g) < ε := by
  have hfg : f - g ∈ C.𝓛 := C.𝓛.sub_mem hf hg
  have hε₁pos : 0 ≤ ε₁ := (norm_nonneg _).trans h.le
  have h1 : (C.nm (f - g)).toReal < ε₁ ^ 2 := by
    rw [← C.norm_emb_sq hfg, C.emb_sub hf hg]
    exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
  exact lt_of_le_of_lt (C.dm_le hfg.1 hfg.2.1) (hε₁ _ (C.nm_lt_top hfg).ne h1)

end Ctx

theorem main (c u d₁ d₂ : ℝ) (T : Finset 𝔾)
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hfin : Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, globalPoints (𝓞 F) F γ * s ∈ centreCutSiegelSet F c u d₁ d₂})
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (φ φ' : 𝔾 → ℂ) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφξ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hφ'ξ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ')
    (hφm : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (hφ'm : MemLp φ' 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (hφs : IsKfSmooth F φ) (hφ's : IsKfSmooth F φ')
    (hφU : ∀ g : 𝔾, ∀ k ∈ levelU F N, φ (g * k) = φ g)
    (hne : ∃ g, φ' g ≠ 0)
    (hspan : IsInTranslateSpanOn F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ φ') :
    (∃ (t : Finset 𝔾) (l : 𝔾 → ℂ),
        (∀ h ∈ t, h ∈ finiteAdelicGL2Subgroup F) ∧
        (∀ g : 𝔾, ∀ k ∈ levelU F N,
          ∑ h ∈ t, l h * φ' (g * k * h) = ∑ h ∈ t, l h * φ' (g * h)) ∧
        ∃ g, ∑ h ∈ t, l h * φ' (g * h) ≠ 0) ∧
    (∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (n : ℕ) (t : Fin n → Finset 𝔾) (l : Fin n → 𝔾 → ℂ) (x : Fin n → 𝔾),
        (∀ i, ∀ h ∈ t i, h ∈ finiteAdelicGL2Subgroup F) ∧
        (∀ i, ∀ g : 𝔾, ∀ k ∈ levelU F N,
          ∑ h ∈ t i, l i h * φ' (g * k * h) = ∑ h ∈ t i, l i h * φ' (g * h)) ∧
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
            (‖φ' y - ∑ i, ∑ h ∈ t i, l i h * φ' (y * x i * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε) := by

  obtain ⟨ν, M, χ, hM, hχ, hχ1, hmain⟩ :=
    AutomorphicForm.exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
      F c u d₁ d₂ T hc hd₁ hd hcov hfin ξ
  let C : Ctx F :=
    { c := c, u := u, d₁ := d₁, d₂ := d₂, T := T, hc := hc, hd₁ := hd₁, hd := hd, hcov := hcov,
      ξ := ξ, ν := ν, M := M, χ := χ, hM := hM, hχ := hχ, hχ1 := hχ1,
      hB1 := fun ψ h1 h2 => (hmain ψ h1 h2).1,
      hB2 := fun ψ h1 h2 => (hmain ψ h1 h2).2.1,
      hB3 := fun ψ h1 h2 => (hmain ψ h1 h2).2.2 }
  have hφL : φ ∈ C.𝓛 := ⟨hφ, hφξ, hφm⟩
  have hφ'L : φ' ∈ C.𝓛 := ⟨hφ', hφ'ξ, hφ'm⟩
  have hφS : φ ∈ C.𝓢 := ⟨hφL, hφs⟩
  have hφ'S : φ' ∈ C.𝓢 := ⟨hφ'L, hφ's⟩

  have hspan' : ∀ ε : ℝ, 0 < ε →
      ∃ v ∈ Submodule.span ℂ (Set.range fun x : 𝔾 => rtHom F x φ), ‖C.emb φ' - C.emb v‖ < ε := by
    intro ε hε
    obtain ⟨ε', hε'pos, hε'⟩ := C.exists_eps_of_real ε hε
    obtain ⟨s, l, hsl⟩ := hspan ε' hε'pos
    set v : 𝔾 → ℂ := ∑ h ∈ s, l h • rt F h φ with hv
    have hvmem : v ∈ Submodule.span ℂ (Set.range fun x : 𝔾 => rtHom F x φ) :=
      Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
    have hvL : v ∈ C.𝓛 := C.𝓛.sum_mem fun h _ => C.𝓛.smul_mem _ (C.rt_mem hφL h)
    refine ⟨v, hvmem, C.norm_emb_sub_lt hφ'L hvL hε (hε' _ ?_)⟩
    have heq : C.dm (φ' - v) = ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
        (‖φ' y - ∑ h ∈ s, l h * φ (y * h)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
      unfold Ctx.dm
      congr 1
      funext y
      simp only [hv, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, rt_apply, smul_eq_mul]
    rw [heq]
    exact hsl

  have hengine := InnerProductSpace.exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average
    (rtHom F) C.𝓢 (fun x f hf => C.rt_mem_𝓢 x hf) C.emb
    (fun a b f g hf hg => C.emb_lincomb a b hf.1 hg.1)
    C.cχ C.cχ_pos (fun x f hf => C.norm_emb_rt_sq x hf.1)
    (fun g => ∀ y : 𝔾, ∀ k ∈ levelU F N, g (y * k) = g y) (levelAvg (levelU F N))
    (fun a b f g hf hg => C.levelAvg_lincomb_𝓢 N a b hf hg)
    (fun f hf => C.levelAvg_invariant_𝓢 N hf)
    (fun f hf g hg hgU => C.inner_emb_levelAvg N hf hg.1 hgU)
    φ φ' hφS hφU hφ'S hspan' (W N φ') (W_le_𝓢 C hφ'S) (W_le_orbit hφ's)
    (fun x w hw => rt_mem_W x hw) (fun w hw => levelAvg_mem_W C hφ'S hw)
    (fun x => levelAvg_rt_mem_W hφ's x)

  have hii : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (n : ℕ) (t : Fin n → Finset 𝔾) (l : Fin n → 𝔾 → ℂ) (x : Fin n → 𝔾),
        (∀ i, ∀ h ∈ t i, h ∈ finiteAdelicGL2Subgroup F) ∧
        (∀ i, ∀ g : 𝔾, ∀ k ∈ levelU F N,
          ∑ h ∈ t i, l i h * φ' (g * k * h) = ∑ h ∈ t i, l i h * φ' (g * h)) ∧
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
            (‖φ' y - ∑ i, ∑ h ∈ t i, l i h * φ' (y * x i * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε := by
    intro ε hε
    obtain ⟨ε₁, hε₁pos, hε₁⟩ := C.exists_real_of_eps ε hε
    obtain ⟨w, hw, hlt⟩ := hengine ε₁ hε₁pos
    have hwL : w ∈ C.𝓛 := (W_le_𝓢 C hφ'S hw).1
    obtain ⟨n, t, l, x, hm, hi, rfl⟩ := rep_of_mem_W hφ's hw
    refine ⟨n, t, l, x, hm, hi, ?_⟩
    have h := C.dm_sub_lt hφ'L hwL hε₁ hlt
    unfold Ctx.dm at h
    simp only [Pi.sub_apply] at h
    exact h
  refine ⟨?_, hii⟩

  by_contra hcon
  push Not at hcon
  have hzero : ∀ w ∈ W N φ', w = 0 := by
    intro w hw
    obtain ⟨n, t, l, x, hm, hi, rfl⟩ := rep_of_mem_W hφ's hw
    funext y
    simp only [Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact hcon (t i) (l i) (hm i) (hi i) (y * x i)
  have hnm : C.nm φ' = 0 := by
    have hnorm : ‖C.emb φ'‖ = 0 := by
      refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
      obtain ⟨w, hw, hlt⟩ := hengine ε hε
      rw [hzero w hw] at hlt
      have h0 : C.emb 0 = 0 := by
        have := C.emb_lincomb 0 0 C.𝓛.zero_mem C.𝓛.zero_mem
        simpa using this
      rw [h0, sub_zero] at hlt
      linarith
    have h1 : (C.nm φ').toReal = 0 := by
      rw [← C.norm_emb_sq hφ'L, hnorm]; norm_num
    rcases (ENNReal.toReal_eq_zero_iff _).mp h1 with h | h
    · exact h
    · exact absurd h (C.nm_lt_top hφ'L).ne
  have hdm : C.dm φ' = 0 := by
    have := C.dm_le hφ' hφ'ξ
    rw [hnm, mul_zero] at this
    exact le_antisymm this (zero_le)

  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds g₀
  obtain ⟨Nc, hNc⟩ :=
    AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
      F c u d₁ d₂ T hd hcov ξ hKc
  have hK0 : ∫⁻ y in K, (‖φ' y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := by
    have h := hNc φ' hφ'ξ hφ'
    have hdm' : ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
        (‖φ' y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := hdm
    rw [hdm', mul_zero] at h
    exact le_antisymm h (zero_le)
  have hmeas : Measurable fun y : 𝔾 => ((‖φ' y‖₊ : ℝ≥0∞)) ^ 2 :=
    (hφ'.measurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  rw [lintegral_eq_zero_iff hmeas] at hK0

  set O : Set 𝔾 := interior K ∩ {y | φ' y ≠ 0} with hO
  have hOopen : IsOpen O := isOpen_interior.inter (isOpen_ne_fun hφ' continuous_const)
  have hg₀O : g₀ ∈ O := ⟨mem_interior_iff_mem_nhds.mpr hKn, hg₀⟩
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hOpos : 0 < adelicGLHaar (Fin 2) (𝓞 F) F O := hOopen.measure_pos _ ⟨g₀, hg₀O⟩
  have hOK : O ⊆ K := fun y hy => interior_subset hy.1
  have hae : ∀ᵐ y ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict K), ((‖φ' y‖₊ : ℝ≥0∞)) ^ 2 = 0 := hK0
  rw [ae_restrict_iff' hKc.isClosed.measurableSet] at hae
  have hnull : adelicGLHaar (Fin 2) (𝓞 F) F O = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hae)
    simp only [Set.mem_setOf_eq]
    intro himp
    have hy2 : φ' y ≠ 0 := hy.2
    have hne2 : ((‖φ' y‖₊ : ℝ≥0∞)) ^ 2 ≠ 0 := by simp [hy2]
    exact hne2 (himp (hOK hy))
  exact absurd hnull hOpos.ne'

end Assembly

end LevelAverageFinSol
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite.LevelAverageFinSol"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite.LevelAverageFinSol"

open LevelAverageFinSol in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hfin : Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, globalPoints (𝓞 F) F γ * s ∈ centreCutSiegelSet F c u d₁ d₂})
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφa : IsSmoothAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hφ'a : IsSmoothAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ')
    (hφU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      φ (g * k) = φ g)
    (hne : ∃ g, φ' g ≠ 0)
    (hspan : IsInTranslateSpanOn F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ φ') :
    (∃ (t : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
        (∀ h ∈ t, h ∈ finiteAdelicGL2Subgroup F) ∧
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
          ∑ h ∈ t, l h * φ' (g * k * h) = ∑ h ∈ t, l h * φ' (g * h)) ∧
        ∃ g, ∑ h ∈ t, l h * φ' (g * h) ≠ 0) ∧
    (∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (n : ℕ) (t : Fin n → Finset (AdelicGL2 (𝓞 F) F)) (l : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
        (x : Fin n → AdelicGL2 (𝓞 F) F),
        (∀ i, ∀ h ∈ t i, h ∈ finiteAdelicGL2Subgroup F) ∧
        (∀ i, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
          ∑ h ∈ t i, l i h * φ' (g * k * h) = ∑ h ∈ t i, l i h * φ' (g * h)) ∧
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
            (‖φ' y - ∑ i, ∑ h ∈ t i, l i h * φ' (y * x i * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε) := by
  have h1 := (@AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _
    (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F) _ _ _ _ _).mp hφa.1
  have h2 := (@AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _
    (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F) _ _ _ _ _).mp hφ'a.1
  exact LevelAverageFinSol.main c u d₁ d₂ T hc hd₁ hd hcov hfin ξ N hN φ φ' hφ hφ' h1.1 h2.1 h1.2 h2.2
    hφa.2 hφ'a.2 hφU hne hspan

end S_AutomorphicForm_exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite
end P2MW
export P2MW.S_AutomorphicForm_exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite (solution)
