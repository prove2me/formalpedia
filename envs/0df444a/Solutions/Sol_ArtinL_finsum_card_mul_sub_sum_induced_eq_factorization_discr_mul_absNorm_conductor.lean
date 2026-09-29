-- Prove2me | solution 1 for ArtinL.finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3cee7d9a-fc9f-5d74-ae22-b460f3bac494

import Mathlib
import Definitions.Def_ArtinL_Conductor
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_Abelian_finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
import Theorems.Thm_ArtinL_Abelian_factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent
import Theorems.Thm_NumberField_card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor
p2m_attr_erase "instance" "FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk"
p2m_attr_erase "simp" "TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace INDsk

section Unfold

variable {G : Type*} [Group G] [Fintype G]

open scoped Classical in

noncomputable def extChar (H : Subgroup G) (χ : H →* ℂˣ) (g : G) : ℂ :=
  if hg : g ∈ H then ((χ ⟨g, hg⟩ : ℂˣ) : ℂ) else 0

open scoped Classical in
lemma extChar_of_mem {H : Subgroup G} (χ : H →* ℂˣ) (t : H) : extChar H χ (t : G) = ((χ t : ℂˣ) : ℂ) := by
  simp [extChar, t.2]

open scoped Classical in
lemma extChar_of_not_mem {H : Subgroup G} (χ : H →* ℂˣ) {g : G} (hg : g ∉ H) : extChar H χ g = 0 := by
  simp [extChar, hg]

open scoped Classical in

lemma sum_subgroup_eq_sum_ite (N : Subgroup G) (f : G → ℂ) :
    ∑ g : ↥N, f g = ∑ g : G, if g ∈ N then f g else 0 := by
  rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter (· ∈ N)) (p := (· ∈ N)) (fun g => by simp)]

open scoped Classical in

lemma sum_dite_conj_eq (H N : Subgroup G) (χ : H →* ℂˣ) (x : G) :
    ∑ g : ↥N, (if hx : x⁻¹ * (g : G) * x ∈ H then ((χ ⟨x⁻¹ * (g : G) * x, hx⟩ : ℂˣ) : ℂ) else 0) =
      ∑ t : ↥H, (if x * (t : G) * x⁻¹ ∈ N then ((χ t : ℂˣ) : ℂ) else 0) := by
  have h1 : ∀ g : ↥N, (if hx : x⁻¹ * (g : G) * x ∈ H then ((χ ⟨x⁻¹ * (g : G) * x, hx⟩ : ℂˣ) : ℂ) else 0) =
      extChar H χ (x⁻¹ * g * x) := fun g => rfl
  simp_rw [h1]
  have h2 : ∀ t : ↥H, (if x * (t : G) * x⁻¹ ∈ N then ((χ t : ℂˣ) : ℂ) else 0) =
      (if x * (t : G) * x⁻¹ ∈ N then extChar H χ t else 0) := fun t => by rw [extChar_of_mem]
  simp_rw [h2]
  rw [sum_subgroup_eq_sum_ite N (fun g => extChar H χ (x⁻¹ * g * x)),
    sum_subgroup_eq_sum_ite H (fun t => if x * t * x⁻¹ ∈ N then extChar H χ t else 0)]

  rw [← Equiv.sum_comp (MulAut.conj x).toEquiv]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [show x⁻¹ * (x * t * x⁻¹) * x = t by group]
  by_cases ht : t ∈ H
  · simp [ht]
  · simp [ht, extChar_of_not_mem χ ht]

end Unfold

section ConjOrbit

open scoped Pointwise

variable {B : Type*} [CommRing B] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G B]

lemma smul_ideal_pow (x : G) (I : Ideal B) (k : ℕ) : (x • I) ^ k = x • I ^ k := by
  simp only [Ideal.pointwise_smul_def, Ideal.map_pow]

lemma mem_inertia_smul_pow_iff (x g : G) (I : Ideal B) (k : ℕ) :
    g ∈ ((x • I) ^ k).inertia G ↔ x⁻¹ * g * x ∈ (I ^ k).inertia G := by
  rw [smul_ideal_pow]
  constructor
  · intro hg z
    have := hg (x • z)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, ← mul_smul, ← mul_smul,
      inv_smul_smul] at this
    rw [Submodule.mem_toAddSubgroup]
    simpa [mul_assoc] using this
  · intro hg y
    have := hg (x⁻¹ • y)
    rw [Submodule.mem_toAddSubgroup] at this ⊢
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, ← mul_smul]
    rw [← mul_smul, show x⁻¹ * g * x * x⁻¹ = x⁻¹ * g by group] at this
    exact this

end ConjOrbit

section Orbit

variable {G : Type*} [Group G] [Fintype G] {α : Type*} [MulAction G α]

open scoped Classical in
lemma card_filter_smul_eq (a : α) (g₀ : G) :
    (Finset.univ.filter fun x : G => x • a = g₀ • a).card = Nat.card (MulAction.stabilizer G a) := by
  have hS : Nat.card (MulAction.stabilizer G a) = ((MulAction.stabilizer G a : Set G).toFinset).card := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]; rfl
  rw [hS]
  refine Finset.card_bij' (fun x _ => g₀⁻¹ * x) (fun s _ => g₀ * s) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Set.mem_toFinset, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul, hx, inv_smul_smul]
  · intro s hs
    simp only [Set.mem_toFinset, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_smul, hs]
  · intro x _; simp
  · intro s _; simp

open scoped Classical in
lemma sum_smul_eq_card_stabilizer_mul_sum_orbit [DecidableEq α] (a : α) (Φ : α → ℂ) :
    ∑ x : G, Φ (x • a) = Nat.card (MulAction.stabilizer G a) * ∑ b ∈ Finset.univ.image (fun x : G => x • a), Φ b := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image (fun x : G => x • a)) (g := fun x : G => x • a)
    (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨g₀, -, rfl⟩ := Finset.mem_image.mp hb
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2], Finset.sum_const, nsmul_eq_mul]
  congr 2
  convert card_filter_smul_eq a g₀

end Orbit

section Setting

open scoped Pointwise
open IsDedekindDomain

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]

noncomputable abbrev Gj (Q : Ideal (𝓞 F)) (j : ℕ) : Subgroup (F ≃ₐ[ℚ] F) := (Q ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)

lemma mem_Gj_smul_iff (x g : F ≃ₐ[ℚ] F) (Q : Ideal (𝓞 F)) (j : ℕ) :
    g ∈ Gj F (x • Q) j ↔ x⁻¹ * g * x ∈ Gj F Q j :=
  mem_inertia_smul_pow_iff x g Q (j + 1)

lemma Gj_antitone (Q : Ideal (𝓞 F)) : Antitone (Gj F Q) := fun i j hij g hg y =>
  Ideal.pow_le_pow_right (by omega) (hg y)

lemma card_Gj_smul (x : F ≃ₐ[ℚ] F) (Q : Ideal (𝓞 F)) (j : ℕ) : Nat.card (Gj F (x • Q) j) = Nat.card (Gj F Q j) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨x⁻¹ * g * x, (mem_Gj_smul_iff F x g Q j).mp g.2⟩
      invFun := fun g => ⟨x * g * x⁻¹, (mem_Gj_smul_iff F x _ Q j).mpr (by simpa [mul_assoc] using g.2)⟩
      left_inv := fun g => by ext; simp [mul_assoc]
      right_inv := fun g => by ext; simp [mul_assoc] }

open scoped Classical in

lemma card_filter_conj_mem_eq (H : Subgroup (F ≃ₐ[ℚ] F)) (x : F ≃ₐ[ℚ] F) (Q : Ideal (𝓞 F)) (j : ℕ) :
    (Finset.univ.filter fun t : ↥H => x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F Q j).card = Nat.card ↥(Gj F (x⁻¹ • Q) j ⊓ H) := by
  have hiff : ∀ t : ↥H, x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F Q j ↔ (t : F ≃ₐ[ℚ] F) ∈ Gj F (x⁻¹ • Q) j := fun t => by
    rw [mem_Gj_smul_iff, inv_inv]
  simp_rw [hiff]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun t => ⟨(t.1 : F ≃ₐ[ℚ] F), Subgroup.mem_inf.mpr ⟨t.2, t.1.2⟩⟩
      invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.mp g.2).2⟩, (Subgroup.mem_inf.mp g.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma span_ne_bot {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero

lemma image_smul_eq_primesOverFinset [DecidableEq (Ideal (𝓞 F))] (p : ℕ) (hp : p.Prime) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal]
    (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) :
    Finset.univ.image (fun x : F ≃ₐ[ℚ] F => x • 𝔓) = IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F) := by
  haveI : 𝔓.LiesOver (Ideal.span {(p : ℤ)}) := ⟨h𝔓.symm⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have horb := Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 F) (F ≃ₐ[ℚ] F) (Ideal.span {(p : ℤ)}) 𝔓
  ext Q
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rw [IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) (𝓞 F), ← horb, MulAction.mem_orbit_iff]

lemma card_stabilizer_eq_card_inertia_mul_inertiaDeg (p : ℕ) (hp : p.Prime) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal]
    (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) :
    Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) 𝔓) = Nat.card (Gj F 𝔓 0) * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔓 := by
  haveI : 𝔓.LiesOver (Ideal.span {(p : ℤ)}) := ⟨h𝔓.symm⟩
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Field (ℤ ⧸ Ideal.span {(p : ℤ)}) := Ideal.Quotient.field _
  letI : Field (𝓞 F ⧸ 𝔓) := Ideal.Quotient.field _
  rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := F ≃ₐ[ℚ] F) (Ideal.span {(p : ℤ)}) 𝔓,
    Ideal.inertiaDeg'_eq_inertiaDeg]
  simp [Gj, pow_one]

lemma eq_one_of_forall_smul_eq (g : F ≃ₐ[ℚ] F) (hg : ∀ y : 𝓞 F, g • y = y) : g = 1 := by
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have ha : g (a : F) = a := congrArg ((↑) : 𝓞 F → F) (hg a)
  have hb' : g (b : F) = b := congrArg ((↑) : 𝓞 F → F) (hg b)
  simp [map_div₀, ha, hb']

lemma exists_forall_Gj_eq_bot (p : ℕ) (hp : p.Prime) :
    ∃ J : ℕ, ∀ Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F), ∀ j, J ≤ j → Gj F Q j = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  have hone : ∀ (Q : Ideal (𝓞 F)), Q.IsPrime → ∃ J : ℕ, Gj F Q J = ⊥ := by
    intro Q hQ
    have hQ' : Q ≠ ⊤ := hQ.ne_top
    have hkr : ⨅ i : ℕ, Q ^ i = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain Q hQ'
    have hg : ∀ g : F ≃ₐ[ℚ] F, g ≠ 1 → ∃ n : ℕ, g ∉ Gj F Q n := by
      intro g hg1
      by_contra hall
      push Not at hall
      apply hg1 (eq_one_of_forall_smul_eq F g fun y => ?_)
      have hmem : g • y - y ∈ ⨅ i : ℕ, Q ^ i := by
        refine Ideal.mem_iInf.mpr fun i => ?_
        rcases i with _ | i
        · simp
        · exact hall i y
      rw [hkr, Ideal.mem_bot, sub_eq_zero] at hmem
      exact hmem
    choose! n hn using hg
    refine ⟨Finset.univ.sup n, le_bot_iff.mp fun g hgm => ?_⟩
    by_contra hg1
    exact hn g hg1 (Gj_antitone F Q (Finset.le_sup (Finset.mem_univ g)) hgm)
  choose! J hJ using hone
  refine ⟨(IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F)).sup J, fun Q hQ j hj => le_bot_iff.mp ?_⟩
  have hle : J Q ≤ j := (Finset.le_sup ((IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) (𝓞 F)).mpr hQ)).trans hj
  exact (hJ Q hQ.1) ▸ Gj_antitone F Q hle

end Setting

section Regroup

open scoped Pointwise
open IsDedekindDomain

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]

open scoped Classical in

lemma sum_apply_inv_smul_eq (p : ℕ) (hp : p.Prime) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal] (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)})
    (Φ : Ideal (𝓞 F) → ℂ) :
    ∑ x : F ≃ₐ[ℚ] F, Φ (x⁻¹ • 𝔓) =
      Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) 𝔓) * ∑ 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F), Φ 𝔔 := by
  rw [← Equiv.sum_comp (Equiv.inv (F ≃ₐ[ℚ] F))]
  simp only [Equiv.inv_apply, inv_inv]
  rw [sum_smul_eq_card_stabilizer_mul_sum_orbit 𝔓 Φ, image_smul_eq_primesOverFinset F p hp 𝔓 h𝔓]

open scoped Classical in

lemma sum_card_filter_conj_eq (H : Subgroup (F ≃ₐ[ℚ] F)) (p : ℕ) (hp : p.Prime) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal]
    (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) (j : ℕ) :
    ∑ x : F ≃ₐ[ℚ] F, ((Finset.univ.filter fun t : ↥H => x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F 𝔓 j).card : ℂ) =
      Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) 𝔓) *
        ∑ 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F), (Nat.card ↥(Gj F 𝔔 j ⊓ H) : ℂ) := by
  simp_rw [card_filter_conj_mem_eq]
  exact sum_apply_inv_smul_eq F p hp 𝔓 h𝔓 (fun Q => (Nat.card ↥(Gj F Q j ⊓ H) : ℂ))

open scoped Classical in

lemma sum_sum_ite_conj_eq (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) (p : ℕ) (hp : p.Prime) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal]
    (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) (j : ℕ) :
    ∑ x : F ≃ₐ[ℚ] F, ∑ t : ↥H, (if x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F 𝔓 j then (1 - ((χ t : ℂˣ) : ℂ)) else 0) =
      Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) 𝔓) *
        ∑ 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F),
          ∑ t : ↥H, (if (t : F ≃ₐ[ℚ] F) ∈ Gj F 𝔔 j then (1 - ((χ t : ℂˣ) : ℂ)) else 0) := by
  have hiff : ∀ (x : F ≃ₐ[ℚ] F) (t : ↥H), x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F 𝔓 j ↔ (t : F ≃ₐ[ℚ] F) ∈ Gj F (x⁻¹ • 𝔓) j :=
    fun x t => by rw [mem_Gj_smul_iff, inv_inv]
  simp_rw [hiff]
  exact sum_apply_inv_smul_eq F p hp 𝔓 h𝔓 (fun Q => ∑ t : ↥H, (if (t : F ≃ₐ[ℚ] F) ∈ Gj F Q j then (1 - ((χ t : ℂˣ) : ℂ)) else 0))

end Regroup

section Bridge

open IsDedekindDomain

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F] (H : Subgroup (F ≃ₐ[ℚ] F))

noncomputable def toGalFixed (h : H) : (F ≃ₐ[IntermediateField.fixedField H] F) :=
  IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)
    ⟨h, by rw [IntermediateField.fixingSubgroup_fixedField H]; exact h.2⟩

lemma restrictScalars_toGalFixed (h : H) : (toGalFixed F H h).restrictScalars ℚ = h :=
  ArtinL.Abelian.restrictScalars_fixingSubgroupEquiv _ _

lemma toGalFixed_bijective : Function.Bijective (toGalFixed F H) := by
  constructor
  · intro a b hab
    have := congrArg (AlgEquiv.restrictScalars ℚ) hab
    rw [restrictScalars_toGalFixed, restrictScalars_toGalFixed] at this
    exact Subtype.ext this
  · intro σ
    refine ⟨⟨σ.restrictScalars ℚ, ?_⟩, ?_⟩
    · have : σ.restrictScalars ℚ ∈ (IntermediateField.fixedField H).fixingSubgroup := fun x => σ.commutes x
      rwa [IntermediateField.fixingSubgroup_fixedField H] at this
    · apply AlgEquiv.restrictScalars_injective ℚ
      rw [restrictScalars_toGalFixed]

lemma toGalFixed_smul (h : H) (y : 𝓞 F) : toGalFixed F H h • y = (h : F ≃ₐ[ℚ] F) • y := by
  apply Subtype.ext
  show (toGalFixed F H h) (y : F) = (h : F ≃ₐ[ℚ] F) (y : F)
  rw [← restrictScalars_toGalFixed F H h]
  rfl

lemma toGalFixed_mem_inertia_iff (h : H) (I : Ideal (𝓞 F)) :
    toGalFixed F H h ∈ I.inertia (F ≃ₐ[IntermediateField.fixedField H] F) ↔ (h : F ≃ₐ[ℚ] F) ∈ I.inertia (F ≃ₐ[ℚ] F) := by
  simp only [Ideal.inertia, AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup, toGalFixed_smul]

lemma ofSubgroup_toGalFixed (χ : H →* ℂˣ) (h : H) : ArtinL.Abelian.ofSubgroup H χ (toGalFixed F H h) = χ h :=
  ArtinL.Abelian.ofSubgroup_fixingSubgroupEquiv H χ h

open scoped Classical in

lemma sum_ite_mem_inertia_eq (χ : H →* ℂˣ) (I : Ideal (𝓞 F)) :
    ∑ t : ↥H, (if (t : F ≃ₐ[ℚ] F) ∈ I.inertia (F ≃ₐ[ℚ] F) then (1 - ((χ t : ℂˣ) : ℂ)) else 0) =
      ∑ σ : ↥(I.inertia (F ≃ₐ[IntermediateField.fixedField H] F)),
        (1 - ((ArtinL.Abelian.ofSubgroup H χ (σ : F ≃ₐ[IntermediateField.fixedField H] F) : ℂˣ) : ℂ)) := by
  rw [sum_subgroup_eq_sum_ite (I.inertia (F ≃ₐ[IntermediateField.fixedField H] F))
    (fun σ => 1 - ((ArtinL.Abelian.ofSubgroup H χ σ : ℂˣ) : ℂ))]
  rw [← (Equiv.ofBijective _ (toGalFixed_bijective F H)).sum_comp]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.ofBijective_apply, toGalFixed_mem_inertia_iff, ofSubgroup_toGalFixed]

end Bridge

section WGroup

open IsDedekindDomain

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F] (H : Subgroup (F ≃ₐ[ℚ] F))

abbrev Kf : Type := ↥(IntermediateField.fixedField H)

open scoped Classical in

noncomputable def cE (ψ : (F ≃ₐ[Kf F H] F) →* ℂˣ) (P : Ideal (𝓞 (Kf F H))) : ℕ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then ArtinL.Abelian.conductorExponent ψ ⟨P, h.1, h.2⟩ else 0

open scoped Classical in
lemma cE_eq (ψ : (F ≃ₐ[Kf F H] F) →* ℂˣ) (w : HeightOneSpectrum (𝓞 (Kf F H))) :
    cE F H ψ w.asIdeal = ArtinL.Abelian.conductorExponent ψ w := by
  rw [cE, dif_pos ⟨w.isPrime, w.ne_bot⟩]

variable {F H} in
lemma natCast_mem_of_mem_primesOver {p : ℕ} {𝔔 : Ideal (𝓞 F)} (h𝔔 : 𝔔 ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F)) :
    ((p : ℕ) : 𝓞 F) ∈ 𝔔 := by
  have : (p : ℤ) ∈ 𝔔.under ℤ := by rw [← h𝔔.2.over]; exact Ideal.subset_span rfl
  simpa using this

variable {F H} in

lemma under_mem_primesOverFinset {p : ℕ} (hp : p.Prime) {𝔔 : Ideal (𝓞 F)}
    (h𝔔 : 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F)) :
    𝔔.under (𝓞 (Kf F H)) ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 (Kf F H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp)] at h𝔔 ⊢
  haveI := h𝔔.1; haveI := h𝔔.2
  exact ⟨Ideal.IsPrime.under _ 𝔔, inferInstance⟩

variable {F H} in
lemma under_ne_bot {p : ℕ} (hp : p.Prime) {𝔔 : Ideal (𝓞 F)}
    (h𝔔 : 𝔔 ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F)) : 𝔔.under (𝓞 (Kf F H)) ≠ ⊥ := by
  intro h
  have hp' : ((p : ℕ) : 𝓞 (Kf F H)) ∈ 𝔔.under (𝓞 (Kf F H)) := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact natCast_mem_of_mem_primesOver h𝔔
  rw [h, Ideal.mem_bot] at hp'
  exact hp.ne_zero (by exact_mod_cast hp')

lemma inertiaDeg_mul_sum_ramificationIdx_mul_cE_eq (ψ : (F ≃ₐ[Kf F H] F) →* ℂˣ)
    (p : ℕ) (hp : p.Prime) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal] (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) :
    (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔓 *
        ∑ 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F),
          Ideal.ramificationIdx' (𝔔.under (𝓞 (Kf F H))) 𝔔 * cE F H ψ (𝔔.under (𝓞 (Kf F H))) =
      Nat.card H * ∑ P₀ ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 (Kf F H)),
          (Ideal.span {(p : ℤ)}).inertiaDeg' P₀ * cE F H ψ P₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : 𝔓.LiesOver (Ideal.span {(p : ℤ)}) := ⟨h𝔓.symm⟩
  set T := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F)
  set T₀ := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 (Kf F H))
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := T₀) (g := fun 𝔔 : Ideal (𝓞 F) => 𝔔.under (𝓞 (Kf F H)))
    (fun 𝔔 h𝔔 => under_mem_primesOverFinset hp h𝔔)]
  refine Finset.sum_congr rfl fun P₀ hP₀ => ?_
  have hP₀' := (IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) (𝓞 (Kf F H))).mp hP₀
  haveI : P₀.IsPrime := hP₀'.1
  haveI : P₀.LiesOver (Ideal.span {(p : ℤ)}) := hP₀'.2
  have hP₀ne : P₀ ≠ ⊥ := by
    intro h
    have hp' : ((p : ℕ) : 𝓞 (Kf F H)) ∈ P₀ := by
      have : (p : ℤ) ∈ P₀.under ℤ := by rw [← hP₀'.2.over]; exact Ideal.subset_span rfl
      simpa using this
    rw [h, Ideal.mem_bot] at hp'
    exact hp.ne_zero (by exact_mod_cast hp')
  haveI : P₀.IsMaximal := hP₀'.1.isMaximal hP₀ne

  have hfib : T.filter (fun 𝔔 => 𝔔.under (𝓞 (Kf F H)) = P₀) = IsDedekindDomain.primesOverFinset P₀ (𝓞 F) := by
    ext 𝔔
    rw [Finset.mem_filter, IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) (𝓞 F),
      IsDedekindDomain.mem_primesOverFinset_iff hP₀ne (𝓞 F)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, ⟨h3.symm⟩⟩
    · rintro ⟨h1, h2⟩
      haveI := h1; haveI := h2
      exact ⟨⟨h1, Ideal.LiesOver.trans 𝔔 P₀ (Ideal.span {(p : ℤ)})⟩, h2.over.symm⟩
  rw [hfib]

  have hsum : ∑ 𝔔 ∈ IsDedekindDomain.primesOverFinset P₀ (𝓞 F),
      (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔓 * (Ideal.ramificationIdx' (𝔔.under (𝓞 (Kf F H))) 𝔔 * cE F H ψ (𝔔.under (𝓞 (Kf F H)))) =
      (Ideal.span {(p : ℤ)}).inertiaDeg' P₀ * cE F H ψ P₀ *
        ∑ 𝔔 ∈ IsDedekindDomain.primesOverFinset P₀ (𝓞 F), Ideal.ramificationIdx' P₀ 𝔔 * Ideal.inertiaDeg' P₀ 𝔔 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔔 h𝔔 => ?_
    have h𝔔' := (IsDedekindDomain.mem_primesOverFinset_iff hP₀ne (𝓞 F)).mp h𝔔
    haveI : 𝔔.IsPrime := h𝔔'.1
    haveI : 𝔔.LiesOver P₀ := h𝔔'.2
    haveI : 𝔔.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans 𝔔 P₀ _
    have hunder : 𝔔.under (𝓞 (Kf F H)) = P₀ := h𝔔'.2.over.symm
    haveI : 𝔔.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal 𝔔 P₀
    rw [hunder, Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) 𝔓,
      Ideal.inertiaDeg_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) 𝔓 𝔔 (F ≃ₐ[ℚ] F),
      ← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) 𝔔,
      Ideal.inertiaDeg'_algebra_tower (Ideal.span {(p : ℤ)}) P₀ 𝔔]
    ring
  rw [hsum, Ideal.sum_ramification_inertia (R := 𝓞 (Kf F H)) (𝓞 F) (Kf F H) F hP₀ne,
    IntermediateField.finrank_fixedField_eq_card]
  ring

end WGroup

section PerLevel

open scoped Pointwise
open IsDedekindDomain

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F] (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ)

open scoped Classical in

noncomputable def defect (𝔔 : Ideal (𝓞 F)) (j : ℕ) : ℂ :=
  ∑ t : ↥H, (if (t : F ≃ₐ[ℚ] F) ∈ Gj F 𝔔 j then (1 - ((χ t : ℂˣ) : ℂ)) else 0)

open scoped Classical in
lemma sum_ite_chi_eq (x : F ≃ₐ[ℚ] F) (𝔓 : Ideal (𝓞 F)) (j : ℕ) :
    ∑ t : ↥H, (if x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F 𝔓 j then ((χ t : ℂˣ) : ℂ) else 0) =
      ((Finset.univ.filter fun t : ↥H => x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F 𝔓 j).card : ℂ) -
        ∑ t : ↥H, (if x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F 𝔓 j then (1 - ((χ t : ℂˣ) : ℂ)) else 0) := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

open scoped Classical in

lemma term_eq (p : ℕ) (hp : p.Prime) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal] (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) (j : ℕ) :
    ((Nat.card (Gj F 𝔓 j) : ℂ) / (Nat.card (Gj F 𝔓 0) : ℂ)) *
        (((H.index : ℕ) : ℂ) - ((Nat.card (Gj F 𝔓 j) : ℂ))⁻¹ *
          ∑ g : ↥(Gj F 𝔓 j), ((Nat.card H : ℂ)⁻¹ *
            ∑ x : F ≃ₐ[ℚ] F, (if hx : x⁻¹ * (g : F ≃ₐ[ℚ] F) * x ∈ H then ((χ ⟨x⁻¹ * (g : F ≃ₐ[ℚ] F) * x, hx⟩ : ℂˣ) : ℂ) else 0))) =
      ((Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) 𝔓) : ℂ) / ((Nat.card (Gj F 𝔓 0) : ℂ) * (Nat.card H : ℂ))) *
        ∑ 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F),
          (((Nat.card (Gj F 𝔔 j) : ℂ) - (Nat.card ↥(Gj F 𝔔 j ⊓ H) : ℂ)) + defect F H χ 𝔔 j) := by

  have hinner : ∑ g : ↥(Gj F 𝔓 j), ((Nat.card H : ℂ)⁻¹ *
      ∑ x : F ≃ₐ[ℚ] F, (if hx : x⁻¹ * (g : F ≃ₐ[ℚ] F) * x ∈ H then ((χ ⟨x⁻¹ * (g : F ≃ₐ[ℚ] F) * x, hx⟩ : ℂˣ) : ℂ) else 0)) =
      (Nat.card H : ℂ)⁻¹ * (∑ x : F ≃ₐ[ℚ] F, ((Finset.univ.filter fun t : ↥H => x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F 𝔓 j).card : ℂ) -
        ∑ x : F ≃ₐ[ℚ] F, ∑ t : ↥H, (if x * (t : F ≃ₐ[ℚ] F) * x⁻¹ ∈ Gj F 𝔓 j then (1 - ((χ t : ℂˣ) : ℂ)) else 0)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [sum_dite_conj_eq, sum_ite_chi_eq]
  rw [hinner, sum_card_filter_conj_eq F H p hp 𝔓 h𝔓 j, sum_sum_ite_conj_eq F H χ p hp 𝔓 h𝔓 j]

  have hcard : ((H.index : ℕ) : ℂ) * (Nat.card H : ℂ) * (Nat.card (Gj F 𝔓 j) : ℂ) =
      (Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) 𝔓) : ℂ) *
        ∑ 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F), (Nat.card (Gj F 𝔔 j) : ℂ) := by
    rw [← sum_apply_inv_smul_eq F p hp 𝔓 h𝔓 (fun Q => (Nat.card (Gj F Q j) : ℂ))]
    simp only [card_Gj_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_mul_card H]
    push_cast; ring
  have hH : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hGj : (Nat.card (Gj F 𝔓 j) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hG0 : (Nat.card (Gj F 𝔓 0) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  simp only [defect]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  field_simp
  linear_combination hcard

end PerLevel

section Final

open IsDedekindDomain

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F] (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ)

lemma defect_eq_zero_of_eq_bot {𝔔 : Ideal (𝓞 F)} {j : ℕ} (h : Gj F 𝔔 j = ⊥) : defect F H χ 𝔔 j = 0 := by
  classical
  unfold defect
  refine Finset.sum_eq_zero fun t _ => ?_
  split_ifs with ht
  · rw [h, Subgroup.mem_bot] at ht
    have : t = 1 := Subtype.ext ht
    simp [this]
  · rfl

lemma card_sub_card_eq_zero_of_eq_bot {𝔔 : Ideal (𝓞 F)} {j : ℕ} (h : Gj F 𝔔 j = ⊥) :
    Nat.card (Gj F 𝔔 j) - Nat.card ↥(Gj F 𝔔 j ⊓ H) = 0 := by
  rw [h, bot_inf_eq, Subgroup.card_bot]

open scoped Classical in

lemma finsum_indicator_eq_sum (ψ : (F ≃ₐ[Kf F H] F) →* ℂˣ) (p : ℕ) (hp : p.Prime) :
    (∑ᶠ w : HeightOneSpectrum (𝓞 (Kf F H)),
        if ((p : ℕ) : 𝓞 (Kf F H)) ∈ w.asIdeal then
          (Ideal.span {(p : ℤ)}).inertiaDeg' w.asIdeal * ArtinL.Abelian.conductorExponent ψ w
        else 0) =
      ∑ P₀ ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 (Kf F H)), (Ideal.span {(p : ℤ)}).inertiaDeg' P₀ * cE F H ψ P₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set T₀ := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 (Kf F H))
  have hmem : ∀ P ∈ T₀, P.IsPrime ∧ P ≠ ⊥ := fun P hP => by
    have hP' := (IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) (𝓞 (Kf F H))).mp hP
    refine ⟨hP'.1, fun h => ?_⟩
    have : (p : ℤ) ∈ P.under ℤ := by rw [← hP'.2.over]; exact Ideal.subset_span rfl
    rw [h] at this
    simp only [Ideal.under_bot, Ideal.mem_bot, Int.natCast_eq_zero] at this
    exact hp.ne_zero this
  let ι : {P // P ∈ T₀} → HeightOneSpectrum (𝓞 (Kf F H)) := fun P => ⟨P.1, (hmem P.1 P.2).1, (hmem P.1 P.2).2⟩
  have hι : Function.Injective ι := fun a b h => Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)
  rw [finsum_eq_sum_of_support_subset _ (s := T₀.attach.map ⟨ι, hι⟩) ?_]
  · rw [Finset.sum_map, ← Finset.sum_attach T₀]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hp' : ((p : ℕ) : 𝓞 (Kf F H)) ∈ (ι P).asIdeal := by
      have hP' := (IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) (𝓞 (Kf F H))).mp P.2
      have : (p : ℤ) ∈ P.1.under ℤ := by rw [← hP'.2.over]; exact Ideal.subset_span rfl
      simpa using this
    simp only [Function.Embedding.coeFn_mk, if_pos hp', ← cE_eq]
    rfl
  · intro w hw
    rw [Function.mem_support] at hw
    have hpw : ((p : ℕ) : 𝓞 (Kf F H)) ∈ w.asIdeal := by by_contra h; exact hw (if_neg h)
    have hwT : w.asIdeal ∈ T₀ := by
      rw [IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp)]
      refine ⟨w.isPrime, ⟨?_⟩⟩
      refine ((Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_)).symm.trans rfl |>.symm
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show (p : ℤ) ∈ w.asIdeal.under ℤ
      rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact hpw
    refine Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨⟨w.asIdeal, hwT⟩, Finset.mem_attach _ _, ?_⟩)
    rfl

end Final

end INDsk

open scoped Pointwise in
open scoped Classical in
theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ)
    (p : ℕ) (hp : p.Prime) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal]
    (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) :
    (∑ᶠ j : ℕ, ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ) /
          (Nat.card ((𝔓 ^ 1).inertia (F ≃ₐ[ℚ] F)) : ℂ)) *
        (((H.index : ℕ) : ℂ) - ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ))⁻¹ *
          ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)),
            ((Nat.card H : ℂ)⁻¹ *
              ∑ x : F ≃ₐ[ℚ] F,
                if hx : x⁻¹ * (g : F ≃ₐ[ℚ] F) * x ∈ H then (((χ ⟨x⁻¹ * (g : F ≃ₐ[ℚ] F) * x, hx⟩ : ℂˣ)) : ℂ)
                else 0))) =
      ((((discr (IntermediateField.fixedField H)).natAbs *
          Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup H χ))).factorization p : ℕ) : ℂ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : 𝔓.LiesOver (Ideal.span {(p : ℤ)}) := ⟨h𝔓.symm⟩
  obtain ⟨J, hJ⟩ := INDsk.exists_forall_Gj_eq_bot F p hp
  set T := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F) with hT
  set T₀ := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 (INDsk.Kf F H)) with hT₀
  have hTmem : ∀ 𝔔 ∈ T, 𝔔 ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F) := fun 𝔔 h =>
    (IsDedekindDomain.mem_primesOverFinset_iff (INDsk.span_ne_bot hp) (𝓞 F)).mp h
  set ψ := ArtinL.Abelian.ofSubgroup H χ with hψ

  set e₀ : ℂ := (Nat.card (INDsk.Gj F 𝔓 0) : ℂ) with he₀
  set f₀ : ℕ := (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔓 with hf₀
  have he₀ne : e₀ ≠ 0 := by rw [he₀]; exact_mod_cast Nat.card_pos.ne'
  have hHne : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hstab : (Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) 𝔓) : ℂ) = e₀ * f₀ := by
    rw [he₀, hf₀]; exact_mod_cast INDsk.card_stabilizer_eq_card_inertia_mul_inertiaDeg F p hp 𝔓 h𝔓
  set c : ℂ := (Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) 𝔓) : ℂ) / (e₀ * (Nat.card H : ℂ)) with hc
  have hc' : c = (f₀ : ℂ) / (Nat.card H : ℂ) := by
    rw [hc, hstab]; field_simp

  set B : ℕ → ℂ := fun j => c * ∑ 𝔔 ∈ T,
    (((Nat.card (INDsk.Gj F 𝔔 j) : ℂ) - (Nat.card ↥(INDsk.Gj F 𝔔 j ⊓ H) : ℂ)) + INDsk.defect F H χ 𝔔 j) with hB
  have hBzero : ∀ j, J ≤ j → B j = 0 := fun j hj => by
    simp only [hB]
    rw [Finset.sum_eq_zero fun 𝔔 h𝔔 => ?_, mul_zero]
    have hbot := hJ 𝔔 (hTmem 𝔔 h𝔔) j hj
    rw [INDsk.defect_eq_zero_of_eq_bot F H χ hbot, hbot, bot_inf_eq, Subgroup.card_bot]
    simp
  have hsuppB : Function.support B ⊆ ((Finset.range J : Finset ℕ) : Set ℕ) := fun j hj => by
    by_contra h
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
    exact hj (hBzero j h)

  refine (finsum_congr fun j => INDsk.term_eq F H χ p hp 𝔓 h𝔓 j).trans ?_
  rw [show (fun j : ℕ => (Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) 𝔓) : ℂ) / (e₀ * (Nat.card H : ℂ)) * ∑ 𝔔 ∈ T,
    (((Nat.card (INDsk.Gj F 𝔔 j) : ℂ) - (Nat.card ↥(INDsk.Gj F 𝔔 j ⊓ H) : ℂ)) + INDsk.defect F H χ 𝔔 j)) = B from rfl]
  rw [finsum_eq_sum_of_support_subset B hsuppB]
  simp only [hB]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  rw [mul_add]

  have hD : c * ∑ 𝔔 ∈ T, ∑ j ∈ Finset.range J, ((Nat.card (INDsk.Gj F 𝔔 j) : ℂ) - (Nat.card ↥(INDsk.Gj F 𝔔 j ⊓ H) : ℂ)) =
      (((discr ↥(IntermediateField.fixedField H)).natAbs.factorization p : ℕ) : ℂ) := by
    have hC3 := NumberField.card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0 (↥F) H p hp 𝔓 h𝔓

    have hinner : ∀ 𝔔 ∈ T, (∑ᶠ j : ℕ, (Nat.card ((𝔔 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) - Nat.card ↥(((𝔔 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) ⊓ H))) =
        ∑ j ∈ Finset.range J, (Nat.card (INDsk.Gj F 𝔔 j) - Nat.card ↥(INDsk.Gj F 𝔔 j ⊓ H)) := fun 𝔔 h𝔔 => by
      refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
      by_contra h
      simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
      exact hj (INDsk.card_sub_card_eq_zero_of_eq_bot F H (hJ 𝔔 (hTmem 𝔔 h𝔔) j h))
    have houter : (∑ᶠ 𝔔 : (Ideal.span {(p : ℤ)}).primesOver (𝓞 F), ∑ᶠ j : ℕ,
        (Nat.card (((𝔔 : Ideal (𝓞 F)) ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) -
          Nat.card ↥((((𝔔 : Ideal (𝓞 F)) ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) ⊓ H))) =
        ∑ 𝔔 ∈ T, ∑ j ∈ Finset.range J, (Nat.card (INDsk.Gj F 𝔔 j) - Nat.card ↥(INDsk.Gj F 𝔔 j ⊓ H)) := by
      rw [show (∑ᶠ 𝔔 : (Ideal.span {(p : ℤ)}).primesOver (𝓞 F), ∑ᶠ j : ℕ,
          (Nat.card (((𝔔 : Ideal (𝓞 F)) ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) -
            Nat.card ↥((((𝔔 : Ideal (𝓞 F)) ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) ⊓ H))) =
          ∑ᶠ 𝔔 ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F), ∑ᶠ j : ℕ,
            (Nat.card ((𝔔 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) - Nat.card ↥(((𝔔 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) ⊓ H)) from
        finsum_set_coe_eq_finsum_mem (s := (Ideal.span {(p : ℤ)}).primesOver (𝓞 F))
          (f := fun 𝔔 : Ideal (𝓞 F) => ∑ᶠ j : ℕ,
            (Nat.card ((𝔔 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) - Nat.card ↥(((𝔔 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) ⊓ H)))]
      rw [← IsDedekindDomain.coe_primesOverFinset (INDsk.span_ne_bot hp) (𝓞 F), finsum_mem_coe_finset]
      exact Finset.sum_congr rfl hinner
    rw [houter] at hC3
    have hcast : ((∑ 𝔔 ∈ T, ∑ j ∈ Finset.range J, (Nat.card (INDsk.Gj F 𝔔 j) - Nat.card ↥(INDsk.Gj F 𝔔 j ⊓ H)) : ℕ) : ℂ) =
        ∑ 𝔔 ∈ T, ∑ j ∈ Finset.range J, ((Nat.card (INDsk.Gj F 𝔔 j) : ℂ) - (Nat.card ↥(INDsk.Gj F 𝔔 j ⊓ H) : ℂ)) := by
      push_cast [Nat.cast_sub (Subgroup.card_le_of_le (inf_le_left : INDsk.Gj F _ _ ⊓ H ≤ _))]
      rfl
    have hC3' : (Nat.card H : ℂ) * (((discr ↥(IntermediateField.fixedField H)).natAbs.factorization p : ℕ) : ℂ) =
        (f₀ : ℂ) * ∑ 𝔔 ∈ T, ∑ j ∈ Finset.range J, ((Nat.card (INDsk.Gj F 𝔔 j) : ℂ) - (Nat.card ↥(INDsk.Gj F 𝔔 j ⊓ H) : ℂ)) := by
      rw [← hcast, hf₀]; exact_mod_cast hC3
    rw [hc', div_mul_eq_mul_div, div_eq_iff hHne]
    exact hC3'.symm.trans (mul_comm _ _)

  have hE : c * ∑ 𝔔 ∈ T, ∑ j ∈ Finset.range J, INDsk.defect F H χ 𝔔 j =
      (((Ideal.absNorm (ArtinL.Abelian.conductor ψ)).factorization p : ℕ) : ℂ) := by

    have hper : ∀ 𝔔 ∈ T, ∑ j ∈ Finset.range J, INDsk.defect F H χ 𝔔 j =
        ((Ideal.ramificationIdx' (𝔔.under (𝓞 (INDsk.Kf F H))) 𝔔 * INDsk.cE F H ψ (𝔔.under (𝓞 (INDsk.Kf F H))) : ℕ) : ℂ) := by
      intro 𝔔 h𝔔
      have h𝔔' := hTmem 𝔔 h𝔔
      haveI : 𝔔.IsPrime := h𝔔'.1
      haveI : 𝔔.IsMaximal := h𝔔'.1.isMaximal (fun h => by
        have := INDsk.natCast_mem_of_mem_primesOver h𝔔'
        rw [h, Ideal.mem_bot] at this
        exact hp.ne_zero (by exact_mod_cast this))
      let w : IsDedekindDomain.HeightOneSpectrum (𝓞 (INDsk.Kf F H)) :=
        ⟨𝔔.under (𝓞 (INDsk.Kf F H)), Ideal.IsPrime.under _ 𝔔, INDsk.under_ne_bot hp h𝔔'⟩
      have hC1 := ArtinL.Abelian.finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
        (INDsk.Kf F H) F ψ w 𝔔 rfl
      rw [← INDsk.cE_eq] at hC1
      rw [← finsum_eq_sum_of_support_subset (fun j => INDsk.defect F H χ 𝔔 j) (s := Finset.range J) fun j hj => by
        by_contra h
        simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
        exact hj (INDsk.defect_eq_zero_of_eq_bot F H χ (hJ 𝔔 h𝔔' j h))]
      rw [← hC1]
      refine finsum_congr fun j => ?_
      exact INDsk.sum_ite_mem_inertia_eq F H χ (𝔔 ^ (j + 1))
    rw [Finset.sum_congr rfl hper, ← Nat.cast_sum, hc']
    have hW := INDsk.inertiaDeg_mul_sum_ramificationIdx_mul_cE_eq F H ψ p hp 𝔓 h𝔓
    have hC2 := ArtinL.Abelian.factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent
      (INDsk.Kf F H) F ψ p hp
    rw [INDsk.finsum_indicator_eq_sum F H ψ p hp] at hC2
    rw [hC2]
    have hW' : (f₀ : ℂ) * ((∑ 𝔔 ∈ T, Ideal.ramificationIdx' (𝔔.under (𝓞 (INDsk.Kf F H))) 𝔔 * INDsk.cE F H ψ (𝔔.under (𝓞 (INDsk.Kf F H))) : ℕ) : ℂ) =
        (Nat.card H : ℂ) * ((∑ P₀ ∈ T₀, (Ideal.span {(p : ℤ)}).inertiaDeg' P₀ * INDsk.cE F H ψ P₀ : ℕ) : ℂ) := by
      rw [hf₀]; exact_mod_cast hW
    rw [div_mul_eq_mul_div, div_eq_iff hHne]
    exact hW'.trans (mul_comm _ _)
  rw [hD, hE, ← Nat.cast_add, Nat.factorization_mul (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero _))
    (ArtinL.Abelian.absNorm_conductor_pos ψ).ne', Finsupp.add_apply]

end S_ArtinL_finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor
end P2MW
export P2MW.S_ArtinL_finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor (solution)
