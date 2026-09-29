-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/30e8de50-f689-5357-8bc1-0998e395e8d1

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_add
import Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq.AlgebraicCurve IsLocalRing Polynomial IntermediateField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation Place Place.ord_zero Place.ord_inv Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor genusFF IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed LSpace ell mem_lSpace_iff_ord ConstantsAreBase ell_zero_eq_one_of_constantsAreBase RiemannGenusReachedAt mul_mem_lSpace_add finiteDimensional_lSpace RegularProlongation.finrank_span_residue_eq_finrank stichtenothGenusExists_of_isCurveOver indexOfSpecialty_eq_of_genusReached indexOfSpecialty_eq_finrank_H1 essFiniteType_of_transcendental_of_finiteDimensional constantsAreBase_of_deg_eq_one Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord RegularProlongation.eq_integers_of_forall_mem_adjoin_iff RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring RegularProlongation.mul_min_ord_residue_le_of_monic"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero integers residue_algebraMap algebraMap_mem_iff residue finrank_span_residue_eq_finrank eq_integers_of_forall_mem_adjoin_iff exists_monic_coeff_natDegree_le_of_forall_valuationSubring mul_min_ord_residue_le_of_monic"
namespace CbPrime
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adjoin_inv_eq (y : F) :
    IntermediateField.adjoin K ({y⁻¹} : Set F) = IntermediateField.adjoin K ({y} : Set F) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K y)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self K y⁻¹)
    rwa [inv_inv] at h

theorem finrank_congr_of_eq {E₁ E₂ : IntermediateField K F} (h : E₁ = E₂) :
    Module.finrank E₁ F = Module.finrank E₂ F := by
  subst h
  rfl

theorem isIntegral_of_subring_le {S T : Subring F} (h : S ≤ T) {f : F}
    (hf : IsIntegral S f) : IsIntegral T f := by
  obtain ⟨p, hp, hpf⟩ := hf
  refine ⟨p.map (Subring.inclusion h), hp.map _, ?_⟩
  rw [eval₂_map]
  exact hpf

theorem isIntegral_adjoin_of_forall_valuationSubring (x f : F)
    (hf : ∀ V : ValuationSubring F, (∀ c : K, algebraMap K F c ∈ V) → x ∈ V → f ∈ V) :
    IsIntegral (Algebra.adjoin K ({x} : Set F)) f := by
  set s : Set F := Set.range (algebraMap K F) ∪ {x} with hs
  have h := iInf_valuationSubring_superset (s := s)
  have hmem : f ∈ (integralClosure (Subring.closure s) F).toSubring := by
    rw [← h]
    simp only [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    exact hf V (fun c => hV (Or.inl ⟨c, rfl⟩)) (hV (Or.inr rfl))
  have hint : IsIntegral (Subring.closure s) f := hmem
  have hcl : Subring.closure s = (Algebra.adjoin K ({x} : Set F)).toSubring :=
    (Algebra.adjoin_eq_ring_closure _).symm
  have hint' : IsIntegral (Algebra.adjoin K ({x} : Set F)).toSubring f :=
    isIntegral_of_subring_le hcl.le hint
  exact hint'

noncomputable def placeOfValuationSubring (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) (hV : V ≠ ⊤) : Place K F where
  toValuationSubring := V
  algebraMap_mem' := hK
  ne_top' := hV
  isPrincipalIdealRing' :=
    ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x V hK hV

@[scoped simp] theorem placeOfValuationSubring_toValuationSubring (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) (hV : V ≠ ⊤) :
    (placeOfValuationSubring x V hK hV).toValuationSubring = V := rfl

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ v.toValuationSubring.zero_mem)
  by_contra h
  exact hf ((v.mem_iff_ord_nonneg hf0).mpr (not_lt.mp h))

theorem mem_valuationSubring_of_mem_lSpace (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) (m : ℕ) {f : F}
    (hf : f ∈ LSpace (m • D)) (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) :
    (x ∈ V → f ∈ V) ∧ (x ∉ V → f * (x ^ m)⁻¹ ∈ V) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [V.zero_mem]
  by_cases hV : V = ⊤
  · subst hV
    exact ⟨fun _ => ValuationSubring.mem_top _, fun _ => ValuationSubring.mem_top _⟩
  set v : Place K F := placeOfValuationSubring x V hK hV with hv
  have hVv : v.toValuationSubring = V := rfl
  have hford : ∀ w : Place K F, -((m • D) w) ≤ w.ord f :=
    ((mem_lSpace_iff_ord.mp hf).resolve_left hf0)
  have hfv : -((m : ℤ) * D v) ≤ v.ord f := by
    have := hford v
    simpa [Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul] using this
  rw [hD v] at hfv
  constructor
  · intro hxV
    rcases eq_or_ne x 0 with rfl | hx0
    ·
      have : (0 : ℤ) ≤ v.ord f := by simpa [Place.ord_zero] using hfv
      rw [← hVv]
      exact (v.mem_iff_ord_nonneg hf0).mpr this
    · have hxord : 0 ≤ v.ord x := (v.mem_iff_ord_nonneg hx0).mp (hVv ▸ hxV)
      have hmax : max 0 (-v.ord x) = 0 := max_eq_left (by linarith)
      rw [hmax, mul_zero, neg_zero] at hfv
      rw [← hVv]
      exact (v.mem_iff_ord_nonneg hf0).mpr hfv
  · intro hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    have hxord : v.ord x < 0 := ord_neg_of_not_mem v (hVv ▸ hxV)
    have hmax : max 0 (-v.ord x) = -v.ord x := max_eq_right (by linarith)
    rw [hmax] at hfv
    have hne : f * (x ^ m)⁻¹ ≠ 0 := mul_ne_zero hf0 (inv_ne_zero (pow_ne_zero _ hx0))
    rw [← hVv]
    refine (v.mem_iff_ord_nonneg hne).mpr ?_
    rw [v.ord_mul hf0 (inv_ne_zero (pow_ne_zero _ hx0)), v.ord_inv, ← zpow_natCast,
      v.ord_zpow]
    nlinarith

theorem exists_poleDivisor [HasPrincipalDivisors K F] {x : F} (hx : x ≠ 0) :
    ∃ D : Divisor K F, (∀ v : Place K F, D v = max 0 (-v.ord x)) ∧ ∀ v : Place K F, 0 ≤ D v := by
  obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx
  exact ⟨Finsupp.mapRange (fun n => max 0 (-n)) (by simp) P, fun v => by simp [hP v],
    fun v => by simp⟩

theorem nonempty_place_of_transcendental [IsAlgClosed K] {x : F} (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : Nonempty (Place K F) := by
  by_contra h
  have hx' : x ∈ (algebraMap K F).range :=
    Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hx fun v => (h ⟨v⟩).elim
  obtain ⟨c, rfl⟩ := hx'
  exact hx (isAlgebraic_algebraMap c)

theorem finiteDimensional_lSpace_zero_of_constantsAreBase (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  have h : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
  rw [h]
  infer_instance

theorem genusFF_eq_of_riemannGenusReachedAt [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] (hC : ConstantsAreBase K F)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (genusFF K F : ℤ) = γ := by
  have h1 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [indexOfSpecialty_eq_finrank_H1, ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h1
  rw [genusFF]
  push_cast at h1 ⊢
  linarith

end Generic

section Riemann

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_mem_lSpace_sub_of_forall_eq_ord {f : F} {P : Divisor K F}
    (hP : ∀ v : Place K F, P v = v.ord f) {E : Divisor K F} {g : F} (hg : g ∈ LSpace E) :
    g * f ∈ LSpace (E - P) := by
  have hfmem : f ∈ LSpace (-P) :=
    mem_lSpace_iff_ord.mpr (Or.inr fun v => by simp [hP v])
  simpa [sub_eq_add_neg] using mul_mem_lSpace_add hg hfmem

noncomputable def mulRight (f : F) (E E' : Divisor K F)
    (h : ∀ g ∈ LSpace E, g * f ∈ LSpace E') : LSpace E →ₗ[K] LSpace E' where
  toFun g := ⟨(g : F) * f, h g g.2⟩
  map_add' a b := Subtype.ext (by simp [add_mul])
  map_smul' c a := Subtype.ext (by simp)

theorem ell_sub_eq_of_forall_eq_ord {f : F} (hf0 : f ≠ 0) {P : Divisor K F}
    (hP : ∀ v : Place K F, P v = v.ord f) (E : Divisor K F) : ell (E - P) = ell E := by
  have h1 : ∀ g ∈ LSpace E, g * f ∈ LSpace (E - P) := fun g hg =>
    mul_mem_lSpace_sub_of_forall_eq_ord hP hg
  have hP' : ∀ v : Place K F, (-P) v = v.ord f⁻¹ := fun v => by simp [hP v, Place.ord_inv]
  have h2 : ∀ g ∈ LSpace (E - P), g * f⁻¹ ∈ LSpace E := fun g hg => by
    simpa using mul_mem_lSpace_sub_of_forall_eq_ord hP' hg
  let e : LSpace E ≃ₗ[K] LSpace (E - P) :=
    { mulRight f E (E - P) h1 with
      invFun := mulRight f⁻¹ (E - P) E h2
      left_inv := fun g => Subtype.ext (by simp [mulRight, mul_inv_cancel_right₀ hf0])
      right_inv := fun g => Subtype.ext (by simp [mulRight, inv_mul_cancel_right₀ hf0]) }
  exact (LinearEquiv.finrank_eq e).symm

theorem exists_forall_degree_nsmul_sub_ell_eq [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {γ : ℤ} {D₀ : Divisor K F}
    (h : RiemannGenusReachedAt γ D₀) {D : Divisor K F} (hD : 0 < Divisor.degree D) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      Divisor.degree (m • D) - (ell (m • D) : ℤ) = γ - 1 := by
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℕ, Divisor.degree D₀ + γ ≤ (m₁ : ℤ) * Divisor.degree D := by
    refine ⟨(Divisor.degree D₀ + γ).toNat, ?_⟩
    calc Divisor.degree D₀ + γ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) := Int.self_le_toNat _
      _ = ((Divisor.degree D₀ + γ).toNat : ℤ) * 1 := (mul_one _).symm
      _ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) * Divisor.degree D :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
  refine ⟨m₁, fun m hm => ?_⟩
  have hdegm : Divisor.degree (m • D) = (m : ℤ) * Divisor.degree D := by
    rw [map_nsmul, nsmul_eq_mul]
  have hineq := h.isMax (m • D - D₀)
  have hmm : (m₁ : ℤ) * Divisor.degree D ≤ (m : ℤ) * Divisor.degree D :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hD.le
  have hell_pos : 0 < ell (m • D - D₀) := by
    have : (1 : ℤ) ≤ ell (m • D - D₀) := by
      rw [map_sub, hdegm] at hineq
      linarith
    exact_mod_cast this
  haveI : FiniteDimensional K (LSpace (m • D - D₀)) := finiteDimensional_lSpace _
  obtain ⟨⟨f, hfmem⟩, hf0⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := LSpace (m • D - D₀))).mp hell_pos
  have hf0 : f ≠ 0 := fun h0 => hf0 (Subtype.ext h0)
  obtain ⟨P, hP, hP0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hle : D₀ - P ≤ m • D := fun v => by
    have := (mem_lSpace_iff_ord.mp hfmem).resolve_left hf0 v
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply] at this ⊢
    rw [hP v]
    linarith
  have h' : RiemannGenusReachedAt γ (D₀ - P) :=
    { finite := finiteDimensional_lSpace _
      eq := by
        rw [ell_sub_eq_of_forall_eq_ord hf0 hP, map_sub, hP0, sub_zero]
        exact h.eq
      isMax := h.isMax }
  exact h'.eq_of_ge hle

end Riemann

section Prolongation

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem mem_of_isRoot_monic {P : A[X]} (hP : P.Monic) {x : L}
    (hx : (P.map (algebraMap A L)).IsRoot x) : x ∈ A := by
  have hint : IsIntegral A x := ⟨P, hP, by rwa [← eval_map, ← IsRoot.def]⟩
  have : IsIntegrallyClosed A := inferInstance
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff L).mp this hint
  rw [← hy]
  exact y.2

theorem isAlgClosed_residueField [IsAlgClosed L] : IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := Ideal.Quotient.mk_surjective
  obtain ⟨P, hPp, hPdeg, hPmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (mem_lifts_of_surjective hsurj p) hp
  have hdeg : (P.map (algebraMap A L)).degree ≠ 0 := by
    rw [hPmon.degree_map, hPdeg]
    exact fun h0 => hirr.not_isUnit (isUnit_iff_degree_eq_zero.mpr h0) |>.elim
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  have hxA : x ∈ A := mem_of_isRoot_monic hPmon hx
  refine ⟨IsLocalRing.residue A ⟨x, hxA⟩, ?_⟩
  have hPx : P.eval ⟨x, hxA⟩ = 0 := by
    have h1 : (P.map (algebraMap A L)).eval x = 0 := hx
    rw [eval_map] at h1
    have h2 : algebraMap A L (P.eval ⟨x, hxA⟩) = 0 := by
      rw [← eval₂_at_apply]; exact h1
    exact (map_eq_zero_iff _ (IsFractionRing.injective A L)).mp h2
  rw [← hPp, eval_map, eval₂_at_apply, hPx, map_zero]

theorem transcendental_coe [IsAlgClosed L] (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x)) : Transcendental L (x : F) := by
  intro halg
  have hint : IsIntegral L (x : F) := halg.isIntegral
  have h1 : (minpoly L (x : F)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one L (x : F) h1
  have hcA : c ∈ A := (R.algebraMap_mem_iff c).mp (hc ▸ x.2)
  apply hx
  have hxeq : x = constHom R ⟨c, hcA⟩ := Subtype.ext hc.symm
  rw [hxeq, residue_constHom]
  exact isAlgebraic_algebraMap _

theorem mem_of_mem_span (R : RegularProlongation A F Fbar) (V : Submodule L F) {h : Fbar}
    (hh : h ∈ Submodule.span (ResidueField A)
      {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) :
    ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h := by
  induction hh using Submodule.span_induction with
  | mem h hh => exact hh
  | zero => exact ⟨0, by simp, map_zero _⟩
  | add h₁ h₂ _ _ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁, rfl⟩ := ih₁
    obtain ⟨f₂, hf₂, rfl⟩ := ih₂
    exact ⟨f₁ + f₂, by simpa using V.add_mem hf₁ hf₂, map_add _ _ _⟩
  | smul κ h _ ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    obtain ⟨α, hα⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal A) κ
    refine ⟨constHom R α * f, ?_, ?_⟩
    · have : ((constHom R α * f : R.integers) : F) = (α : L) • (f : F) := by
        simp [Algebra.smul_def]
      rw [this]
      exact V.smul_mem _ hf
    · rw [map_mul, residue_constHom, ← hα, Algebra.smul_def]
      rfl

theorem residue_mem_lSpace_nsmul (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    {D : Divisor L F} (hD : ∀ v : Place L F, D v = max 0 (-v.ord (x : F)))
    {Dbar : Divisor (ResidueField A) Fbar}
    (hDbar : ∀ w : Place (ResidueField A) Fbar, Dbar w = max 0 (-w.ord (R.residue x)))
    (m : ℕ) {f : R.integers} (hf : (f : F) ∈ LSpace (m • D)) :
    R.residue f ∈ LSpace (m • Dbar) := by
  obtain ⟨p, hp, hpdeg, hroot⟩ :=
    AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring
      A R x hx (f : F) m
      (fun V hV hxV => (mem_valuationSubring_of_mem_lSpace (x : F) D hD m hf V hV).1 hxV)
      (fun V hV hxV => (mem_valuationSubring_of_mem_lSpace (x : F) D hD m hf V hV).2 hxV)
      (fun V hV => by
        rw [AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff
          A R x hx hfin hdeg V hV]
        exact f.2)
  have hM := AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_monic
    A R x f m p hp hpdeg hroot
  refine mem_lSpace_iff_ord.mpr (Or.inr fun w => ?_)
  have h1 := hM w
  have h2 : -((m : ℤ) * Dbar w) = (m : ℤ) * min 0 (w.ord (R.residue x)) := by
    rw [hDbar w, ← mul_neg]
    congr 1
    rcases le_total 0 (w.ord (R.residue x)) with h0 | h0
    · rw [max_eq_left (by linarith), min_eq_left h0, neg_zero]
    · rw [max_eq_right (by linarith), min_eq_right h0, neg_neg]
  have h3 : (m • Dbar) w = (m : ℤ) * Dbar w := by simp
  rw [h3, h2]
  exact h1

end Prolongation

section Chart

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  [IsCurveOver (ResidueField A) Fbar]

theorem chart (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hgood : genusFF (ResidueField A) Fbar = genusFF L F)
    (h : Fbar) (hh : IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) h) :
    ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h := by
  classical

  haveI hk : IsAlgClosed (ResidueField A) := isAlgClosed_residueField
  haveI : PerfectField (ResidueField A) := IsAlgClosed.perfectField _
  haveI : PerfectField L := IsAlgClosed.perfectField _
  have hxL : Transcendental L (x : F) := transcendental_coe R x hx
  haveI hfdb : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  haveI hfd : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  haveI : Nonempty (Place L F) := nonempty_place_of_transcendental hxL
  haveI : Nonempty (Place (ResidueField A) Fbar) := nonempty_place_of_transcendental hx
  have hC : ConstantsAreBase L F :=
    constantsAreBase_of_deg_eq_one (Classical.arbitrary (Place L F))
      (IsCurveOver.deg_eq_one_of_isAlgClosed _)
  have hCb : ConstantsAreBase (ResidueField A) Fbar :=
    constantsAreBase_of_deg_eq_one (Classical.arbitrary (Place (ResidueField A) Fbar))
      (IsCurveOver.deg_eq_one_of_isAlgClosed _)
  haveI : FiniteDimensional L (LSpace (0 : Divisor L F)) :=
    finiteDimensional_lSpace_zero_of_constantsAreBase hC
  haveI : FiniteDimensional (ResidueField A) (LSpace (0 : Divisor (ResidueField A) Fbar)) :=
    finiteDimensional_lSpace_zero_of_constantsAreBase hCb
  haveI : Algebra.EssFiniteType L F :=
    essFiniteType_of_transcendental_of_finiteDimensional hxL hfd
  haveI : Algebra.EssFiniteType (ResidueField A) Fbar :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hfdb

  obtain ⟨-, -, γ, D₀, hR⟩ := stichtenothGenusExists_of_isCurveOver hC
  obtain ⟨-, -, γb, Db₀, hRb⟩ := stichtenothGenusExists_of_isCurveOver hCb
  have hγ : (genusFF L F : ℤ) = γ := genusFF_eq_of_riemannGenusReachedAt hC hR
  have hγb : (genusFF (ResidueField A) Fbar : ℤ) = γb :=
    genusFF_eq_of_riemannGenusReachedAt hCb hRb
  have hγγ : γ = γb := by rw [← hγ, ← hγb, hgood]

  have hx0 : (x : F) ≠ 0 := fun h0 => hxL (h0 ▸ isAlgebraic_zero)
  have hxb0 : R.residue x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  obtain ⟨D, hD, hD0⟩ := exists_poleDivisor (K := L) hx0
  obtain ⟨Db, hDb, hDb0⟩ := exists_poleDivisor (K := ResidueField A) hxb0
  have hdegD := Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (x : F) hxL D hD
  have hdegDb := Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (R.residue x) hx Db hDb
  have hDD : Divisor.degree D = Divisor.degree Db := by rw [hdegD, hdegDb, hdeg]
  have hDbpos : 0 < Divisor.degree Db := by rw [hdegDb]; exact_mod_cast hfin

  obtain ⟨m₁, hm₁⟩ := exists_forall_degree_nsmul_sub_ell_eq hRb hDbpos

  have key : ∀ m : ℕ, m₁ ≤ m → ∀ g ∈ LSpace (m • Db),
      ∃ f : R.integers, (f : F) ∈ LSpace (m • D) ∧ R.residue f = g := by
    intro m hm g hg
    haveI : FiniteDimensional L (LSpace (m • D)) := finiteDimensional_lSpace _
    haveI : FiniteDimensional (ResidueField A) (LSpace (m • Db)) := finiteDimensional_lSpace _
    set S : Submodule (ResidueField A) Fbar := Submodule.span (ResidueField A)
      {h : Fbar | ∃ f : R.integers, (f : F) ∈ LSpace (m • D) ∧ R.residue f = h} with hS
    have hSle : S ≤ LSpace (m • Db) := by
      rw [hS, Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact residue_mem_lSpace_nsmul R x hx hfin hdeg hD hDb m hf
    have hfinS : Module.finrank (ResidueField A) S = Module.finrank L (LSpace (m • D)) :=
      AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank A R x hx hfin hdeg
        (LSpace (m • D))
    have hRi := hR.isMax (m • D)
    have hexact := hm₁ m hm
    have hle : Module.finrank (ResidueField A) (LSpace (m • Db)) ≤
        Module.finrank (ResidueField A) S := by
      rw [hfinS]
      have h1 : Divisor.degree (m • D) = Divisor.degree (m • Db) := by
        rw [map_nsmul, map_nsmul, hDD]
      have : (ell (m • Db) : ℤ) ≤ ell (m • D) := by linarith
      exact_mod_cast this
    have hEq : S = LSpace (m • Db) := Submodule.eq_of_le_of_finrank_le hSle hle
    have hgS : g ∈ S := hEq ▸ hg
    exact mem_of_mem_span R _ hgS

  rcases eq_or_ne h 0 with rfl | hh0
  · exact ⟨0, by simpa using isIntegral_zero, map_zero _⟩
  let m₀ : ℕ := Db.support.sup fun w => (-(w.ord h)).toNat
  have hmem : h ∈ LSpace ((max m₀ m₁) • Db) := by
    refine mem_lSpace_iff_ord.mpr (Or.inr fun w => ?_)
    have h2 : ((max m₀ m₁ • Db) w : ℤ) = ((max m₀ m₁ : ℕ) : ℤ) * Db w := by simp
    rw [h2]
    by_cases hxw : R.residue x ∈ w.toValuationSubring
    · have hhw : h ∈ w.toValuationSubring := w.mem_toValuationSubring_of_isIntegral_adjoin hxw hh
      have h1 : 0 ≤ w.ord h := (w.mem_iff_ord_nonneg hh0).mp hhw
      have h3 : (0 : ℤ) ≤ ((max m₀ m₁ : ℕ) : ℤ) * Db w := mul_nonneg (by positivity) (hDb0 w)
      linarith
    · have hord : w.ord (R.residue x) < 0 := ord_neg_of_not_mem w hxw
      have hDbw : Db w = -w.ord (R.residue x) := by
        rw [hDb w]; exact max_eq_right (by linarith)
      have hsupp : w ∈ Db.support := by
        rw [Finsupp.mem_support_iff, hDbw]; omega
      have hm₀ : (-(w.ord h)).toNat ≤ m₀ :=
        Finset.le_sup (f := fun w => (-(w.ord h)).toNat) hsupp
      have h1 : -(w.ord h) ≤ (m₀ : ℤ) := by
        have := Int.self_le_toNat (-(w.ord h)); omega
      have h3 : (m₀ : ℤ) ≤ ((max m₀ m₁ : ℕ) : ℤ) := by exact_mod_cast le_max_left _ _
      have h4 : (1 : ℤ) ≤ Db w := by rw [hDbw]; omega
      have h5 : (0 : ℤ) ≤ ((max m₀ m₁ : ℕ) : ℤ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  obtain ⟨f, hf, hfh⟩ := key (max m₀ m₁) (le_max_right _ _) h hmem
  exact ⟨f, isIntegral_adjoin_of_forall_valuationSubring (x : F) (f : F) fun V hV hxV =>
    (mem_valuationSubring_of_mem_lSpace (x : F) D hD _ hf V hV).1 hxV, hfh⟩

end Chart

end AlgebraicCurve.RegularProlongation.CbPrime
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq.AlgebraicCurve.RegularProlongation.CbPrime"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq.AlgebraicCurve"

open _root_.AlgebraicCurve.RegularProlongation _root_.P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq.AlgebraicCurve.RegularProlongation in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F) :
    (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
    (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h) := by
  refine ⟨fun h hh => CbPrime.chart R x hx hfin hdeg hgood h hh, fun h hh => ?_⟩

  have hxb0 : R.residue x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hxb0
  have hxy : x * (↑u⁻¹ : R.integers) = 1 := by rw [← hu]; exact u.mul_inv
  have hx0 : (x : F) ≠ 0 := fun h0 => by
    have := congrArg Subtype.val hxy
    simp [h0] at this
  have hyF : ((↑u⁻¹ : R.integers) : F) = (x : F)⁻¹ := by
    have h1 : (x : F) * ((↑u⁻¹ : R.integers) : F) = 1 := by exact_mod_cast congrArg Subtype.val hxy
    exact eq_inv_of_mul_eq_one_right h1
  have hyres : R.residue (↑u⁻¹ : R.integers) = (R.residue x)⁻¹ := by
    have h1 : R.residue x * R.residue (↑u⁻¹ : R.integers) = 1 := by rw [← map_mul, hxy, map_one]
    exact eq_inv_of_mul_eq_one_right h1
  have hytr : Transcendental (IsLocalRing.ResidueField A) (R.residue (↑u⁻¹ : R.integers)) := by
    rw [hyres]
    exact fun halg => hx (IsAlgebraic.inv_iff.mp halg)
  have hEb : IntermediateField.adjoin (IsLocalRing.ResidueField A)
      ({R.residue (↑u⁻¹ : R.integers)} : Set Fbar) =
      IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar) := by
    rw [hyres]; exact CbPrime.adjoin_inv_eq _
  have hE : IntermediateField.adjoin L ({((↑u⁻¹ : R.integers) : F)} : Set F) =
      IntermediateField.adjoin L ({(x : F)} : Set F) := by
    rw [hyF]; exact CbPrime.adjoin_inv_eq _
  have hfin' := hfin
  rw [← CbPrime.finrank_congr_of_eq hEb] at hfin'
  have hdeg' := hdeg
  rw [← CbPrime.finrank_congr_of_eq hEb, ← CbPrime.finrank_congr_of_eq hE] at hdeg'
  have hh' : IsIntegral
      (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue (↑u⁻¹ : R.integers)}) h := by
    rw [hyres]; exact hh
  obtain ⟨f, hf, hfh⟩ := CbPrime.chart R _ hytr hfin' hdeg' hgood h hh'
  refine ⟨f, ?_, hfh⟩
  rw [hyF] at hf
  exact hf

end S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq (solution)
