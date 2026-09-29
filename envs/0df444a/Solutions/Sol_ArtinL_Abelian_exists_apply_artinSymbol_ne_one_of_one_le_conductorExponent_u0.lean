-- Prove2me | solution 1 for ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e5c3266b-94b1-5fc8-bbed-811dd499d5a8

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_M4aHerbrand_finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_M4aHerbrand_inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap
import Theorems.Thm_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
import Theorems.Thm_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Theorems.Thm_ArtinL_Abelian_apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one
import Theorems.Thm_M4aHerbrand_exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup
import Theorems.Thm_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt
import Theorems.Thm_ArtinL_Abelian_natCeil_swanConductor_eq
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_sub_algebraMap_mem_adicCompletionIntegers
import Theorems.Thm_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin
open M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
open scoped IsMulCommutative RestrictedProduct

namespace ArtinL
p2m_export "ArtinL" "Abelian.inertiaGroup Abelian.ramificationGroup Abelian.IsUnramifiedAt Abelian.swanConductor Abelian.conductorExponent Abelian.apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one Abelian.forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt Abelian.natCeil_swanConductor_eq"
namespace T1lg
p2m_open "ArtinL"
p2m_open "IsDedekindDomain NumberField NumberField.InfinitePlace.NumberField HeckeCharacter LanglandsTunnell.P2.Artin M4aHerbrand"

variable (K : Type*) [Field K] [NumberField K]

theorem snd_algebraMap_apply (a : K) (w : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((algebraMap K (AdeleRing (𝓞 K) K) a).2 : FiniteAdeleRing (𝓞 K) K) w) = w.valuation K a := by
  change Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) a) w) = _
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem archRealProjTau_algebraMap (τ : K →+* ℝ) (a : Kˣ) :
    archRealProjTau K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) = τ a := by
  unfold archRealProjTau
  change InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf K τ)
      ((a : K) : (placeOf K τ).Completion) = τ a
  have h1 : InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf K τ) ((a : K) : (placeOf K τ).Completion) =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal (isReal_placeOf K τ) ((a : K) : (placeOf K τ).Completion) := rfl
  rw [h1, InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply]
  change (InfinitePlace.mk (Complex.ofRealHom.comp τ)).embedding (a : K) = _
  rw [InfinitePlace.embedding_mk_eq_of_isReal (isReal_compOfRealHom K τ)]
  rfl

theorem archSign_algebraMap_iff (τ : K →+* ℝ) (a : Kˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) ↔ 0 < τ a := by
  unfold archSign
  rw [archRealProjTau_algebraMap]

theorem placeOrd_projFin (x : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (projFin K x) w = -WithZero.log (Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w)) := rfl

theorem dvd_span_of_forall_pow_count_dvd {R : Type*} [CommRing R] [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) {r : R}
    (h : ∀ w : HeightOneSpectrum R, w.asIdeal ^ (Associates.mk w.asIdeal).count (Associates.mk I).factors ∣ Ideal.span {r}) :
    I ∣ Ideal.span {r} := by
  classical
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI]

  rw [finprod_eq_prod _ (Ideal.finite_mulSupport hI)]
  refine Finset.prod_dvd_of_coprime ?_ fun w _ => h w
  intro w _ w' _ hne
  exact (Ideal.isCoprime_iff_sup_eq.2 ((w.isMaximal.coprime_of_ne w'.isMaximal
    (fun heq => hne (HeightOneSpectrum.ext heq))))).pow

theorem v_algebraMap (w : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (w.adicCompletion K) k) = w.valuation K k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k

theorem snd_inv_apply (x : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w =
      ((((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  have h : (((x * x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 =
      ((x : AdeleRing (𝓞 K) K)).2 * (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 := Prod.snd_mul _ _
  rw [← fad_mul_apply, ← h, mul_inv_cancel, Units.val_one]
  exact fad_one_apply K w

theorem snd_mul_apply (x y : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (((x * y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w =
      (((x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w * (((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w := by
  have h : (((x * y : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 =
      ((x : AdeleRing (𝓞 K) K)).2 * ((y : AdeleRing (𝓞 K) K)).2 := Prod.snd_mul _ _
  rw [h, fad_mul_apply]

theorem algebraMap_fad_apply (k : K) (w : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) w = algebraMap K (w.adicCompletion K) k := by
  rw [FiniteAdeleRing.algebraMap_apply]; rfl

end ArtinL.T1lg

namespace T1bBody

section single
open scoped Classical
variable (F : Type) [Field F] [NumberField F]

noncomputable def finSingle (w : HeightOneSpectrum (𝓞 F)) : w.adicCompletion F →* FiniteAdeleRing (𝓞 F) F where
  toFun x := (RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) w x :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
  map_one' := RestrictedProduct.mulSingle_one _ w
  map_mul' x y := RestrictedProduct.mulSingle_mul _ w x y

theorem finSingle_apply_same (w : HeightOneSpectrum (𝓞 F)) (x : w.adicCompletion F) : finSingle F w x w = x :=
  RestrictedProduct.mulSingle_eq_same _ w x

theorem finSingle_apply_of_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (x : w.adicCompletion F) : finSingle F w x w' = 1 :=
  RestrictedProduct.mulSingle_eq_of_ne _ x h

noncomputable def adeleSingle (w : HeightOneSpectrum (𝓞 F)) : w.adicCompletion F →* AdeleRing (𝓞 F) F where
  toFun x := (show AdeleRing (𝓞 F) F from ((1 : InfiniteAdeleRing F), finSingle F w x))
  map_one' := by rw [map_one]; rfl
  map_mul' x y := by
    rw [map_mul]
    change ((1 : InfiniteAdeleRing F), finSingle F w x * finSingle F w y) =
      (((1 : InfiniteAdeleRing F), finSingle F w x) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) * ((1 : InfiniteAdeleRing F), finSingle F w y)
    rw [Prod.mk_mul_mk, one_mul]

noncomputable def iotaW (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ := Units.map (adeleSingle F w)

theorem finPart_iotaW_same (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) : finPart w (iotaW F w x) = x :=
  Units.ext (finSingle_apply_same F w x)

theorem finPart_iotaW_of_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (x : (w.adicCompletion F)ˣ) : finPart w' (iotaW F w x) = 1 :=
  Units.ext (finSingle_apply_of_ne F w w' h x)

theorem infPart_iotaW (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) : infPart (iotaW F w x) = 1 := Units.ext rfl

theorem iotaW_mem_idelesTrivialOn (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    iotaW F w x ∈ idelesTrivialOn (𝓞 F) F ({w}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
  ⟨infPart_iotaW F w x, fun w' hw' => finPart_iotaW_of_ne F w w' (by simpa using hw') x⟩

end single

section counts
variable {K : Type} [Field K] [NumberField K]

noncomputable def cnt (I : Ideal (𝓞 K)) (w : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk w.asIdeal).count (Associates.mk I).factors

theorem cnt_mul {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (w : HeightOneSpectrum (𝓞 K)) :
    cnt (I * J) w = cnt I w + cnt J w := by
  classical
  unfold cnt
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 hI) (Associates.mk_ne_zero.2 hJ) w.associates_irreducible]

theorem cnt_pow_self (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : cnt (w.asIdeal ^ n) w = n := by
  classical
  unfold cnt
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 w.ne_bot) w.associates_irreducible,
    Associates.count_self w.associates_irreducible, mul_one]

theorem cnt_pow_of_ne {w u : HeightOneSpectrum (𝓞 K)} (h : u ≠ w) (n : ℕ) : cnt (w.asIdeal ^ n) u = 0 := by
  classical
  unfold cnt
  have hne : Associates.mk u.asIdeal ≠ Associates.mk w.asIdeal := fun heq =>
    h (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 heq)))
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 w.ne_bot) u.associates_irreducible,
    Associates.count_eq_zero_of_ne u.associates_irreducible w.associates_irreducible hne, mul_zero]

theorem cnt_eq_zero_of_not_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {w : HeightOneSpectrum (𝓞 K)} (h : ¬ w.asIdeal ∣ I) : cnt I w = 0 := by
  classical
  by_contra hne
  exact h ((Associates.count_ne_zero_iff_dvd hI w.irreducible).1 hne)

theorem valued_algebraMap_eq (α : 𝓞 K) (hα : α ≠ 0) (w : HeightOneSpectrum (𝓞 K)) :
    Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = WithZero.exp (-(cnt (Ideal.span {α}) w : ℤ)) := by
  have h1 : Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = w.valuation K (α : K) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (α : K)
  rw [h1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hα]
  rfl

theorem cnt_eq_zero_of_valued_sub_one_le (α : 𝓞 K) (hα : α ≠ 0) (w : HeightOneSpectrum (𝓞 K)) {m : ℕ} (hm : 1 ≤ m)
    (h : Valued.v (algebraMap K (w.adicCompletion K) (α : K) - 1) ≤ WithZero.exp (-(m : ℤ))) :
    Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧ cnt (Ideal.span {α}) w = 0 := by
  have hlt : Valued.v (algebraMap K (w.adicCompletion K) (α : K) - 1) < 1 :=
    h.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hone : Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 := by
    rw [show algebraMap K (w.adicCompletion K) (α : K) = 1 + (algebraMap K (w.adicCompletion K) (α : K) - 1) by ring]
    exact Valuation.map_one_add_of_lt _ hlt
  refine ⟨hone, ?_⟩
  rw [valued_algebraMap_eq α hα w] at hone
  have := WithZero.exp_injective (hone.trans WithZero.exp_zero.symm)
  omega

theorem valued_sub_one_le_of_mem {𝔞 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) {α : 𝓞 K} (h : α - 1 ∈ 𝔞) (w : HeightOneSpectrum (𝓞 K))
    (hw : w.asIdeal ∣ 𝔞) :
    Valued.v (algebraMap K (w.adicCompletion K) (α : K) - 1) ≤ WithZero.exp (-(cnt 𝔞 w : ℤ)) := by
  have h1 := (HeckeCharacter.mem_iff_forall_valued_algebraMap_finiteAdeleRing_le K 𝔞 h𝔞 (α - 1)).1 h w hw
  have e : (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((α - 1 : 𝓞 K) : K)) w = algebraMap K (w.adicCompletion K) (α : K) - 1 := by
    rw [show ((α - 1 : 𝓞 K) : K) = (α : K) - 1 from rfl, map_sub, map_one]
    rfl
  rwa [e] at h1

end counts

end T1bBody

namespace T1bBody
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem not_isUnramifiedAt_of_one_le (ψ : (L ≃ₐ[K] L) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (hf : 1 ≤ ArtinL.Abelian.conductorExponent ψ v) : ¬ ArtinL.Abelian.IsUnramifiedAt ψ v := by
  intro hunr
  have hG : ∀ i : ℕ, ∀ σ ∈ ArtinL.Abelian.ramificationGroup K L v (i + 1), ψ σ = 1 := fun i σ hσ =>
    hunr σ ((show ArtinL.Abelian.ramificationGroup K L v (i + 1) ≤ ArtinL.Abelian.inertiaGroup K L v from
      fun _ h x => Ideal.pow_le_self (Nat.succ_ne_zero _) (h x)) hσ)
  have hswan : ArtinL.Abelian.swanConductor ψ v = 0 := by
    unfold ArtinL.Abelian.swanConductor
    exact finsum_eq_zero_of_forall_eq_zero fun i => by rw [if_pos (hG i), mul_zero]
  rw [ArtinL.Abelian.conductorExponent, if_pos hunr, hswan, Nat.ceil_zero] at hf
  exact Nat.not_succ_le_zero 0 hf

end T1bBody

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (𝔪' : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔪')
    (N : ℕ)
    (hN : ∀ (β : 𝓞 K) (hβ : β ≠ 0) (𝔪 : Ideal (𝓞 K)) (hc : principalUnit K β hβ ∈ coprimeToModulus K 𝔪),
      (∀ τ : K →+* ℝ, 0 < τ (β : K)) → β - 1 ∈ v.asIdeal ^ N * 𝔪' →
        ψ (artinSymbol K L 𝔪 ⟨principalUnit K β hβ, hc⟩) = 1)
    (hf : 1 ≤ ArtinL.Abelian.conductorExponent ψ v) :
    ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K (v.asIdeal * 𝔪')),
      (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧ α - 1 ∈ v.asIdeal ^ (ArtinL.Abelian.conductorExponent ψ v - 1) * 𝔪' ∧
        ψ (artinSymbol K L (v.asIdeal * 𝔪') ⟨principalUnit K α hα, hc⟩) ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon

  obtain ⟨𝔯, h𝔯0, h𝔯⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd K L
  obtain ⟨𝔣, -, -, hadm⟩ := LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd K L 𝔯 h𝔯0 h𝔯
    (Module.finrank K L)
  obtain ⟨r, hr₁, hr₂, hr₃, hr₄⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank K L 𝔣 hadm
  have h𝔪'0 : 𝔪' ≠ ⊥ := fun h => hv (h ▸ dvd_zero _)
  set wL : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L) := fun u =>
    ⟨LanglandsTunnell.P2.Artin.primeAbove K L u, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K L u⟩ with hwL
  have hwLu : ∀ u, (wL u).under (𝓞 K) = u := fun u => HeightOneSpectrum.ext (LanglandsTunnell.P2.Artin.under_primeAbove K L u)
  have hram : ¬ ArtinL.Abelian.IsUnramifiedAt ψ v := T1bBody.not_isUnramifiedAt_of_one_le ψ v hf
  have hfswan : ArtinL.Abelian.conductorExponent ψ v = 1 + ⌈ArtinL.Abelian.swanConductor ψ v⌉₊ := by
    rw [ArtinL.Abelian.conductorExponent, if_neg hram]

  have hN_of : ∀ N' : ℕ, 1 ≤ N' → ArtinL.Abelian.conductorExponent ψ v - 1 ≤ N' →
      ∀ (β : 𝓞 K) (hβ : β ≠ 0) (𝔪 : Ideal (𝓞 K)) (hc : principalUnit K β hβ ∈ coprimeToModulus K 𝔪),
        (∀ τ : K →+* ℝ, 0 < τ (β : K)) → β - 1 ∈ v.asIdeal ^ N' * 𝔪' → ψ (artinSymbol K L 𝔪 ⟨principalUnit K β hβ, hc⟩) = 1 := by
    intro N' hN'1 hN'f β hβ 𝔪 hc' hposβ hβ1
    have hle1 : v.asIdeal ^ N' * 𝔪' ≤ v.asIdeal * 𝔪' :=
      Ideal.mul_mono_left ((Ideal.pow_le_pow_right hN'1).trans (by rw [pow_one]))
    have hlef : v.asIdeal ^ N' * 𝔪' ≤ v.asIdeal ^ (ArtinL.Abelian.conductorExponent ψ v - 1) * 𝔪' :=
      Ideal.mul_mono_left (Ideal.pow_le_pow_right hN'f)
    have hc₀ : principalUnit K β hβ ∈ coprimeToModulus K (v.asIdeal * 𝔪') := principalUnit_mem_coprimeToModulus K hβ (hle1 hβ1)
    exact hcon β hβ hc₀ hposβ (hlef hβ1)

  rcases Nat.eq_zero_or_pos ⌈ArtinL.Abelian.swanConductor ψ v⌉₊ with hk0 | hkpos
  ·

    have hf1 : ArtinL.Abelian.conductorExponent ψ v = 1 := by rw [hfswan, hk0]
    have hbad : ∃ σ ∈ ArtinL.Abelian.inertiaGroup K L v, ψ σ ≠ 1 := by
      by_contra h
      push Not at h
      exact hram h
    obtain ⟨σ, hσI, hψσ⟩ := hbad
    obtain ⟨y, hy, hry⟩ := Subgroup.mem_map.1
      (M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v (wL v) (hwLu v) hσI)
    have hyT : y ∈ idelesTrivialOn (𝓞 K) K ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := unitIdelesTrivialOn_le_idelesTrivialOn _ _ _ hy
    have hyU := (NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one K _ y).1 hy.1
    have hy1 : ∀ w, w ≠ v → finPart w y = 1 := fun w hw => hyT.2 w (by simpa using hw)
    have hy2 : ∀ w, (((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = ((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K) :=
      fun w => rfl
    have hyunit : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
      intro w
      by_cases hw : w = v
      · subst hw; exact hyU w (by simp)
      · rw [hy2, hy1 w hw, Units.val_one, map_one]
    have hyinf : ((y : AdeleRing (𝓞 K) K).1) = 1 := congrArg Units.val hyT.1

    set 𝔤 : Ideal (𝓞 K) := v.asIdeal ^ 1 * 𝔪' with h𝔤
    have h𝔤0 : 𝔤 ≠ ⊥ := mul_ne_zero (pow_ne_zero _ v.ne_bot) h𝔪'0
    have hcnt𝔤 : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ v → T1bBody.cnt 𝔤 u = T1bBody.cnt 𝔪' u := fun u hu => by
      rw [h𝔤, T1bBody.cnt_mul (pow_ne_zero _ v.ne_bot) h𝔪'0, T1bBody.cnt_pow_of_ne hu, zero_add]
    have hcnt𝔤v : T1bBody.cnt 𝔤 v = 1 := by
      rw [h𝔤, T1bBody.cnt_mul (pow_ne_zero _ v.ne_bot) h𝔪'0, T1bBody.cnt_pow_self, T1bBody.cnt_eq_zero_of_not_dvd h𝔪'0 hv]
    have LG1 := ArtinL.Abelian.apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one K L ψ v 𝔪' hv 1
      (hN_of 1 le_rfl (by omega)) 𝔣 hadm r hr₁ hr₂ hr₃ hr₄

    set S : Finset (HeightOneSpectrum (𝓞 K)) := insert v (Ideal.finite_factors h𝔪'0).toFinset with hS
    have hvS : v ∈ S := Finset.mem_insert_self _ _
    have hS𝔪' : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔪' → w ∈ S := fun w hw =>
      Finset.mem_insert_of_mem ((Ideal.finite_factors h𝔪'0).mem_toFinset.2 hw)
    have hSdvd : ∀ w ∈ S, w.asIdeal ∣ v.asIdeal * 𝔪' := by
      intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact dvd_mul_right _ _
      · exact Dvd.dvd.mul_left ((Ideal.finite_factors h𝔪'0).mem_toFinset.1 hw) _
    set M : ℕ := 1 + S.sup (fun w => T1bBody.cnt 𝔪' w) with hM
    have hM1 : 1 ≤ M := Nat.le_add_right _ _
    have hM𝔪' : ∀ w ∈ S, T1bBody.cnt 𝔪' w ≤ M := fun w hw =>
      (Finset.le_sup (f := fun w => T1bBody.cnt 𝔪' w) hw).trans (Nat.le_add_left _ _)
    have hexpM : ∀ n : ℕ, n ≤ M → WithZero.exp (-(M : ℤ)) ≤ WithZero.exp (-(n : ℤ)) := fun n hn =>
      WithZero.exp_le_exp.2 (by omega)
    have hexpM1 : WithZero.exp (-(M : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

    obtain ⟨𝔥, h𝔥0, h𝔥w⟩ : ∃ 𝔥 : Ideal (𝓞 K), 𝔥 ≠ ⊥ ∧
        ∀ w ∈ S, ∀ z : 𝓞 K, z ∈ 𝔥 → w.intValuation z ≤ WithZero.exp (-(M : ℤ)) := by
      refine ⟨(v.asIdeal * 𝔪') ^ M, pow_ne_zero _ (mul_ne_zero v.ne_bot h𝔪'0), fun w hw z hz => ?_⟩
      have h1 : w.asIdeal ^ M ∣ (v.asIdeal * 𝔪') ^ M := pow_dvd_pow_of_dvd (hSdvd w hw) M
      have h2 : (v.asIdeal * 𝔪') ^ M ∣ Ideal.span {z} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hz)
      exact (HeightOneSpectrum.intValuation_le_pow_iff_dvd w z M).2 (h1.trans h2)
    obtain ⟨π, hπ𝔥, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔥0
    have hπK : (π : K) ≠ 0 := fun h => hπ0 (by exact_mod_cast h)

    obtain ⟨x₀, hx₀⟩ := IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers K
      ((((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) * algebraMap K (FiniteAdeleRing (𝓞 K) K) (π : K)⁻¹)
    have ht_close : ∀ w : HeightOneSpectrum (𝓞 K),
        Valued.v ((((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (π * x₀)) ≤
          w.valuation K (π : K) := by
      intro w
      have h1 := hx₀ w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, fad_mul_apply] at h1
      have hπw : (algebraMap K (FiniteAdeleRing (𝓞 K) K) (π : K)⁻¹) w = (algebraMap K (w.adicCompletion K) (π : K))⁻¹ := by
        rw [ArtinL.T1lg.algebraMap_fad_apply, map_inv₀]
      rw [hπw] at h1
      have hπw0 : algebraMap K (w.adicCompletion K) (π : K) ≠ 0 := by
        rw [ne_eq, map_eq_zero]; exact hπK
      have : (((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (π * x₀) =
          algebraMap K (w.adicCompletion K) (π : K) *
            ((((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w * (algebraMap K (w.adicCompletion K) (π : K))⁻¹ -
              algebraMap K (w.adicCompletion K) x₀) := by
        rw [mul_sub, mul_left_comm, mul_inv_cancel₀ hπw0, mul_one, map_mul]
      rw [this, map_mul, ArtinL.T1lg.v_algebraMap]
      exact mul_le_of_le_one_right' h1

    have ht_int : ∀ w : HeightOneSpectrum (𝓞 K), w.valuation K ((π : K) * x₀) ≤ 1 := by
      intro w
      have h1 := ht_close w
      have hπ1 : w.valuation K (π : K) ≤ 1 := by rw [HeightOneSpectrum.valuation_of_algebraMap]; exact w.intValuation_le_one π
      rw [← ArtinL.T1lg.v_algebraMap K w]
      have := Valuation.map_sub Valued.v ((((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w)
        (((((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w) - algebraMap K (w.adicCompletion K) ((π : K) * x₀))
      rw [sub_sub_cancel, hyunit w] at this
      exact this.trans (max_le le_rfl (h1.trans hπ1))
    obtain ⟨t, ht⟩ : ∃ t : 𝓞 K, (t : K) = (π : K) * x₀ := by
      obtain ⟨t, ht⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((π : K) * x₀) ht_int
      exact ⟨t, ht⟩

    obtain ⟨δ, hδ0, hδ1, hδsign⟩ := NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff K 𝔥 h𝔥0
      {φ : K →+* ℝ | φ (t : K) < 0}
    set α : 𝓞 K := t * δ with hαdef
    have htK : (t : K) = (π : K) * x₀ := ht
    have hαK' : (α : K) = (t : K) * (δ : K) := by rw [hαdef]; push_cast; rfl

    have hvt : ∀ w ∈ S, Valued.v (algebraMap K (w.adicCompletion K) (t : K)) = 1 := by
      intro w hw
      have h1 : Valued.v ((((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (t : K)) < 1 := by
        rw [htK]
        refine (ht_close w).trans_lt ?_
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact (h𝔥w w hw π hπ𝔥).trans_lt hexpM1
      rw [← hyunit w]
      refine Valuation.map_eq_of_sub_lt Valued.v ?_
      rw [Valuation.map_sub_swap, hyunit w]
      exact h1
    have ht0 : t ≠ 0 := by
      intro h
      have := hvt v hvS
      rw [h, show ((0 : 𝓞 K) : K) = 0 from rfl, map_zero, map_zero] at this
      exact zero_ne_one this
    have hvδ1 : ∀ w ∈ S, Valued.v (algebraMap K (w.adicCompletion K) (δ : K) - 1) ≤ WithZero.exp (-(M : ℤ)) := by
      intro w hw
      have : algebraMap K (w.adicCompletion K) (δ : K) - 1 = algebraMap K (w.adicCompletion K) (((δ - 1 : 𝓞 K)) : K) := by
        rw [show (((δ - 1 : 𝓞 K)) : K) = (δ : K) - 1 by push_cast; rfl, map_sub, map_one]
      rw [this, ArtinL.T1lg.v_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      exact h𝔥w w hw _ hδ1
    have hα_close : ∀ w ∈ S,
        Valued.v ((((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (α : K)) ≤
          WithZero.exp (-(M : ℤ)) := by
      intro w hw
      have h1 : Valued.v ((((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (t : K)) ≤
          WithZero.exp (-(M : ℤ)) := by
        rw [htK]
        refine (ht_close w).trans ?_
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact h𝔥w w hw π hπ𝔥
      have h2 : Valued.v (algebraMap K (w.adicCompletion K) (t : K) - algebraMap K (w.adicCompletion K) (α : K)) ≤ WithZero.exp (-(M : ℤ)) := by
        have : algebraMap K (w.adicCompletion K) (t : K) - algebraMap K (w.adicCompletion K) (α : K) =
            algebraMap K (w.adicCompletion K) (t : K) * -(algebraMap K (w.adicCompletion K) (δ : K) - 1) := by
          rw [hαK', map_mul]; ring
        rw [this, map_mul, Valuation.map_neg, hvt w hw, one_mul]
        exact hvδ1 w hw
      have := Valuation.map_add Valued.v
        ((((y : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) w - algebraMap K (w.adicCompletion K) (t : K))
        (algebraMap K (w.adicCompletion K) (t : K) - algebraMap K (w.adicCompletion K) (α : K))
      rw [sub_add_sub_cancel] at this
      exact this.trans (max_le h1 h2)
    have hvα : ∀ w ∈ S, Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 := by
      intro w hw
      rw [← hyunit w]
      refine Valuation.map_eq_of_sub_lt Valued.v ?_
      rw [Valuation.map_sub_swap, hyunit w]
      exact (hα_close w hw).trans_lt hexpM1
    have hα0 : α ≠ 0 := mul_ne_zero ht0 hδ0
    have hαK : (α : K) ≠ 0 := fun h => hα0 (by exact_mod_cast h)

    have hpos : ∀ τ : K →+* ℝ, 0 < τ (α : K) := by
      intro τ
      have htτ : τ (t : K) ≠ 0 := by
        rw [ne_eq, map_eq_zero_iff τ τ.injective]; exact_mod_cast ht0
      have hδτ : τ (δ : K) ≠ 0 := by
        rw [ne_eq, map_eq_zero_iff τ τ.injective]; exact_mod_cast hδ0
      have hmul : τ (α : K) = τ (t : K) * τ (δ : K) := by rw [hαK', map_mul]
      rw [hmul]
      rcases lt_or_gt_of_ne htτ with h | h
      · exact mul_pos_of_neg_of_neg h ((hδsign τ).2 h)
      · have : ¬ τ (δ : K) < 0 := fun h' => (lt_irrefl _ (((hδsign τ).1 h').trans h))
        exact mul_pos h (lt_of_le_of_ne (not_lt.1 this) (Ne.symm hδτ))

    have hvalα : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v (algebraMap K (w.adicCompletion K) (α : K)) =
        WithZero.exp (-(T1bBody.cnt (Ideal.span {α}) w : ℤ)) := fun w => T1bBody.valued_algebraMap_eq α hα0 w
    have hcntS : ∀ w ∈ S, T1bBody.cnt (Ideal.span {α}) w = 0 := by
      intro w hw
      have := (hvα w hw)
      rw [hvalα] at this
      have := WithZero.exp_injective (this.trans WithZero.exp_zero.symm)
      omega
    have hα1 : α - 1 ∈ 𝔪' := by
      refine (HeckeCharacter.mem_iff_forall_valued_algebraMap_finiteAdeleRing_le K 𝔪' h𝔪'0 (α - 1)).2 fun w hw => ?_
      have hwS : w ∈ S := hS𝔪' w hw
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have e : (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((α - 1 : 𝓞 K) : K)) w = algebraMap K (w.adicCompletion K) (α : K) - 1 := by
        rw [show ((α - 1 : 𝓞 K) : K) = (α : K) - 1 from rfl, map_sub, map_one]
        rfl
      rw [e]
      have h := hα_close w hwS
      rw [hy2, hy1 w hwv, Units.val_one, Valuation.map_sub_swap] at h
      exact h.trans (hexpM _ (hM𝔪' w hwS))
    have hcα : principalUnit K α hα0 ∈ coprimeToModulus K (v.asIdeal * 𝔪') := by
      rw [mem_coprimeToModulus_iff]
      intro w hw
      have hwS : w ∈ S := by
        rcases w.prime.dvd_or_dvd hw with h | h
        · have : w = v := HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.dvd_iff_le.1 h)).symm
          exact this ▸ hvS
        · exact hS𝔪' w h
      rw [principalUnit_val, FractionalIdeal.count_coe K w (show (Ideal.span {α} : Ideal (𝓞 K)) ≠ 0 from
        fun h => hα0 (Ideal.span_singleton_eq_bot.1 h)), show (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {α})).factors =
        T1bBody.cnt (Ideal.span {α}) w from rfl, hcntS w hwS, Nat.cast_zero]
    have hα𝔪' : α - 1 ∈ 𝔪' := hα1

    set aU : ∀ u : HeightOneSpectrum (𝓞 K), (u.adicCompletion K)ˣ := fun u =>
      Units.map (algebraMap K (u.adicCompletion K) : K →* u.adicCompletion K) (Units.mk0 (α : K) hαK) with haU
    set x : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ := fun u => T1bBody.iotaW K u (aU u) with hxdef
    have hx : ∀ u, x u ∈ idelesTrivialOn (𝓞 K) K ({u}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := fun u =>
      T1bBody.iotaW_mem_idelesTrivialOn K u (aU u)
    have hxfin : ∀ u, finPart u (x u) = aU u := fun u => T1bBody.finPart_iotaW_same K u (aU u)
    have hxu : ∀ u, ((finPart u (x u) : (u.adicCompletion K)ˣ) : u.adicCompletion K) = algebraMap K (u.adicCompletion K) α := fun u => by
      rw [hxfin]; rfl
    have hxne : ∀ u w, w ≠ u → finPart w (x u) = 1 := fun u w h => T1bBody.finPart_iotaW_of_ne K u w h (aU u)
    have hxinf : ∀ u, infPart (x u) = 1 := fun u => T1bBody.infPart_iotaW K u (aU u)

    have hx2 : ∀ u w, ((((x u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) =
        ((finPart w (x u) : (w.adicCompletion K)ˣ) : w.adicCompletion K) := fun u w => rfl
    obtain ⟨hsuppfin, hprod⟩ := M4aHerbrand.finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      (α : K) hpos x hx hxu

    have hsym : artinSymbol K L (v.asIdeal * 𝔪') ⟨principalUnit K α hα0, hcα⟩ =
        ∏ᶠ w : HeightOneSpectrum (𝓞 K), artinFrob K L w ^ (T1bBody.cnt (Ideal.span {α}) w : ℤ) := by
      unfold artinSymbol
      rw [raySymbolHom_apply]
      change raySymbol K (artinFrob K L)
        ((principalUnit K α hα0 : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
      rw [principalUnit_val]
      unfold raySymbol
      refine finprod_congr fun w => ?_
      rw [FractionalIdeal.count_coe K w (show (Ideal.span {α} : Ideal (𝓞 K)) ≠ 0 from
        fun h => hα0 (Ideal.span_singleton_eq_bot.1 h))]
      rfl

    have hord : ∀ u, placeOrd K (projFin K (x u)) u = (T1bBody.cnt (Ideal.span {α}) u : ℤ) := fun u => by
      unfold placeOrd
      change -WithZero.log (Valued.v ((((x u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) u)) = _
      rw [hx2, hxu, hvalα, WithZero.log_exp, neg_neg]
    have hdec : ∀ u, ∃ i ∈ (LanglandsTunnell.P2.Artin.primeAbove K L u).inertia (L ≃ₐ[K] L),
        r (x u) = i * artinFrob K L u ^ (T1bBody.cnt (Ideal.span {α}) u : ℤ) := fun u => by
      have h := M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ u (aU u)
        (x u) (hx u) (hxfin u) (wL u) (hwLu u) (artinFrob K L u) (LanglandsTunnell.P2.Artin.isArithFrobAt_artinFrob K L u)
      rw [hord] at h
      exact ⟨_, h, by rw [inv_mul_cancel_right]⟩

    have hunit_kill : ∀ u : HeightOneSpectrum (𝓞 K), ¬ u.asIdeal ∣ 𝔤 →
        ∀ i ∈ (LanglandsTunnell.P2.Artin.primeAbove K L u).inertia (L ≃ₐ[K] L), ψ i = 1 := by
      intro u hu i hi
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1
        (M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ u (wL u) (hwLu u) hi)
      have hyT' : y' ∈ idelesTrivialOn (𝓞 K) K ({u}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := unitIdelesTrivialOn_le_idelesTrivialOn _ _ _ hy'
      have hyU' := (NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one K _ y').1 hy'.1
      have hy1' : ∀ w, w ≠ u → finPart w y' = 1 := fun w hw => hyT'.2 w (by simpa using hw)
      have hyunit' : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((y' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
        intro w
        by_cases hw : w = u
        · subst hw; exact hyU' w (by simp)
        · change Valued.v ((finPart w y' : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1
          rw [hy1' w hw, Units.val_one, map_one]
      refine LG1 y' ⟨fun w hw => ?_, fun τ => ?_⟩ hyT'.1 hyunit'
      · have hwu : w ≠ u := fun h => hu (h ▸ hw)
        rw [map_one, inv_one, mul_one]
        change Valued.v ((finPart w y' : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1 ∧
          Valued.v (((finPart w y' : (w.adicCompletion K)ˣ) : w.adicCompletion K) - 1) ≤ _
        rw [hy1' w hwu, Units.val_one, map_one, sub_self, map_zero]
        exact ⟨rfl, zero_le'⟩
      · rw [map_one, inv_one, mul_one]
        exact archSign_of_fst_eq_one K τ (congrArg Units.val hyT'.1)

    have hadj_of : ∀ (u : HeightOneSpectrum (𝓞 K)) (𝔞 : Ideal (𝓞 K)),
        (u.asIdeal ∣ 𝔞 → Valued.v (algebraMap K (u.adicCompletion K) (α : K)) = 1 ∧
          Valued.v (algebraMap K (u.adicCompletion K) (α : K) - 1) ≤ WithZero.exp (-(T1bBody.cnt 𝔞 u : ℤ))) →
        IsAdjuster K 𝔞 (x u) 1 := by
      intro u 𝔞 hu
      refine ⟨fun w hw => ?_, fun τ => ?_⟩
      · rw [map_one, inv_one, mul_one, hx2]
        by_cases hwu : w = u
        · subst hwu
          rw [hxu]
          exact hu hw
        · rw [hxne u w hwu, Units.val_one, map_one, sub_self, map_zero]
          exact ⟨rfl, zero_le'⟩
      · rw [map_one, inv_one, mul_one]
        exact archSign_of_fst_eq_one K τ (congrArg Units.val (hxinf u))

    have hunits_of : ∀ u : HeightOneSpectrum (𝓞 K), Valued.v (algebraMap K (u.adicCompletion K) (α : K)) = 1 →
        ∀ w : HeightOneSpectrum (𝓞 K), Valued.v ((((x u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
      intro u hu w
      rw [hx2]
      by_cases hwu : w = u
      · subst hwu; rwa [hxu]
      · rw [hxne u w hwu, Units.val_one, map_one]

    have hmain' : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ v → ψ (r (x u)) = ψ (artinFrob K L u) ^ (T1bBody.cnt (Ideal.span {α}) u : ℤ) := by
      intro u huv
      by_cases hu𝔤 : u.asIdeal ∣ 𝔤
      ·
        have hu𝔪' : u.asIdeal ∣ 𝔪' := by
          rcases (u.prime.dvd_or_dvd hu𝔤) with h | h
          · exact absurd (HeightOneSpectrum.ext (v.isMaximal.eq_of_le u.isPrime.ne_top (Ideal.dvd_iff_le.1 (u.prime.dvd_of_dvd_pow h))).symm) huv
          · exact h
        have hcpos : 1 ≤ T1bBody.cnt 𝔪' u := Nat.one_le_iff_ne_zero.2 fun h0 =>
          ((Associates.count_ne_zero_iff_dvd h𝔪'0 u.irreducible).2 hu𝔪') h0
        have hval1 : Valued.v (algebraMap K (u.adicCompletion K) (α : K) - 1) ≤ WithZero.exp (-(T1bBody.cnt 𝔪' u : ℤ)) :=
          T1bBody.valued_sub_one_le_of_mem h𝔪'0 hα𝔪' u hu𝔪'
        obtain ⟨hone, hcnt0⟩ := T1bBody.cnt_eq_zero_of_valued_sub_one_le α hα0 u hcpos hval1
        have hadj : IsAdjuster K 𝔤 (x u) 1 := hadj_of u 𝔤 (fun _ => ⟨hone, by rwa [hcnt𝔤 u huv]⟩)
        rw [hcnt0, Int.ofNat_zero, zpow_zero]
        exact LG1 (x u) hadj (hxinf u) (hunits_of u hone)
      ·
        obtain ⟨i, hi, hri⟩ := hdec u
        rw [hri, map_mul, hunit_kill u hu𝔤 i hi, one_mul, map_zpow]

    have hxv : ψ (r (x v)) = ψ σ := by
      have hyv0 : ((finPart v y : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 := (finPart v y).ne_zero
      have hvy : Valued.v ((finPart v y : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by rw [← hy2]; exact hyunit v
      set z : (AdeleRing (𝓞 K) K)ˣ := x v * y⁻¹ with hz
      have hz2 : ∀ w, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) =
          ((finPart w (x v) : (w.adicCompletion K)ˣ) : w.adicCompletion K) * (((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K))⁻¹ := by
        intro w
        change ((finPart w z : (w.adicCompletion K)ˣ) : w.adicCompletion K) = _
        rw [hz, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      have hzunit : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
        intro w
        rw [hz2, map_mul, map_inv₀, ← hy2, hyunit w, inv_one, mul_one, ← hx2]
        exact hunits_of v (hvα v hvS) w
      have hzadj : IsAdjuster K 𝔤 z 1 := by
        refine ⟨fun w hw => ?_, fun τ => ?_⟩
        · rw [map_one, inv_one, mul_one]
          refine ⟨hzunit w, ?_⟩
          rw [hz2]
          by_cases hwv : w = v
          · subst hwv
            rw [show (Associates.mk w.asIdeal).count (Associates.mk 𝔤).factors = T1bBody.cnt 𝔤 w from rfl, hxu, hcnt𝔤v, Nat.cast_one]

            have e : algebraMap K (w.adicCompletion K) (α : K) * (((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K))⁻¹ - 1 =
                (algebraMap K (w.adicCompletion K) (α : K) - ((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K)) *
                  (((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K))⁻¹ := by
              rw [sub_mul, mul_inv_cancel₀ hyv0]
            rw [e, map_mul, map_inv₀, hvy, inv_one, mul_one, Valuation.map_sub_swap, ← hy2]
            exact (hα_close w hvS).trans (hexpM 1 hM1)
          · have hw𝔪' : w.asIdeal ∣ 𝔪' := by
              rcases (w.prime.dvd_or_dvd hw) with h | h
              · exact absurd (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.dvd_iff_le.1 (w.prime.dvd_of_dvd_pow h))).symm) hwv
              · exact h
            rw [hxne v w hwv, hy1 w hwv, Units.val_one, inv_one, mul_one, sub_self, map_zero]
            exact zero_le'
        · rw [map_one, inv_one, mul_one, hz, archSign_mul]
          exact iff_of_true (archSign_of_fst_eq_one K τ (congrArg Units.val (hxinf v))) ((archSign_inv K τ y).2 (archSign_of_fst_eq_one K τ hyinf))
      have hzinf : infPart z = 1 := by rw [hz, map_mul, map_inv, hxinf v, hyT.1, inv_one, mul_one]
      have hkillz := LG1 z hzadj hzinf hzunit
      rw [hz, map_mul, map_inv, map_mul, map_inv, hry, mul_inv_eq_one] at hkillz
      exact hkillz

    have hcntv : T1bBody.cnt (Ideal.span {α}) v = 0 := hcntS v hvS
    have hfinFrob : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 K) =>
        ψ (artinFrob K L w) ^ (T1bBody.cnt (Ideal.span {α}) w : ℤ)).Finite := by
      refine (Ideal.finite_factors (I := Ideal.span {α}) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hα0)).subset
        fun w hw => ?_
      rw [Function.mem_mulSupport] at hw
      by_contra hwd
      exact hw (by rw [T1bBody.cnt_eq_zero_of_not_dvd (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hα0) hwd, Int.ofNat_zero, zpow_zero])
    have hfinFrob' : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 K) =>
        artinFrob K L w ^ (T1bBody.cnt (Ideal.span {α}) w : ℤ)).Finite := by
      refine (Ideal.finite_factors (I := Ideal.span {α}) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hα0)).subset
        fun w hw => ?_
      rw [Function.mem_mulSupport] at hw
      by_contra hwd
      exact hw (by rw [T1bBody.cnt_eq_zero_of_not_dvd (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hα0) hwd, Int.ofNat_zero, zpow_zero])

    set g : HeightOneSpectrum (𝓞 K) → ℂˣ := fun u => if u = v then ψ σ else 1 with hg
    have hsplit : ∀ u, ψ (r (x u)) = g u * ψ (artinFrob K L u) ^ (T1bBody.cnt (Ideal.span {α}) u : ℤ) := by
      intro u
      by_cases huv : u = v
      · rw [huv, hxv, hcntv, Int.ofNat_zero, zpow_zero, mul_one]; simp [hg]
      · rw [hmain' u huv]; simp [hg, huv]
    have hgsupp : (Function.mulSupport g) ⊆ {v} := by
      intro u hu
      rw [Function.mem_mulSupport] at hu
      by_contra huv
      rw [Set.mem_singleton_iff] at huv
      exact hu (by simp [hg, huv])
    have hprodψ : ∏ᶠ u, ψ (r (x u)) = ψ σ * ∏ᶠ u, ψ (artinFrob K L u) ^ (T1bBody.cnt (Ideal.span {α}) u : ℤ) := by
      rw [show (fun u => ψ (r (x u))) = fun u => g u * ψ (artinFrob K L u) ^ (T1bBody.cnt (Ideal.span {α}) u : ℤ) from funext hsplit,
        finprod_mul_distrib ((Set.finite_singleton v).subset hgsupp) hfinFrob, finprod_eq_single g v (fun u hu => by simp [hg, hu]),
        show g v = ψ σ by simp [hg]]
    have hψart : ψ (artinSymbol K L (v.asIdeal * 𝔪') ⟨principalUnit K α hα0, hcα⟩) = (ψ σ)⁻¹ := by
      rw [hsym, MonoidHom.map_finprod ψ hfinFrob']
      have h1 : ψ (∏ᶠ u, r (x u)) = 1 := by rw [hprod, map_one]
      rw [MonoidHom.map_finprod ψ hsuppfin, hprodψ] at h1
      rw [show (fun w => ψ (artinFrob K L w ^ (T1bBody.cnt (Ideal.span {α}) w : ℤ))) =
        fun w => ψ (artinFrob K L w) ^ (T1bBody.cnt (Ideal.span {α}) w : ℤ) from funext fun w => map_zpow ψ _ _]
      exact eq_inv_of_mul_eq_one_right h1
    have hone := hcon α hα0 hcα hpos (by rw [hf1, Nat.sub_self, pow_zero, one_mul]; exact hα1)
    rw [hψart, inv_eq_one] at hone
    exact hψσ hone
  ·
    set k := ⌈ArtinL.Abelian.swanConductor ψ v⌉₊ with hk
    have hHA : (k : ℚ) = ArtinL.Abelian.swanConductor ψ v := ArtinL.Abelian.natCeil_swanConductor_eq K L ψ v hram
    have hnot := (ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt K L ψ v hram (k : ℚ) (Nat.cast_nonneg k)).not.2
      (by rw [← hHA]; exact lt_irrefl _)
    push Not at hnot
    obtain ⟨σ, hσ, hψσ⟩ := hnot
    obtain ⟨y, hyT, hyadj, hry⟩ := M4aHerbrand.exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      v (wL v) (hwLu v) k hkpos (σ : L ≃ₐ[K] L) (Subgroup.mem_map_of_mem _ hσ)

    have hy1 : ∀ w, w ≠ v → finPart w y = 1 := fun w hw => hyT.2 w (by simpa using hw)
    have hyv := hyadj.cong v (dvd_pow_self _ (by omega))
    rw [map_one, inv_one, mul_one] at hyv
    have hyunit : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
      intro w
      by_cases hw : w = v
      · subst hw; exact hyv.1
      · change Valued.v ((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1
        rw [hy1 w hw, Units.val_one, map_one]
    have hyadj' : IsAdjuster K (v.asIdeal ^ k * 𝔪') y 1 := by
      refine ⟨fun w hw => ?_, hyadj.sign⟩
      rw [map_one, inv_one, mul_one]
      by_cases hwv : w = v
      · subst hwv
        refine ⟨hyv.1, hyv.2.trans_eq ?_⟩
        rw [show (Associates.mk w.asIdeal).count (Associates.mk (w.asIdeal ^ k)).factors = T1bBody.cnt (w.asIdeal ^ k) w from rfl,
          show (Associates.mk w.asIdeal).count (Associates.mk (w.asIdeal ^ k * 𝔪')).factors = T1bBody.cnt (w.asIdeal ^ k * 𝔪') w from rfl,
          T1bBody.cnt_mul (pow_ne_zero _ w.ne_bot) h𝔪'0, T1bBody.cnt_pow_self, T1bBody.cnt_eq_zero_of_not_dvd h𝔪'0 hv, add_zero]
      · change Valued.v ((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1 ∧
          Valued.v (((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K) - 1) ≤ _
        rw [hy1 w hwv, Units.val_one, map_one, sub_self, map_zero]
        exact ⟨rfl, zero_le'⟩
    have hkill := ArtinL.Abelian.apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one K L ψ v 𝔪' hv k
      (hN_of k hkpos (by rw [hfswan]; omega)) 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ y hyadj' hyT.1 hyunit
    rw [hry] at hkill
    exact hψσ hkill

end S_ArtinL_Abelian_exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0
end P2MW
export P2MW.S_ArtinL_Abelian_exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0 (solution)
