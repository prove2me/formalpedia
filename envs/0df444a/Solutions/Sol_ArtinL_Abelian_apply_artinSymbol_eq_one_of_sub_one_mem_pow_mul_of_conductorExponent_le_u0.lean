-- Prove2me | solution 1 for ArtinL.Abelian.apply_artinSymbol_eq_one_of_sub_one_mem_pow_mul_of_conductorExponent_le_u0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/350f7465-2025-57a3-89e3-2ca894b28799

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_M4aHerbrand_finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
import Theorems.Thm_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_M4aHerbrand_inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap
import Theorems.Thm_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
import Theorems.Thm_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Theorems.Thm_M4aHerbrand_idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow
import Theorems.Thm_ArtinL_Abelian_apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_pow_mul_of_conductorExponent_le_u0
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin
open M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
open scoped IsMulCommutative RestrictedProduct

namespace T1aBody

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

end T1aBody

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (𝔪' : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔪')
    (N : ℕ)
    (hN : ∀ (β : 𝓞 K) (hβ : β ≠ 0) (𝔪 : Ideal (𝓞 K)) (hc : principalUnit K β hβ ∈ coprimeToModulus K 𝔪),
      (∀ τ : K →+* ℝ, 0 < τ (β : K)) → β - 1 ∈ v.asIdeal ^ N * 𝔪' →
        ψ (artinSymbol K L 𝔪 ⟨principalUnit K β hβ, hc⟩) = 1)
    (n : ℕ) (hn : ArtinL.Abelian.conductorExponent ψ v ≤ n)
    (𝔪 : Ideal (𝓞 K)) (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔪)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (α : K)) (h1 : α - 1 ∈ v.asIdeal ^ n * 𝔪') :
    ψ (artinSymbol K L 𝔪 ⟨principalUnit K α hα, hc⟩) = 1 := by
  classical

  obtain ⟨𝔯, h𝔯0, h𝔯⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd K L
  obtain ⟨𝔣, -, -, hadm⟩ := LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd K L 𝔯 h𝔯0 h𝔯
    (Module.finrank K L)
  obtain ⟨r, hr₁, hr₂, hr₃, hr₄⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank K L 𝔣 hadm

  set 𝔤 : Ideal (𝓞 K) := v.asIdeal ^ N * 𝔪' with h𝔤
  have h𝔪'0 : 𝔪' ≠ ⊥ := fun h => hv (h ▸ dvd_zero _)
  have h𝔤0 : 𝔤 ≠ ⊥ := mul_ne_zero (pow_ne_zero _ v.ne_bot) h𝔪'0
  have hcnt𝔤 : ∀ u : HeightOneSpectrum (𝓞 K), u ≠ v → T1aBody.cnt 𝔤 u = T1aBody.cnt 𝔪' u := fun u hu => by
    rw [h𝔤, T1aBody.cnt_mul (pow_ne_zero _ v.ne_bot) h𝔪'0, T1aBody.cnt_pow_of_ne hu, zero_add]
  have hαK : (α : K) ≠ 0 := fun h => hα (by exact_mod_cast h)
  have hα𝔪' : α - 1 ∈ 𝔪' := Ideal.mul_le_right h1
  have hαvn : α - 1 ∈ v.asIdeal ^ n := Ideal.mul_le_left h1

  set aU : ∀ u : HeightOneSpectrum (𝓞 K), (u.adicCompletion K)ˣ := fun u =>
    Units.map (algebraMap K (u.adicCompletion K) : K →* u.adicCompletion K) (Units.mk0 (α : K) hαK) with haU
  set x : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ := fun u => T1aBody.iotaW K u (aU u) with hxdef
  have hx : ∀ u, x u ∈ idelesTrivialOn (𝓞 K) K ({u}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := fun u =>
    T1aBody.iotaW_mem_idelesTrivialOn K u (aU u)
  have hxfin : ∀ u, finPart u (x u) = aU u := fun u => T1aBody.finPart_iotaW_same K u (aU u)
  have hxu : ∀ u, ((finPart u (x u) : (u.adicCompletion K)ˣ) : u.adicCompletion K) = algebraMap K (u.adicCompletion K) α := fun u => by
    rw [hxfin]; rfl
  have hxne : ∀ u w, w ≠ u → finPart w (x u) = 1 := fun u w h => T1aBody.finPart_iotaW_of_ne K u w h (aU u)
  have hxinf : ∀ u, infPart (x u) = 1 := fun u => T1aBody.infPart_iotaW K u (aU u)

  have hx2 : ∀ u w, ((((x u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) =
      ((finPart w (x u) : (w.adicCompletion K)ˣ) : w.adicCompletion K) := fun u w => rfl
  have hvalα : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v (algebraMap K (w.adicCompletion K) (α : K)) =
      WithZero.exp (-(T1aBody.cnt (Ideal.span {α}) w : ℤ)) := fun w => T1aBody.valued_algebraMap_eq α hα w
  obtain ⟨hsuppfin, hprod⟩ := M4aHerbrand.finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
    (α : K) hpos x hx hxu

  have hsym : artinSymbol K L 𝔪 ⟨principalUnit K α hα, hc⟩ =
      ∏ᶠ w : HeightOneSpectrum (𝓞 K), artinFrob K L w ^ (T1aBody.cnt (Ideal.span {α}) w : ℤ) := by
    unfold artinSymbol
    rw [raySymbolHom_apply]
    change raySymbol K (artinFrob K L)
      ((principalUnit K α hα : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
    rw [principalUnit_val]
    unfold raySymbol
    refine finprod_congr fun w => ?_
    rw [FractionalIdeal.count_coe K w (show (Ideal.span {α} : Ideal (𝓞 K)) ≠ 0 from
      fun h => hα (Ideal.span_singleton_eq_bot.1 h))]
    rfl

  set wL : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L) := fun u =>
    ⟨LanglandsTunnell.P2.Artin.primeAbove K L u, inferInstance, LanglandsTunnell.P2.Artin.primeAbove_ne_bot K L u⟩ with hwL
  have hwLu : ∀ u, (wL u).under (𝓞 K) = u := fun u => HeightOneSpectrum.ext (LanglandsTunnell.P2.Artin.under_primeAbove K L u)
  have hord : ∀ u, placeOrd K (projFin K (x u)) u = (T1aBody.cnt (Ideal.span {α}) u : ℤ) := fun u => by
    unfold placeOrd
    change -WithZero.log (Valued.v ((((x u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) u)) = _
    rw [hx2, hxu, hvalα, WithZero.log_exp, neg_neg]
  have hdec : ∀ u, ∃ i ∈ (LanglandsTunnell.P2.Artin.primeAbove K L u).inertia (L ≃ₐ[K] L),
      r (x u) = i * artinFrob K L u ^ (T1aBody.cnt (Ideal.span {α}) u : ℤ) := fun u => by
    have h := M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ u (aU u)
      (x u) (hx u) (hxfin u) (wL u) (hwLu u) (artinFrob K L u) (LanglandsTunnell.P2.Artin.isArithFrobAt_artinFrob K L u)
    rw [hord] at h
    exact ⟨_, h, by rw [inv_mul_cancel_right]⟩

  have hunit_kill : ∀ u : HeightOneSpectrum (𝓞 K), ¬ u.asIdeal ∣ 𝔤 →
      ∀ i ∈ (LanglandsTunnell.P2.Artin.primeAbove K L u).inertia (L ≃ₐ[K] L), ψ i = 1 := by
    intro u hu i hi
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1
      (M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ u (wL u) (hwLu u) hi)
    have hyT : y ∈ idelesTrivialOn (𝓞 K) K ({u}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := unitIdelesTrivialOn_le_idelesTrivialOn _ _ _ hy
    have hyU := (NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one K _ y).1 hy.1
    have hy1 : ∀ w, w ≠ u → finPart w y = 1 := fun w hw => hyT.2 w (by simpa using hw)
    have hyunit : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
      intro w
      by_cases hw : w = u
      · subst hw; exact hyU w (by simp)
      · change Valued.v ((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1
        rw [hy1 w hw, Units.val_one, map_one]
    refine ArtinL.Abelian.apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one K L ψ v 𝔪' hv N hN 𝔣 hadm r
      hr₁ hr₂ hr₃ hr₄ y ⟨fun w hw => ?_, fun τ => ?_⟩ hyT.1 hyunit
    · have hwu : w ≠ u := fun h => hu (h ▸ hw)
      rw [map_one, inv_one, mul_one]
      change Valued.v ((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1 ∧
        Valued.v (((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K) - 1) ≤ _
      rw [hy1 w hwu, Units.val_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le'⟩
    · rw [map_one, inv_one, mul_one]
      exact archSign_of_fst_eq_one K τ (congrArg Units.val hyT.1)

  have hadj_of : ∀ (u : HeightOneSpectrum (𝓞 K)) (𝔞 : Ideal (𝓞 K)),
      (u.asIdeal ∣ 𝔞 → Valued.v (algebraMap K (u.adicCompletion K) (α : K)) = 1 ∧
        Valued.v (algebraMap K (u.adicCompletion K) (α : K) - 1) ≤ WithZero.exp (-(T1aBody.cnt 𝔞 u : ℤ))) →
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
  have hmain : ∀ u : HeightOneSpectrum (𝓞 K), ψ (r (x u)) = ψ (artinFrob K L u) ^ (T1aBody.cnt (Ideal.span {α}) u : ℤ) := by
    intro u
    by_cases hu𝔤 : u.asIdeal ∣ 𝔤
    · by_cases huv : u = v
      · subst huv
        rcases Nat.eq_zero_or_pos n with hn0 | hn1
        ·
          subst hn0
          have hunr : ArtinL.Abelian.IsUnramifiedAt ψ u := by
            by_contra hram
            have : 1 ≤ ArtinL.Abelian.conductorExponent ψ u := by
              rw [ArtinL.Abelian.conductorExponent, if_neg hram]; exact Nat.le_add_right _ _
            omega
          obtain ⟨i, hi, hri⟩ := hdec u
          have hψi : ψ i = 1 := hunr i hi
          rw [hri, map_mul, hψi, one_mul, map_zpow]
        ·
          have hval1 : Valued.v (algebraMap K (u.adicCompletion K) (α : K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
            have h := T1aBody.valued_sub_one_le_of_mem (pow_ne_zero _ u.ne_bot) hαvn u (dvd_pow_self _ (by omega))
            rwa [T1aBody.cnt_pow_self] at h
          obtain ⟨hone, hcnt0⟩ := T1aBody.cnt_eq_zero_of_valued_sub_one_le α hα u hn1 hval1
          have hadj : IsAdjuster K (u.asIdeal ^ n) (x u) 1 :=
            hadj_of u (u.asIdeal ^ n) (fun _ => ⟨hone, by rwa [T1aBody.cnt_pow_self]⟩)
          have hmem := M4aHerbrand.idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow K L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ u
            (wL u) (hwLu u) n hn1 (x u) (hx u) hadj
          obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.1 hmem
          rw [← hσeq, hcnt0, Int.ofNat_zero, zpow_zero]
          exact ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le K L ψ u n hn σ hσ
      ·
        have hu𝔪' : u.asIdeal ∣ 𝔪' := by
          rcases (u.prime.dvd_or_dvd hu𝔤) with h | h
          · exact absurd (HeightOneSpectrum.ext (v.isMaximal.eq_of_le u.isPrime.ne_top (Ideal.dvd_iff_le.1 (u.prime.dvd_of_dvd_pow h))).symm) huv
          · exact h
        have hcpos : 1 ≤ T1aBody.cnt 𝔪' u := Nat.one_le_iff_ne_zero.2 fun h0 =>
          ((Associates.count_ne_zero_iff_dvd h𝔪'0 u.irreducible).2 hu𝔪') h0
        have hval1 : Valued.v (algebraMap K (u.adicCompletion K) (α : K) - 1) ≤ WithZero.exp (-(T1aBody.cnt 𝔪' u : ℤ)) :=
          T1aBody.valued_sub_one_le_of_mem h𝔪'0 hα𝔪' u hu𝔪'
        obtain ⟨hone, hcnt0⟩ := T1aBody.cnt_eq_zero_of_valued_sub_one_le α hα u hcpos hval1
        have hadj : IsAdjuster K 𝔤 (x u) 1 := hadj_of u 𝔤 (fun _ => ⟨hone, by rwa [hcnt𝔤 u huv]⟩)
        rw [hcnt0, Int.ofNat_zero, zpow_zero]
        exact ArtinL.Abelian.apply_idelicArtinMap_eq_one_of_isAdjuster_of_forall_valued_eq_one K L ψ v 𝔪' hv N hN 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
          (x u) hadj (hxinf u) (hunits_of u hone)
    ·
      obtain ⟨i, hi, hri⟩ := hdec u
      rw [hri, map_mul, hunit_kill u hu𝔤 i hi, one_mul, map_zpow]

  have hfinFrob : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 K) =>
      artinFrob K L w ^ (T1aBody.cnt (Ideal.span {α}) w : ℤ)).Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {α}) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hα)).subset
      fun w hw => ?_
    rw [Function.mem_mulSupport] at hw
    by_contra hwd
    exact hw (by rw [T1aBody.cnt_eq_zero_of_not_dvd (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hα) hwd, Int.ofNat_zero, zpow_zero])
  rw [hsym, MonoidHom.map_finprod ψ hfinFrob]
  rw [show (fun w : HeightOneSpectrum (𝓞 K) => ψ (artinFrob K L w ^ (T1aBody.cnt (Ideal.span {α}) w : ℤ))) =
      fun w => ψ (r (x w)) from funext fun w => by rw [map_zpow, hmain]]
  rw [← MonoidHom.map_finprod ψ hsuppfin, hprod, map_one]

end S_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_pow_mul_of_conductorExponent_le_u0
end P2MW
export P2MW.S_ArtinL_Abelian_apply_artinSymbol_eq_one_of_sub_one_mem_pow_mul_of_conductorExponent_le_u0 (solution)
