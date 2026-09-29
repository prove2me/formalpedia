-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_place_laurentBaseChange_of_deg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/abf98bcf-d564-55d7-9922-1e24955f502e

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom
import Theorems.Thm_ModularCurve_coeffMap_coeffEmb_of_ringHom
import Theorems.Thm_ModularCurve_order_coeffMap
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries
import Theorems.Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_order_eq_ord
import Theorems.Thm_ModularCurve_order_sum_algebraMap_mul_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply"
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

set_option autoImplicit false

open scoped TensorProduct
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one.AlgebraicCurve ModularCurve P2MW.S_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one.ModularCurve"

noncomputable section

open IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff linearIndependent_coeffEmb baseChangeHom baseChangeHom_one_tmul baseChangeHom_injective baseChangeHom_mem baseChangeEquiv coeffMap_mem_laurentBaseChange_of_ringHom coeffMap_coeffEmb_of_ringHom order_coeffMap order_sum_algebraMap_mul_coeffMap"
p2m_open "ModularCurve"

private theorem algebraMap_mul_eq_smul' {L : Type*} [Field L] (c : L) (y : LaurentSeries L) :
    algebraMap L (LaurentSeries L) c * y = c • y := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]

private theorem coeffMap_algebraMap_of_ringHom {K K' : Type*} [Field K] [Field K']
    (σ : K →+* K') (c : K) :
    coeffMap σ (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (σ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

private theorem linearIndependent_coeffMap_of_ringHom {K K' : Type*} [Field K] [Field K']
    (σ : K →+* K') {ι : Type*} {v : ι → LaurentSeries K} (hv : LinearIndependent K v) :
    LinearIndependent K' (fun i => coeffMap σ (v i)) := by
  classical
  letI : Algebra K K' := σ.toAlgebra
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  let b := Module.Free.chooseBasis K K'
  refine b.forall_coord_eq_zero_iff.mp fun k => ?_
  have hk : ∑ j ∈ s, (b.coord k (g j)) • v j = 0 := by
    ext n
    have hn := congrArg (fun x : LaurentSeries K' => b.coord k (x.coeff n)) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul,
      HahnSeries.coeff_zero, map_zero] at hn
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero]
    rw [← hn, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), show σ ((v j).coeff n) * g j = ((v j).coeff n) • g j from
      (Algebra.smul_def _ _).symm, map_smul, smul_eq_mul, mul_comm]
  exact hv s (fun j => b.coord k (g j)) hk i hi

private def seam₀ (K : Type*) [Field K] [Algebra ℚ K] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    F₀ →+* laurentBaseChange K F₀ :=
  ((coeffEmb K).comp (F₀.val : F₀ →+* LaurentSeries ℚ)).codRestrict (laurentBaseChange K F₀)
    (fun f => coeffEmb_mem_laurentBaseChange K f.2)

private theorem coe_seam₀ (K : Type*) [Field K] [Algebra ℚ K]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (f : F₀) :
    (seam₀ K F₀ f : LaurentSeries K) = coeffEmb K (f : LaurentSeries ℚ) := rfl

private def valRat (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : F₀ →ₗ[ℚ] LaurentSeries ℚ :=
  ((F₀.val : F₀ →+* LaurentSeries ℚ) : F₀ →+ LaurentSeries ℚ).toRatLinearMap

section Core

variable {K K' : Type*} [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'] (σ : K →+* K')
  (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (φ : laurentBaseChange K F₀ →ₐ[K] LaurentSeries K)

private def seamσ : laurentBaseChange K F₀ →+* laurentBaseChange K' F₀ :=
  ((coeffMap σ).comp
      ((laurentBaseChange K F₀).val : laurentBaseChange K F₀ →+* LaurentSeries K)).codRestrict
    (laurentBaseChange K' F₀) (fun x => coeffMap_mem_laurentBaseChange_of_ringHom σ F₀ x.2)

private theorem coe_seamσ (x : laurentBaseChange K F₀) :
    (seamσ σ F₀ x : LaurentSeries K') = coeffMap σ (x : LaurentSeries K) := rfl

private def psi : F₀ →+* LaurentSeries K' :=
  (coeffMap σ).comp ((φ : laurentBaseChange K F₀ →+* LaurentSeries K).comp (seam₀ K F₀))

private def gRat : K' ⊗[ℚ] F₀ →ₐ[ℚ] LaurentSeries K' :=
  Algebra.TensorProduct.productMap (algebraMap K' (LaurentSeries K')).toRatAlgHom
    (psi σ F₀ φ).toRatAlgHom

private theorem gRat_tmul (c : K') (f : F₀) :
    gRat σ F₀ φ (c ⊗ₜ f) =
      algebraMap K' (LaurentSeries K') c * coeffMap σ (φ (seam₀ K F₀ f)) :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ c f

private def gAlg : K' ⊗[ℚ] F₀ →ₐ[K'] LaurentSeries K' :=
  { gRat σ F₀ φ with
    commutes' := fun c => by
      change gRat σ F₀ φ (algebraMap K' (K' ⊗[ℚ] F₀) c) = algebraMap K' (LaurentSeries K') c
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        gRat_tmul, map_one, map_one, map_one, mul_one] }

private theorem gAlg_tmul (c : K') (f : F₀) :
    gAlg σ F₀ φ (c ⊗ₜ f) =
      algebraMap K' (LaurentSeries K') c * coeffMap σ (φ (seam₀ K F₀ f)) :=
  gRat_tmul σ F₀ φ c f

private theorem gAlg_one_tmul (f : F₀) :
    gAlg σ F₀ φ (1 ⊗ₜ f) = coeffMap σ (φ (seam₀ K F₀ f)) := by
  rw [gAlg_tmul, map_one, one_mul]

private def gLin : K' ⊗[ℚ] F₀ →ₗ[K'] LaurentSeries K' where
  toFun := gAlg σ F₀ φ
  map_add' := map_add _
  map_smul' c x := by
    rw [RingHom.id_apply, ← algebraMap_mul_eq_smul', ← (gAlg σ F₀ φ).commutes c, ← map_mul,
      ← Algebra.smul_def]

private theorem gLin_apply (x : K' ⊗[ℚ] F₀) : gLin σ F₀ φ x = gAlg σ F₀ φ x := rfl

private theorem linearIndependent_phi_seam₀ {ι : Type*} (bF : Module.Basis ι ℚ F₀) :
    LinearIndependent K (fun i => φ (seam₀ K F₀ (bF i))) := by
  have hbF : LinearIndependent ℚ (fun i => ((bF i : F₀) : LaurentSeries ℚ)) :=
    bF.linearIndependent.map' (valRat F₀) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hK := linearIndependent_coeffEmb K hbF
  rw [linearIndependent_iff'] at hK ⊢
  intro s g hg i hi
  refine hK s g ?_ i hi
  have h1 : φ (∑ j ∈ s, algebraMap K (laurentBaseChange K F₀) (g j) * seam₀ K F₀ (bF j)) = 0 := by
    rw [map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, AlgHom.commutes, algebraMap_mul_eq_smul']
  have h2 : ∑ j ∈ s, algebraMap K (laurentBaseChange K F₀) (g j) * seam₀ K F₀ (bF j) = 0 :=
    (map_eq_zero_iff _ (φ : laurentBaseChange K F₀ →+* LaurentSeries K).injective).mp h1
  have h3 := congrArg (laurentBaseChange K F₀).val h2
  rw [map_sum, map_zero] at h3
  rw [← h3]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]

  exact (algebraMap_mul_eq_smul' (g j) _).symm

private theorem gAlg_injective : Function.Injective (gAlg σ F₀ φ) := by
  classical
  let bF := Module.Free.chooseBasis ℚ F₀
  let B := Algebra.TensorProduct.basis K' bF
  have hli : LinearIndependent K' (gLin σ F₀ φ ∘ B) := by
    have h : (gLin σ F₀ φ ∘ B : _ → LaurentSeries K') =
        fun i => coeffMap σ (φ (seam₀ K F₀ (bF i))) := by
      funext i
      rw [Function.comp_apply, gLin_apply, Algebra.TensorProduct.basis_apply, gAlg_one_tmul]
    rw [h]
    exact linearIndependent_coeffMap_of_ringHom σ (linearIndependent_phi_seam₀ F₀ φ bF)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hrepr : Finsupp.linearCombination K' (gLin σ F₀ φ ∘ B) (B.repr x) = 0 := by
    rw [← Finsupp.apply_linearCombination, B.linearCombination_repr]
    exact hx
  have h0 : B.repr x = 0 := linearIndependent_iff.mp hli (B.repr x) hrepr
  rw [← B.linearCombination_repr x, h0, map_zero]

end Core

private def bcRestrict (K' : Type*) [Field K'] [Algebra ℚ K']
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : K' ⊗[ℚ] F₀ →+* laurentBaseChange K' F₀ :=
  (baseChangeHom K' F₀ : K' ⊗[ℚ] F₀ →+* LaurentSeries K').codRestrict (laurentBaseChange K' F₀)
    (baseChangeHom_mem K' F₀)

private theorem coe_bcRestrict (K' : Type*) [Field K'] [Algebra ℚ K']
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (a : K' ⊗[ℚ] F₀) :
    (bcRestrict K' F₀ a : LaurentSeries K') = baseChangeHom K' F₀ a := rfl

private theorem exists_ringHom_lift {K' : Type*} [Field K'] [Algebra ℚ K']
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {L : Type*} [Field L]
    (g : K' ⊗[ℚ] F₀ →+* L) (hg : Function.Injective g) :
    ∃ ι₀ : laurentBaseChange K' F₀ →+* L, ∀ a, ι₀ (bcRestrict K' F₀ a) = g a := by
  letI : Algebra (K' ⊗[ℚ] F₀) (laurentBaseChange K' F₀) := (bcRestrict K' F₀).toAlgebra
  haveI : FaithfulSMul (K' ⊗[ℚ] F₀) (laurentBaseChange K' F₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b h =>
      baseChangeHom_injective K' F₀ (congrArg Subtype.val h)
  haveI : IsFractionRing (K' ⊗[ℚ] F₀) (laurentBaseChange K' F₀) := by
    refine IsFractionRing.of_field (R := K' ⊗[ℚ] F₀) (K := laurentBaseChange K' F₀) fun z => ?_
    have hz : (z : LaurentSeries K') ∈ Subfield.closure
        (Set.range (algebraMap K' (LaurentSeries K')) ∪
          ⇑(coeffEmb K') '' (F₀ : Set (LaurentSeries ℚ))) :=
      mem_laurentBaseChange_iff.mp z.2
    rw [Subfield.mem_closure_iff] at hz
    obtain ⟨y, hy, d, hd, hyd⟩ := hz
    have hle : Subring.closure (Set.range (algebraMap K' (LaurentSeries K')) ∪
          ⇑(coeffEmb K') '' (F₀ : Set (LaurentSeries ℚ)))
        ≤ (baseChangeHom K' F₀ : K' ⊗[ℚ] F₀ →+* LaurentSeries K').range := by
      refine Subring.closure_le.mpr ?_
      rintro _ (⟨c, rfl⟩ | ⟨f, hf, rfl⟩)
      · exact ⟨algebraMap K' (K' ⊗[ℚ] F₀) c, (baseChangeHom K' F₀).commutes c⟩
      · exact ⟨(1 : K') ⊗ₜ ⟨f, hf⟩, baseChangeHom_one_tmul K' F₀ ⟨f, hf⟩⟩
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp (hle hy)
    obtain ⟨b, hb⟩ := RingHom.mem_range.mp (hle hd)
    refine ⟨a, b, Subtype.ext ?_⟩
    rw [IntermediateField.coe_div]
    change (z : LaurentSeries K') = baseChangeHom K' F₀ a / baseChangeHom K' F₀ b
    rw [← hyd, ← ha, ← hb]
    rfl
  exact ⟨IsFractionRing.lift hg, fun a => IsFractionRing.lift_algebraMap hg a⟩

section CoreTheorem

variable {K K' : Type*} [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'] (σ : K →+* K')
  (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (φ : laurentBaseChange K F₀ →ₐ[K] LaurentSeries K)

private theorem lift_seamσ (ι₀ : laurentBaseChange K' F₀ →+* LaurentSeries K')
    (hι₀ : ∀ a, ι₀ (bcRestrict K' F₀ a) = gAlg σ F₀ φ a)
    (hcomm : ∀ c : K', ι₀ (algebraMap K' (laurentBaseChange K' F₀) c)
      = algebraMap K' (LaurentSeries K') c)
    (x : laurentBaseChange K F₀) : ι₀ (seamσ σ F₀ x) = coeffMap σ (φ x) := by
  obtain ⟨y, hy⟩ := x
  change y ∈ IntermediateField.adjoin K (⇑(coeffEmb K) '' (F₀ : Set (LaurentSeries ℚ))) at hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      have h1 : ι₀ (seamσ σ F₀ (seam₀ K F₀ ⟨f, hf⟩)) = coeffMap σ (φ (seam₀ K F₀ ⟨f, hf⟩)) := by
        rw [← gAlg_one_tmul, ← hι₀]
        congr 1
        refine Subtype.ext ?_
        rw [coe_seamσ, coe_seam₀, coe_bcRestrict, baseChangeHom_one_tmul]
        exact coeffMap_coeffEmb_of_ringHom σ _
      exact h1
  | algebraMap c =>
      have h1 : ι₀ (seamσ σ F₀ (algebraMap K (laurentBaseChange K F₀) c))
          = coeffMap σ (φ (algebraMap K (laurentBaseChange K F₀) c)) := by
        rw [AlgHom.commutes, coeffMap_algebraMap_of_ringHom σ c, ← hcomm (σ c)]
        congr 1

        exact Subtype.ext (coeffMap_algebraMap_of_ringHom σ c)
      exact h1
  | add y z hy hz ihy ihz =>
      change ι₀ (seamσ σ F₀ (⟨y, hy⟩ + ⟨z, hz⟩)) = coeffMap σ (φ (⟨y, hy⟩ + ⟨z, hz⟩))
      rw [map_add, map_add, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      change ι₀ (seamσ σ F₀ (⟨y, hy⟩⁻¹)) = coeffMap σ (φ (⟨y, hy⟩⁻¹))
      rw [map_inv₀, map_inv₀, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      change ι₀ (seamσ σ F₀ (⟨y, hy⟩ * ⟨z, hz⟩)) = coeffMap σ (φ (⟨y, hy⟩ * ⟨z, hz⟩))
      rw [map_mul, map_mul, map_mul, map_mul, ihy, ihz]

end CoreTheorem

end ModularCurve

namespace ModularCurve p2m_export "ModularCurve" "coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff linearIndependent_coeffEmb baseChangeHom baseChangeHom_one_tmul baseChangeHom_injective baseChangeHom_mem baseChangeEquiv coeffMap_mem_laurentBaseChange_of_ringHom coeffMap_coeffEmb_of_ringHom order_coeffMap order_sum_algebraMap_mul_coeffMap" end ModularCurve
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.exists_algHom_laurentBaseChange_of_ringHom
    {K K' : Type*} [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'] (σ : K →+* K')
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (φ : laurentBaseChange K F₀ →ₐ[K] LaurentSeries K) :
    ∃ ι' : laurentBaseChange K' F₀ →ₐ[K'] LaurentSeries K',
      ∀ (x : laurentBaseChange K F₀) (x' : laurentBaseChange K' F₀),
        (x' : LaurentSeries K') = coeffMap σ (x : LaurentSeries K) → ι' x' = coeffMap σ (φ x) := by
  obtain ⟨ι₀, hι₀⟩ := ModularCurve.exists_ringHom_lift F₀
    (ModularCurve.gAlg σ F₀ φ : K' ⊗[ℚ] F₀ →+* LaurentSeries K') (ModularCurve.gAlg_injective σ F₀ φ)
  have hcomm : ∀ c : K', ι₀ (algebraMap K' (laurentBaseChange K' F₀) c)
      = algebraMap K' (LaurentSeries K') c := by
    intro c
    have h1 : algebraMap K' (laurentBaseChange K' F₀) c
        = ModularCurve.bcRestrict K' F₀ (algebraMap K' (K' ⊗[ℚ] F₀) c) :=
      Subtype.ext ((baseChangeHom K' F₀).commutes c).symm
    rw [h1, hι₀]
    exact (ModularCurve.gAlg σ F₀ φ).commutes c
  refine ⟨{ ι₀ with commutes' := hcomm }, fun x x' hx' => ?_⟩
  have hx'eq : x' = ModularCurve.seamσ σ F₀ x := Subtype.ext hx'
  rw [hx'eq]
  exact ModularCurve.lift_seamσ σ F₀ φ ι₀ hι₀ hcomm x

end

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.exists_ord_mul_eq_order_of_algHom_laurentSeries" namespace Place p2m_export "AlgebraicCurve.Place" "ext deg ord ord_coe_irreducible toValuationSubring uniformizer_alt exists_ord_mul_eq_order_of_algHom_laurentSeries exists_algHom_laurentSeries_order_eq_ord" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in
private theorem AlgebraicCurve.Place.exists_place_laurentBaseChange_of_deg_eq_one
    {K K' : Type*} [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'] (σ : K →+* K')
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (v : Place K (laurentBaseChange K F₀)) (hv : v.deg = 1) :
    ∃ w : Place K' (laurentBaseChange K' F₀),
      (∀ (x : laurentBaseChange K F₀) (x' : laurentBaseChange K' F₀),
          (x' : LaurentSeries K') = coeffMap σ (x : LaurentSeries K) → w.ord x' = v.ord x) ∧
      (∀ {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (c : ι → K') (x : ι → laurentBaseChange K F₀),
          (∀ a : ι → K, ∑ i ∈ s, σ (a i) * c i = 0 → ∀ i ∈ s, a i = 0) →
          (∀ i ∈ s, x i ≠ 0) →
          ∀ y : laurentBaseChange K' F₀,
            (y : LaurentSeries K')
                = ∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (x i : LaurentSeries K) →
            w.ord y = s.inf' hs (fun i => v.ord (x i))) := by

  obtain ⟨φ, hφ⟩ := v.exists_algHom_laurentSeries_order_eq_ord hv

  obtain ⟨ι', hseam⟩ := ModularCurve.exists_algHom_laurentBaseChange_of_ringHom σ F₀ φ

  have hσinj : Function.Injective σ := σ.injective
  let seam : laurentBaseChange K F₀ → laurentBaseChange K' F₀ := fun x =>
    ⟨coeffMap σ (x : LaurentSeries K), coeffMap_mem_laurentBaseChange_of_ringHom σ F₀ x.2⟩
  have hseam' : ∀ x : laurentBaseChange K F₀, ι' (seam x) = coeffMap σ (φ x) :=
    fun x => hseam x (seam x) rfl
  have hι'seam_order : ∀ x : laurentBaseChange K F₀, (ι' (seam x)).order = v.ord x := fun x => by
    rw [hseam' x, order_coeffMap hσinj, hφ x]

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hordπ : v.ord (π : laurentBaseChange K F₀) = 1 := v.ord_coe_irreducible hπ
  have hι'π : (ι' (seam (π : laurentBaseChange K F₀))).order = 1 :=
    (hι'seam_order _).trans hordπ

  obtain ⟨w, γ, hγpos, hw⟩ := AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K' ι'
    ⟨seam (π : laurentBaseChange K F₀), by rw [hι'π]; exact one_ne_zero⟩

  have hγ1 : (γ : ℤ) = 1 := by
    have hdvd : (γ : ℤ) ∣ 1 :=
      ⟨w.ord (seam (π : laurentBaseChange K F₀)),
        by rw [mul_comm]; exact ((hw _).trans hι'π).symm⟩
    have := Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
    omega
  have hw' : ∀ y : laurentBaseChange K' F₀, w.ord y = (ι' y).order := fun y => by
    have := hw y; rw [hγ1, mul_one] at this; exact this
  refine ⟨w, ?_, ?_⟩
  ·
    intro x x' hxx'
    rw [hw' x', hseam x x' hxx', order_coeffMap hσinj, hφ x]
  ·
    intro ι s hs c x hc hx y hy

    have hy' : y = ∑ i ∈ s, algebraMap K' (laurentBaseChange K' F₀) (c i) * seam (x i) := by
      refine Subtype.ext ?_
      push_cast
      exact hy

    have hι'y : ι' y = ∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (φ (x i)) := by
      rw [hy']
      simp only [map_sum, map_mul, AlgHom.commutes, hseam']

    have hfnz : ∀ i ∈ s, φ (x i) ≠ 0 := fun i hi => by
      have hxi := hx i hi
      exact fun h0 => hxi ((φ : laurentBaseChange K F₀ →+* LaurentSeries K).injective
        (by simpa using h0))
    have hexp3 := ModularCurve.order_sum_algebraMap_mul_coeffMap σ s hs c hc
      (fun i => φ (x i)) hfnz
    rw [hw' y, hι'y, hexp3.2]
    exact Finset.inf'_congr hs rfl fun i _ => hφ (x i)

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one.AlgebraicCurve.Place in
open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one.AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one.ModularCurve in

theorem solution {K K' : Type*} [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'] (σ : K →+* K')
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (v : Place K (laurentBaseChange K F₀)) (hv : v.deg = 1) :
    ∃ w : Place K' (laurentBaseChange K' F₀),
      (∀ (x : laurentBaseChange K F₀) (x' : laurentBaseChange K' F₀),
          (x' : LaurentSeries K') = coeffMap σ (x : LaurentSeries K) → w.ord x' = v.ord x) ∧
      (∀ {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (c : ι → K') (x : ι → laurentBaseChange K F₀),
          (∀ a : ι → K, ∑ i ∈ s, σ (a i) * c i = 0 → ∀ i ∈ s, a i = 0) →
          (∀ i ∈ s, x i ≠ 0) →
          ∀ y : laurentBaseChange K' F₀,
            (y : LaurentSeries K')
                = ∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (x i : LaurentSeries K) →
            w.ord y = s.inf' hs (fun i => v.ord (x i))) :=
  AlgebraicCurve.Place.exists_place_laurentBaseChange_of_deg_eq_one σ F₀ v hv

#print axioms solution

end S_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one (solution)
