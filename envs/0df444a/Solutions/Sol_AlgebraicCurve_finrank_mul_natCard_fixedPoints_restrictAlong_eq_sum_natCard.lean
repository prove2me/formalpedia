-- Prove2me | solution 1 for AlgebraicCurve.finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/fb3a99f0-caca-53ef-8e3f-7faed01fa8ec

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_restrict_ofAlgAut_smul
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.ofAlgAut Place Place.ext Place.restrictAlong Place.restrict_toValuationSubring Place.mem_fiberOver Place.exists_algEquiv_smul_eq_of_restrict_eq Place.restrict_ofAlgAut_smul Place.exists_restrict_eq"
p2m_open "AlgebraicCurve"

namespace BombieriCount

open MulAction

universe uK uF uM uE

variable {K : Type uK} {F' : Type uF} {M : Type uM} [Field K] [Field F'] [Field M] [Algebra K F']
  [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]

theorem restrictAlong_toValuationSubring {E : Type uE} [Field E] [Algebra K E]
    (ψ : E →ₐ[K] E) (hψ : ψ.toRingHom.IsIntegral) (W : Place K E) :
    (W.restrictAlong ψ hψ).toValuationSubring = W.toValuationSubring.comap ψ.toRingHom :=
  rfl

theorem restrict_restrictAlong [Algebra.IsIntegral F' M]
    (φ : F' →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (ψ : M →ₐ[K] M) (hψ : ψ.toRingHom.IsIntegral)
    (hcomp : ∀ x : F', ψ (algebraMap F' M x) = algebraMap F' M (φ x)) (W : Place K M) :
    (W.restrictAlong ψ hψ).restrict F' = (W.restrict F').restrictAlong φ hφ := by
  apply Place.ext
  ext x
  rw [Place.restrict_toValuationSubring, ValuationSubring.mem_comap,
    restrictAlong_toValuationSubring, ValuationSubring.mem_comap,
    restrictAlong_toValuationSubring, ValuationSubring.mem_comap,
    Place.restrict_toValuationSubring, ValuationSubring.mem_comap]
  change ψ (algebraMap F' M x) ∈ W.toValuationSubring ↔
    algebraMap F' M (φ x) ∈ W.toValuationSubring
  rw [hcomp]

def galToSemilinearAut : (M ≃ₐ[F'] M) →* SemilinearAut K M where
  toFun τ := SemilinearAut.ofAlgAut (τ.restrictScalars K)
  map_one' := by
    have : ((1 : M ≃ₐ[F'] M).restrictScalars K) = 1 := AlgEquiv.ext fun _ => rfl
    rw [this, map_one]
  map_mul' σ τ := by
    have : ((σ * τ).restrictScalars K) = σ.restrictScalars K * τ.restrictScalars K :=
      AlgEquiv.ext fun _ => rfl
    rw [this, map_mul]

abbrev galPlaceAction : MulAction (M ≃ₐ[F'] M) (Place K M) :=
  MulAction.compHom (Place K M) (galToSemilinearAut (K := K) (F' := F') (M := M))

attribute [local instance] galPlaceAction

theorem gal_smul_def (τ : M ≃ₐ[F'] M) (W : Place K M) :
    τ • W = SemilinearAut.ofAlgAut (τ.restrictScalars K) • W :=
  rfl

theorem restrict_gal_smul [Algebra.IsIntegral F' M] (τ : M ≃ₐ[F'] M) (W : Place K M) :
    (τ • W).restrict F' = W.restrict F' := by
  rw [gal_smul_def]
  exact Place.restrict_ofAlgAut_smul τ W

variable [FiniteDimensional F' M] [IsGalois F' M]

theorem orbit_eq_fiberOver (W : Place K M) :
    orbit (M ≃ₐ[F'] M) W = ((W.restrict F').fiberOver M : Set (Place K M)) := by
  ext W'
  rw [Finset.mem_coe, Place.mem_fiberOver, mem_orbit_iff]
  constructor
  · rintro ⟨τ, rfl⟩
    exact restrict_gal_smul τ W
  · intro h
    obtain ⟨σ, hσ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq W W' h
    exact ⟨σ, hσ⟩

theorem card_fiberOver_mul_card_stabilizer (W : Place K M) :
    ((W.restrict F').fiberOver M).card * Nat.card (stabilizer (M ≃ₐ[F'] M) W) =
      Nat.card (M ≃ₐ[F'] M) := by
  rw [← Set.ncard_coe_finset, ← orbit_eq_fiberOver, ← index_stabilizer,
    Subgroup.index_mul_card]

theorem sum_fiberOver_card_stabilizer (P : Place K F') :
    ∑ W ∈ P.fiberOver M, Nat.card (stabilizer (M ≃ₐ[F'] M) W) = Nat.card (M ≃ₐ[F'] M) := by
  obtain ⟨W₀, hW₀⟩ := Place.exists_restrict_eq (M := M) P
  have hpos : 0 < (P.fiberOver M).card :=
    Finset.card_pos.mpr ⟨W₀, (Place.mem_fiberOver P).mpr hW₀⟩
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [Finset.mul_sum]
  calc ∑ W ∈ P.fiberOver M, (P.fiberOver M).card * Nat.card (stabilizer (M ≃ₐ[F'] M) W)
      = ∑ W ∈ P.fiberOver M, Nat.card (M ≃ₐ[F'] M) := by
        refine Finset.sum_congr rfl fun W hW => ?_
        have hWP : W.restrict F' = P := (Place.mem_fiberOver P).mp hW
        rw [← card_fiberOver_mul_card_stabilizer (K := K) (F' := F') W, hWP]
    _ = (P.fiberOver M).card * Nat.card (M ≃ₐ[F'] M) := by
        rw [Finset.sum_const, smul_eq_mul]

open scoped Classical in
omit [IsGalois F' M] in

theorem card_filter_smul_eq (W : Place K M) (σ : M ≃ₐ[F'] M) :
    (Finset.univ.filter fun τ : M ≃ₐ[F'] M => σ • W = τ • W).card =
      Nat.card (stabilizer (M ≃ₐ[F'] M) W) := by
  classical
  have himg : (Finset.univ.filter fun τ : M ≃ₐ[F'] M => σ • W = τ • W) =
      (Finset.univ.filter fun ρ : M ≃ₐ[F'] M => ρ • W = W).image (σ * ·) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨σ⁻¹ * τ, ?_, by group⟩
      rw [mul_smul, ← h, ← mul_smul, inv_mul_cancel, one_smul]
    · rintro ⟨ρ, hρ, rfl⟩
      rw [mul_smul, hρ]
  rw [himg, Finset.card_image_of_injective _ (mul_right_injective σ)]
  have e : (stabilizer (M ≃ₐ[F'] M) W) ≃
      ((Finset.univ.filter fun ρ : M ≃ₐ[F'] M => ρ • W = W : Finset (M ≃ₐ[F'] M)) :
        Set (M ≃ₐ[F'] M)) :=
    Equiv.subtypeEquivRight fun ρ => by
      rw [Finset.mem_coe, Finset.mem_filter, mem_stabilizer_iff]
      simp
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_coe_finset]

end BombieriCount

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard.AlgebraicCurve AlgebraicCurve.BombieriCount MulAction in
theorem solution
    (K F' M : Type*) [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M] [Algebra F' M]
    [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (φ : F' →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (ψ : M →ₐ[K] M) (hψ : ψ.toRingHom.IsIntegral)
    (hcomp : ∀ x : F', ψ (algebraMap F' M x) = algebraMap F' M (φ x))
    (hfin : (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφ)).Finite) :
    (∀ τ : M ≃ₐ[F'] M,
        {W : AlgebraicCurve.Place K M | W.restrictAlong ψ hψ =
            AlgebraicCurve.SemilinearAut.ofAlgAut (τ.restrictScalars K) • W}.Finite) ∧
      Module.finrank F' M *
          Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφ)) =
        ∑ τ : M ≃ₐ[F'] M,
          Nat.card {W : AlgebraicCurve.Place K M | W.restrictAlong ψ hψ =
            AlgebraicCurve.SemilinearAut.ofAlgAut (τ.restrictScalars K) • W} := by
  classical
  letI : MulAction (M ≃ₐ[F'] M) (Place K M) := galPlaceAction

  set Fix := Function.fixedPoints (Place.restrictAlong φ hφ) with hFix
  let Fixf : Finset (Place K F') := hfin.toFinset
  have hmemFixf : ∀ P, P ∈ Fixf ↔ Place.restrictAlong φ hφ P = P := fun P => by
    rw [Set.Finite.mem_toFinset, hFix, Function.mem_fixedPoints_iff]
  let X : Finset (Place K M) := Fixf.biUnion fun P => P.fiberOver M
  have hmemX : ∀ W, W ∈ X ↔ Place.restrictAlong φ hφ (W.restrict F') = W.restrict F' := by
    intro W
    simp only [X, Finset.mem_biUnion, Place.mem_fiberOver, hmemFixf]
    constructor
    · rintro ⟨P, hP, rfl⟩; exact hP
    · intro h; exact ⟨_, h, rfl⟩

  have hsmul : ∀ (τ : M ≃ₐ[F'] M) (W : Place K M),
      SemilinearAut.ofAlgAut (τ.restrictScalars K) • W = τ • W := fun _ _ => rfl

  have hsol_mem : ∀ (τ : M ≃ₐ[F'] M) (W : Place K M),
      W.restrictAlong ψ hψ = τ • W → W ∈ X := by
    intro τ W h
    rw [hmemX, ← restrict_restrictAlong φ hφ ψ hψ hcomp, h, restrict_gal_smul]

  have hSeq : ∀ τ : M ≃ₐ[F'] M,
      {W : Place K M | W.restrictAlong ψ hψ =
          SemilinearAut.ofAlgAut (τ.restrictScalars K) • W} =
        ((X.filter fun W => W.restrictAlong ψ hψ = τ • W : Finset (Place K M)) :
          Set (Place K M)) := by
    intro τ
    ext W
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hsmul]
    exact ⟨fun h => ⟨hsol_mem τ W h, h⟩, fun h => h.2⟩
  refine ⟨fun τ => ?_, ?_⟩
  · rw [hSeq τ]
    exact Finset.finite_toSet _

  have hcardS : ∀ τ : M ≃ₐ[F'] M,
      Nat.card {W : Place K M | W.restrictAlong ψ hψ =
          SemilinearAut.ofAlgAut (τ.restrictScalars K) • W} =
        (X.filter fun W => W.restrictAlong ψ hψ = τ • W).card := by
    intro τ
    rw [hSeq τ, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  simp_rw [hcardS]

  have hFixcard : Nat.card Fix = Fixf.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  rw [hFixcard]

  have hswap : ∑ τ : M ≃ₐ[F'] M, (X.filter fun W => W.restrictAlong ψ hψ = τ • W).card =
      ∑ W ∈ X, (Finset.univ.filter fun τ : M ≃ₐ[F'] M => W.restrictAlong ψ hψ = τ • W).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]

  have hinner : ∀ W ∈ X,
      (Finset.univ.filter fun τ : M ≃ₐ[F'] M => W.restrictAlong ψ hψ = τ • W).card =
        Nat.card (stabilizer (M ≃ₐ[F'] M) W) := by
    intro W hW
    have hV : (W.restrictAlong ψ hψ).restrict F' = W.restrict F' := by
      rw [restrict_restrictAlong φ hφ ψ hψ hcomp, (hmemX W).mp hW]
    obtain ⟨σ, hσ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq W _ hV
    rw [hsmul] at hσ
    rw [← hσ]
    convert card_filter_smul_eq W σ
  rw [Finset.sum_congr rfl hinner]

  have hmaps : ∀ W ∈ X, W.restrict F' ∈ Fixf := by
    intro W hW
    rw [hmemFixf]
    exact (hmemX W).mp hW
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ P ∈ Fixf,
      (X.filter fun W => W.restrict F' = P) = P.fiberOver M := by
    intro P hP
    ext W
    simp only [Finset.mem_filter, Place.mem_fiberOver, hmemX]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      exact (hmemFixf P).mp hP
  rw [Finset.sum_congr rfl fun P hP => by rw [hfib P hP, sum_fiberOver_card_stabilizer]]
  rw [Finset.sum_const, smul_eq_mul, IsGalois.card_aut_eq_finrank, mul_comm]

end S_AlgebraicCurve_finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard
end P2MW
export P2MW.S_AlgebraicCurve_finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard (solution)
