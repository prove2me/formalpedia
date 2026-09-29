-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/08b4fd95-ebfb-5ae2-9686-c0b980932d5c

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_HahnSeries_RamificationBound
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_one_of_hahnSeries_embedding_of_isGalois
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one.AlgebraicCurve Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_eq_one_of_hahnSeries_embedding_of_isGalois Place.exists_restrict_eq"
namespace Place
p2m_export "AlgebraicCurve.Place" "ord ramificationIndex_pos ord_restrict ord_eq_one_of_hahnSeries_embedding_of_isGalois exists_restrict_eq"
namespace HahnUnramDescentAux
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

theorem algebraMap_hahn_eq_C {K L : Type*} [Field K] [Field L] [Algebra K L] (c : K) :
    (algebraMap K (HahnSeries ℚ L)) c = HahnSeries.C (algebraMap K L c) := by
  first
  | exact HahnSeries.algebraMap_apply
  | rw [HahnSeries.algebraMap_apply', IsScalarTower.algebraMap_apply K L (PowerSeries L),
      PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
  | (rw [HahnSeries.algebraMap_apply']
     have h2 : algebraMap K (PowerSeries L) c = PowerSeries.C (algebraMap K L c) := by
       simp [IsScalarTower.algebraMap_apply K L (PowerSeries L)]
     rw [h2, HahnSeries.ofPowerSeries_C])

theorem eval₂_C_single_one {L : Type*} [Field L] (q : L[X]) :
    q.eval₂ (HahnSeries.C : L →+* HahnSeries ℚ L) (HahnSeries.single (1 : ℚ) (1 : L))
      = HahnSeries.ofPowerSeries ℚ L (q : PowerSeries L) := by
  have heq : (Polynomial.eval₂RingHom (HahnSeries.C : L →+* HahnSeries ℚ L)
        (HahnSeries.single (1 : ℚ) (1 : L)))
      = (HahnSeries.ofPowerSeries ℚ L).comp (Polynomial.coeToPowerSeries.ringHom (R := L)) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, HahnSeries.ofPowerSeries_X]
  have := congrArg (fun f : L[X] →+* HahnSeries ℚ L => f q) heq
  simpa [Polynomial.coeToPowerSeries.ringHom_apply] using this

theorem hasRamBound_one_ofPowerSeries {L : Type*} [Field L] (x : PowerSeries L) :
    HahnSeries.HasRamBound 1 (HahnSeries.ofPowerSeries ℚ L x) := by
  intro g hg
  have hg' : g ∈ Set.range ((↑) : ℕ → ℚ) := by
    by_contra h
    rw [HahnSeries.mem_support, HahnSeries.ofPowerSeries_apply] at hg
    exact hg (HahnSeries.embDomain_notin_range (by simpa using h))
  obtain ⟨m, rfl⟩ := hg'
  exact ⟨(m : ℤ), by push_cast; ring⟩

theorem aeval_C_add_single {K L : Type*} [Field K] [Field L] [Algebra K L] (a : L) (p : K[X]) :
    Polynomial.aeval (R := K) (HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L)) p
      = HahnSeries.ofPowerSeries ℚ L
          ((((p.map (algebraMap K L)).comp (X + C a) : L[X])) : PowerSeries L) := by
  set t : HahnSeries ℚ L := HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L) with ht
  have h1 : (Polynomial.aeval (R := K) t).toRingHom
      = Polynomial.eval₂RingHom ((HahnSeries.C : L →+* HahnSeries ℚ L).comp (algebraMap K L)) t := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C, algebraMap_hahn_eq_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply]
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have h2 := congrArg (fun f : K[X] →+* HahnSeries ℚ L => f p) h1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coe_eval₂RingHom] at h2
  rw [h2, ← Polynomial.eval₂_map, ← eval₂_C_single_one, Polynomial.eval₂_comp,
    Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, ht, add_comm]

theorem aeval_C_add_single_injective {K L : Type*} [Field K] [Field L] [Algebra K L] (a : L) :
    Function.Injective
      (Polynomial.aeval (R := K) (HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L))) := by
  intro p₁ p₂ h
  have h' := h
  rw [aeval_C_add_single, aeval_C_add_single] at h'
  have h3 := HahnSeries.ofPowerSeries_injective h'
  rw [Polynomial.coe_inj] at h3
  have h4 : (p₁.map (algebraMap K L)) = (p₂.map (algebraMap K L)) := by
    have := congrArg (fun r : L[X] => r.comp (X - C a)) h3
    simpa [Polynomial.comp_assoc] using this
  exact Polynomial.map_injective _ (algebraMap K L).injective h4

end AlgebraicCurve.Place.HahnUnramDescentAux

open AlgebraicCurve.Place.HahnUnramDescentAux in

theorem solution
    {K L F : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F]
    (p : Polynomial K) (hp : Irreducible p) (a : L)
    (ha : Polynomial.aeval a p = 0) (ha' : Polynomial.aeval a (Polynomial.derivative p) ≠ 0)
    (hF : ∀ ψ : F →ₐ[K] HahnSeries ℚ L,
      ψ (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
          = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L) →
        ∀ x : F, HahnSeries.HasRamBound 1 (ψ x))
    (w : AlgebraicCurve.Place K F)
    (hw : 0 < w.ord (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p))) :
    w.ord (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p)) = 1 := by
  classical
  set t : HahnSeries ℚ L := HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L) with ht
  set X₀ : RatFunc K := algebraMap (Polynomial K) (RatFunc K) Polynomial.X with hX₀
  set f₀ : RatFunc K := algebraMap (Polynomial K) (RatFunc K) p with hf₀

  let E := AlgebraicClosure F
  haveI : Algebra.IsAlgebraic (RatFunc K) E := Algebra.IsAlgebraic.trans (RatFunc K) F E
  haveI : IsAlgClosure (RatFunc K) E := IsAlgClosure.ofAlgebraic (RatFunc K) F E
  let M := IntermediateField.normalClosure (RatFunc K) F E
  haveI : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite (RatFunc K) F M
  haveI : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq (fun c => rfl)
  haveI : Algebra.IsSeparable F M := Algebra.isSeparable_tower_top_of_isSeparable (RatFunc K) F M

  let φ : Polynomial K →ₐ[K] HahnSeries ℚ L := Polynomial.aeval t
  have hφ : nonZeroDivisors (Polynomial K)
      ≤ Submonoid.comap φ (nonZeroDivisors (HahnSeries ℚ L)) := by
    intro q hq
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    rw [mem_nonZeroDivisors_iff_ne_zero] at hq
    intro h0
    exact hq (aeval_C_add_single_injective (K := K) a (by rw [map_zero]; exact h0))
  let τ : RatFunc K →ₐ[K] HahnSeries ℚ L := RatFunc.liftAlgHom φ hφ
  have hτp : ∀ q : Polynomial K, τ (algebraMap (Polynomial K) (RatFunc K) q) = φ q := by
    intro q
    have h := RatFunc.liftAlgHom_apply_div φ hφ q 1
    rwa [map_one, div_one, map_one, div_one] at h
  have hτX : τ X₀ = t := by rw [hX₀, hτp]; exact Polynomial.aeval_X t
  letI : Algebra (RatFunc K) (HahnSeries ℚ L) := τ.toRingHom.toAlgebra
  have hτalg : ∀ r : RatFunc K, algebraMap (RatFunc K) (HahnSeries ℚ L) r = τ r := fun r => rfl
  haveI : IsAlgClosed (HahnSeries ℚ L) := HahnSeries.isAlgClosed_rat

  let ψM : M →ₐ[RatFunc K] HahnSeries ℚ L := IsAlgClosed.lift
  let ψ : M →ₐ[K] HahnSeries ℚ L :=
    { toRingHom := ψM.toRingHom
      commutes' := fun c => by
        show ψM (algebraMap K M c) = algebraMap K (HahnSeries ℚ L) c
        rw [IsScalarTower.algebraMap_apply K (RatFunc K) M, ψM.commutes, hτalg, τ.commutes] }
  have hψapply : ∀ m : M, ψ m = ψM m := fun m => rfl
  have hψX : ψ (algebraMap (RatFunc K) M X₀)
      = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L) := by
    rw [hψapply, ψM.commutes, hτalg]
    exact hτX

  have hLaurent : ∀ y : HahnSeries ℚ L,
      y ∈ HahnSeries.puiseuxRamSubfield L Nat.one_pos ↔ HahnSeries.HasRamBound 1 y :=
    fun y => HahnSeries.mem_puiseuxRamSubfield_iff Nat.one_pos
  have hτmem : ∀ r : RatFunc K, τ r ∈ HahnSeries.puiseuxRamSubfield L Nat.one_pos := by
    intro r
    refine RatFunc.induction_on (P := fun r => τ r ∈ HahnSeries.puiseuxRamSubfield L Nat.one_pos)
      r (fun p₁ q₁ _ => ?_)
    show τ (algebraMap K[X] (RatFunc K) p₁ / algebraMap K[X] (RatFunc K) q₁) ∈ _
    rw [map_div₀, hτp, hτp]
    refine div_mem ?_ ?_ <;>
    · rw [hLaurent]
      show HahnSeries.HasRamBound 1 (Polynomial.aeval (R := K) t _)
      rw [ht, aeval_C_add_single]
      exact hasRamBound_one_ofPowerSeries _
  let T : Subfield (HahnSeries ℚ L) := HahnSeries.puiseuxRamSubfield L Nat.one_pos
  let S : IntermediateField (RatFunc K) M :=
    (T.comap ψM.toRingHom).toIntermediateField (fun r => by
      show ψM (algebraMap (RatFunc K) M r) ∈ T
      rw [ψM.commutes]
      exact hτmem r)
  have hmemS : ∀ m : M, m ∈ S ↔ ψM m ∈ T := fun m => Iff.rfl
  have hS : S = ⊤ := by
    apply IntermediateField.lift_injective M
    rw [IntermediateField.lift_top]
    refine le_antisymm (IntermediateField.lift_le S) ?_
    show IntermediateField.normalClosure (RatFunc K) F E ≤ IntermediateField.lift S
    unfold IntermediateField.normalClosure
    refine iSup_le (fun g => ?_)
    rintro x ⟨y, rfl⟩
    have hgy : ∀ y : F, g y ∈ M := fun y => AlgHom.fieldRange_le_normalClosure g ⟨y, rfl⟩
    let g' : F →ₐ[RatFunc K] M := g.codRestrict M.toSubalgebra hgy
    show ((g' y : M) : E) ∈ IntermediateField.lift S
    rw [IntermediateField.mem_lift, hmemS, hLaurent]

    let ψF : F →ₐ[K] HahnSeries ℚ L :=
      { toRingHom := (ψM.comp g').toRingHom
        commutes' := fun c => by
          show ψM (g' (algebraMap K F c)) = algebraMap K (HahnSeries ℚ L) c
          rw [IsScalarTower.algebraMap_apply K (RatFunc K) F, g'.commutes, ψM.commutes, hτalg,
            τ.commutes] }
    have hψFapply : ∀ x : F, ψF x = ψM (g' x) := fun x => rfl
    have hψF : ψF (algebraMap (RatFunc K) F X₀) = t := by
      rw [hψFapply, g'.commutes, ψM.commutes, hτalg]
      exact hτX
    have := hF ψF hψF y
    rwa [hψFapply] at this
  have hψLaurent : ∀ m : M, HahnSeries.HasRamBound 1 (ψ m) := by
    intro m
    have hm : m ∈ S := by rw [hS]; exact IntermediateField.mem_top
    rw [hψapply]
    exact (hLaurent _).mp ((hmemS m).mp hm)

  have hcore := AlgebraicCurve.Place.ord_eq_one_of_hahnSeries_embedding_of_isGalois
    (K := K) (L := L) (M := M) p hp a ha ha' ψ hψX hψLaurent

  obtain ⟨W, hWw⟩ := AlgebraicCurve.Place.exists_restrict_eq (K := K) (F' := F) (M := M) w
  have hrel := W.ord_restrict (F := F) (algebraMap (RatFunc K) F f₀)
  rw [hWw, ← IsScalarTower.algebraMap_apply (RatFunc K) F M] at hrel
  have he := W.ramificationIndex_pos (F := F)
  have hWpos : 0 < W.ord (algebraMap (RatFunc K) M f₀) := by
    rw [hrel]; exact mul_pos (by exact_mod_cast he) hw
  have hW1 := hcore W hWpos
  rw [hrel] at hW1
  exact Int.eq_one_of_mul_eq_one_left hw.le hW1

end

end S_AlgebraicCurve_Place_ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one (solution)
