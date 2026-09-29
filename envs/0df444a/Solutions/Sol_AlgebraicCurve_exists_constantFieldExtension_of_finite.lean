-- Prove2me | solution 1 for AlgebraicCurve.exists_constantFieldExtension_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/830c06ad-06c5-509d-95f9-3939f8269a55

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_constantFieldExtension_of_finite
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open Polynomial
open scoped IntermediateField

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Divisor LSpace mem_lSpace_iff mem_lSpace_iff_ord algebraMap_mem_lSpace_zero ConstantsAreBase Place.extendConstants Place.exists_integralClosureAt_of_ord_fiber_nonneg isCurveOver_iff_exists_transcendental_finiteDimensional essFiniteType_of_transcendental_of_finiteDimensional"
p2m_open "AlgebraicCurve"

namespace ConstFieldExtOfFinite

universe u v

section Constants

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem mem_range_of_forall_mem (hC : ConstantsAreBase k F) {y : F}
    (hy : ∀ v : Place k F, y ∈ v.toValuationSubring) : y ∈ (algebraMap k F).range := by
  have hmem : y ∈ LSpace (0 : Divisor k F) := by
    rw [mem_lSpace_iff]
    intro v
    simpa using v.adicValuation_le_one_of_mem (hy v)
  have hC' : LSpace (0 : Divisor k F) = LinearMap.range (Algebra.linearMap k F) := hC
  rw [hC', LinearMap.mem_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc⟩

theorem mem_range_of_isIntegral (hC : ConstantsAreBase k F) {y : F} (hy : IsIntegral k y) :
    y ∈ (algebraMap k F).range := by
  have hmem : y ∈ LSpace (0 : Divisor k F) := by
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    rw [v.ord_eq_zero_of_isAlgebraic hy.isAlgebraic]
    simp
  have hC' : LSpace (0 : Divisor k F) = LinearMap.range (Algebra.linearMap k F) := hC
  rw [hC', LinearMap.mem_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc⟩

end Constants

section Minpoly

variable {k F M : Type*} [Field k] [Field F] [Field M] [Algebra k F] [Algebra F M]
  [Algebra k M] [IsScalarTower k F M]

theorem minpoly_eq_map (hconst : ∀ y : F, IsIntegral k y → y ∈ (algebraMap k F).range)
    {β : M} (hβ : IsIntegral k β) :
    minpoly F β = (minpoly k β).map (algebraMap k F) := by
  have hPm : (minpoly k β).Monic := minpoly.monic hβ
  have hQm : (minpoly F β).Monic := minpoly.monic hβ.tower_top
  have hdvd : minpoly F β ∣ (minpoly k β).map (algebraMap k F) :=
    minpoly.dvd_map_of_isScalarTower k F β

  have hlift : minpoly F β ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F hPm hQm hdvd
    rw [lifts_iff_coeff_lifts] at h1
    obtain ⟨c, hc⟩ := h1 n
    have hint : IsIntegral k ((minpoly F β).coeff n) := by
      rw [← hc]
      exact c.2
    exact hconst _ hint
  obtain ⟨Q₀, hQ₀, hdeg, hQ₀m⟩ := lifts_and_natDegree_eq_and_monic hlift hQm
  have haeval : aeval β Q₀ = 0 := by
    rw [← aeval_map_algebraMap F β Q₀, hQ₀]
    exact minpoly.aeval F β
  have hPQ₀ : minpoly k β ∣ Q₀ := minpoly.dvd k β haeval
  have h1 : (minpoly k β).natDegree ≤ (minpoly F β).natDegree := by
    rw [← hdeg]
    exact natDegree_le_of_dvd hPQ₀ hQ₀m.ne_zero
  have h2 : ((minpoly k β).map (algebraMap k F)).natDegree ≤ (minpoly F β).natDegree := by
    rwa [natDegree_map]
  exact (eq_of_monic_of_dvd_of_natDegree_le hQm (hPm.map _) hdvd h2).symm

end Minpoly

theorem exists_irreducible_natDegree_eq (k : Type u) [Field k] [Finite k] (r : ℕ)
    (hr : 0 < r) : ∃ g : k[X], g.Monic ∧ Irreducible g ∧ g.natDegree = r := by
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  haveI : NeZero r := ⟨hr.ne'⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k (FiniteField.Extension k (ringChar k) r)
  have hint : IsIntegral k α := .of_finite k α
  refine ⟨minpoly k α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  rw [(Field.primitive_element_iff_minpoly_natDegree_eq k α).mp hα,
    FiniteField.finrank_extension k (ringChar k) r]

section Tower

theorem finite_and_separable_of_tower {k F F' E : Type*} [Field k] [Field F] [Field F']
    [Field E] [Algebra k F] [Algebra F F'] [Algebra E F'] {t : F}
    (hfd : FiniteDimensional k⟮t⟯ F) (hsep : Algebra.IsSeparable k⟮t⟯ F)
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (ψ : k⟮t⟯ →+* E) (hψ : ∀ x, algebraMap E F' (ψ x) = algebraMap F F' x) :
    FiniteDimensional E F' ∧ Algebra.IsSeparable E F' := by
  haveI : IsScalarTower k⟮t⟯ F F' := inferInstance
  haveI : Module.Finite k⟮t⟯ F' := Module.Finite.trans F F'
  haveI : Algebra.IsSeparable k⟮t⟯ F' := Algebra.IsSeparable.trans k⟮t⟯ F F'
  letI : Algebra k⟮t⟯ E := ψ.toAlgebra
  haveI : IsScalarTower k⟮t⟯ E F' := IsScalarTower.of_algebraMap_eq fun x => (hψ x).symm
  exact ⟨Module.Finite.of_restrictScalars_finite k⟮t⟯ E F',
    Algebra.isSeparable_tower_top_of_isSeparable k⟮t⟯ E F'⟩

theorem algebraMap_mem_adjoin {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F]
    [Algebra F F'] [Algebra k F'] [IsScalarTower k F F']
    (K' : Type*) [Field K'] [Algebra k K'] [Algebra K' F'] [IsScalarTower k K' F']
    (t : F) (x : k⟮t⟯) :
    algebraMap F F' x ∈ K'⟮algebraMap F F' t⟯ := by
  have hmap : (k⟮t⟯).map (IsScalarTower.toAlgHom k F F') = k⟮algebraMap F F' t⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hx : algebraMap F F' x ∈ k⟮algebraMap F F' t⟯ := by
    rw [← hmap, IntermediateField.mem_map]
    exact ⟨x, x.2, rfl⟩
  have hle : k⟮algebraMap F F' t⟯ ≤ (K'⟮algebraMap F F' t⟯).restrictScalars k :=
    IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self K' _))
  exact (IntermediateField.mem_restrictScalars k).mp (hle hx)

end Tower

section Construction

variable (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F] (g : k[X])

abbrev gF : (ULift.{u} F)[X] := g.map (algebraMap k (ULift.{u} F))

abbrev Kx : Type u := AdjoinRoot g

abbrev Fx : Type (max u v) := AdjoinRoot (gF k F g)

theorem eval₂_root_eq_zero :
    g.eval₂ (algebraMap k (Fx k F g)) (AdjoinRoot.root (gF k F g)) = 0 := by
  rw [IsScalarTower.algebraMap_eq k (ULift.{u} F) (Fx k F g), ← eval₂_map,
    AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.eval₂_root _

scoped instance algebraKxFx : Algebra (Kx k g) (Fx k F g) :=
  (AdjoinRoot.lift (algebraMap k (Fx k F g)) (AdjoinRoot.root (gF k F g))
    (eval₂_root_eq_zero k F g)).toAlgebra

theorem algebraMap_Kx_eq :
    algebraMap (Kx k g) (Fx k F g) =
      AdjoinRoot.lift (algebraMap k (Fx k F g)) (AdjoinRoot.root (gF k F g))
        (eval₂_root_eq_zero k F g) := rfl

scoped instance isScalarTower_k_Kx_Fx : IsScalarTower k (Kx k g) (Fx k F g) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [algebraMap_Kx_eq, AdjoinRoot.algebraMap_eq g, AdjoinRoot.lift_of]

theorem algebraMap_root :
    algebraMap (Kx k g) (Fx k F g) (AdjoinRoot.root g) = AdjoinRoot.root (gF k F g) := by
  rw [algebraMap_Kx_eq, AdjoinRoot.lift_root]

theorem algebraMap_F₁_apply (c : ULift.{u} F) :
    algebraMap (ULift.{u} F) (Fx k F g) c = algebraMap F (Fx k F g) c.down := by
  rw [IsScalarTower.algebraMap_apply F (ULift.{u} F) (Fx k F g)]
  congr 1

theorem adjoin_range_eq_top :
    Algebra.adjoin F (Set.range (algebraMap (Kx k g) (Fx k F g))) = ⊤ := by
  set S := Algebra.adjoin F (Set.range (algebraMap (Kx k g) (Fx k F g)))
  have hF₁ : ∀ c : ULift.{u} F, algebraMap (ULift.{u} F) (Fx k F g) c ∈ S := fun c => by
    rw [algebraMap_F₁_apply]
    exact Subalgebra.algebraMap_mem S _
  have hroot : AdjoinRoot.root (gF k F g) ∈ S :=
    Algebra.subset_adjoin ⟨AdjoinRoot.root g, algebraMap_root k F g⟩
  refine eq_top_iff.mpr fun x _ => ?_
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    rw [← AdjoinRoot.aeval_eq, aeval_eq_sum_range]
    refine Subalgebra.sum_mem S fun i _ => ?_
    rw [Algebra.smul_def]
    exact Subalgebra.mul_mem S (hF₁ _) (Subalgebra.pow_mem S hroot _)

theorem finite_F₁ : Module.Finite F (ULift.{u} F) :=
  Module.Finite.equiv (ULift.moduleEquiv : ULift.{u} F ≃ₗ[F] F).symm

theorem finrank_F₁ : Module.finrank F (ULift.{u} F) = 1 := by
  rw [LinearEquiv.finrank_eq (ULift.moduleEquiv : ULift.{u} F ≃ₗ[F] F), Module.finrank_self]

variable {g}

theorem gF_ne_zero (hg : g.Monic) : gF k F g ≠ 0 := (hg.map _).ne_zero

theorem finiteDimensional_Fx (hg : g.Monic) : FiniteDimensional F (Fx k F g) := by
  haveI : Module.Finite F (ULift.{u} F) := finite_F₁ F
  haveI : Module.Finite (ULift.{u} F) (Fx k F g) :=
    (AdjoinRoot.powerBasis (gF_ne_zero k F hg)).finite
  exact Module.Finite.trans (ULift.{u} F) (Fx k F g)

theorem finrank_Fx (hg : g.Monic) : Module.finrank F (Fx k F g) = g.natDegree := by
  haveI : Module.Finite F (ULift.{u} F) := finite_F₁ F
  have h1 : Module.finrank (ULift.{u} F) (Fx k F g) = g.natDegree :=
    ((AdjoinRoot.powerBasis (gF_ne_zero k F hg)).finrank).trans
      ((AdjoinRoot.powerBasis_dim _).trans (natDegree_map _))
  have h2 := Module.finrank_mul_finrank F (ULift.{u} F) (Fx k F g)
  rw [finrank_F₁, one_mul] at h2
  exact h2.symm.trans h1

theorem finrank_Kx (hg : g.Monic) : Module.finrank k (Kx k g) = g.natDegree := by
  rw [(AdjoinRoot.powerBasis hg.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

theorem finite_Kx [Finite k] (hg : g.Monic) : Finite (Kx k g) := by
  haveI : Module.Finite k (Kx k g) := (AdjoinRoot.powerBasis hg.ne_zero).finite
  exact Module.finite_of_finite k

theorem hconst_ulift (hconst : ∀ y : F, IsIntegral k y → y ∈ (algebraMap k F).range)
    (y : ULift.{u} F) (hy : IsIntegral k y) : y ∈ (algebraMap k (ULift.{u} F)).range := by
  have hy' : IsIntegral k y.down := by
    have := hy.map (ULift.algEquiv (R := k) (A := F)).toAlgHom
    simpa using this
  obtain ⟨c, hc⟩ := hconst _ hy'
  refine ⟨c, ?_⟩
  rw [ULift.algebraMap_eq, hc]

theorem irreducible_gF (hconst : ∀ y : F, IsIntegral k y → y ∈ (algebraMap k F).range)
    (hg : g.Monic) (hirr : Irreducible g) : Irreducible (gF k F g) := by
  have hdeg : (gF k F g).degree ≠ 0 := by
    rw [degree_map]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨β, hβ⟩ :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure (ULift.{u} F)) (gF k F g) hdeg
  have hβg : aeval β g = 0 := by rwa [aeval_map_algebraMap] at hβ
  have hβint : IsIntegral k β := ⟨g, hg, by rwa [← aeval_def]⟩
  have hmin : minpoly k β = g := (minpoly.eq_of_irreducible_of_monic hirr hβg hg).symm
  have key := minpoly_eq_map (M := AlgebraicClosure (ULift.{u} F)) (hconst_ulift k F hconst)
    hβint
  rw [hmin] at key
  change Irreducible ((g).map (algebraMap k (ULift.{u} F)))
  rw [← key]
  exact minpoly.irreducible hβint.tower_top

theorem isSeparable_Fx [Fact (Irreducible (gF k F g))] (hg : g.Monic) (hsep : g.Separable) :
    Algebra.IsSeparable F (Fx k F g) := by
  haveI : Algebra.IsSeparable F (ULift.{u} F) := ⟨fun y => by
    have : y = algebraMap F (ULift.{u} F) y.down := by rw [ULift.algebraMap_eq]; rfl
    rw [this]
    exact isSeparable_algebraMap y.down⟩
  haveI : Algebra.IsSeparable (ULift.{u} F) (Fx k F g) := by
    have hne := gF_ne_zero k F hg
    have hroot : IsSeparable (ULift.{u} F) (AdjoinRoot.root (gF k F g)) := by
      show (minpoly _ _).Separable
      rw [AdjoinRoot.minpoly_root hne, (hg.map _).leadingCoeff, inv_one, C_1, mul_one]
      exact hsep.map
    have htop : (ULift.{u} F)⟮AdjoinRoot.root (gF k F g)⟯ = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      have hx : x ∈ Algebra.adjoin (ULift.{u} F) {AdjoinRoot.root (gF k F g)} := by
        rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
      exact IntermediateField.algebra_adjoin_le_adjoin _ _ hx
    have h1 : Algebra.IsSeparable (ULift.{u} F) (ULift.{u} F)⟮AdjoinRoot.root (gF k F g)⟯ :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hroot
    rw [htop] at h1
    haveI := h1
    exact Algebra.IsSeparable.of_algHom (ULift.{u} F)
      (↥(⊤ : IntermediateField (ULift.{u} F) (Fx k F g)))
      (IntermediateField.topEquiv (F := ULift.{u} F) (E := Fx k F g)).symm.toAlgHom
  exact Algebra.IsSeparable.trans F (ULift.{u} F) (Fx k F g)

theorem ord_extendConstants {K K' L : Type*} [Field K] [Field K'] [Field L] [Algebra K K']
    [Algebra K' L] [Algebra K L] [IsScalarTower K K' L] [Algebra.IsIntegral K K']
    (w : Place K L) (f : L) : (Place.extendConstants K' w).ord f = w.ord f := rfl

end Construction

section Curve

variable (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F]
  [IsCurveOver k F] [Algebra.EssFiniteType k F] {g : k[X]}
  [Fact (Irreducible g)] [Fact (Irreducible (gF k F g))]

theorem curve_data (hg : g.Monic) :
    IsCurveOver k (Fx k F g) ∧ IsCurveOver (Kx k g) (Fx k F g) ∧
      Algebra.EssFiniteType (Kx k g) (Fx k F g) := by
  have hirr : Irreducible g := Fact.out
  haveI : Module.Finite k (Kx k g) := (AdjoinRoot.powerBasis hg.ne_zero).finite
  haveI : Algebra.IsIntegral k (Kx k g) := Algebra.IsIntegral.of_finite k _
  haveI : Finite (Kx k g) := finite_Kx k hg
  haveI : FiniteDimensional F (Fx k F g) := finiteDimensional_Fx k F hg
  haveI : Algebra.IsSeparable F (Fx k F g) :=
    isSeparable_Fx k F hg (PerfectField.separable_of_irreducible hirr)
  obtain ⟨t, ht, hfd, hsep⟩ :=
    (isCurveOver_iff_exists_transcendental_finiteDimensional (K := k) (F := F)).mp
      inferInstance
  set t' := algebraMap F (Fx k F g) t with ht'def
  have ht' : Transcendental k t' :=
    (transcendental_algebraMap_iff (algebraMap F (Fx k F g)).injective).mpr ht
  have ht'' : Transcendental (Kx k g) t' := fun halg =>
    ht' (isIntegral_trans _ halg.isIntegral).isAlgebraic
  obtain ⟨hfd₁, hsep₁⟩ := finite_and_separable_of_tower (F' := Fx k F g) (E := k⟮t'⟯) hfd hsep
    (((algebraMap F (Fx k F g)).comp (algebraMap k⟮t⟯ F)).codRestrict (k⟮t'⟯)
      (fun x => algebraMap_mem_adjoin k t x)) (fun _ => rfl)
  obtain ⟨hfd₂, hsep₂⟩ := finite_and_separable_of_tower (F' := Fx k F g) (E := (Kx k g)⟮t'⟯)
    hfd hsep
    (((algebraMap F (Fx k F g)).comp (algebraMap k⟮t⟯ F)).codRestrict ((Kx k g)⟮t'⟯)
      (fun x => algebraMap_mem_adjoin (Kx k g) t x)) (fun _ => rfl)
  haveI : Algebra.EssFiniteType k (Fx k F g) :=
    essFiniteType_of_transcendental_of_finiteDimensional ht' hfd₁
  have hess : Algebra.EssFiniteType (Kx k g) (Fx k F g) :=
    essFiniteType_of_transcendental_of_finiteDimensional ht'' hfd₂
  haveI := hess
  exact ⟨(isCurveOver_iff_exists_transcendental_finiteDimensional).mpr ⟨t', ht', hfd₁, hsep₁⟩,
    (isCurveOver_iff_exists_transcendental_finiteDimensional).mpr ⟨t', ht'', hfd₂, hsep₂⟩,
    hess⟩

omit [IsCurveOver k F] [Algebra.EssFiniteType k F] in

theorem isIntegral_of_ord_nonneg (hC : ConstantsAreBase k F) (hg : g.Monic)
    [IsCurveOver k (Fx k F g)] {z : Fx k F g} (hz0 : z ≠ 0)
    (hordk : ∀ w : Place k (Fx k F g), 0 ≤ w.ord z) : IsIntegral k z := by
  haveI : FiniteDimensional F (Fx k F g) := finiteDimensional_Fx k F hg
  haveI : Algebra.IsSeparable F (Fx k F g) :=
    isSeparable_Fx k F hg (PerfectField.separable_of_irreducible Fact.out)
  have hcoef : ∀ v : Place k F, ∀ n, (minpoly F z).coeff n ∈ v.toValuationSubring := by
    intro v n
    obtain ⟨c, hc⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg (F := F) (v := v)
      hz0 (fun w _ => hordk w)
    have hint : IsIntegral v.toValuationSubring z := by
      rw [← hc]
      exact c.2
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F hint, coeff_map]
    exact SetLike.coe_mem _
  have hlifts : minpoly F z ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    obtain ⟨c, hc⟩ := mem_range_of_forall_mem hC (fun v => hcoef v n)
    exact ⟨c, hc⟩
  obtain ⟨Q₀, hQ₀, -, hQ₀m⟩ :=
    lifts_and_natDegree_eq_and_monic hlifts (minpoly.monic (IsIntegral.of_finite F z))
  refine ⟨Q₀, hQ₀m, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F z Q₀, hQ₀]
  exact minpoly.aeval F z

theorem constantsAreBase (hC : ConstantsAreBase k F) (hg : g.Monic) :
    ConstantsAreBase (Kx k g) (Fx k F g) := by
  have hirr : Irreducible g := Fact.out
  obtain ⟨hC1, hC2, -⟩ := curve_data k F hg
  haveI := hC1
  haveI := hC2
  haveI : FiniteDimensional F (Fx k F g) := finiteDimensional_Fx k F hg
  haveI : Module.Finite k (Kx k g) := (AdjoinRoot.powerBasis hg.ne_zero).finite
  haveI : Algebra.IsIntegral k (Kx k g) := Algebra.IsIntegral.of_finite k _
  have hconst : ∀ y : F, IsIntegral k y → y ∈ (algebraMap k F).range :=
    fun y hy => mem_range_of_isIntegral hC hy
  refine le_antisymm ?_ ?_
  · intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact zero_mem _

    have hordk : ∀ w : Place k (Fx k F g), 0 ≤ w.ord z := by
      intro w
      rw [mem_lSpace_iff_ord] at hz
      rcases hz with h | h
      · exact absurd h hz0
      · have := h (Place.extendConstants (Kx k g) w)
        rw [ord_extendConstants] at this
        simpa using this

    have hzint : IsIntegral k z := isIntegral_of_ord_nonneg k F hC hg hz0 hordk

    have hzint' : IsIntegral (Kx k g) z := hzint.tower_top
    haveI : FiniteDimensional (Kx k g) (Kx k g)⟮z⟯ :=
      IntermediateField.adjoin.finiteDimensional hzint'
    haveI : IsScalarTower k (Kx k g)⟮z⟯ (Fx k F g) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite k (Kx k g)⟮z⟯ := Module.Finite.trans (Kx k g) _
    haveI : Algebra.IsSeparable k (Kx k g)⟮z⟯ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨β, hβ⟩ := Field.exists_primitive_element k (Kx k g)⟮z⟯
    have hβdeg : (minpoly k β).natDegree = Module.finrank k (Kx k g)⟮z⟯ :=
      (Field.primitive_element_iff_minpoly_natDegree_eq k β).mp hβ
    set β' : Fx k F g := algebraMap ((Kx k g)⟮z⟯) (Fx k F g) β with hβ'def
    have hβ'int : IsIntegral k β' := (IsIntegral.of_finite k β).algebraMap
    have h1 : minpoly k β' = minpoly k β :=
      minpoly.algebraMap_eq (algebraMap ((Kx k g)⟮z⟯) (Fx k F g)).injective β
    have h2 : minpoly F β' = (minpoly k β').map (algebraMap k F) := minpoly_eq_map hconst hβ'int
    have h3 : (minpoly F β').natDegree ≤ Module.finrank F (Fx k F g) := by
      rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite F β')]
      exact LinearMap.finrank_le_finrank_of_injective (f := (F⟮β'⟯).val.toLinearMap)
        (fun a b h => Subtype.ext h)
    have hup : Module.finrank k (Kx k g)⟮z⟯ ≤ g.natDegree := by
      rw [h2, natDegree_map, h1, hβdeg, finrank_Fx k F hg] at h3
      exact h3
    set φ := (IsScalarTower.toAlgHom k (Kx k g) (Kx k g)⟮z⟯).toLinearMap with hφdef
    have hφinj : Function.Injective φ := (algebraMap (Kx k g) (Kx k g)⟮z⟯).injective
    have hlow : g.natDegree ≤ Module.finrank k (Kx k g)⟮z⟯ := by
      rw [← finrank_Kx k hg]
      exact LinearMap.finrank_le_finrank_of_injective hφinj
    have heq : Module.finrank k (Kx k g) = Module.finrank k (Kx k g)⟮z⟯ := by
      rw [finrank_Kx k hg]
      exact le_antisymm hlow hup
    have hsurj : Function.Surjective φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hφinj
    obtain ⟨c, hc⟩ := hsurj ⟨z, IntermediateField.mem_adjoin_simple_self _ z⟩
    refine ⟨c, ?_⟩
    have hc' : ((φ c : (Kx k g)⟮z⟯) : Fx k F g) = z := by rw [hc]
    rw [← hc']
    change algebraMap (Kx k g) (Fx k F g) c = _
    rw [IsScalarTower.algebraMap_apply (Kx k g) ((Kx k g)⟮z⟯) (Fx k F g) c]
    rfl
  · rintro z ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c

end Curve

end ConstFieldExtOfFinite
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_constantFieldExtension_of_finite.AlgebraicCurve.ConstFieldExtOfFinite"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_constantFieldExtension_of_finite.AlgebraicCurve.ConstFieldExtOfFinite P2MW.S_AlgebraicCurve_exists_constantFieldExtension_of_finite.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_constantFieldExtension_of_finite.AlgebraicCurve.ConstFieldExtOfFinite P2MW.S_AlgebraicCurve_exists_constantFieldExtension_of_finite.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_constantFieldExtension_of_finite.AlgebraicCurve AlgebraicCurve.ConstFieldExtOfFinite in
universe u v in
theorem solution
    (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) (r : ℕ) (hr : 0 < r) :
    ∃ (k' : Type u) (F' : Type (max u v)) (_ : Field k') (_ : Finite k') (_ : Field F')
      (_ : Algebra k k') (_ : Algebra k' F') (_ : Algebra k F') (_ : Algebra F F')
      (_ : IsScalarTower k k' F') (_ : IsScalarTower k F F') (_ : FiniteDimensional F F')
      (_ : AlgebraicCurve.IsCurveOver k' F') (_ : Algebra.EssFiniteType k' F'),
      Module.finrank k k' = r ∧
        Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤ ∧
          AlgebraicCurve.ConstantsAreBase k' F' := by
  obtain ⟨g, hg, hirr, hdeg⟩ := exists_irreducible_natDegree_eq k r hr
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  have hconst : ∀ y : F, IsIntegral k y → y ∈ (algebraMap k F).range :=
    fun y hy => mem_range_of_isIntegral hC hy
  haveI : Fact (Irreducible (gF k F g)) := ⟨irreducible_gF k F hconst hg hirr⟩
  obtain ⟨-, hC2, hess⟩ := curve_data k F hg
  exact ⟨Kx k g, Fx k F g, inferInstance, finite_Kx k hg, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    finiteDimensional_Fx k F hg, hC2, hess, (finrank_Kx k hg).trans hdeg,
    adjoin_range_eq_top k F g, constantsAreBase k F hC hg⟩

end S_AlgebraicCurve_exists_constantFieldExtension_of_finite
end P2MW
export P2MW.S_AlgebraicCurve_exists_constantFieldExtension_of_finite (solution)
