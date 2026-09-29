-- Prove2me | solution 1 for AlgebraicCurve.Pic0.periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4b1e9e74-1167-5254-b906-301f18d2bf00

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.GroupTheory.Abelianization.Defs
import Theorems.Thm_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Theorems.Thm_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Omega_theta_isometricAut
import Theorems.Thm_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_mulEquiv
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_isCurveOver_and_essFiniteType_intermediateField_of_transcendental_mem
import Theorems.Thm_AlgebraicCurve_exists_place_notMem_ord_neg_and_forall_ord_eq_one
import Theorems.Thm_CerednikDrinfeld_Omega_semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq
import Theorems.Thm_CerednikDrinfeld_Mumford_addMonoidHom_eq_of_apply_QL_eq_of_apply_eq_of_eq_pic0Mk_single_sub_single
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_theta_multiplier_and_torusPoint_apply_eq_of_mumfordQuotient
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqV AlgebraicCurve.TotallyDegenerateCovering.instFintypeV AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqE AlgebraicCurve.TotallyDegenerateCovering.instFintypeE"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq CerednikDrinfeld.DegeneracyData.FiniteHom.comp_deg CerednikDrinfeld.DegeneracyData.FiniteHom.pullback_apply CerednikDrinfeld.DegeneracyData.FiniteHom.comp_mapE AlgebraicCurve.TotallyDegenerateCovering.Hom.mk.injEq CerednikDrinfeld.DegeneracyData.FiniteHom.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.FiniteHom.mk.injEq AlgebraicCurve.TotallyDegenerateCovering.Hom.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.FiniteHom.pullbackFun_apply CerednikDrinfeld.DegeneracyData.FiniteHom.pushforward_apply AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_b AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_w AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_a AlgebraicCurve.TotallyDegenerateCovering.mk.sizeOf_spec AlgebraicCurve.TotallyDegenerateCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ValuationSubring.ratCast_mem_ratClosure ValuationSubring.intCast_mem_ratClosure ValuationSubring.natCast_mem_ratClosure LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

namespace S3

theorem pathCycle_apply_congr {G W : Type} [Group G] [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    [DecidableEq (QuotEdge G 𝒯)] {E E' : Type} (orb : E → QuotEdge G 𝒯) (orb' : E' → QuotEdge G 𝒯)
    (v₀ : W) (g : G) (e : E) (e' : E') (h : orb e = orb' e') :
    pathCycle 𝒯 orb v₀ g e = pathCycle 𝒯 orb' v₀ g e' := by
  unfold pathCycle
  by_cases hr : 𝒯.Reachable v₀ (g • v₀)
  · rw [dif_pos hr, dif_pos hr]
    simp only [walkCycle, h]
  · rw [dif_neg hr, dif_neg hr]
    rfl

def conjEquiv {P : Type} [Group P] (H : Subgroup P) (p : P)
    (h₁ : ∀ x : P, x ∈ H → p * x * p⁻¹ ∈ H) (h₂ : ∀ x : P, x ∈ H → p⁻¹ * x * p ∈ H) : ↥H ≃* ↥H where
  toFun x := ⟨p * x * p⁻¹, h₁ x x.2⟩
  invFun x := ⟨p⁻¹ * x * p, h₂ x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[scoped simp] theorem conjEquiv_coe {P : Type} [Group P] (H : Subgroup P) (p : P)
    (h₁ : ∀ x : P, x ∈ H → p * x * p⁻¹ ∈ H) (h₂ : ∀ x : P, x ∈ H → p⁻¹ * x * p ∈ H) (x : ↥H) :
    ((conjEquiv H p h₁ h₂ x : ↥H) : P) = p * x * p⁻¹ := rfl

theorem essFiniteType_of_top {K F : Type} [Field K] [Field F] [Algebra K F]
    (h : Algebra.EssFiniteType K (⊤ : IntermediateField K F)) : Algebra.EssFiniteType K F :=
  haveI := h
  Algebra.EssFiniteType.of_surjective (⊤ : IntermediateField K F).val (fun x => ⟨⟨x, IntermediateField.mem_top⟩, rfl⟩)

theorem unitsBaseChange_coe {K L : Type} [Field K] [Field L] [Algebra K L] (q : Additive Kˣ) :
    ((Additive.toMul (unitsBaseChange K L q) : Lˣ) : L) = algebraMap K L ((Additive.toMul q : Kˣ) : K) := rfl

theorem additive_units_ext {L : Type} [Monoid L] {a b : Additive Lˣ}
    (h : ((Additive.toMul a : Lˣ) : L) = ((Additive.toMul b : Lˣ) : L)) : a = b :=
  Additive.toMul.injective (Units.ext h)

end S3
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient.S3"

set_option maxHeartbeats 8000000 in
theorem S3.q_equiv

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (hϖr : Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ) = Valued.v ((r : ℕ) : A.valuation.Completion))

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    [DecidablePred (· ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))

    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (hfg : ∃ x : FC, Transcendental A.valuation.Completion x ∧ FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_onto : Function.Surjective pt)

    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (galFC : S →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_base : ∀ (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC σ) c = (scalar σ) • c)
    (hgal : ∀ σ : S, ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) ∧ (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))))
    (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hπV : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV σ (eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ σ e, D.w (πE σ e) = D.w e)
    (hsgn_pos : ∀ σ e, sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hsgn_neg : ∀ σ e, sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e))
    (hπ_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → πV (ι τ) = 1 ∧ πE (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)))
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e)
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (hord : ∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
    Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k)))
    (hinK : ∀ σ : ↥(A.decompositionSubgroup ℚ),
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
      ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion))
    (hhens : ∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord)
    (hQ : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γ.map ρ),
          ((((Additive.toMul (P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
              (↥K)ˣ) : ↥K) : A.valuation.Completion) * Omega.period (Γ.map ρ).subtype x y α β = 1))
    (eFull : P.TorusPoints →+ Pic0 A.valuation.Completion FC) (hsurj : Function.Surjective eFull)
    (hker : ∀ u : P.TorusPoints, eFull u = 0 ↔ u ∈ P.periodLattice)
    (hΘ : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : P.TorusPoints), (∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC),
          (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt ⟨a, ha⟩) 1 - Finsupp.single (pt ⟨b, hb⟩) 1 →
          eFull u = Pic0.mk Dv)) :
    (∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ x y : ↥(ribbonKernel D),
      s (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion) =
        (((Additive.toMul (P.Q (actZ σ x) (actZ σ y)) : (↥K)ˣ) : ↥K) : A.valuation.Completion)) := by
  intro σ s hs
  obtain ⟨n, t, hn, hreal⟩ := hgal σ

  have hst : ∀ c : A.valuation.Completion, s c = t.toRingEquiv c := by
    intro c
    have h := hreal (algebraMap A.valuation.Completion FC c)
    rw [SemilinearAut.smul_algebraMap, hgalFC_base, ← hs, AlgEquiv.commutes, AlgEquiv.commutes,
      Mumford.algebraMap_invariantFieldOf_coe, Mumford.algebraMap_invariantFieldOf_coe,
      Mumford.AmbientSemilinearAut.fracMap_algebraMap_const, Mumford.smul_algebraMap_const] at h
    exact (algebraMap A.valuation.Completion (FractionRing (Omega.HolRingOf ϖ ρ))).injective h

  have hT : (BruhatTits.tree R₀ K₀).IsTree := BruhatTits.tree_isTree R₀ K₀
  obtain ⟨hconn, hcol⟩ := BruhatTits.tree_connected_and_colorable_two R₀ K₀
  have hτ : ∀ (g : ↥(Γ.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) =
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
    fun g w => htp g.2 w
  have hadj : ∀ u v : LT.LatticeTree.Vertex R₀ K₀, (BruhatTits.tree R₀ K₀).Adj u v →
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) v := by
    intro u v huv h
    have h1 := (vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter (↥(Γ.map ρ))
      (BruhatTits.tree R₀ K₀) hconn hcol (LT.LatticeTree.stdVertex R₀ K₀)).1 u v huv
    rw [h] at h1
    have h2 : (1 : ZMod 2) = 0 := by
      have := congrArg (fun t => t - Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) v) h1
      simpa using this.symm
    exact absurd h2 (by decide)
  have ha' : ∀ e : E, eV.symm (D.a e) =
      Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eE.symm e).1.out.fst := by
    intro e; rw [Equiv.symm_apply_eq]; simpa using hDa (eE.symm e)
  have hb' : ∀ e : E, eV.symm (D.b e) =
      Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eE.symm e).1.out.snd := by
    intro e; rw [Equiv.symm_apply_eq]; simpa using hDb (eE.symm e)
  have hΦ' : ∀ g : ↥(Γ.map ρ), (Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) =
      Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e => (eE.symm e).1) v₀ g := by
    intro g; funext e
    have := hΦ g (eE.symm e)
    rw [Equiv.apply_symm_apply] at this
    rw [this]; exact S3.pathCycle_apply_congr _ _ _ v₀ g _ _ rfl
  have hBS :=
    surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle (G := ↥(Γ.map ρ))
      (BruhatTits.tree R₀ K₀) hT
      (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτ hadj
      D eE.symm eV.symm ha' hb' v₀ Φ hΦ'
  have hsurj : Function.Surjective Φ := hBS.1
  have hgen : ∀ x : ↥(ribbonKernel D), ∃ α : ↥(Γ.map ρ), Φ (Additive.ofMul (Abelianization.of α)) = x := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    obtain ⟨a, rfl⟩ : ∃ a : ↥(Γ.map ρ), Additive.ofMul (Abelianization.of a) = y :=
      QuotientGroup.mk_surjective (Additive.toMul y)
    exact ⟨a, rfl⟩

  have hAC : IsAlgClosed A.valuation.Completion :=
    ValuationSubring.isAlgClosed_completion_of_liesOverPrime r (Fact.out) A hA
  have hEFT : Algebra.EssFiniteType A.valuation.Completion FC := by
    haveI := hAC
    have h3 := AlgebraicCurve.isCurveOver_and_essFiniteType_intermediateField_of_transcendental_mem
      A.valuation.Completion FC (⊤ : IntermediateField A.valuation.Completion FC) hfg.choose IntermediateField.mem_top
      hfg.choose_spec.1 hfg
    exact S3.essFiniteType_of_top h3.2.1
  haveI hEFT' := hEFT

  have hP := AlgebraicCurve.exists_place_notMem_ord_neg_and_forall_ord_eq_one
    (K := A.valuation.Completion) (F := FC) (∅ : Finset (Place A.valuation.Completion FC))
  obtain ⟨P₀, hP₀rest⟩ := hP
  have hP' := AlgebraicCurve.exists_place_notMem_ord_neg_and_forall_ord_eq_one
    (K := A.valuation.Completion) (F := FC) ({P₀} : Finset (Place A.valuation.Completion FC))
  obtain ⟨P₁, xP₁, hP₁, hP₁rest⟩ := hP'
  have hz₀' := hpt_onto P₀
  obtain ⟨z₀, hz₀⟩ := hz₀'
  have hz₁' := hpt_onto P₁
  obtain ⟨z₁, hz₁⟩ := hz₁'
  have hne : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (z₀ : A.valuation.Completion) ≠ (z₁ : A.valuation.Completion) := by
    intro γ h
    apply hP₁
    rw [Finset.mem_singleton, ← hz₁, ← hz₀]
    refine ((hpt_fib z₀ z₁).2 ⟨γ, Subtype.ext ?_⟩).symm
    rw [Omega.coe_smul_upperHalfPlane]; exact h.symm

  have h₁ : ∀ x : PGL(2, K₀), x ∈ Γ.map ρ → ρ n * x * (ρ n)⁻¹ ∈ Γ.map ρ := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨n * m * n⁻¹, (hn m).1 hm, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have h₂ : ∀ x : PGL(2, K₀), x ∈ Γ.map ρ → (ρ n)⁻¹ * x * ρ n ∈ Γ.map ρ := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨n⁻¹ * m * n, (hn (n⁻¹ * m * n)).2 (by simpa [mul_assoc] using hm), ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hφ : ∀ g : ↥(Γ.map ρ), (Γ.map ρ).subtype (S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂ g) =
      ρ n * (Γ.map ρ).subtype g * (ρ n)⁻¹ := fun g => rfl

  have hnat : ∀ γ : ↥(Γ.map ρ), Φ (Additive.ofMul (Abelianization.of (S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂ γ))) =
      actZ σ (Φ (Additive.ofMul (Abelianization.of γ))) :=
    fun γ => apply_conj_eq_actZ_apply_of_apply_eq_pathCycle K₀ R₀ G ρ Γ htp E V D eE v₀ Φ hΦ n hn (πE σ) (sgn σ)
      (hπE σ n t hn hreal) (actZ σ) (hactZ σ) γ (S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂ γ) rfl

  have htz₀ : t.toRingEquiv (z₀ : A.valuation.Completion) ∈ Omega.upperHalfPlane K₀ A.valuation.Completion :=
    t.mapsTo_upperHalfPlane z₀.2
  have htz₁ : t.toRingEquiv (z₁ : A.valuation.Completion) ∈ Omega.upperHalfPlane K₀ A.valuation.Completion :=
    t.mapsTo_upperHalfPlane z₁.2
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion),
      w₀ = (ρ n) • ⟨t.toRingEquiv (z₀ : A.valuation.Completion), htz₀⟩ := ⟨_, rfl⟩
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion),
      w₁ = (ρ n) • ⟨t.toRingEquiv (z₁ : A.valuation.Completion), htz₁⟩ := ⟨_, rfl⟩
  have hw₀c : (w₀ : A.valuation.Completion) = Omega.pmoebius K₀ (ρ n) (t.toRingEquiv (z₀ : A.valuation.Completion)) := by
    rw [hw₀, Omega.coe_smul_upperHalfPlane]
  have hw₁c : (w₁ : A.valuation.Completion) = Omega.pmoebius K₀ (ρ n) (t.toRingEquiv (z₁ : A.valuation.Completion)) := by
    rw [hw₁, Omega.coe_smul_upperHalfPlane]
  have hne' : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (w₀ : A.valuation.Completion) ≠ (w₁ : A.valuation.Completion) := by
    intro γ h
    apply hne ((S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂).symm γ)
    rw [hw₀c, hw₁c, ← Omega.pmoebius_mul K₀ htz₀] at h
    have h' : Omega.pmoebius K₀ ((ρ n)⁻¹ * ((γ : PGL(2, K₀)) * ρ n)) (t.toRingEquiv (z₀ : A.valuation.Completion)) =
        t.toRingEquiv (z₁ : A.valuation.Completion) := by
      rw [Omega.pmoebius_mul K₀ htz₀, h, ← Omega.pmoebius_mul K₀ htz₁, inv_mul_cancel, Omega.pmoebius_one]
    have h'' : t.toRingEquiv (Omega.pmoebius K₀ (((S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂).symm γ : ↥(Γ.map ρ)) : PGL(2, K₀))
        (z₀ : A.valuation.Completion)) = t.toRingEquiv (z₁ : A.valuation.Completion) := by
      rw [t.comm_pmoebius _ z₀.2, ← h']
      show Omega.pmoebius K₀ ((ρ n)⁻¹ * (γ : PGL(2, K₀)) * ρ n) _ = _
      rw [mul_assoc]
    exact t.toRingEquiv.injective h''

  intro x y
  have hxα' := hgen x
  obtain ⟨α, hxα⟩ := hxα'
  have hyβ' := hgen y
  obtain ⟨β, hyβ⟩ := hyβ'
  rw [← hxα, ← hyβ]
  have hQ0 := hQ z₀ z₁ z₀.2 z₁.2 hne α β
  have hQ1 := hQ w₀ w₁ w₀.2 w₁.2 hne' (S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂ α) (S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂ β)
  rw [hnat α, hnat β] at hQ1

  have hper : Omega.period (Γ.map ρ).subtype (w₀ : A.valuation.Completion) (w₁ : A.valuation.Completion)
      (S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂ α) (S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂ β) =
      t.toRingEquiv (Omega.period (Γ.map ρ).subtype (z₀ : A.valuation.Completion) (z₁ : A.valuation.Completion) α β) := by
    rw [hw₀c, hw₁c, Omega.period_pmoebius_pmoebius_mulEquiv (Γ.map ρ).subtype (S3.conjEquiv (Γ.map ρ) (ρ n) h₁ h₂) (ρ n)
      hφ htz₀ htz₁ α β]
    unfold Omega.period
    rw [show Omega.pmoebius K₀ ((Γ.map ρ).subtype α) (t.toRingEquiv (z₀ : A.valuation.Completion)) =
        t.toRingEquiv (Omega.pmoebius K₀ ((Γ.map ρ).subtype α) (z₀ : A.valuation.Completion)) from (t.comm_pmoebius _ z₀.2).symm,
      show Omega.pmoebius K₀ ((Γ.map ρ).subtype β) (t.toRingEquiv (z₁ : A.valuation.Completion)) =
        t.toRingEquiv (Omega.pmoebius K₀ ((Γ.map ρ).subtype β) (z₁ : A.valuation.Completion)) from (t.comm_pmoebius _ z₁.2).symm]
    exact Omega.theta_isometricAut (Γ.map ρ).subtype t z₀.2 (Omega.pmoebius_mem_upperHalfPlane K₀ z₀.2 _) z₁.2
      (Omega.pmoebius_mem_upperHalfPlane K₀ z₁.2 _)
  rw [hper, ← hst] at hQ1

  have hsQ0 := congrArg s hQ0
  rw [map_mul, map_one] at hsQ0
  have key : ∀ a₀ a₁ c₀ : A.valuation.Completion, a₀ * c₀ = 1 → a₁ * c₀ = 1 → a₀ = a₁ := by
    intro a₀ a₁ c₀ h0 h1
    calc a₀ = a₀ * (a₁ * c₀) := by rw [h1, mul_one]
      _ = a₁ * (a₀ * c₀) := by ring
      _ = a₁ := by rw [h0, mul_one]
  exact key _ _ _ hsQ0 hQ1

set_option maxHeartbeats 8000000 in
theorem S3.eFull_equiv

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (hϖr : Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ) = Valued.v ((r : ℕ) : A.valuation.Completion))

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    [DecidablePred (· ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))

    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (hfg : ∃ x : FC, Transcendental A.valuation.Completion x ∧ FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_onto : Function.Surjective pt)

    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (galFC : S →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_base : ∀ (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC σ) c = (scalar σ) • c)
    (hgal : ∀ σ : S, ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) ∧ (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))))
    (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hπV : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV σ (eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ σ e, D.w (πE σ e) = D.w e)
    (hsgn_pos : ∀ σ e, sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hsgn_neg : ∀ σ e, sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e))
    (hπ_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → πV (ι τ) = 1 ∧ πE (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)))
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e)
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (hord : ∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
    Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k)))
    (hinK : ∀ σ : ↥(A.decompositionSubgroup ℚ),
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
      ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion))
    (hhens : ∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord)
    (hQ : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γ.map ρ),
          ((((Additive.toMul (P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
              (↥K)ˣ) : ↥K) : A.valuation.Completion) * Omega.period (Γ.map ρ).subtype x y α β = 1))
    (eFull : P.TorusPoints →+ Pic0 A.valuation.Completion FC) (hsurj : Function.Surjective eFull)
    (hker : ∀ u : P.TorusPoints, eFull u = 0 ↔ u ∈ P.periodLattice)
    (hΘ : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : P.TorusPoints), (∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC),
          (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt ⟨a, ha⟩) 1 - Finsupp.single (pt ⟨b, hb⟩) 1 →
          eFull u = Pic0.mk Dv))
    (hQσ : (∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ x y : ↥(ribbonKernel D),
      s (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion) =
        (((Additive.toMul (P.Q (actZ σ x) (actZ σ y)) : (↥K)ˣ) : ↥K) : A.valuation.Completion))) :
    (∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ u : P.TorusPoints,
      eFull (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
        (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) :
          ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) u)) = ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion FC) (Pic0 A.valuation.Completion FC)).comp galFC) σ (eFull u)) := by
  intro σ s hs u
  obtain ⟨n, t, hn, hreal⟩ := hgal σ

  have hL : ∃ L : P.TorusPoints →+ Pic0 A.valuation.Completion FC, ∀ v : P.TorusPoints,
      L v = eFull (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
        (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) v)) :=
    ⟨eFull.comp (((P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)).comp
      (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)))).toAddMonoidHom),
      fun v => rfl⟩
  obtain ⟨L, hLv⟩ := hL
  have hR : ∃ R : P.TorusPoints →+ Pic0 A.valuation.Completion FC, ∀ v : P.TorusPoints, R v = galFC σ • eFull v :=
    ⟨(DistribMulAction.toAddMonoidHom (Pic0 A.valuation.Completion FC) (galFC σ)).comp eFull, fun v => rfl⟩
  obtain ⟨R, hRv⟩ := hR
  suffices hLR : L = R by
    have := congrArg (fun f : P.TorusPoints →+ Pic0 A.valuation.Completion FC => f u) hLR
    simp only [hLv, hRv] at this
    exact this

  have hΛ : ∀ z : ↥(ribbonKernel D), L (P.QL z) = R (P.QL z) := by
    intro z
    have hmem : P.QL (actZ σ z) ∈ P.periodLattice := LinearMap.mem_range_self _ _
    have hmem0 : P.QL z ∈ P.periodLattice := LinearMap.mem_range_self _ _
    have hq : P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
        (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) (P.QL z)) =
        P.QL (actZ σ z) := by
      refine LinearMap.ext fun x => S3.additive_units_ext ?_
      rw [PeriodDatum.coeffMap_apply, PeriodDatum.precomp_apply, PeriodDatum.QL_apply, PeriodDatum.QL_apply,
        toMul_ofMul, Units.coe_map, S3.unitsBaseChange_coe, S3.unitsBaseChange_coe, MonoidHom.coe_coe]
      have h := hQσ σ s hs z (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) x)
      rw [show actZ σ (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) x) = x from
        LinearEquiv.apply_symm_apply (actZ σ) x] at h
      exact h
    rw [hLv, hRv, hq, (hker _).2 hmem, (hker _).2 hmem0, ← Pic0.mk_zero, SemilinearAut.pic0_smul_mk, map_zero]

  have hdiff : ∀ (v : P.TorusPoints) (a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion))
      (Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC)),
      (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt a) 1 - Finsupp.single (pt b) 1 →
      eFull v = Pic0.mk Dv → L v = R v := by
    intro v a b Dv hDv hv

    obtain ⟨z₀, hz₀, hz₀a, hz₀b, c, hc, u₀, hu₀⟩ :=
      exists_theta_multiplier_and_torusPoint_apply_eq_of_mumfordQuotient A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ
        hex hϖr G ρ Γ htp hfin FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt K ord P
        (a : A.valuation.Completion) (b : A.valuation.Completion) a.2 b.2
    have hu₀v : eFull u₀ = Pic0.mk Dv :=
      hΘ a b z₀ a.2 b.2 hz₀ hz₀a hz₀b c hc u₀ hu₀ Dv (by simpa using hDv)

    have hker0 : eFull (v - u₀) = 0 := by rw [map_sub, hv, hu₀v, sub_self]
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 ((hker _).1 hker0)
    have hvz : v = u₀ + P.QL z := by rw [hz]; abel

    obtain ⟨ha', hb', hz₀', hz₀a', hz₀b', c', hc', hu₀'⟩ :=
      exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr
        G ρ Γ htp hfin FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal
        πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ K ord P σ s hs n t hn hreal
        (a : A.valuation.Completion) (b : A.valuation.Completion) z₀ a.2 b.2 hz₀ hz₀a hz₀b c hc u₀ hu₀

    have hpa : galFC σ • pt a = pt ⟨Omega.pmoebius K₀ (ρ n) (t.toRingEquiv (a : A.valuation.Completion)), ha'⟩ := by
      rw [semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff A K₀ ϖ G ρ Γ FC eFC pt hpt.1 (galFC σ) n t hreal a]
      try exact congrArg pt (Subtype.ext (Omega.coe_smul_upperHalfPlane _ _))
    have hpb : galFC σ • pt b = pt ⟨Omega.pmoebius K₀ (ρ n) (t.toRingEquiv (b : A.valuation.Completion)), hb'⟩ := by
      rw [semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff A K₀ ϖ G ρ Γ FC eFC pt hpt.1 (galFC σ) n t hreal b]
      try exact congrArg pt (Subtype.ext (Omega.coe_smul_upperHalfPlane _ _))
    have hDv' : ((SemilinearAut.degZeroSMulHom (galFC σ) Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC)) :
        Divisor A.valuation.Completion FC) =
        Finsupp.single (pt ⟨Omega.pmoebius K₀ (ρ n) (t.toRingEquiv (a : A.valuation.Completion)), ha'⟩) 1 -
          Finsupp.single (pt ⟨Omega.pmoebius K₀ (ρ n) (t.toRingEquiv (b : A.valuation.Completion)), hb'⟩) 1 := by
      rw [SemilinearAut.coe_degZeroSMulHom, hDv, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single, hpa, hpb]
    have hLu₀ : L u₀ = R u₀ := by
      rw [hLv, hRv, hu₀v, SemilinearAut.pic0_smul_mk]
      exact hΘ _ _ _ ha' hb' hz₀' hz₀a' hz₀b' c' hc' _ hu₀' _ hDv'
    rw [hvz, map_add, map_add, hLu₀, hΛ z]
  exact addMonoidHom_eq_of_apply_QL_eq_of_apply_eq_of_eq_pic0Mk_single_sub_single A hA K₀ FC E V D pt hpt_onto K ord P
    eFull hsurj hker (Pic0 A.valuation.Completion FC) L R hΛ hdiff

set_option maxHeartbeats 8000000 in
theorem solution

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (hϖr : Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ) = Valued.v ((r : ℕ) : A.valuation.Completion))

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    [DecidablePred (· ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))

    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (hfg : ∃ x : FC, Transcendental A.valuation.Completion x ∧ FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_onto : Function.Surjective pt)

    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (galFC : S →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_base : ∀ (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC σ) c = (scalar σ) • c)
    (hgal : ∀ σ : S, ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) ∧ (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))))
    (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hπV : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV σ (eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ σ e, D.w (πE σ e) = D.w e)
    (hsgn_pos : ∀ σ e, sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hsgn_neg : ∀ σ e, sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e))
    (hπ_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → πV (ι τ) = 1 ∧ πE (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)))
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e)
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (hord : ∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
    Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k)))
    (hinK : ∀ σ : ↥(A.decompositionSubgroup ℚ),
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
      ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion))
    (hhens : ∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord)
    (hQ : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γ.map ρ),
          ((((Additive.toMul (P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
              (↥K)ˣ) : ↥K) : A.valuation.Completion) * Omega.period (Γ.map ρ).subtype x y α β = 1))
    (eFull : P.TorusPoints →+ Pic0 A.valuation.Completion FC) (hsurj : Function.Surjective eFull)
    (hker : ∀ u : P.TorusPoints, eFull u = 0 ↔ u ∈ P.periodLattice)
    (hΘ : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : P.TorusPoints), (∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC),
          (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt ⟨a, ha⟩) 1 - Finsupp.single (pt ⟨b, hb⟩) 1 →
          eFull u = Pic0.mk Dv)) :
    (∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ x y : ↥(ribbonKernel D),
      s (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion) =
        (((Additive.toMul (P.Q (actZ σ x) (actZ σ y)) : (↥K)ˣ) : ↥K) : A.valuation.Completion)) ∧
    (∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ u : P.TorusPoints,
      eFull (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
        (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) :
          ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) u)) = ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion FC) (Pic0 A.valuation.Completion FC)).comp galFC) σ (eFull u)) := by
  have h1 := S3.q_equiv A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ Γ htp hfin FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ K ord hord hinK hhens P hQ eFull hsurj hker hΘ
  exact ⟨h1, S3.eFull_equiv A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ Γ htp hfin FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ K ord hord hinK hhens P hQ eFull hsurj hker hΘ h1⟩

end S_AlgebraicCurve_Pic0_periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient (solution)
