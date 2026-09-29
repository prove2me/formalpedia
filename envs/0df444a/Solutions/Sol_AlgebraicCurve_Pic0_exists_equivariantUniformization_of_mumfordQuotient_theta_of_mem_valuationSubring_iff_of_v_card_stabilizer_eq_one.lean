-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/fbe42af9-9386-58b7-886e-cfb01bebaec8

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
import Theorems.Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_AlgebraicCurve_Pic0_exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient
import Theorems.Thm_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one
import Theorems.Thm_AlgebraicCurve_Pic0_periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqV AlgebraicCurve.TotallyDegenerateCovering.instFintypeV AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqE AlgebraicCurve.TotallyDegenerateCovering.instFintypeE"
p2m_attr_erase "simp" "ValuationSubring.ratCast_mem_ratClosure ValuationSubring.intCast_mem_ratClosure ValuationSubring.natCast_mem_ratClosure CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq CerednikDrinfeld.DegeneracyData.FiniteHom.comp_deg CerednikDrinfeld.DegeneracyData.FiniteHom.pullback_apply CerednikDrinfeld.DegeneracyData.FiniteHom.comp_mapE AlgebraicCurve.TotallyDegenerateCovering.Hom.mk.injEq CerednikDrinfeld.DegeneracyData.FiniteHom.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.FiniteHom.mk.injEq AlgebraicCurve.TotallyDegenerateCovering.Hom.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.FiniteHom.pullbackFun_apply CerednikDrinfeld.DegeneracyData.FiniteHom.pushforward_apply AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_b AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_w AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_a AlgebraicCurve.TotallyDegenerateCovering.mk.sizeOf_spec AlgebraicCurve.TotallyDegenerateCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

namespace ECOmega

theorem inv_of_pins

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
    (hQeq : ∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ x y : ↥(ribbonKernel D),
      s (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion) =
        (((Additive.toMul (P.Q (actZ σ x) (actZ σ y)) : (↥K)ˣ) : ↥K) : A.valuation.Completion))
    (heFeq : ∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ u : P.TorusPoints,
      eFull (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
        (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) :
          ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) u)) = ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion FC) (Pic0 A.valuation.Completion FC)).comp galFC) σ (eFull u)) :
      (∀ z : Pic0 A.valuation.Completion FC,
        (∀ τ : ↥(A.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → galFC (ι τ) • z = z) →
        ∃ u : P.TorusPoints,
          (∀ τ : ↥(A.decompositionSubgroup ℚ),
            (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
            ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = τ • c) → P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u) ∧
          eFull u = z) := by

  haveI : Fact (A.DecompositionIsometric ℚ) :=
    ⟨fun σ x => ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A σ.2 x⟩

  let 𝒰 : EquivariantUniformization r D A hA (Pic0 A.valuation.Completion FC) S scalar actZ
      ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion FC) (Pic0 A.valuation.Completion FC)).comp galFC) :=
    { K := K, ord := ord, ord_spec := hord, inertia_K := hinK, hensel_K := hhens, P := P, eFull := eFull,
      eFull_surjective := hsurj, eFull_ker := hker, Q_equiv := hQeq, eFull_equiv := heFeq }

  have hι_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → actZ (ι τ) = 1 := by
    intro τ hτ
    obtain ⟨-, hπE1, hsgn1⟩ := hπ_inertia τ hτ
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    funext e
    have := hactZ (ι τ) x e
    rw [hπE1, hsgn1, Equiv.Perm.one_apply, Units.val_one, one_mul] at this
    exact this
  intro z hz
  exact CerednikDrinfeld.Mumford.EquivariantUniformization.exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq
    𝒰 ι hι hι_inertia z (fun τ hτ => by
      show galFC (ι τ) • z = z
      exact hz τ hτ)

end ECOmega

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

    (htame : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) w) : ℕ) : A.valuation.Completion) = 1)

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
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e) :
    ∃ 𝒰 : EquivariantUniformization r D A hA (Pic0 A.valuation.Completion FC) S scalar actZ
        ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion FC) (Pic0 A.valuation.Completion FC)).comp galFC),

      (∀ z : Pic0 A.valuation.Completion FC,
        (∀ τ : ↥(A.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → galFC (ι τ) • z = z) →
        ∃ u : 𝒰.P.TorusPoints,
          (∀ τ : ↥(A.decompositionSubgroup ℚ),
            (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
            ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = τ • c) → 𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u) ∧
          𝒰.eFull u = z) ∧

      (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γ.map ρ),
          ((((Additive.toMul (𝒰.P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰.K)ˣ) : ↥𝒰.K) : A.valuation.Completion) * Omega.period (Γ.map ρ).subtype x y α β = 1) ∧

      (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰.P.TorusPoints), (∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC),
          (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt ⟨a, ha⟩) 1 - Finsupp.single (pt ⟨b, hb⟩) 1 →
          𝒰.eFull u = Pic0.mk Dv) := by
  have h1 := AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ Γ htp hfin FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ
  obtain ⟨K, ord, hord, hinK, hhens, P, hQ⟩ := h1
  have h2 := AlgebraicCurve.Pic0.exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ Γ htp hfin htame FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ K ord hord hinK hhens P hQ
  obtain ⟨eFull, hsurj, hker, hΘ⟩ := h2
  have h3 := AlgebraicCurve.Pic0.periodDatum_equivariant_of_theta_pinned_uniformization_of_mumfordQuotient A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ Γ htp hfin FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ K ord hord hinK hhens P hQ eFull hsurj hker hΘ
  obtain ⟨hQeq, heFeq⟩ := h3
  have h4 := ECOmega.inv_of_pins A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ Γ htp hfin FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ K ord hord hinK hhens P hQ eFull hsurj hker hQeq heFeq
  exact ⟨⟨K, ord, hord, hinK, hhens, P, eFull, hsurj, hker, hQeq, heFeq⟩, h4, hQ, hΘ⟩

end S_AlgebraicCurve_Pic0_exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_equivariantUniformization_of_mumfordQuotient_theta_of_mem_valuationSubring_iff_of_v_card_stabilizer_eq_one (solution)
