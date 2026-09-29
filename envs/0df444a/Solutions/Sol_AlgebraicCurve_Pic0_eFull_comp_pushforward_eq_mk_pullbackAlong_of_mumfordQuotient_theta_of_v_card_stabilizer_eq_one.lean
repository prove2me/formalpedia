-- Prove2me | solution 1 for AlgebraicCurve.Pic0.eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3ea083b3-b069-5b02-96d9-550e19b13140

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.GroupTheory.Abelianization.Defs
import Theorems.Thm_AlgebraicCurve_Divisor_degZero_le_closure_single_sub_single_of_surjective
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_comp_pushforward_mem_periodLattice_of_forall_eq
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_Pic0_exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation Valuation.algebraCompletion Valuation.uniformContinuousConstSMul_withVal Valuation.continuousConstSMul_withVal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq Valuation.algebraMap_completion_apply ValuationSubring.ratCast_mem_ratClosure ValuationSubring.intCast_mem_ratClosure ValuationSubring.natCast_mem_ratClosure CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_AlgebraicCurve_Pic0_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one.CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.PseudoUniformizer Omega.IsExhausted Omega.holRing Omega.HolRingOf Omega.pmoebius Omega.upperHalfPlane Omega.theta Omega.period Mumford.invariantFieldOf Mumford.vertexType Mumford.typePreserving tree BruhatTits.tree Mumford.GraphAction Mumford.QuotEdge Mumford.QuotVert Mumford.PeriodDatum Mumford.PeriodDatum.QL_apply DegeneracyData pushforward ribbonKernel Mumford.pathCycle Mumford.PeriodDatum.comp_pushforward_mem_periodLattice_of_forall_eq"
namespace SqGlueC
p2m_open "CerednikDrinfeld"

open CerednikDrinfeld.Mumford.PeriodDatum in

theorem comp_mem_periodLattice_of_proj
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [DecidableEq V₁] [Fintype E₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂}
    {L : Type} [Field L] [Algebra ℚ L] (K₁ K₂ : IntermediateField ℚ L)
    {ord₁ : Additive (↥K₁)ˣ →+ ℤ} {ord₂ : Additive (↥K₂)ˣ →+ ℤ}
    (P₁ : Mumford.PeriodDatum D₁ ↥K₁ L ord₁) (P₂ : Mumford.PeriodDatum D₂ ↥K₂ L ord₂)
    (pull : ↥(ribbonKernel D₂) →ₗ[ℤ] ↥(ribbonKernel D₁)) (push : ↥(ribbonKernel D₁) →ₗ[ℤ] ↥(ribbonKernel D₂))
    (hproj : ∀ (x : ↥(ribbonKernel D₂)) (y : ↥(ribbonKernel D₁)),
      ((((Additive.toMul (P₁.Q (pull x) y)) : (↥K₁)ˣ) : ↥K₁) : L) = ((((Additive.toMul (P₂.Q x (push y))) : (↥K₂)ˣ) : ↥K₂) : L))
    (u : P₁.TorusPoints) (hu : u ∈ P₁.periodLattice) : u.comp pull ∈ P₂.periodLattice := by
  obtain ⟨x₁, rfl⟩ := hu
  refine ⟨push x₁, ?_⟩
  ext y
  rw [LinearMap.comp_apply, Mumford.PeriodDatum.QL_apply, Mumford.PeriodDatum.QL_apply, P₁.Q_symm, P₂.Q_symm]
  exact (hproj y x₁).symm

theorem square_of_generators
    {M U₁ U₂ T₁ T₂ Z₂ : Type} [AddCommGroup M] [AddCommGroup U₁] [AddCommGroup U₂] [AddCommGroup T₁] [AddCommGroup T₂]
    [AddCommGroup Z₂] (Z : AddSubgroup M)
    (mk₁ : ↥Z →+ T₁) (ψ : ↥Z →+ Z₂) (mk₂ : Z₂ →+ T₂)
    (e₁ : U₁ →+ T₁) (he₁ : Function.Surjective e₁) (Λ₁ : AddSubgroup U₁) (hker₁ : ∀ u, e₁ u = 0 ↔ u ∈ Λ₁)
    (e₂ : U₂ →+ T₂) (N : U₁ →+ U₂) (hN : ∀ u ∈ Λ₁, e₂ (N u) = 0)
    (S : Set M) (hS : ∀ s ∈ S, ∃ hs : s ∈ Z, ∃ w₀ : U₁, e₁ w₀ = mk₁ ⟨s, hs⟩ ∧ e₂ (N w₀) = mk₂ (ψ ⟨s, hs⟩))
    (D : ↥Z) (hD : (D : M) ∈ AddSubgroup.closure S) (w : U₁) (hw : e₁ w = mk₁ D) : e₂ (N w) = mk₂ (ψ D) := by

  have hlift : ∀ (D : ↥Z) (w₀ : U₁), e₁ w₀ = mk₁ D → e₂ (N w₀) = mk₂ (ψ D) →
      ∀ w : U₁, e₁ w = mk₁ D → e₂ (N w) = mk₂ (ψ D) := by
    intro D w₀ h₀ h₀' w hw
    have hk : w - w₀ ∈ Λ₁ := (hker₁ _).1 (by rw [map_sub, hw, h₀, sub_self])
    have := hN _ hk
    rw [map_sub, map_sub, sub_eq_zero] at this
    rw [this, h₀']

  let P : M → Prop := fun x => ∃ hx : x ∈ Z, ∀ w : U₁, e₁ w = mk₁ ⟨x, hx⟩ → e₂ (N w) = mk₂ (ψ ⟨x, hx⟩)
  have hP : P (D : M) := by
    refine AddSubgroup.closure_induction (p := fun x _ => P x) ?_ ?_ ?_ ?_ hD
    · intro s hs
      obtain ⟨hsZ, w₀, h₀, h₀'⟩ := hS s hs
      exact ⟨hsZ, hlift _ w₀ h₀ h₀'⟩
    · refine ⟨Z.zero_mem, fun w hw => ?_⟩
      have h0 : (⟨0, Z.zero_mem⟩ : ↥Z) = 0 := rfl
      rw [h0, map_zero] at hw
      rw [h0, map_zero, map_zero]
      have := hN _ ((hker₁ _).1 hw)
      exact this
    · rintro x y _ _ ⟨hx, hPx⟩ ⟨hy, hPy⟩
      refine ⟨Z.add_mem hx hy, fun w hw => ?_⟩
      obtain ⟨w₁, hw₁⟩ := he₁ (mk₁ ⟨x, hx⟩)
      have hxy : (⟨x + y, Z.add_mem hx hy⟩ : ↥Z) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      have hw₂ : e₁ (w - w₁) = mk₁ ⟨y, hy⟩ := by
        rw [map_sub, hw, hw₁, hxy, map_add, add_sub_cancel_left]
      have e1' := hPx w₁ hw₁
      have e2' := hPy (w - w₁) hw₂
      have hsplit : w = w₁ + (w - w₁) := by rw [add_sub_cancel]
      rw [hsplit, map_add, map_add, e1', e2', hxy, map_add, map_add]
    · rintro x _ ⟨hx, hPx⟩
      refine ⟨Z.neg_mem hx, fun w hw => ?_⟩
      have hnx : (⟨-x, Z.neg_mem hx⟩ : ↥Z) = -⟨x, hx⟩ := rfl
      have hw' : e₁ (-w) = mk₁ ⟨x, hx⟩ := by rw [map_neg, hw, hnx, map_neg, neg_neg]
      have e1' := hPx (-w) hw'
      rw [map_neg, map_neg, neg_eq_iff_eq_neg] at e1'
      rw [e1', hnx, map_neg, map_neg]
  obtain ⟨hx, hPx⟩ := hP
  exact hPx w hw

theorem deg_eq_one_of_isAlgClosed {K F : Type} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (v : Place K F) : v.deg = 1 := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  have e : K ≃ₐ[K] v.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) IsAlgClosed.algebraMap_bijective_of_isIntegral
  unfold Place.deg
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

end CerednikDrinfeld.SqGlueC

set_option maxHeartbeats 4000000 in

theorem solution

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)

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
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)

    (Γd : Subgroup G) (htpd : Γd.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfind : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γd.map ρ)) d))

    (htamed : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer ↥(Γd.map ρ) w) : ℕ) : A.valuation.Completion) = 1)

    (Fd : Type) [Field Fd] [Algebra A.valuation.Completion Fd] [hcurved : IsCurveOver A.valuation.Completion Fd]
    (eFd : Fd ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd))

    (Ed Vd : Type) [Fintype Ed] [Fintype Vd] [DecidableEq Ed] [DecidableEq Vd]
    (Dd : DegeneracyData Ed Vd)
    (eVd : Mumford.QuotVert ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vd)
    (eEd : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ed)
    (hDad : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.a (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dd.b (eEd e) = eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDwd : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dd.w (eEd e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γd.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀))]
    (Φd : Additive (Abelianization ↥(Γd.map ρ)) →+ ↥(ribbonKernel Dd))
    (hΦd : ∀ γ : ↥(Γd.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φd (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dd)) : Ed → ℤ) (eEd e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (ptd : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion Fd)
    (hpt_fibd : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), ptd z = ptd z' ↔ ∃ γ : ↥(Γd.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_ontod : Function.Surjective ptd)

    (hptd : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : Fd),
        x ∈ (ptd z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFd x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (ptd z).evalAt (eFd.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFd.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (ptd z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (Γc : Subgroup G) (htpc : Γc.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfinc : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γc.map ρ)) d))

    (htamec : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer ↥(Γc.map ρ) w) : ℕ) : A.valuation.Completion) = 1)

    (Fc : Type) [Field Fc] [Algebra A.valuation.Completion Fc] [hcurvec : IsCurveOver A.valuation.Completion Fc]
    (eFc : Fc ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc))

    (Ec Vc : Type) [Fintype Ec] [Fintype Vc] [DecidableEq Ec] [DecidableEq Vc]
    (Dc : DegeneracyData Ec Vc)
    (eVc : Mumford.QuotVert ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ Vc)
    (eEc : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ Ec)
    (hDac : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.a (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDbc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, Dc.b (eEc e) = eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDwc : ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (Dc.w (eEc e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γc.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀))]
    (Φc : Additive (Abelianization ↥(Γc.map ρ)) →+ ↥(ribbonKernel Dc))
    (hΦc : ∀ γ : ↥(Γc.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φc (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel Dc)) : Ec → ℤ) (eEc e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (ptc : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion Fc)
    (hpt_fibc : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), ptc z = ptc z' ↔ ∃ γ : ↥(Γc.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_ontoc : Function.Surjective ptc)

    (hptc : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : Fc),
        x ∈ (ptc z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFc x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (ptc z).evalAt (eFc.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFc.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (ptc z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (actZd : S →* (↥(ribbonKernel Dd) ≃ₗ[ℤ] ↥(ribbonKernel Dd))) (gald : S →* SemilinearAut A.valuation.Completion Fd)
    (actZc : S →* (↥(ribbonKernel Dc) ≃ₗ[ℤ] ↥(ribbonKernel Dc))) (galc : S →* SemilinearAut A.valuation.Completion Fc)
    (𝒰d : EquivariantUniformization r Dd A hA (Pic0 A.valuation.Completion Fd) S scalar actZd
      ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion Fd) (Pic0 A.valuation.Completion Fd)).comp gald))
    (𝒰c : EquivariantUniformization r Dc A hA (Pic0 A.valuation.Completion Fc) S scalar actZc
      ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion Fc) (Pic0 A.valuation.Completion Fc)).comp galc))
    (hQd : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γd.map ρ),
          ((((Additive.toMul (𝒰d.P.Q (Φd (Additive.ofMul (Abelianization.of α))) (Φd (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion) * Omega.period (Γd.map ρ).subtype x y α β = 1))
    (hΘd : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γd.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γd.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γd.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γd.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰d.P.TorusPoints), (∀ γ : ↥(Γd.map ρ), u (Φd (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fd),
          (Dv : Divisor A.valuation.Completion Fd) = Finsupp.single (ptd ⟨a, ha⟩) 1 - Finsupp.single (ptd ⟨b, hb⟩) 1 →
          𝒰d.eFull u = Pic0.mk Dv))
    (hQc : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γc.map ρ),
          ((((Additive.toMul (𝒰c.P.Q (Φc (Additive.ofMul (Abelianization.of α))) (Φc (Additive.ofMul (Abelianization.of β))))) :
              (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion) * Omega.period (Γc.map ρ).subtype x y α β = 1))
    (hΘc : (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γc.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γc.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γc.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γc.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : 𝒰c.P.TorusPoints), (∀ γ : ↥(Γc.map ρ), u (Φc (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := Fc),
          (Dv : Divisor A.valuation.Completion Fc) = Finsupp.single (ptc ⟨a, ha⟩) 1 - Finsupp.single (ptc ⟨b, hb⟩) 1 →
          𝒰c.eFull u = Pic0.mk Dv))

    (g : G) (hg : ρ g ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) (hArr : Γd ≤ Γc.map (MulAut.conj g).toMonoidHom)
    (φ : Fc →ₐ[A.valuation.Completion] Fd)
    (hφ : ∀ x : Fc, ((eFd (φ x) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γd)) : FractionRing (Omega.HolRingOf ϖ ρ)) =
      g • ((eFc x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γc)) : FractionRing (Omega.HolRingOf ϖ ρ)))
    (hφC : φ.toRingHom.IsIntegral) (hfinC : FiniteAlong A.valuation.Completion φ) (hsepC : SeparableAlong A.valuation.Completion φ)
    (μ : Dd.FiniteHom Dc)
    (hμV : ∀ v : LT.LatticeTree.Vertex R₀ K₀, μ.mapV (eVd (Quotient.mk (MulAction.orbitRel ↥(Γd.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) =
      eVc (Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) ((ρ g)⁻¹ • v)))
    (hμE : ∀ e : {e : Mumford.QuotEdge ↥(Γd.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, ((eEc.symm (μ.mapE (eEd e))).1) = Quotient.mk (MulAction.orbitRel ↥(Γc.map ρ) (BruhatTits.tree R₀ K₀).Dart) ((ρ g)⁻¹ • e.1.out))
    (hdeg : ((μ.degTotal : ℕ)) = finrankAlong A.valuation.Completion φ)

    (hproj : ∀ (x : ↥(ribbonKernel Dc)) (y : ↥(ribbonKernel Dd)),
      ((((Additive.toMul (𝒰d.P.Q (μ.pullback x) y)) : (↥𝒰d.K)ˣ) : ↥𝒰d.K) : A.valuation.Completion) =
        ((((Additive.toMul (𝒰c.P.Q x (μ.pushforward y))) : (↥𝒰c.K)ˣ) : ↥𝒰c.K) : A.valuation.Completion)) :
    ∀ (u : 𝒰c.P.TorusPoints) (D₁ : Divisor.degZero (K := A.valuation.Completion) (F := Fc)) (D₁' : Divisor.degZero (K := A.valuation.Completion) (F := Fd)),
      𝒰c.eFull u = Pic0.mk D₁ →
      (D₁' : Divisor A.valuation.Completion Fd) = Divisor.pullbackAlong φ hφC (D₁ : Divisor A.valuation.Completion Fc) →
      𝒰d.eFull (u.comp μ.pushforward) = Pic0.mk D₁' := by
  classical
  intro u D₁ D₁' hu hD₁'
  haveI _hAC : IsAlgClosed A.valuation.Completion := ValuationSubring.isAlgClosed_completion_of_liesOverPrime r Fact.out A hA

  have hFI : FundamentalIdentityAlong A.valuation.Completion φ hφC := AlgebraicCurve.fundamentalIdentityAlong φ hφC hfinC hsepC

  have hnat : ∀ w : 𝒰c.P.TorusPoints, w ∈ 𝒰c.P.periodLattice → w.comp μ.pushforward ∈ 𝒰d.P.periodLattice :=
    fun w hw => CerednikDrinfeld.Mumford.PeriodDatum.comp_pushforward_mem_periodLattice_of_forall_eq μ 𝒰d.P 𝒰c.P
      (fun x y => hproj x y) w hw

  let N : 𝒰c.P.TorusPoints →+ 𝒰d.P.TorusPoints := (LinearMap.lcomp ℤ (Additive (A.valuation.Completion)ˣ) μ.pushforward).toAddMonoidHom
  have hN : ∀ w : 𝒰c.P.TorusPoints, N w = w.comp μ.pushforward := fun _ => rfl
  let ψ : Divisor.degZero (K := A.valuation.Completion) (F := Fc) →+ Divisor.degZero (K := A.valuation.Completion) (F := Fd) :=
    ((Divisor.pullbackAlong φ hφC).comp (Divisor.degZero (K := A.valuation.Completion) (F := Fc)).subtype).codRestrict _
      (fun D => Divisor.pullbackAlong_mem_degZero φ hφC hFI D.2)
  have hψ : ∀ D : Divisor.degZero (K := A.valuation.Completion) (F := Fc), (ψ D : Divisor A.valuation.Completion Fd) = Divisor.pullbackAlong φ hφC D := fun _ => rfl
  have hkerN : ∀ w ∈ 𝒰c.P.periodLattice.toAddSubgroup, 𝒰d.eFull (N w) = 0 :=
    fun w hw => (𝒰d.eFull_ker _).2 (hnat w hw)

  have hdeg1 : ∀ v : Place A.valuation.Completion Fc, v.deg = 1 := fun v => CerednikDrinfeld.SqGlueC.deg_eq_one_of_isAlgClosed v
  have hgen0 : ∀ a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion),
      (Finsupp.single (ptc a) (1 : ℤ) - Finsupp.single (ptc b) 1) ∈ Divisor.degZero (K := A.valuation.Completion) (F := Fc) := by
    intro a b
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]; simp

  have N3_theta_conorm : ∀ (a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)),
      ∃ w₀ : 𝒰c.P.TorusPoints, 𝒰c.eFull w₀ = Pic0.mk ⟨_, hgen0 a b⟩ ∧
        𝒰d.eFull (w₀.comp μ.pushforward) = Pic0.mk (ψ ⟨_, hgen0 a b⟩) := fun a b =>
    AlgebraicCurve.Pic0.exists_eFull_eq_mk_single_sub_single_and_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one
      A hA K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ v₀ Γd htpd hfind htamed Fd eFd Ed Vd Dd eVd eEd hDad hDbd hDwd Φd hΦd ptd hpt_fibd hpt_ontod hptd Γc htpc hfinc htamec Fc eFc Ec Vc Dc eVc eEc hDac hDbc hDwc Φc hΦc ptc hpt_fibc hpt_ontoc hptc S scalar actZd gald actZc galc 𝒰d 𝒰c hQd hΘd hQc hΘc g hg hArr φ hφ hφC hfinC hsepC μ hμV hμE hdeg a b ⟨_, hgen0 a b⟩ (ψ ⟨_, hgen0 a b⟩) rfl (hψ _)

  have hmem : (D₁ : Divisor A.valuation.Completion Fc) ∈
      AddSubgroup.closure {D : Divisor A.valuation.Completion Fc | ∃ a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), D = Finsupp.single (ptc a) 1 - Finsupp.single (ptc b) 1} :=
    AlgebraicCurve.Divisor.degZero_le_closure_single_sub_single_of_surjective A.valuation.Completion Fc ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) ptc hpt_ontoc D₁.2

  have key := CerednikDrinfeld.SqGlueC.square_of_generators (Divisor.degZero (K := A.valuation.Completion) (F := Fc))
    (QuotientAddGroup.mk' _) ψ (QuotientAddGroup.mk' _) 𝒰c.eFull 𝒰c.eFull_surjective 𝒰c.P.periodLattice.toAddSubgroup
    (fun w => 𝒰c.eFull_ker w) 𝒰d.eFull N hkerN
    {D : Divisor A.valuation.Completion Fc | ∃ a b : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), D = Finsupp.single (ptc a) 1 - Finsupp.single (ptc b) 1}
    (by
      rintro s ⟨a, b, rfl⟩
      obtain ⟨w₀, h₀, h₀'⟩ := N3_theta_conorm a b
      exact ⟨hgen0 a b, w₀, h₀, h₀'⟩)
    D₁ hmem u hu
  have hD₁eq : D₁' = ψ D₁ := Subtype.ext (by rw [hψ]; exact hD₁')
  rw [hD₁eq]
  exact key

end S_AlgebraicCurve_Pic0_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_eFull_comp_pushforward_eq_mk_pullbackAlong_of_mumfordQuotient_theta_of_v_card_stabilizer_eq_one (solution)
