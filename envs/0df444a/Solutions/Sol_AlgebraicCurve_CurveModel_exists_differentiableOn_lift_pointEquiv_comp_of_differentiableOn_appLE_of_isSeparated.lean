-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_differentiableOn_lift_pointEquiv_comp_of_differentiableOn_appLE_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ed73a084-0818-5e4d-9d75-21fadc1da4df

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicCurve_CurveModel_isOpen_and_differentiableAt_appLE_pointEquivPlace_symm_of_meromorphicOrderAt_eq_ord
import Theorems.Thm_AlgebraicGeometry_exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
import Theorems.Thm_Complex_contDiffOn_one_of_differentiableOn_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_differentiableOn_lift_pointEquiv_comp_of_differentiableOn_appLE_of_isSeparated
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra AlgebraicCurve CerednikDrinfeld.QM Topology
open scoped Manifold ContDiff

theorem solution
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} [IsSeparated f] {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
    (hL1 : ∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀))
    (hAN : ∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ)))
    (hCOV : ∀ v₀ : Fin g → ℂ,
      ∃ (U : G.Opens) (t : Fin g → Γ(G, U)) (ε : ℝ) (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
        (F : (Fin g → ℂ) → (Fin g → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀)
    (F : Type) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (M : CurveModel ℂ F)
    (ν : M.C ⟶ G) (hν : ν ≫ f = M.toBase)
    (v₀ : Place ℂ F) (w₀ : Fin g → ℂ)
    (hw₀ : e (mapPt ν hν (M.pointEquivPlace.symm v₀)) = (w₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)) :
    ∃ (ε : ℝ) (vl : ℂ → (Fin g → ℂ)), 0 < ε ∧
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) v₀ v₀) ε ⊆ (extChartAt 𝓘(ℂ, ℂ) v₀).target ∧
      DifferentiableOn ℂ vl (Metric.ball (extChartAt 𝓘(ℂ, ℂ) v₀ v₀) ε) ∧
      vl (extChartAt 𝓘(ℂ, ℂ) v₀ v₀) = w₀ ∧
      ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v₀ v₀) ε,
        e (mapPt ν hν (M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z))) =
          (vl z : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by
  classical
  set c₀ : ℂ := extChartAt 𝓘(ℂ, ℂ) v₀ v₀ with hc₀
  have hsymm0 : (extChartAt 𝓘(ℂ, ℂ) v₀).symm c₀ = v₀ := by rw [hc₀]; exact extChartAt_to_inv (I := 𝓘(ℂ, ℂ)) v₀

  set Pz : ℂ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f :=
    fun z => mapPt ν hν (M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z)) with hPz
  have hP0 : e (Pz c₀) = (w₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by rw [hPz]; simp only [hsymm0]; exact hw₀

  obtain ⟨U₁, t, ε₁, D, Φ, hε₁, hball, hΦval, hΦD⟩ := hCOV w₀

  have h2 : ∃ (ginv : (Fin g → ℂ) → (Fin g → ℂ)) (r : ℝ), 0 < r ∧ r ≤ ε₁ ∧
      (∀ x ∈ Metric.ball w₀ r, ginv (Φ x) = x) ∧ ginv (Φ w₀) = w₀ ∧
      (∀ᶠ y in 𝓝 (Φ w₀), DifferentiableAt ℂ ginv y) := by
    have hΦdiff : DifferentiableOn ℂ Φ (Metric.ball w₀ ε₁) := by
      refine differentiableOn_pi.2 fun i => ?_
      obtain ⟨-, Fi, hFidiff, hFival⟩ := hAN U₁ (t i)
      have hcongr : ∀ x ∈ Metric.ball w₀ ε₁, (fun x => Φ x i) x = Fi x := by
        intro x hx
        simp only [hΦval x (hball x hx) hx, hFival x (hball x hx)]
      exact (hFidiff.mono (fun x hx => hball x hx)).congr hcongr
    have hC1 : ContDiffOn ℂ 1 Φ (Metric.ball w₀ ε₁) :=
      Complex.contDiffOn_one_of_differentiableOn_pi Metric.isOpen_ball hΦdiff
    have hC1at : ContDiffAt ℂ 1 Φ w₀ := hC1.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε₁))
    have h10 : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
    have hstrict : HasStrictFDerivAt Φ (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) w₀ := hC1at.hasStrictFDerivAt' hΦD h10
    refine ⟨hC1at.localInverse hΦD h10, ?_⟩
    have hg0 : hC1at.localInverse hΦD h10 (Φ w₀) = w₀ := hC1at.localInverse_apply_image hΦD h10
    have hleft : ∀ᶠ x in 𝓝 w₀, hC1at.localInverse hΦD h10 (Φ x) = x := hstrict.eventually_left_inverse
    have hginvC1 : ContDiffAt ℂ 1 (hC1at.localInverse hΦD h10) (Φ w₀) := hC1at.to_localInverse hΦD h10
    have hgdiff : ∀ᶠ y in 𝓝 (Φ w₀), DifferentiableAt ℂ (hC1at.localInverse hΦD h10) y := by
      filter_upwards [hginvC1.eventually (by simp)] with y hy
      exact hy.differentiableAt h10
    obtain ⟨r₀, hr₀, hsub⟩ := Metric.mem_nhds_iff.1 hleft
    exact ⟨min r₀ ε₁, lt_min hr₀ hε₁, min_le_right _ _,
      fun x hx => hsub (Metric.ball_subset_ball (min_le_left _ _) hx), hg0, hgdiff⟩

  have h1 : ∃ (hc : ℂ → (Fin g → ℂ)) (ρ₁ : ℝ), 0 < ρ₁ ∧
      Metric.ball c₀ ρ₁ ⊆ (extChartAt 𝓘(ℂ, ℂ) v₀).target ∧
      DifferentiableOn ℂ hc (Metric.ball c₀ ρ₁) ∧
      ∀ z ∈ Metric.ball c₀ ρ₁, ∃ hz : ⊤ ≤ (Pz z).1 ⁻¹ᵁ U₁,
        hc z = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pz z).1.appLE U₁ ⊤ hz) (t i)) := by
    have hpre1 : ∀ z, (Pz z).1 ⁻¹ᵁ U₁ =
        (M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z)).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₁) := fun z => rfl
    have hbase : e.symm (w₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) = Pz c₀ := by rw [← hP0, Equiv.symm_apply_apply]
    obtain ⟨hS1open, -⟩ :=
      AlgebraicCurve.CurveModel.isOpen_and_differentiableAt_appLE_pointEquivPlace_symm_of_meromorphicOrderAt_eq_ord
        F hfg hF M (ν ⁻¹ᵁ U₁) (0 : Γ(M.C, ν ⁻¹ᵁ U₁))
    have hv0S1 : ⊤ ≤ (M.pointEquivPlace.symm v₀).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₁) := by
      have := hball w₀ (Metric.mem_ball_self hε₁)
      rw [hbase, hpre1, hsymm0] at this; exact this
    have hGi : ∀ i : Fin g, ∃ Gi : Place ℂ F → ℂ,
        (∀ (v : Place ℂ F) (h : ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₁)),
          Gi v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((M.pointEquivPlace.symm v).1.appLE (ν ⁻¹ᵁ U₁) ⊤ h) (ν.app U₁ (t i)))) ∧
        ∀ v : Place ℂ F, ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₁) →
          DifferentiableAt ℂ (fun z : ℂ => Gi ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v) := fun i =>
      (AlgebraicCurve.CurveModel.isOpen_and_differentiableAt_appLE_pointEquivPlace_symm_of_meromorphicOrderAt_eq_ord
        F hfg hF M (ν ⁻¹ᵁ U₁) (ν.app U₁ (t i))).2
    choose Gi hGival hGidiff using hGi
    have hN : ((extChartAt 𝓘(ℂ, ℂ) v₀).symm ⁻¹'
        ({v | ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₁)} ∩ (extChartAt 𝓘(ℂ, ℂ) v₀).source)) ∩
        (extChartAt 𝓘(ℂ, ℂ) v₀).target ∈ 𝓝 c₀ := by
      refine Filter.inter_mem ?_ ?_
      · apply (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v₀).preimage_mem_nhds
        rw [hsymm0]
        exact Filter.inter_mem (hS1open.mem_nhds hv0S1) (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) v₀)
      · rw [hc₀]; exact extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) v₀
    obtain ⟨ρ₁, hρ₁, hsub⟩ := Metric.mem_nhds_iff.1 hN
    refine ⟨fun z i => Gi i ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z), ρ₁, hρ₁, fun z hz => (hsub hz).2, ?_, ?_⟩
    ·
      intro z₁ hz₁
      obtain ⟨⟨hv₁S, hv₁src⟩, hz₁tgt⟩ := hsub hz₁
      apply DifferentiableAt.differentiableWithinAt
      refine differentiableAt_pi.2 fun i => ?_
      set v₁ : Place ℂ F := (extChartAt 𝓘(ℂ, ℂ) v₀).symm z₁ with hv₁
      have hA1 : DifferentiableAt ℂ (fun z : ℂ => Gi i ((extChartAt 𝓘(ℂ, ℂ) v₁).symm z)) (extChartAt 𝓘(ℂ, ℂ) v₁ v₁) :=
        hGidiff i v₁ hv₁S

      have hy : z₁ ∈ ((extChartAt 𝓘(ℂ, ℂ) v₀).symm ≫ extChartAt 𝓘(ℂ, ℂ) v₁).source := by
        rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
        refine ⟨hz₁tgt, ?_⟩
        show (extChartAt 𝓘(ℂ, ℂ) v₀).symm z₁ ∈ (extChartAt 𝓘(ℂ, ℂ) v₁).source
        exact mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) v₁
      have hτ : ContDiffWithinAt ℂ ω (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v₀).symm) (Set.range 𝓘(ℂ, ℂ)) z₁ :=
        contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, ℂ)) v₁ v₀ hy
      have hτ' : DifferentiableAt ℂ (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v₀).symm) z₁ := by
        have h' : ContDiffAt ℂ ω (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v₀).symm) z₁ :=
          hτ.contDiffAt (by simp)
        exact h'.differentiableAt (by simp)
      have heq : (fun z : ℂ => Gi i ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z)) =ᶠ[𝓝 z₁]
          ((fun z : ℂ => Gi i ((extChartAt 𝓘(ℂ, ℂ) v₁).symm z)) ∘ (extChartAt 𝓘(ℂ, ℂ) v₁ ∘ (extChartAt 𝓘(ℂ, ℂ) v₀).symm)) := by
        have hn : (extChartAt 𝓘(ℂ, ℂ) v₀).symm ⁻¹' (extChartAt 𝓘(ℂ, ℂ) v₁).source ∈ 𝓝 z₁ :=
          (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ, ℂ)) hz₁tgt).preimage_mem_nhds
            ((isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) v₁).mem_nhds (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) v₁))
        filter_upwards [hn] with z hz
        simp only [Function.comp_apply]
        rw [(extChartAt 𝓘(ℂ, ℂ) v₁).left_inv hz]
      refine (Filter.EventuallyEq.differentiableAt_iff heq).2 ?_
      exact DifferentiableAt.comp z₁ hA1 hτ'
    · intro z hz
      obtain ⟨⟨hzS, -⟩, -⟩ := hsub hz
      have hz' : ⊤ ≤ (Pz z).1 ⁻¹ᵁ U₁ := by rw [hpre1]; exact hzS
      refine ⟨hz', ?_⟩
      funext i
      show Gi i ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z) = _
      rw [hGival i _ hzS]
      congr 1
  obtain ⟨ginv, r, hr, hrε, hleft, hg0, hgdiff⟩ := h2
  obtain ⟨hc, ρ₁, hρ₁, htarget, hhdiff, hhval⟩ := h1

  have h3 : ∃ ρ₂ : ℝ, 0 < ρ₂ ∧ ∀ z ∈ Metric.ball c₀ ρ₂, ∃ w ∈ Metric.ball w₀ r,
      e (Pz z) = (w : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by
    obtain ⟨U₂, fs, ε₂, h₀, hε₂, hTN⟩ :=
      AlgebraicGeometry.exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
        Λ e hL1 hAN w₀ r hr

    have hbase : e.symm (w₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) = Pz c₀ := by rw [← hP0, Equiv.symm_apply_apply]

    have hpre : ∀ z, (Pz z).1 ⁻¹ᵁ U₂ = (M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z)).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₂) := by
      intro z; rfl

    obtain ⟨hS2open, -⟩ :=
      AlgebraicCurve.CurveModel.isOpen_and_differentiableAt_appLE_pointEquivPlace_symm_of_meromorphicOrderAt_eq_ord
        F hfg hF M (ν ⁻¹ᵁ U₂) (0 : Γ(M.C, ν ⁻¹ᵁ U₂))
    have hv0S2 : ⊤ ≤ (M.pointEquivPlace.symm v₀).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₂) := by
      have := h₀; rw [hbase, hpre, hsymm0] at this; exact this

    have hφ : ∀ φ : Γ(G, U₂), ∃ Gφ : Place ℂ F → ℂ,
        (∀ (v : Place ℂ F) (h : ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₂)),
          Gφ v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((M.pointEquivPlace.symm v).1.appLE (ν ⁻¹ᵁ U₂) ⊤ h) (ν.app U₂ φ))) ∧
        ContinuousAt (fun z : ℂ => Gφ ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z)) c₀ := by
      intro φ
      obtain ⟨-, Gφ, hGval, hGdiff⟩ :=
        AlgebraicCurve.CurveModel.isOpen_and_differentiableAt_appLE_pointEquivPlace_symm_of_meromorphicOrderAt_eq_ord
          F hfg hF M (ν ⁻¹ᵁ U₂) (ν.app U₂ φ)
      exact ⟨Gφ, hGval, by rw [hc₀]; exact (hGdiff v₀ hv0S2).continuousAt⟩
    choose Gφ hGφval hGφcont using hφ

    have hN : ((extChartAt 𝓘(ℂ, ℂ) v₀).symm ⁻¹' {v | ⊤ ≤ (M.pointEquivPlace.symm v).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₂)}) ∩
        (⋂ φ ∈ fs, {z : ℂ | ‖Gφ φ ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z) - Gφ φ v₀‖ < ε₂}) ∈ 𝓝 c₀ := by
      refine Filter.inter_mem ?_ ?_
      · apply (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v₀).preimage_mem_nhds
        rw [hsymm0]; exact hS2open.mem_nhds hv0S2
      · refine (Filter.biInter_finset_mem fs).2 fun φ _ => ?_
        have hct := hGφcont φ
        have : (fun z : ℂ => Gφ φ ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z)) ⁻¹' Metric.ball (Gφ φ v₀) ε₂ ∈ 𝓝 c₀ := by
          apply hct.preimage_mem_nhds
          apply Metric.isOpen_ball.mem_nhds
          simp only [Metric.mem_ball, hsymm0, dist_self]; exact hε₂
        refine Filter.mem_of_superset this ?_
        intro z hz; simpa [Metric.mem_ball, dist_eq_norm] using hz
    obtain ⟨ρ₂, hρ₂, hsub⟩ := Metric.mem_nhds_iff.1 hN
    refine ⟨ρ₂, hρ₂, fun z hz => ?_⟩
    obtain ⟨hzS, hzV⟩ := hsub hz
    have hzS' : ⊤ ≤ (M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z)).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₂) := hzS
    have hzP : ⊤ ≤ (Pz z).1 ⁻¹ᵁ U₂ := by rw [hpre]; exact hzS'
    refine hTN (Pz z) hzP ?_
    intro φ hφfs
    have hzφ : ‖Gφ φ ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z) - Gφ φ v₀‖ < ε₂ := by
      have := Set.mem_iInter₂.1 hzV φ hφfs; exact this

    have hval1 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pz z).1.appLE U₂ ⊤ hzP) φ) =
        Gφ φ ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z) := by
      rw [hGφval φ _ hzS']
      congr 1
    have hval0 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (w₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup))).1.appLE U₂ ⊤ h₀) φ) =
        Gφ φ v₀ := by
      have key : ∀ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U₂),
          Q = Pz c₀ → (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U₂ ⊤ hQ) φ) = Gφ φ v₀ := by
        rintro Q hQ rfl
        have hc0S : ⊤ ≤ (M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm c₀)).1 ⁻¹ᵁ (ν ⁻¹ᵁ U₂) := by
          rw [hsymm0]; exact hv0S2
        rw [show Gφ φ v₀ = Gφ φ ((extChartAt 𝓘(ℂ, ℂ) v₀).symm c₀) by rw [hsymm0], hGφval φ _ hc0S]
        congr 1
      exact key _ _ hbase
    rw [hval1, hval0]; exact hzφ
  obtain ⟨ρ₂, hρ₂, hnear⟩ := h3

  have hh0 : hc c₀ = Φ w₀ := by
    obtain ⟨hz, hcz⟩ := hhval c₀ (Metric.mem_ball_self hρ₁)
    rw [hcz, hΦval w₀ (hball w₀ (Metric.mem_ball_self hε₁)) (Metric.mem_ball_self hε₁)]
    have key : ∀ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U₁),
        Q = Pz c₀ → (fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U₁ ⊤ hQ) (t i))) =
          fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pz c₀).1.appLE U₁ ⊤ hz) (t i)) := by
      rintro Q hQ rfl; rfl
    exact (key _ _ (by rw [← e.symm_apply_apply (Pz c₀), hP0])).symm

  have hhcont : ContinuousAt hc c₀ := (hhdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ₁))).continuousAt
  have hρ₃ : ∃ ρ₃ : ℝ, 0 < ρ₃ ∧ ∀ z ∈ Metric.ball c₀ ρ₃, DifferentiableAt ℂ ginv (hc z) := by
    have : hc ⁻¹' {y | DifferentiableAt ℂ ginv y} ∈ 𝓝 c₀ := hhcont.preimage_mem_nhds (by rw [hh0]; exact hgdiff)
    obtain ⟨ρ₃, hρ₃, hsub⟩ := Metric.mem_nhds_iff.1 this
    exact ⟨ρ₃, hρ₃, fun z hz => hsub hz⟩
  obtain ⟨ρ₃, hρ₃, hgd⟩ := hρ₃
  set ε : ℝ := min ρ₁ (min ρ₂ ρ₃) with hεdef
  have hε : 0 < ε := lt_min hρ₁ (lt_min hρ₂ hρ₃)
  have hε1 : Metric.ball c₀ ε ⊆ Metric.ball c₀ ρ₁ := Metric.ball_subset_ball (min_le_left _ _)
  have hε2 : Metric.ball c₀ ε ⊆ Metric.ball c₀ ρ₂ := Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : Metric.ball c₀ ε ⊆ Metric.ball c₀ ρ₃ := Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, fun z => ginv (hc z), hε, hε1.trans htarget, ?_, ?_, ?_⟩
  ·
    intro z hz
    have h1' : DifferentiableAt ℂ hc z := hhdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (hε1 hz))
    exact ((hgd z (hε3 hz)).comp z h1').differentiableWithinAt
  ·
    show ginv (hc c₀) = w₀
    rw [hh0, hg0]
  ·
    intro z hz
    obtain ⟨w, hw, hew⟩ := hnear z (hε2 hz)
    obtain ⟨hzU, hcz⟩ := hhval z (hε1 hz)
    have hwε : w ∈ Metric.ball w₀ ε₁ := Metric.ball_subset_ball hrε hw
    have hΦw : Φ w = hc z := by
      rw [hcz, hΦval w (hball w hwε) hwε]
      have key : ∀ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U₁),
          Q = Pz z → (fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U₁ ⊤ hQ) (t i))) =
            fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pz z).1.appLE U₁ ⊤ hzU) (t i)) := by
        rintro Q hQ rfl; rfl
      exact key _ _ (by rw [← e.symm_apply_apply (Pz z), hew])
    show e (Pz z) = ((ginv (hc z)) : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)
    rw [← hΦw, hleft w hw, hew]

end S_AlgebraicCurve_CurveModel_exists_differentiableOn_lift_pointEquiv_comp_of_differentiableOn_appLE_of_isSeparated
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_differentiableOn_lift_pointEquiv_comp_of_differentiableOn_appLE_of_isSeparated (solution)
