-- Prove2me | solution 1 for AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d7f869c2-81b6-5371-8fc1-685a1078a5b3

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_SemistableModel_bijective_appTop_toBase
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_residue_of_bijective_appTop_of_isReduced
import Theorems.Thm_AlgebraicCurve_SemistableModel_isReduced_pullback_residue_of_level
import Theorems.Thm_AlgebraicCurve_SemistableModel_exists_opens_preimage_eq_of_isClosedMap_of_saturated
import Theorems.Thm_AlgebraicCurve_SemistableModel_fibre_shapes_of_level
import Theorems.Thm_AlgebraicCurve_SemistableModel_smul_div_pow_mem_localRing_of_forall_ord_eq
import Theorems.Thm_AlgebraicCurve_SemistableModel_mem_localRing_iff_mem_range_of_level
import Theorems.Thm_AlgebraicCurve_SemistableModel_exists_eq_one_add_baseToFunctionField_mul_of_level
import Theorems.Thm_ValuationSubring_faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap
import Theorems.Thm_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_SemistableModel_exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

namespace LevelTransferE133

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases h0 : f = 0
  · simp [h0]
  have hle : v.adicValuation f ≤ 1 := by
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero h0
  unfold Place.ord
  have : WithZero.log (v.adicValuation f) ≤ WithZero.log 1 :=
    (WithZero.log_le_log hne one_ne_zero).mpr hle
  rw [WithZero.log_one] at this
  omega

theorem mem_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf0 : f ≠ 0) (hf : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨w, hw⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [hw]
  lift v.ord f to ℕ using hf with n hn
  rw [zpow_natCast]
  exact mul_mem (w : v.toValuationSubring).2 (pow_mem ϖ.2 n)

theorem ord_eq_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf0 : f ≠ 0) :
    v.ord f = 0 ↔ f ∈ v.toValuationSubring ∧ f⁻¹ ∈ v.toValuationSubring := by
  constructor
  · intro h
    exact ⟨mem_of_ord_nonneg v hf0 h.ge, mem_of_ord_nonneg v (inv_ne_zero hf0) (by rw [v.ord_inv, h, neg_zero])⟩
  · rintro ⟨h1, h2⟩
    have a := ord_nonneg_of_mem v h1
    have b := ord_nonneg_of_mem v h2
    rw [v.ord_inv] at b
    omega

end LevelTransferE133

open LevelTransferE133

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    {ιV ιE : Type*} [Fintype ιV] [Fintype ιE] (Fbar : ιV → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : ιE → Annulus A F) (src tgt : ιE → ιV)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : ιE → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : ιE ⊕ ιE,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + Fintype.card ιV =
      (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + Fintype.card ιE + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A))
    (G : Divisor L F)
    (g : F) (hg : g ≠ 0)
    (hkG : ∀ P : Place L F, P.ord g = (k : ℤ) *
      G P)

    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F)
    (hU : (⨆ a, U a) = ⊤) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) =
        G P)
    (hcoc : ∀ a b (x : M.X), x ∈ U a → x ∈ U b →
        ∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
          h a = h b * (1 + algebraMap L F ((t : A) : L) * r))
    (hv1 : ∃ a₀, ∀ P : Place L F, M.pt P ∈ U a₀ ↔
        G P = 0)
    (hv2 : ∀ a, (∀ P : Place L F, M.pt P ∈ U a ↔
          G P = 0) ∨
        (∃ (i : ιV) (q : Place (IsLocalRing.ResidueField A) (Fbar i)), ∀ P : Place L F,
          M.pt P ∈ U a ↔ ((P ∈ (C i).dom ∧ (C i).placeMap P = q) ∨
            (G P = 0 ∧ P.ord (h a) = 0))) ∨
        (∃ e₀ : ιE, ∀ P : Place L F,
          M.pt P ∈ U a ↔ (P ∈ (An e₀).dom ∨
            (G P = 0 ∧ P.ord (h a) = 0))))

    (c : ιV → L) (hc0 : ∀ i, c i ≠ 0)
    (hcunit : ∀ i a, M.gen i ∈ U a →
        c i • (g / h a ^ k) ∈ (C i).integers ∧ (c i • (g / h a ^ k))⁻¹ ∈ (C i).integers)
    (hcslope : ∀ e', A.valuation (c (src e')) = A.valuation (c (tgt e')))

    (K₁ : IntermediateField ↥D.K₀ L) [FiniteDimensional ↥D.K₀ ↥K₁]
    [IsNoetherianRing ↥(A.comap (algebraMap ↥K₁ L))] [HenselianLocalRing ↥(A.comap (algebraMap ↥K₁ L))]
    (j₁ : D.A₀ →+* ↥(A.comap (algebraMap ↥K₁ L))) (ι₁ : ↥(A.comap (algebraMap ↥K₁ L)) →+* A) [IsLocalHom j₁] [IsLocalHom ι₁]
    (hι₁ : Function.Injective ι₁) (hcomp : ι₁.comp j₁ = D.ι)
    (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    (hι₁val : ∀ x : ↥(A.comap (algebraMap ↥K₁ L)), ((ι₁ x : A) : L) = algebraMap ↥K₁ L (x : ↥K₁))
    (hdvr : A ≠ ⊤ → IsDiscreteValuationRing ↥(A.comap (algebraMap ↥K₁ L)))

    (X₁ : Scheme.{u}) [IsIntegral X₁] (f₁ : X₁ ⟶ Spec (CommRingCat.of ↥(A.comap (algebraMap ↥K₁ L)))) [IsProper f₁] [Flat f₁]
    (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase)
    (hnorm₁ : ∀ x : X₁, IsIntegrallyClosed (X₁.presheaf.stalk x))
    (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField)
    (hF₀ : D.F₀ ≤ F₁) (hK₁ : ∀ x : L, x ∈ K₁ → algebraMap L F x ∈ F₁) (halg : Algebra.IsAlgebraic F₁ F)
    (hcompat : ∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
        genericPoint X₁,
      ∀ s : F₁, M.ffEquiv (s : F) =
        ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
          ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s)))

    (hgF₁ : g ∈ F₁) (hhF₁ : ∀ a, h a ∈ F₁) (hcK₁ : ∀ i, c i ∈ K₁) :
    ∃ (c₀ : L) (hc₀F₁ : c₀ • g ∈ F₁) (g₁ : X₁.functionField)
      (r₁ : ℕ) (U₁ : Fin r₁ → X₁.Opens) (h₁ : Fin r₁ → X₁.functionField),
      c₀ ≠ 0 ∧ g₁ = φ₁ ⟨c₀ • g, hc₀F₁⟩ ∧ g₁ ≠ 0 ∧
      IsAlgClosed (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥K₁ L))) ∧ IsUnit ((k : ℕ) : ↥(A.comap (algebraMap ↥K₁ L))) ∧
      (⨆ a, U₁ a) = ⊤ ∧ (∀ a, h₁ a ≠ 0) ∧
      (∀ a (x : X₁), x ∈ U₁ a →
        g₁ / h₁ a ^ k ∈ (algebraMap (X₁.presheaf.stalk x) X₁.functionField).range ∧
        h₁ a ^ k / g₁ ∈ (algebraMap (X₁.presheaf.stalk x) X₁.functionField).range) ∧
      (∀ a b (x : X₁), x ∈ U₁ a → x ∈ U₁ b →
        ∃ t ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥K₁ L)), ∃ s ∈ (algebraMap (X₁.presheaf.stalk x) X₁.functionField).range,
          h₁ a = h₁ b * (1 + AlgebraicCurve.SemistableModel.baseToFunctionField f₁ t * s)) ∧
      Function.Bijective
        (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥(A.comap (algebraMap ↥K₁ L)))))).appTop := by
  classical

  have hA : A ≠ ⊤ := by
    intro hA
    have hπL : ((π : ↥A) : L) ≠ 0 := fun h0 => hπ0 (Subtype.ext h0)
    have hinv : ((π : ↥A) : L)⁻¹ ∈ A := (SetLike.ext_iff.mp hA _).mpr (ValuationSubring.mem_top _)
    have hu : IsUnit (π : ↥A) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hπL)⟩
    exact ((IsLocalRing.mem_maximalIdeal _).mp hπ) hu
  haveI hDVR : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥K₁ L)) := hdvr hA
  obtain ⟨ϖ₁, hϖ₁irr⟩ := IsDiscreteValuationRing.exists_irreducible ↥(A.comap (algebraMap ↥K₁ L))
  have hϖ₁ : IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥K₁ L)) = Ideal.span {ϖ₁} := hϖ₁irr.maximalIdeal_eq
  have hϖ₁0 : ϖ₁ ≠ 0 := hϖ₁irr.ne_zero

  have hAC₁ : IsAlgClosed (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥K₁ L))) := by
    haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
    let ρ : IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥K₁ L)) →+* IsLocalRing.ResidueField ↥A := IsLocalRing.ResidueField.map ι₁
    have hρs : Function.Surjective ρ := by
      intro y
      obtain ⟨a, ha⟩ := hres₁ y
      exact ⟨IsLocalRing.residue _ a, ha⟩
    have hρb : Function.Bijective ρ := ⟨ρ.injective, hρs⟩
    let eρ : IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥K₁ L)) ≃+* IsLocalRing.ResidueField ↥A := RingEquiv.ofBijective ρ hρb
    exact IsAlgClosed.of_ringEquiv (k := IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥K₁ L))) eρ.symm
  have hk0' : k ≠ 0 := by
    rintro rfl
    simp at hk
  have hk₁ : IsUnit ((k : ℕ) : ↥(A.comap (algebraMap ↥K₁ L))) := by
    have h1 : IsUnit ((IsLocalRing.residue ↥A) (ι₁ ((k : ℕ) : ↥(A.comap (algebraMap ↥K₁ L))))) := by simp only [map_natCast]; exact hk
    have h2 : IsUnit (ι₁ ((k : ℕ) : ↥(A.comap (algebraMap ↥K₁ L)))) := by
      by_contra hnu
      have hm : ι₁ ((k : ℕ) : ↥(A.comap (algebraMap ↥K₁ L))) ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [← IsLocalRing.residue_eq_zero_iff] at hm
      rw [hm] at h1
      exact not_isUnit_zero h1
    exact isUnit_of_map_unit ι₁ _ h2

  letI algA : Algebra ↥(A.comap (algebraMap ↥K₁ L)) ↥A := ι₁.toAlgebra
  obtain ⟨hff, hint⟩ := ValuationSubring.faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap
    (K := ↥K₁) (L := L) A hι₁val
  haveI hffI : Module.FaithfullyFlat ↥(A.comap (algebraMap ↥K₁ L)) ↥A := hff
  haveI hflat : Flat (Spec.map (CommRingCat.ofHom ι₁)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (show RingHom.Flat ι₁ from
      (show Module.Flat ↥(A.comap (algebraMap ↥K₁ L)) ↥A from inferInstance))
  have hcl : IsClosedMap (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base := by
    haveI : IsIntegralHom (Spec.map (CommRingCat.ofHom ι₁)) :=
      IsIntegralHom.SpecMap_iff.mpr (show RingHom.IsIntegral ι₁ from algebraMap_isIntegral_iff.mpr hint)
    exact (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).isClosedMap
  have hsurj : Function.Surjective (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base := by
    haveI : Surjective (Spec.map (CommRingCat.ofHom ι₁)) :=
      ⟨show Function.Surjective (PrimeSpectrum.comap ι₁) from PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
    exact (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).surjective

  obtain ⟨hfib_sp, hfib_gen, hfib_pt, hconn_tr⟩ := AlgebraicCurve.SemistableModel.fibre_shapes_of_level M hrk
    ↥(A.comap (algebraMap ↥K₁ L)) ⟨ϖ₁, hϖ₁0, hϖ₁irr.not_isUnit |> (IsLocalRing.mem_maximalIdeal _).mpr⟩ ι₁ hι₁ hres₁ X₁ f₁ e₁ he₁ F₁ φ₁ halg hcompat

  have hΓ : Function.Bijective M.toBase.appTop := AlgebraicCurve.SemistableModel.bijective_appTop_toBase M
  have hΓ₁ : Function.Bijective f₁.appTop := by
    haveI : CompactSpace ↥X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
    haveI : QuasiSeparatedSpace ↥X₁ := (quasiSeparated_iff_quasiSeparatedSpace f₁).mp inferInstance
    have happ : (pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁))).appTop = M.toBase.appTop ≫ e₁.inv.appTop := by
      rw [← he₁, Scheme.Hom.comp_appTop, Category.assoc, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop,
        Category.comp_id]
    have hsnd : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv ≫
        (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥(A.comap (algebraMap ↥K₁ L)) ↥A)))).appTop).hom := by
      change Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv ≫
        (pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁))).appTop).hom
      rw [happ]
      have hb : Function.Bijective e₁.inv.appTop := by
        refine Function.bijective_iff_has_inverse.mpr ⟨e₁.hom.appTop, fun z => ?_, fun z => ?_⟩
        · change (e₁.inv.appTop ≫ e₁.hom.appTop) z = z
          rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]; rfl
        · change (e₁.hom.appTop ≫ e₁.inv.appTop) z = z
          rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]; rfl
      exact (hb.comp hΓ).comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv)
    have hT9 := AlgebraicGeometry.bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat f₁ ↥A hsnd
    have hcomp : f₁.appTop = (Scheme.ΓSpecIso (CommRingCat.of ↥(A.comap (algebraMap ↥K₁ L)))).hom ≫
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(A.comap (algebraMap ↥K₁ L)))).inv ≫ f₁.appTop) := by
      rw [Iso.hom_inv_id_assoc]
    rw [hcomp]
    exact hT9.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ↥(A.comap (algebraMap ↥K₁ L)))).hom)

  have hpre₁ := AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop f₁ hΓ₁
  have hpre : _root_.IsPreconnected (M.toBase.base ⁻¹' {IsLocalRing.closedPoint ↥A}) := hconn_tr hcl hpre₁
  haveI hred : IsReduced (pullback f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥(A.comap (algebraMap ↥K₁ L)))))) :=
    AlgebraicCurve.SemistableModel.isReduced_pullback_residue_of_level M ↥(A.comap (algebraMap ↥K₁ L)) ι₁ hres₁ X₁ f₁ e₁ he₁
  haveI := hAC₁
  have hconn₁ := AlgebraicGeometry.bijective_appTop_pullback_snd_residue_of_bijective_appTop_of_isReduced f₁ hΓ₁

  obtain ⟨c₀, hc₀, hc₀mem, hunit⟩ :=
    AlgebraicCurve.SemistableModel.exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range
      M hpre k g r U h c hc0 hcunit hcslope
  have hc₀K₁ : c₀ ∈ K₁ := by
    rcases hc₀mem with h1 | ⟨i₀, hi₀⟩
    · rw [h1]; exact one_mem _
    · rw [hi₀]; exact hcK₁ i₀
  have hc₀F₁ : c₀ • g ∈ F₁ := by
    rw [Algebra.smul_def]; exact mul_mem (hK₁ _ hc₀K₁) hgF₁

  have hloc : ∀ a (x : M.X), x ∈ U a →
      c₀ • (g / h a ^ k) ∈ SemistableModel.localRing M.X M.ffEquiv x ∧
        (c₀ • (g / h a ^ k))⁻¹ ∈ SemistableModel.localRing M.X M.ffEquiv x := fun a x hx =>
    AlgebraicCurve.SemistableModel.smul_div_pow_mem_localRing_of_forall_ord_eq M k (⇑G) g hg hkG r U h hh hdiv
      c₀ hc₀ hunit a x hx

  have hreg := fun (x : M.X) (u : F) (hu : u ∈ F₁) =>
    AlgebraicCurve.SemistableModel.mem_localRing_iff_mem_range_of_level M ↥(A.comap (algebraMap ↥K₁ L)) ι₁ hres₁ X₁ f₁ e₁ he₁ F₁ φ₁ hcompat x u hu
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk0'
  have hordfib : ∀ (u : F) (hu : u ∈ F₁) (hu0 : u ≠ 0) (P P' : Place L F),
      (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (M.pt P) = (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (M.pt P') → (P.ord u = 0 ↔ P'.ord u = 0) := by
    intro u hu hu0 P P' hPP'
    have key : ∀ P : Place L F, P.ord u = 0 ↔
        (u ∈ SemistableModel.localRing M.X M.ffEquiv (M.pt P) ∧ u⁻¹ ∈ SemistableModel.localRing M.X M.ffEquiv (M.pt P)) := by
      intro P
      rw [ord_eq_zero_iff P hu0, M.localRing_pt P]
      rfl
    rw [key P, key P', hreg (M.pt P) u hu, hreg (M.pt P) u⁻¹ (inv_mem hu), hreg (M.pt P') u hu,
      hreg (M.pt P') u⁻¹ (inv_mem hu), hPP']
  have hGfib : ∀ P P' : Place L F, (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (M.pt P) = (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (M.pt P') →
      ((⇑G) P = 0 ↔ (⇑G) P' = 0) := by
    intro P P' hPP'
    have := hordfib g hgF₁ hg P P' hPP'
    rw [hkG P, hkG P', mul_eq_zero_iff_left hk0, mul_eq_zero_iff_left hk0] at this
    exact this
  have hhfib : ∀ a (P P' : Place L F), (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (M.pt P) = (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (M.pt P') →
      (P.ord (h a) = 0 ↔ P'.ord (h a) = 0) := fun a P P' hPP' => hordfib (h a) (hhF₁ a) (hh a) P P' hPP'
  obtain ⟨U₁, hU₁cov, hU₁⟩ := AlgebraicCurve.SemistableModel.exists_opens_preimage_eq_of_isClosedMap_of_saturated M X₁
    (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) hcl hsurj hfib_sp hfib_gen hfib_pt (⇑G) r U h hU hv2 hGfib hhfib

  have hφinj : Function.Injective φ₁ := φ₁.injective
  refine ⟨c₀, hc₀F₁, φ₁ ⟨c₀ • g, hc₀F₁⟩, r, U₁, fun a => φ₁ ⟨h a, hhF₁ a⟩, hc₀, rfl, ?_, hAC₁, hk₁, hU₁cov, ?_, ?_, ?_, hconn₁⟩
  ·
    rw [map_ne_zero_iff φ₁ hφinj, ne_eq, Subtype.ext_iff]
    exact smul_ne_zero hc₀ hg
  ·
    intro a
    rw [map_ne_zero_iff φ₁ hφinj, ne_eq, Subtype.ext_iff]
    exact hh a
  ·
    intro a x₁ hx₁
    obtain ⟨x, rfl⟩ := hsurj x₁
    have hx : x ∈ U a := (hU₁ a x).mpr hx₁
    obtain ⟨h1, h2⟩ := hloc a x hx
    have hwF₁ : c₀ • (g / h a ^ k) ∈ F₁ := by
      rw [Algebra.smul_def]
      exact mul_mem (hK₁ _ hc₀K₁) (div_mem hgF₁ (pow_mem (hhF₁ a) k))
    have e1 : φ₁ ⟨c₀ • g, hc₀F₁⟩ / φ₁ ⟨h a, hhF₁ a⟩ ^ k = φ₁ ⟨c₀ • (g / h a ^ k), hwF₁⟩ := by
      rw [← map_pow, ← map_div₀]
      congr 1
      apply Subtype.ext
      simp [smul_div_assoc]
    have e2 : φ₁ ⟨h a, hhF₁ a⟩ ^ k / φ₁ ⟨c₀ • g, hc₀F₁⟩ = φ₁ ⟨(c₀ • (g / h a ^ k))⁻¹, inv_mem hwF₁⟩ := by
      rw [← inv_div, e1, ← map_inv₀]
      rfl
    constructor
    · rw [e1]; exact (hreg x _ hwF₁).mp h1
    · rw [e2]; exact (hreg x _ (inv_mem hwF₁)).mp h2
  ·
    intro a b x₁ hxa hxb
    obtain ⟨x, rfl⟩ := hsurj x₁
    have hxa' : x ∈ U a := (hU₁ a x).mpr hxa
    have hxb' : x ∈ U b := (hU₁ b x).mpr hxb
    obtain ⟨t, ht, rr, hrr, hab⟩ := hcoc a b x hxa' hxb'
    have huF₁ : h a / h b ∈ F₁ := div_mem (hhF₁ a) (hhF₁ b)
    have hu_eq : h a / h b = 1 + algebraMap L F ((t : ↥A) : L) * rr := by
      rw [hab, mul_div_cancel_left₀ _ (hh b)]
    obtain ⟨t₁, ht₁, s, hs, hus⟩ :=
      AlgebraicCurve.SemistableModel.exists_eq_one_add_baseToFunctionField_mul_of_level M ↥(A.comap (algebraMap ↥K₁ L)) ι₁ hres₁ ϖ₁ hϖ₁0 hϖ₁
        X₁ f₁ e₁ he₁ F₁ φ₁ hcompat x (h a / h b) huF₁ ⟨t, ht, rr, hrr, hu_eq⟩
    refine ⟨t₁, ht₁, s, hs, ?_⟩
    show φ₁ ⟨h a, hhF₁ a⟩ = φ₁ ⟨h b, hhF₁ b⟩ * (1 + AlgebraicCurve.SemistableModel.baseToFunctionField f₁ t₁ * s)
    rw [← hus, ← map_mul]
    congr 1
    apply Subtype.ext
    show h a = h b * (h a / h b)
    rw [mul_comm, div_mul_cancel₀ _ (hh b)]

end S_AlgebraicCurve_exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent
end P2MW
export P2MW.S_AlgebraicCurve_exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent (solution)
