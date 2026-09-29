-- Prove2me | solution 1 for AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/7bc3b03b-003d-58fa-a8ad-39bc3384ee31

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

namespace SolZ1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace Opposite

section Glue

variable {Y : Scheme.{u}} (U V : Y.Opens) (hcov : U ⊔ V = ⊤) (hdisj : U ⊓ V = ⊥)

include hcov hdisj in
lemma exists_section_eq_one_eq_zero :
    ∃ e : Γ(Y, ⊤), Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op e = 1 ∧
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op e = 0 := by
  let W : Bool → Y.Opens := fun b => cond b U V
  let sf : ∀ b : Bool, Γ(Y, W b) := fun b => Bool.rec (motive := fun b => Γ(Y, W b)) 0 1 b
  have hcover : (⊤ : Y.Opens) ≤ iSup W := by
    rw [← hcov]
    exact sup_le (le_iSup W true) (le_iSup W false)
  have hsub : ∀ b b' : Bool, b ≠ b' → Subsingleton Γ(Y, W b ⊓ W b') := by
    intro b b' hbb'
    have h0 : W b ⊓ W b' = ⊥ := by
      cases b <;> cases b' <;> simp_all [W, inf_comm]
    exact CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty h0)
  have hcompat : TopCat.Presheaf.IsCompatible Y.presheaf W sf := by
    intro b b'
    by_cases hbb' : b = b'
    · subst hbb'; rfl
    · haveI := hsub b b' hbb'
      exact Subsingleton.elim _ _
  obtain ⟨e, he, -⟩ := Y.sheaf.existsUnique_gluing' W ⊤ (fun b => homOfLE le_top) hcover sf hcompat
  exact ⟨e, he true, he false⟩

end Glue

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]

abbrev ιk (A : Type u) [CommRing A] [IsLocalRing A] (k : ℕ) :
    Spec (CommRingCat.of (A ⧸ maximalIdeal A ^ k)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ k)))

abbrev Pk (k : ℕ) : Scheme.{u} := pullback q (ιk A k)

abbrev jk (k : ℕ) : Pk q k ⟶ P := pullback.fst q (ιk A k)

lemma range_ιk (k : ℕ) (hk : k ≠ 0) : Set.range (ιk A k) = {closedPoint A} := by
  have h1 : Set.range (ιk A k) =
      PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk (maximalIdeal A ^ k)) : Set A) := by
    rw [← _root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    rfl
  rw [h1, Ideal.mk_ker, PrimeSpectrum.zeroLocus_pow _ hk]
  ext p
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  constructor
  · intro h
    exact PrimeSpectrum.ext ((IsLocalRing.le_maximalIdeal p.2.ne_top).antisymm h)
  · rintro rfl; exact le_rfl

lemma range_jk (k : ℕ) (hk : k ≠ 0) : Set.range (jk q k) = q ⁻¹' {closedPoint A} := by
  rw [Scheme.Pullback.range_fst, range_ιk k hk]

lemma basicOpen_eq_of_res {Y : Scheme.{u}} (U V : Y.Opens) (hcov : U ⊔ V = ⊤) (e : Γ(Y, ⊤))
    (heU : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op e = 1)
    (heV : Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op e = 0) : Y.basicOpen e = U := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.mem_basicOpen_top]
  constructor
  · intro hunit
    by_contra hxU
    have hxV : x ∈ V := by
      have : x ∈ (U ⊔ V : Y.Opens) := by rw [hcov]; trivial
      exact (Opens.mem_sup.mp this).resolve_left hxU
    have hgerm : Y.presheaf.germ ⊤ x trivial e = 0 := by
      rw [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : V ≤ ⊤)) x hxV, heV, map_zero]
    rw [hgerm] at hunit
    exact not_isUnit_zero hunit
  · intro hxU
    rw [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU, heU, map_one]
    exact isUnit_one

theorem main (hq : Function.Bijective q.appTop) : _root_.IsPreconnected (q ⁻¹' {closedPoint A}) := by
  by_contra hnot
  simp only [_root_.IsPreconnected, not_forall, exists_prop, Set.not_nonempty_iff_eq_empty] at hnot
  obtain ⟨u, v, hu, hv, hsub, hsu, hsv, huv⟩ := hnot
  obtain ⟨c, hc⟩ := AlgebraicGeometry.exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper
    (maximalIdeal A) q 1

  let τ : Pk q 1 ⟶ Pk q (1 + c) :=
    pullback.map q (ιk A 1) q (ιk A (1 + c)) (𝟙 P) (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right 1 c)))))
      (𝟙 _) (by simp) (by
        rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          Ideal.Quotient.factor_comp_mk])
  have hτ : τ ≫ jk q (1 + c) = jk q 1 := by
    simp only [τ, pullback.lift_fst, Category.comp_id]

  let U' : (Pk q (1 + c)).Opens := jk q (1 + c) ⁻¹ᵁ ⟨u, hu⟩
  let V' : (Pk q (1 + c)).Opens := jk q (1 + c) ⁻¹ᵁ ⟨v, hv⟩
  have hrange := range_jk q (1 + c) (by omega)
  have hcov' : U' ⊔ V' = ⊤ := by
    apply top_le_iff.mp
    intro y _
    have hy : jk q (1 + c) y ∈ q ⁻¹' {closedPoint A} := by rw [← hrange]; exact ⟨y, rfl⟩
    rcases hsub hy with h | h
    · exact Opens.mem_sup.mpr (Or.inl h)
    · exact Opens.mem_sup.mpr (Or.inr h)
  have hdisj' : U' ⊓ V' = ⊥ := by
    apply le_bot_iff.mp
    rintro y ⟨hyu, hyv⟩
    have hy : jk q (1 + c) y ∈ q ⁻¹' {closedPoint A} := by rw [← hrange]; exact ⟨y, rfl⟩
    have : jk q (1 + c) y ∈ q ⁻¹' {closedPoint A} ∩ (u ∩ v) := ⟨hy, hyu, hyv⟩
    rw [huv] at this
    exact this
  obtain ⟨e, heU, heV⟩ := exists_section_eq_one_eq_zero U' V' hcov' hdisj'
  have hbasic : (Pk q (1 + c)).basicOpen e = U' := basicOpen_eq_of_res U' V' hcov' e heU heV

  obtain ⟨a, ha⟩ := hc e
  change τ.appTop e = (jk q 1).appTop a at ha
  have hb1 : (Pk q 1).basicOpen ((jk q 1).appTop a) = jk q 1 ⁻¹ᵁ ⟨u, hu⟩ := by
    rw [← ha, ← Scheme.preimage_basicOpen_top, hbasic]
    show (τ ≫ jk q (1 + c)) ⁻¹ᵁ ⟨u, hu⟩ = _
    rw [hτ]

  obtain ⟨b, rfl⟩ := hq.2 a
  have hrange1 := range_jk q 1 one_ne_zero
  by_cases hbu : IsUnit b
  ·
    have htop : jk q 1 ⁻¹ᵁ ⟨u, hu⟩ = ⊤ := by
      rw [← hb1]
      exact Scheme.basicOpen_of_isUnit _ ((hbu.map q.appTop.hom).map (jk q 1).appTop.hom)
    obtain ⟨x, hxS, hxv⟩ := hsv
    obtain ⟨y, rfl⟩ : x ∈ Set.range (jk q 1) := by rw [hrange1]; exact hxS
    have hyu : y ∈ jk q 1 ⁻¹ᵁ ⟨u, hu⟩ := by rw [htop]; trivial
    have : jk q 1 y ∈ q ⁻¹' {closedPoint A} ∩ (u ∩ v) := ⟨hxS, hyu, hxv⟩
    rw [huv] at this
    exact this
  ·
    have hb0 : (ιk A 1).appTop b = 0 := by
      have hnat := Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ 1)))
      have h1 : (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ maximalIdeal A ^ 1))).hom
          ((ιk A 1).appTop b) = Ideal.Quotient.mk (maximalIdeal A ^ 1)
            ((Scheme.ΓSpecIso (CommRingCat.of A)).hom b) := by
        have := congrArg (fun g => (CommRingCat.Hom.hom g) b) hnat
        simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          CommRingCat.hom_ofHom] at this
        exact this
      have h2 : Ideal.Quotient.mk (maximalIdeal A ^ 1)
          ((Scheme.ΓSpecIso (CommRingCat.of A)).hom b) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu'
        exact hbu (by simpa using hu'.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      rw [h2] at h1
      exact (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ maximalIdeal A ^ 1))).commRingCatIsoToRingEquiv.injective
        (h1.trans (map_zero _).symm)
    have hzero : (jk q 1).appTop (q.appTop b) = 0 := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, hb0, map_zero]
    have hbot : jk q 1 ⁻¹ᵁ ⟨u, hu⟩ = ⊥ := by
      rw [← hb1, hzero, Scheme.basicOpen_zero]
    obtain ⟨x, hxS, hxu⟩ := hsu
    obtain ⟨y, rfl⟩ : x ∈ Set.range (jk q 1) := by rw [hrange1]; exact hxS
    have hyu : y ∈ jk q 1 ⁻¹ᵁ ⟨u, hu⟩ := hxu
    rw [hbot] at hyu
    exact hyu

end Main

end SolZ1

end

open AlgebraicGeometry in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (hq : Function.Bijective q.appTop) :
    IsPreconnected (q ⁻¹' {IsLocalRing.closedPoint A}) :=
  SolZ1.main q hq

end S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop (solution)
