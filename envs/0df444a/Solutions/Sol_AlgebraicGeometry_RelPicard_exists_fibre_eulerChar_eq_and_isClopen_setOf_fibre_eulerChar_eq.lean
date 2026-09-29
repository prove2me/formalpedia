-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/26cf5dab-dad8-5914-b966-97a791ee4016

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_linearEquiv_H1_sectionsOf_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq.AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq.AlgebraicGeometry.RelPicard"
open scoped TensorProduct

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsProper Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf LocallyOfFiniteType Spec Scheme IsOpenImmersion Flat IsSeparated HasRingHomProperty.appLE exists_isAffineOpen_mem_and_subset isAffineOpen_top Scheme.fromSpecResidueField_apply IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom HasRingHomProperty Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange RelPicard.exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "fibreAt fibreModule exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField"
namespace ChiClopen
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "TopologicalSpace Opposite AlgebraicGeometry.Scheme.TwoAffineOpenCover"

section H0

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (M : X.Modules)

noncomputable def absheaf : TopCat.Sheaf Ab X := ⟨M.presheaf, ((SheafOfModules.toSheaf _).obj M).property⟩

noncomputable def toH0M (𝒱 : X.TwoAffineOpenCover) :
    letI := moduleSectionsOfHom c M ⊤
    Γ(M, ⊤) →ₗ[R] (𝒱.sectionsOf c M).H0 :=
  letI := moduleSectionsOfHom c M ⊤
  letI := moduleSectionsOfHom c M 𝒱.U0
  letI := moduleSectionsOfHom c M 𝒱.U1
  LinearMap.codRestrict _ ((restrictSections c M (le_top : 𝒱.U0 ≤ ⊤)).prod (restrictSections c M (le_top : 𝒱.U1 ≤ ⊤)))
    (fun s => by
      rw [TwoChartCech.Sections.mem_H0_iff]
      show M.presheaf.map (homOfLE inf_le_left).op (M.presheaf.map (homOfLE le_top).op s) =
        M.presheaf.map (homOfLE inf_le_right).op (M.presheaf.map (homOfLE le_top).op s)
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl)

def chart (𝒱 : X.TwoAffineOpenCover) : ULift.{u} Bool → X.Opens := fun b => if b.down then 𝒱.U1 else 𝒱.U0

theorem iSup_chart (𝒱 : X.TwoAffineOpenCover) : (⊤ : X.Opens) ≤ ⨆ b, chart 𝒱 b := by
  rw [← 𝒱.sup_eq_top]
  refine sup_le ?_ ?_
  · exact le_iSup_of_le ⟨false⟩ le_rfl
  · exact le_iSup_of_le ⟨true⟩ le_rfl

theorem toH0M_bijective (𝒱 : X.TwoAffineOpenCover) : Function.Bijective (toH0M c M 𝒱) := by
  letI := moduleSectionsOfHom c M ⊤
  constructor
  · intro s s' h
    have h0 : M.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op s = M.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op s' :=
      congrArg (fun p : (𝒱.sectionsOf c M).H0 => p.1.1) h
    have h1 : M.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op s = M.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op s' :=
      congrArg (fun p : (𝒱.sectionsOf c M).H0 => p.1.2) h
    apply (absheaf M).eq_of_locally_eq' (chart 𝒱) ⊤ (fun b => homOfLE le_top) (iSup_chart 𝒱)
    rintro ⟨b⟩
    cases b
    · exact h0
    · exact h1
  · rintro ⟨⟨m0, m1⟩, hm⟩
    rw [TwoChartCech.Sections.mem_H0_iff] at hm
    change M.presheaf.map (homOfLE inf_le_left).op m0 = M.presheaf.map (homOfLE inf_le_right).op m1 at hm

    let sf : ∀ b : ULift.{u} Bool, (absheaf M).1.obj (op (chart 𝒱 b)) := fun b =>
      match b with
      | ⟨false⟩ => m0
      | ⟨true⟩ => m1
    have hcomp : TopCat.Presheaf.IsCompatible (absheaf M).1 (chart 𝒱) sf := by
      rintro ⟨b⟩ ⟨b'⟩
      cases b <;> cases b'
      · rfl
      ·
        exact hm
      ·
        show M.presheaf.map (homOfLE (inf_le_left : 𝒱.U1 ⊓ 𝒱.U0 ≤ 𝒱.U1)).op m1 =
          M.presheaf.map (homOfLE (inf_le_right : 𝒱.U1 ⊓ 𝒱.U0 ≤ 𝒱.U0)).op m0
        have e : 𝒱.U1 ⊓ 𝒱.U0 ≤ 𝒱.U0 ⊓ 𝒱.U1 := le_of_eq (inf_comm _ _)
        have := congrArg (M.presheaf.map (homOfLE e).op) hm
        rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← CategoryTheory.comp_apply, ← Functor.map_comp] at this
        exact this.symm
      · rfl
    obtain ⟨s, hs, -⟩ := (absheaf M).existsUnique_gluing' (chart 𝒱) ⊤ (fun b => homOfLE le_top) (iSup_chart 𝒱) sf hcomp
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact Prod.ext (hs ⟨false⟩) (hs ⟨true⟩)

theorem finrank_H0_eq [Module.Finite R R] (𝒱 𝒱' : X.TwoAffineOpenCover) :
    Module.finrank R (𝒱.sectionsOf c M).H0 = Module.finrank R (𝒱'.sectionsOf c M).H0 := by
  letI := moduleSectionsOfHom c M ⊤
  exact ((LinearEquiv.ofBijective _ (toH0M_bijective c M 𝒱)).symm ≪≫ₗ
    LinearEquiv.ofBijective _ (toH0M_bijective c M 𝒱')).finrank_eq

end H0

section Chart

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
  {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) [LocallyOfFiniteType t]
  (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)

noncomputable abbrev reading {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) : ℤ :=
  (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 : ℤ) -
    Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1

omit [IsNoetherianRing R] [Flat c] [LocallyOfFiniteType t] in
theorem isSeparated_fibreAt {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) : IsSeparated (fibreAt c t s) := by
  unfold fibreAt; infer_instance

include 𝒱 hM in

theorem exists_idx (U : T.Opens) (hU : IsAffineOpen U) :
    ∃ idx : (Spec Γ(T, U) : Scheme.{u}) → ℤ, IsLocallyConstant idx ∧
      ∀ (𝔭 : Spec Γ(T, U)) (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
        s.base (IsLocalRing.closedPoint k) = hU.fromSpec.base 𝔭 →
          Nonempty (pullback (pullback.snd c t) s).TwoAffineOpenCover ∧
          ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover, reading c t M s 𝒲 = idx 𝔭 := by

  haveI : IsNoetherianRing Γ(T, U) := by
    have hft : (t.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType t inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    letI := (t.appLE ⊤ U le_top).hom.toAlgebra
    haveI : Algebra.FiniteType Γ(Spec (CommRingCat.of R), ⊤) Γ(T, U) := hft
    haveI : IsNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) :=
      isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
    exact Algebra.FiniteType.isNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) Γ(T, U)

  let j : Spec Γ(T, U) ⟶ T := hU.fromSpec
  haveI : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  let CA : Scheme.{u} := pullback (pullback.snd c t) j
  let πA : CA ⟶ Spec Γ(T, U) := pullback.snd _ _
  let g' : CA ⟶ pullback c t := pullback.fst _ _
  have hcart : IsPullback g' πA (pullback.snd c t) j := IsPullback.of_hasPullback _ _
  have big : IsPullback (g' ≫ pullback.fst c t) πA c (j ≫ t) := hcart.paste_horiz (IsPullback.of_hasPullback c t)
  haveI : IsProper πA := inferInstance
  haveI : Flat πA := inferInstance

  haveI : IsAffineHom (g' ≫ pullback.fst c t) := MorphismProperty.of_isPullback (P := @IsAffineHom) big.flip inferInstance
  let 𝒱A : CA.TwoAffineOpenCover :=
    { U0 := (g' ≫ pullback.fst c t) ⁻¹ᵁ 𝒱.U0
      U1 := (g' ≫ pullback.fst c t) ⁻¹ᵁ 𝒱.U1
      isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage _
      isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage _
      sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
      isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage _ }

  let d := (𝒱A.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff
  let idx : (Spec Γ(T, U) : Scheme.{u}) → ℤ := fun 𝔭 =>
    (Module.finrank 𝔭.asIdeal.ResidueField (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField)) : ℤ) -
      Module.finrank 𝔭.asIdeal.ResidueField
        ((𝔭.asIdeal.ResidueField ⊗[Γ(T, U)] (𝒱A.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).M01) ⧸
          LinearMap.range (d.baseChange 𝔭.asIdeal.ResidueField))
  have hidx : IsLocallyConstant idx :=
    Scheme.TwoAffineOpenCover.isLocallyConstant_finrank_ker_sub_finrank_coker_cechDiff_baseChange πA 𝒱A _ (hM.pullback g')
  refine ⟨idx, hidx, fun 𝔭 k _ s hs => ?_⟩

  obtain ⟨𝒲₀, h𝒲₀⟩ := RelPicard.exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
    c t j πA g' hcart 𝒱A 𝔭 s hs
  obtain ⟨hH0, hH1⟩ := h𝒲₀ M hM
  refine ⟨⟨𝒲₀⟩, fun 𝒲 => ?_⟩
  have e0 : Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 =
      Module.finrank k (𝒲₀.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 :=
    finrank_H0_eq (fibreAt c t s) (fibreModule c t s M) 𝒲 𝒲₀
  haveI := isSeparated_fibreAt c t s
  have htriv := (hM.pullback (pullback.fst (pullback.snd c t) s))
  obtain ⟨eH1⟩ := Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated (fibreAt c t s)
    (fibreModule c t s M) htriv.exists_trivialization 𝒲 𝒲₀
  have e1 : Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 =
      Module.finrank k (𝒲₀.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 := eH1.finrank_eq
  simp only [reading, e0, e1, hH0, hH1, idx, d]

end Chart

end AlgebraicGeometry.RelPicard.ChiClopen

open AlgebraicGeometry.RelPicard.ChiClopen in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    (∀ x : T, ∃ e : ℤ, ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 = e) ∧
    ∀ e : ℤ, IsClopen {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 = e} := by
  classical

  have key : ∀ x : T, ∃ (U : T.Opens) (hU : IsAffineOpen U) (idx : (Spec Γ(T, U) : Scheme.{u}) → ℤ),
      x ∈ U ∧ IsLocallyConstant idx ∧
      ∀ (𝔭 : Spec Γ(T, U)) (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
        s.base (IsLocalRing.closedPoint k) = hU.fromSpec.base 𝔭 →
          Nonempty (pullback (pullback.snd c t) s).TwoAffineOpenCover ∧
          ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover, reading c t M s 𝒲 = idx 𝔭 := by
    intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := T) (x := x) (U := ⊤) trivial
    obtain ⟨idx, hidx, h⟩ := exists_idx c 𝒱 t M hM U hU
    exact ⟨U, hU, idx, hxU, hidx, h⟩
  have hpt : ∀ {U : T.Opens} (hU : IsAffineOpen U) {x : T}, x ∈ U → ∃ 𝔭 : Spec Γ(T, U), hU.fromSpec.base 𝔭 = x :=
    fun {U} hU {x} hx => show x ∈ Set.range hU.fromSpec.base by rw [hU.range_fromSpec]; exact hx

  set S : ℤ → Set T := fun e => {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover, reading c t M s 𝒲 = e} with hS

  have hchart : ∀ {U : T.Opens} (hU : IsAffineOpen U) (idx : (Spec Γ(T, U) : Scheme.{u}) → ℤ),
      (∀ (𝔭 : Spec Γ(T, U)) (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
        s.base (IsLocalRing.closedPoint k) = hU.fromSpec.base 𝔭 →
          Nonempty (pullback (pullback.snd c t) s).TwoAffineOpenCover ∧
          ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover, reading c t M s 𝒲 = idx 𝔭) →
      ∀ (𝔭 : Spec Γ(T, U)) (e : ℤ), hU.fromSpec.base 𝔭 ∈ S e ↔ idx 𝔭 = e := by
    intro U hU idx h 𝔭 e
    constructor
    · intro hx

      have hs : (T.fromSpecResidueField (hU.fromSpec.base 𝔭)).base (IsLocalRing.closedPoint _) = hU.fromSpec.base 𝔭 :=
        Scheme.fromSpecResidueField_apply _ _
      obtain ⟨⟨𝒲⟩, hW⟩ := h 𝔭 _ (T.fromSpecResidueField (hU.fromSpec.base 𝔭)) hs
      rw [← hW 𝒲]
      exact hx _ _ hs 𝒲
    · rintro rfl k _ s hs 𝒲
      exact (h 𝔭 k s hs).2 𝒲
  refine ⟨fun x => ?_, fun e => ?_⟩
  · obtain ⟨U, hU, idx, hxU, -, h⟩ := key x
    obtain ⟨𝔭, rfl⟩ := hpt hU hxU
    exact ⟨idx 𝔭, fun k _ s hs 𝒲 => (h 𝔭 k s hs).2 𝒲⟩
  ·
    show IsClopen (S e)
    have hopen : ∀ e', IsOpen (S e') := by
      intro e'
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨U, hU, idx, hxU, hidx, h⟩ := key x
      obtain ⟨𝔭, rfl⟩ := hpt hU hxU
      refine ⟨hU.fromSpec.base '' {𝔮 | idx 𝔮 = e'}, ?_, ?_, ⟨𝔭, (hchart hU idx h 𝔭 e').mp hx, rfl⟩⟩
      · rintro _ ⟨𝔮, h𝔮, rfl⟩
        exact (hchart hU idx h 𝔮 e').mpr h𝔮
      · exact hU.fromSpec.isOpenEmbedding.isOpenMap _ (hidx.isOpen_fiber e')
    refine ⟨?_, hopen e⟩

    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, hU, idx, hxU, hidx, h⟩ := key x
    obtain ⟨𝔭, rfl⟩ := hpt hU hxU
    have hne : idx 𝔭 ≠ e := fun heq => hx ((hchart hU idx h 𝔭 e).mpr heq)
    refine ⟨S (idx 𝔭), ?_, hopen _, (hchart hU idx h 𝔭 (idx 𝔭)).mpr rfl⟩
    intro y hy hye

    obtain ⟨U', hU', idx', hyU', -, h'⟩ := key y
    obtain ⟨𝔮, rfl⟩ := hpt hU' hyU'
    have hs : (T.fromSpecResidueField (hU'.fromSpec.base 𝔮)).base (IsLocalRing.closedPoint _) = hU'.fromSpec.base 𝔮 :=
      Scheme.fromSpecResidueField_apply _ _
    obtain ⟨⟨𝒲⟩, -⟩ := h' 𝔮 _ (T.fromSpecResidueField (hU'.fromSpec.base 𝔮)) hs
    exact hne ((hy _ _ hs 𝒲).symm.trans (hye _ _ hs 𝒲))

end S_AlgebraicGeometry_RelPicard_exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq (solution)
