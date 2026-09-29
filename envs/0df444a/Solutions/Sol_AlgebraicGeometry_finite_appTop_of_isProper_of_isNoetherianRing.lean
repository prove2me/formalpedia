-- Prove2me | solution 1 for AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/29ac09b0-72ec-5f82-ad2d-63be4b76ae00

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace SolH0F

variable {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))

section Cover

variable [CompactSpace P]

noncomputable def cover (P : Scheme.{u}) [CompactSpace P] : P.OrderedAffineCover :=
  letI 𝒰 := P.affineCover.finiteSubcover
  letI : LinearOrder 𝒰.I₀ :=
    LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
  { ι := 𝒰.I₀
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Cover

section H0

variable (K : P.OrderedAffineCover)

def vtx (i : K.ι) : K.Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by
  have : a = b := (Fin.eq_zero a).trans (Fin.eq_zero b).symm
  simp [this])⟩

lemma idx0_eq_vtx (s : K.Idx 0) : s = vtx K (s.1 0) := by
  apply Subtype.ext
  funext k
  have hk : k = 0 := Fin.eq_zero k
  subst hk; rfl

def edge {i j : K.ι} (h : i < j) : K.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr (fun k => by
    have hk : k = 0 := Fin.eq_zero k
    subst hk; simpa using h)⟩

lemma face_edge_zero {i j : K.ι} (h : i < j) : K.face (edge K h) 0 = vtx K j := by
  apply Subtype.ext; funext k
  have hk : k = 0 := Fin.eq_zero k
  subst hk
  simp [Scheme.OrderedAffineCover.face_val, edge, vtx, Fin.succAbove_zero]

lemma face_edge_one {i j : K.ι} (h : i < j) : K.face (edge K h) 1 = vtx K i := by
  apply Subtype.ext; funext k
  have hk : k = 0 := Fin.eq_zero k
  subst hk
  have : (1 : Fin 2) = Fin.last 1 := rfl
  simp [Scheme.OrderedAffineCover.face_val, edge, vtx, this]

lemma inter_edge_le_left {i j : K.ι} (h : i < j) : K.inter (edge K h) ≤ K.inter (vtx K i) :=
  le_iInf fun _ => (K.inter_le (edge K h) 0).trans (le_of_eq rfl)

lemma inter_edge_le_right {i j : K.ι} (h : i < j) : K.inter (edge K h) ≤ K.inter (vtx K j) :=
  le_iInf fun _ => (K.inter_le (edge K h) 1).trans (le_of_eq rfl)

lemma inf_vtx_le_inter_edge {i j : K.ι} (h : i < j) :
    K.inter (vtx K i) ⊓ K.inter (vtx K j) ≤ K.inter (edge K h) := by
  refine le_iInf fun k => ?_
  fin_cases k
  · exact inf_le_left.trans ((K.inter_le (vtx K i) 0).trans (le_of_eq rfl))
  · exact inf_le_right.trans ((K.inter_le (vtx K j) 0).trans (le_of_eq rfl))

lemma U_le_inter_vtx (i : K.ι) : K.U i ≤ K.inter (vtx K i) := le_iInf fun _ => le_rfl

lemma iSup_inter_vtx : (⊤ : P.Opens) ≤ ⨆ i, K.inter (vtx K i) := by
  rw [← K.iSup_eq_top]
  exact iSup_mono fun i => U_le_inter_vtx K i

noncomputable def toCochain : (OModulePresheaf.unit q).obj ⊤ →ₗ[A] (OModulePresheaf.unit q).cochain K 0 :=
  LinearMap.pi fun s => (OModulePresheaf.unit q).res (le_top : K.inter s ≤ ⊤)

lemma toCochain_apply (x : (OModulePresheaf.unit q).obj ⊤) (s : K.Idx 0) :
    toCochain q K x s = (OModulePresheaf.unit q).res (le_top : K.inter s ≤ ⊤) x := rfl

lemma d_toCochain (x : (OModulePresheaf.unit q).obj ⊤) :
    (OModulePresheaf.unit q).d K 0 (toCochain q K x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply]
  simp only [toCochain_apply, OModulePresheaf.res_res, Pi.zero_apply]
  rw [Fin.sum_univ_two]
  simp

lemma range_toCochain_le : LinearMap.range (toCochain q K) ≤ (OModulePresheaf.unit q).H0 K := by
  rintro _ ⟨x, rfl⟩
  exact d_toCochain q K x

lemma toCochain_injective : Function.Injective (toCochain q K) := by
  intro x y hxy
  refine P.sheaf.eq_of_locally_eq' (fun i => K.inter (vtx K i)) ⊤ (fun i => homOfLE le_top)
    (iSup_inter_vtx K) x y fun i => ?_
  exact congr_fun hxy (vtx K i)

lemma toCochain_surjective (c : (OModulePresheaf.unit q).cochain K 0)
    (hc : (OModulePresheaf.unit q).d K 0 c = 0) : ∃ x, toCochain q K x = c := by

  let sf : ∀ i : K.ι, Γ(P, K.inter (vtx K i)) := fun i => c (vtx K i)
  have key : ∀ {i j : K.ι} (h : i < j),
      (P.presheaf.map (homOfLE (inter_edge_le_left K h)).op).hom (sf i) =
        (P.presheaf.map (homOfLE (inter_edge_le_right K h)).op).hom (sf j) := by
    intro i j h
    have := congr_fun hc (edge K h)
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at this
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      Pi.zero_apply] at this
    rw [add_neg_eq_zero] at this

    have h0 := face_edge_zero K h
    have h1 := face_edge_one K h

    have e0 : ∀ (t : K.Idx 0) (ht : t = vtx K j) (le : K.inter (edge K h) ≤ K.inter t),
        (OModulePresheaf.unit q).res le (c t) =
          (P.presheaf.map (homOfLE (inter_edge_le_right K h)).op).hom (sf j) := by
      rintro t rfl le; rfl
    have e1 : ∀ (t : K.Idx 0) (ht : t = vtx K i) (le : K.inter (edge K h) ≤ K.inter t),
        (OModulePresheaf.unit q).res le (c t) =
          (P.presheaf.map (homOfLE (inter_edge_le_left K h)).op).hom (sf i) := by
      rintro t rfl le; rfl
    rw [e0 _ h0, e1 _ h1] at this
    exact this.symm
  have hcompat : TopCat.Presheaf.IsCompatible P.presheaf (fun i => K.inter (vtx K i)) sf := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · have := congr_arg (P.presheaf.map (homOfLE (inf_vtx_le_inter_edge K hij)).op).hom (key hij)
      simp only [← CommRingCat.comp_apply, ← P.presheaf.map_comp] at this
      exact this
    · rfl
    · have := congr_arg (P.presheaf.map (homOfLE ((le_of_eq (inf_comm _ _)).trans
        (inf_vtx_le_inter_edge K hji))).op).hom (key hji)
      simp only [← CommRingCat.comp_apply, ← P.presheaf.map_comp] at this
      exact this.symm
  obtain ⟨x, hx, -⟩ := P.sheaf.existsUnique_gluing' (fun i => K.inter (vtx K i)) ⊤
    (fun i => homOfLE le_top) (iSup_inter_vtx K) sf hcompat
  refine ⟨x, funext fun s => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, s = vtx K i := ⟨_, idx0_eq_vtx K s⟩
  exact hx i

noncomputable def globalEquivH0 :
    (OModulePresheaf.unit q).obj ⊤ ≃ₗ[A] (OModulePresheaf.unit q).H0 K :=
  LinearEquiv.ofBijective ((toCochain q K).codRestrict _ fun x => d_toCochain q K x)
    ⟨fun x y h => toCochain_injective q K (congr_arg Subtype.val h),
     fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := toCochain_surjective q K c hc
      exact ⟨x, rfl⟩⟩

end H0

theorem finite_appTop [IsNoetherianRing A] [IsProper q] : q.appTop.hom.Finite := by
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  let K := cover P
  have hfin : Module.Finite A ((OModulePresheaf.unit q).H0 K) :=
    (AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isProper q K).1
  have hΓ : Module.Finite A ((OModulePresheaf.unit q).obj ⊤) :=
    Module.Finite.equiv (globalEquivH0 q K).symm

  have h1 : ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appLE ⊤ ⊤ le_top).hom.Finite := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
    exact hΓ
  have h2 : q.appLE ⊤ ⊤ le_top = q.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [h2] at h1
  exact RingHom.Finite.of_comp_finite h1

end SolH0F

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] :
    q.appTop.hom.Finite :=
  SolH0F.finite_appTop q

end S_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing
end P2MW
export P2MW.S_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing (solution)
