-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/08c74dd5-89ba-599f-9db9-897203153d2a

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry"

noncomputable section

namespace FormalGAGAFiniteSqZeroAux

p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite TrivSqZeroExt"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (.of A)} (F : OModulePresheaf q)

scoped instance instModuleMop (U : P.Opens) : Module (Γ(P, U))ᵐᵒᵖ (F.obj U) :=
  Module.compHom (F.obj U) ((RingHom.id Γ(P, U)).fromOpposite fun a b => mul_comm a b)

scoped instance instIsCentralScalar (U : P.Opens) : IsCentralScalar Γ(P, U) (F.obj U) := ⟨fun _ _ => rfl⟩

abbrev T (U : P.Opens) : Type u := TrivSqZeroExt Γ(P, U) (F.obj U)

example (U : P.Opens) : CommRing (T F U) := inferInstance

abbrev rmap {U V : P.Opens} (h : V ≤ U) : Γ(P, U) →+* Γ(P, V) := (P.presheaf.map (homOfLE h).op).hom

def ρ {U V : P.Opens} (h : V ≤ U) : T F U →+* T F V where
  toFun x := (rmap h x.fst, F.res h x.snd)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · change F.res h (x.fst • y.snd + MulOpposite.op y.fst • x.snd) =
        rmap h x.fst • F.res h y.snd + MulOpposite.op (rmap h y.fst) • F.res h x.snd
      rw [map_add, op_smul_eq_smul, op_smul_eq_smul, F.res_smul, F.res_smul]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp

@[scoped simp] lemma fst_ρ {U V : P.Opens} (h : V ≤ U) (x : T F U) : (ρ F h x).fst = rmap h x.fst := rfl
@[scoped simp] lemma snd_ρ {U V : P.Opens} (h : V ≤ U) (x : T F U) : (ρ F h x).snd = F.res h x.snd := rfl

lemma ρ_inl {U V : P.Opens} (h : V ≤ U) (a : Γ(P, U)) : ρ F h (inl a) = inl (rmap h a) :=
  TrivSqZeroExt.ext rfl (by simp)

lemma ρ_inr {U V : P.Opens} (h : V ≤ U) (m : F.obj U) : ρ F h (inr m) = inr (F.res h m) :=
  TrivSqZeroExt.ext (by simp) rfl

lemma ρ_refl (U : P.Opens) : ρ F (le_refl U) = RingHom.id _ := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · change (P.presheaf.map (homOfLE (le_refl U)).op).hom x.fst = x.fst
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), P.presheaf.map_id]; rfl
  · exact F.res_refl_apply U x.snd

lemma ρ_comp {U V W : P.Opens} (h : W ≤ V) (h' : V ≤ U) : (ρ F h).comp (ρ F h') = ρ F (h.trans h') := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · change (P.presheaf.map (homOfLE h).op).hom ((P.presheaf.map (homOfLE h').op).hom x.fst) =
      (P.presheaf.map (homOfLE (h.trans h')).op).hom x.fst
    rw [← CommRingCat.comp_apply, ← P.presheaf.map_comp]; rfl
  · exact F.res_res h h' x.snd

lemma ρ_ρ {U V W : P.Opens} (h : W ≤ V) (h' : V ≤ U) (x : T F U) : ρ F h (ρ F h' x) = ρ F (h.trans h') x :=
  RingHom.congr_fun (ρ_comp F h h') x

def Tfun : P.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (T F U.unop.1)
  map {U V} i := CommRingCat.ofHom (ρ F (toOpens_mono i.unop.le))
  map_id U := by
    ext1
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id]
    exact ρ_refl F U.unop.1
  map_comp {U V W} i j := by
    ext1
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    exact (ρ_comp F _ _).symm

@[scoped simp] lemma Tfun_obj (U : P.AffineZariskiSiteᵒᵖ) : (Tfun F).obj U = CommRingCat.of (T F U.unop.1) := rfl
@[scoped simp] lemma Tfun_map {U V : P.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) :
    (Tfun F).map i = CommRingCat.ofHom (ρ F (toOpens_mono i.unop.le)) := rfl

def α : (toOpensFunctor P).op ⋙ P.presheaf ⟶ Tfun F where
  app U := (CommRingCat.ofHom (algebraMap Γ(P, U.unop.1) (T F U.unop.1)) :
    P.presheaf.obj (op U.unop.1) ⟶ CommRingCat.of (T F U.unop.1))
  naturality {U V} i := by
    ext a
    change algebraMap Γ(P, V.unop.1) (T F V.unop.1) (rmap (toOpens_mono i.unop.le) a) =
      ρ F (toOpens_mono i.unop.le) (algebraMap Γ(P, U.unop.1) (T F U.unop.1) a)
    rw [algebraMap_eq_inl, algebraMap_eq_inl, ρ_inl]

@[scoped simp] lemma α_app (U : P.AffineZariskiSiteᵒᵖ) :
    (α F).app U = (CommRingCat.ofHom (algebraMap Γ(P, U.unop.1) (T F U.unop.1)) :
      P.presheaf.obj (op U.unop.1) ⟶ CommRingCat.of (T F U.unop.1)) := rfl

variable {F}

set_option backward.isDefEq.respectTransparency false in

lemma coequifibered (hq : F.IsQuasicoherent) : (α F).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U f ↦ ?_
  simp only [α_app, CommRingCat.hom_ofHom]
  letI inst : Algebra (T F U.1) (T F (P.basicOpen f)) := (ρ F (P.basicOpen_le f)).toAlgebra
  change IsLocalization.Away (algebraMap Γ(P, U.1) (T F U.1) f) (T F (P.basicOpen f))
  have hΓ : IsLocalization.Away f Γ(P, P.basicOpen f) := U.2.isLocalization_basicOpen f
  have halg : ∀ x : T F U.1, algebraMap (T F U.1) (T F (P.basicOpen f)) x = ρ F (P.basicOpen_le f) x :=
    fun _ => rfl
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · rintro ⟨_, k, rfl⟩
    rw [halg, map_pow, algebraMap_eq_inl, ρ_inl]
    refine IsUnit.pow k (isUnit_inl_iff.mpr ?_)
    exact IsLocalization.map_units (M := .powers f) Γ(P, P.basicOpen f) ⟨f, 1, pow_one f⟩
  · intro z
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, ha⟩ := IsLocalization.surj (.powers f) z.fst
    obtain ⟨k', m, hm⟩ := (hq U f).1 z.snd
    change z.fst * rmap (P.basicOpen_le f) (f ^ k) = rmap (P.basicOpen_le f) a at ha
    refine ⟨⟨algebraMap _ _ (f ^ k') * inl a + algebraMap _ _ (f ^ k) * inr m,
      ⟨algebraMap _ _ (f ^ (k + k')), k + k', (map_pow _ _ _).symm⟩⟩, ?_⟩
    change z * ρ F _ (algebraMap _ _ (f ^ (k + k'))) =
      ρ F _ (algebraMap _ _ (f ^ k') * inl a + algebraMap _ _ (f ^ k) * inr m)
    simp only [map_add, map_mul, algebraMap_eq_inl, ρ_inl, ρ_inr, inl_mul_inl, inl_mul_inr]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_mul, fst_add, fst_inl, fst_inl, fst_inr, add_zero, map_pow, pow_add, ← mul_assoc,
        ← map_pow, ha, mul_comm, map_pow]
    · rw [snd_mul, snd_add, snd_inl, snd_inl, snd_inr, fst_inl, smul_zero, zero_add, zero_add,
        op_smul_eq_smul, F.res_smul, hm, ← mul_smul, ← map_mul, ← pow_add]
  · intro x y hxy
    rw [halg, halg] at hxy
    have h1 : rmap (P.basicOpen_le f) x.fst = rmap (P.basicOpen_le f) y.fst := congrArg fst hxy
    have h2 : F.res (P.basicOpen_le f) (x.snd - y.snd) = 0 := by
      rw [map_sub, sub_eq_zero]; exact congrArg snd hxy
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := .powers f) h1
    obtain ⟨k', hk'⟩ := (hq U f).2 _ h2
    change f ^ k * x.fst = f ^ k * y.fst at hk
    refine ⟨⟨algebraMap _ _ (f ^ (k + k')), k + k', (map_pow _ _ _).symm⟩, ?_⟩
    change algebraMap _ _ (f ^ (k + k')) * x = algebraMap _ _ (f ^ (k + k')) * y
    rw [← sub_eq_zero, ← mul_sub, algebraMap_eq_inl]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_mul, fst_inl, fst_sub, fst_zero, mul_sub, pow_add, mul_comm (f ^ k), mul_assoc, mul_assoc, hk,
        sub_self]
    · rw [snd_mul, fst_inl, snd_inl, snd_sub, snd_zero, smul_zero, add_zero, pow_add, mul_smul, hk', smul_zero]

section Scheme

variable (hq : F.IsQuasicoherent)

def D : (directedCover P).RelativeGluingData := relativeGluingData (coequifibered hq)

scoped instance : ((D hq).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

abbrev Y : Scheme.{u} := (D hq).glued

abbrev p : Y hq ⟶ P := (D hq).toBase

def ιU (U : P.AffineZariskiSite) : Spec (CommRingCat.of (T F U.1)) ⟶ Y hq := colimit.ι (D hq).functor U

lemma D_cover_f (U : P.AffineZariskiSite) : (D hq).cover.f U = ιU hq U := by
  simp [D, ιU]

scoped instance ιU_isOpenImmersion (U : P.AffineZariskiSite) : IsOpenImmersion (ιU hq U) := by
  rw [← D_cover_f]; exact (D hq).cover.map_prop U

lemma D_functor_map {U V : P.AffineZariskiSite} (i : U ⟶ V) :
    (D hq).functor.map i = Spec.map (CommRingCat.ofHom (ρ F (toOpens_mono i.le))) := rfl

include hq in

lemma isOpenImmersion_SpecMap_ρ {U V : P.AffineZariskiSite} (i : U ⟶ V) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (ρ F (toOpens_mono i.le))) :
      Spec (CommRingCat.of (T F U.1)) ⟶ Spec (CommRingCat.of (T F V.1))) :=
  (D hq).instIsOpenImmersionMapI₀Functor i

@[reassoc]
lemma SpecMap_ι {U V : P.AffineZariskiSite} (i : U ⟶ V) :
    Spec.map (CommRingCat.ofHom (ρ F (toOpens_mono i.le))) ≫ ιU hq V = ιU hq U :=
  colimit.w (D hq).functor i

lemma ι_toBase (U : P.AffineZariskiSite) :
    ιU hq U ≫ p hq = Spec.map ((α F).app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

lemma toBase_preimage (U : P.AffineZariskiSite) : p hq ⁻¹ᵁ U.1 = (ιU hq U).opensRange := by
  have h := (D hq).toBase_preimage_eq_opensRange_ι U
  simp only [ιU]
  first | exact h | (simp at h ⊢; exact h)

lemma opensRange_functor_map_basicOpen (V : P.AffineZariskiSite) (r : Γ(P, V.1)) :
    ((D hq).functor.map (homOfLE (V.basicOpen_le r))).opensRange = PrimeSpectrum.basicOpen (inl r : T F V.1) :=
  opensRange_relativeGluingData_map (Tfun F) (α F) (coequifibered hq) (U := V) r

lemma SpecMap_ρ_ι {U V : P.AffineZariskiSite} (h : V.1 ≤ U.1) :
    Spec.map (CommRingCat.ofHom (ρ F h)) ≫ ιU hq U = ιU hq V := by

  let J : Type u := {r : (P.presheaf.obj (op U.1)) // P.basicOpen r ≤ V.1}
  let r' : J → (P.presheaf.obj (op V.1)) := fun r => rmap h r.1
  have hbo : ∀ r : J, P.basicOpen (r' r) = P.basicOpen r.1 := fun r =>
    (P.basicOpen_res r.1 (homOfLE h).op).trans (inf_eq_right.mpr r.2)
  have hspan : Ideal.span (Set.range r') = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨r, hr, hxr⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (h hx)
    refine Opens.mem_iSup.mpr ⟨⟨r' ⟨r, hr⟩, ⟨r, hr⟩, rfl⟩, ?_⟩
    change x ∈ P.basicOpen (r' ⟨r, hr⟩)
    rw [hbo]; exact hxr
  have hspanT : Ideal.span (Set.range fun r : J => (inl (r' r) : T F V.1)) = ⊤ := by
    have : Ideal.map (algebraMap Γ(P, V.1) (T F V.1)) (Ideal.span (Set.range r')) = ⊤ := by
      rw [hspan, Ideal.map_top]
    rw [Ideal.map_span, ← Set.range_comp] at this
    exact this
  have iV : ∀ r : J, V.basicOpen (r' r) ≤ V := fun r => V.basicOpen_le (r' r)
  have iU : ∀ r : J, V.basicOpen (r' r) ≤ U := fun r => ⟨r.1, (hbo r).symm⟩
  let 𝒲 : (Spec (CommRingCat.of (T F V.1))).OpenCover :=
    { I₀ := J
      X := fun r => Spec (CommRingCat.of (T F (P.basicOpen (r' r))))
      f := fun r => Spec.map (CommRingCat.ofHom (ρ F (P.basicOpen_le (r' r))))
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, fun r => isOpenImmersion_SpecMap_ρ hq (homOfLE (iV r))⟩
        have hx : ∃ r : J, x ∈ PrimeSpectrum.basicOpen (inl (r' r) : T F V.1) := by
          by_contra hcon
          push Not at hcon
          have hle : Ideal.span (Set.range fun r : J => (inl (r' r) : T F V.1)) ≤ x.asIdeal :=
            Ideal.span_le.mpr (by
              rintro _ ⟨r, rfl⟩
              by_contra h'
              exact hcon r ((PrimeSpectrum.mem_basicOpen _ _).mpr h'))
          rw [hspanT, top_le_iff] at hle
          exact x.2.ne_top hle
        obtain ⟨r, hr⟩ := hx
        rw [← opensRange_functor_map_basicOpen hq V (r' r)] at hr
        obtain ⟨y, hy⟩ := hr
        exact ⟨r, y, hy⟩ }
  refine Cover.hom_ext 𝒲 _ _ fun r ↦ ?_
  change Spec.map (CommRingCat.ofHom (ρ F (P.basicOpen_le (r' r)))) ≫ Spec.map (CommRingCat.ofHom (ρ F h)) ≫
    ιU hq U = Spec.map (CommRingCat.ofHom (ρ F (P.basicOpen_le (r' r)))) ≫ ιU hq V
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ρ_comp]
  exact (SpecMap_ι hq (homOfLE (iU r))).trans (SpecMap_ι hq (homOfLE (iV r))).symm

end Scheme

section Sections

variable (hq : F.IsQuasicoherent)

lemma appLE_congr_hom {X₁ X₂ : Scheme.{u}} {f g : X₁ ⟶ X₂} (hfg : f = g) (U : X₂.Opens) (V : X₁.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst hfg; rfl

lemma appLE_top_top {X₁ X₂ : Scheme.{u}} (f : X₁ ⟶ X₂) (e : (⊤ : X₁.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have : (homOfLE e).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [this]
  simp

lemma preimage_ι_eq_top (U : P.AffineZariskiSite) : ιU hq U ⁻¹ᵁ (p hq ⁻¹ᵁ U.1) = ⊤ := by
  rw [toBase_preimage, Scheme.Hom.preimage_opensRange]

lemma le_preimage_ι (U : P.AffineZariskiSite) :
    (⊤ : (Spec (CommRingCat.of (T F U.1))).Opens) ≤ ιU hq U ⁻¹ᵁ (p hq ⁻¹ᵁ U.1) :=
  (preimage_ι_eq_top hq U).ge

def eHom (U : P.AffineZariskiSite) : Γ(Y hq, p hq ⁻¹ᵁ U.1) ⟶ CommRingCat.of (T F U.1) :=
  (ιU hq U).appLE (p hq ⁻¹ᵁ U.1) ⊤ (le_preimage_ι hq U) ≫ (Scheme.ΓSpecIso (CommRingCat.of (T F U.1))).hom

scoped instance isIso_eHom (U : P.AffineZariskiSite) : IsIso (eHom hq U) := by
  have h1 : IsIso ((ιU hq U).app (p hq ⁻¹ᵁ U.1)) := Scheme.Hom.isIso_app _ _ (by rw [toBase_preimage])
  have h2 : IsIso ((Spec (CommRingCat.of (T F U.1))).presheaf.map (homOfLE (le_preimage_ι hq U)).op) := by
    have : homOfLE (le_preimage_ι hq U) = eqToHom (preimage_ι_eq_top hq U).symm := Subsingleton.elim _ _
    rw [this, eqToHom_op]; infer_instance
  unfold eHom Scheme.Hom.appLE
  infer_instance

def e (U : P.AffineZariskiSite) : Γ(Y hq, p hq ⁻¹ᵁ U.1) ≃+* T F U.1 :=
  (asIso (eHom hq U)).commRingCatIsoToRingEquiv

lemma e_apply (U : P.AffineZariskiSite) (x : Γ(Y hq, p hq ⁻¹ᵁ U.1)) : e hq U x = eHom hq U x := rfl

lemma map_eHom {U V : P.AffineZariskiSite} (h : V.1 ≤ U.1) :
    (Y hq).presheaf.map (homOfLE ((p hq).preimage_mono h)).op ≫ eHom hq V = eHom hq U ≫ CommRingCat.ofHom (ρ F h) := by
  unfold eHom
  have hle : (⊤ : (Spec (CommRingCat.of (T F V.1))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (ρ F h)) ≫ ιU hq U) ⁻¹ᵁ (p hq ⁻¹ᵁ U.1) := by
    rw [Scheme.Hom.comp_preimage, preimage_ι_eq_top]; exact (Opens.map_top _).ge
  rw [Scheme.Hom.map_appLE_assoc,
    appLE_congr_hom (SpecMap_ρ_ι hq h).symm (p hq ⁻¹ᵁ U.1) ⊤ _ hle,
    ← Scheme.Hom.appLE_comp_appLE _ _ (p hq ⁻¹ᵁ U.1) ⊤ ⊤ (le_preimage_ι hq U) (Opens.map_top _).ge,
    Category.assoc, appLE_top_top, Scheme.ΓSpecIso_naturality, Category.assoc]

lemma e_map {U V : P.AffineZariskiSite} (h : V.1 ≤ U.1) (x : Γ(Y hq, p hq ⁻¹ᵁ U.1)) :
    e hq V ((Y hq).presheaf.map (homOfLE ((p hq).preimage_mono h)).op x) = ρ F h (e hq U x) := by
  rw [e_apply, e_apply, ← CommRingCat.comp_apply, map_eHom hq h, CommRingCat.comp_apply]
  rfl

lemma appLE_eHom (U : P.AffineZariskiSite) :
    (p hq).appLE U.1 (p hq ⁻¹ᵁ U.1) le_rfl ≫ eHom hq U = (α F).app (op U) := by
  have h1 : (⊤ : (Spec _).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by rw [IsAffineOpen.fromSpec_preimage_self]
  have h2 : (⊤ : (Spec (CommRingCat.of (T F U.1))).Opens) ≤
      (Spec.map ((α F).app (op U)) ≫ U.2.fromSpec) ⁻¹ᵁ U.1 := by
    rw [Scheme.Hom.comp_preimage]; exact (Opens.map_top _).ge.trans ((Spec.map _).preimage_mono h1)
  have h4 : U.2.fromSpec.appLE U.1 ⊤ h1 = (Scheme.ΓSpecIso Γ(P, U.1)).inv := by
    rw [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc, ← CategoryTheory.Functor.map_comp]
    have : ((eqToHom U.2.fromSpec_preimage_self).op ≫ (homOfLE h1).op) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.comp_id]
  have h5 : (Spec.map ((α F).app (op U))).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (T F U.1))).hom =
      (Scheme.ΓSpecIso (P.presheaf.obj (op U.1))).hom ≫ (α F).app (op U) :=
    Scheme.ΓSpecIso_naturality _
  unfold eHom
  rw [Scheme.Hom.appLE_comp_appLE_assoc, appLE_congr_hom (ι_toBase hq U) U.1 ⊤ _ h2]
  trans (U.2.fromSpec.appLE U.1 ⊤ h1 ≫ (Spec.map ((α F).app (op U))).appLE ⊤ ⊤ (Opens.map_top _).ge) ≫
    (Scheme.ΓSpecIso (CommRingCat.of (T F U.1))).hom
  · congr 1
  rw [h4, Category.assoc, appLE_top_top]
  exact (congrArg ((Scheme.ΓSpecIso Γ(P, U.1)).inv ≫ ·) h5).trans (Iso.inv_hom_id_assoc _ _)

lemma e_appLE (U : P.AffineZariskiSite) (a : Γ(P, U.1)) :
    e hq U ((p hq).appLE U.1 (p hq ⁻¹ᵁ U.1) le_rfl a) = inl a := by
  rw [e_apply, ← CommRingCat.comp_apply, appLE_eHom, α_app]
  rfl

theorem isFinite_p (hc : F.IsCoherent) : IsFinite (p hq) := by
  refine AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData (coequifibered hq) fun U => ?_
  change (algebraMap Γ(P, U.1) (T F U.1)).Finite
  rw [RingHom.finite_algebraMap]
  haveI : Module.Finite Γ(P, U.1) (F.obj U.1) := hc ⟨U.1, U.2⟩
  exact inferInstanceAs (Module.Finite Γ(P, U.1) (Γ(P, U.1) × F.obj U.1))

end Sections

section AffineHom

variable (hq : F.IsQuasicoherent)

scoped instance isAffineHom_p : IsAffineHom (p hq) :=
  isAffineHom_of_forall_exists_isAffineOpen _ fun x => by
    obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top P).ge (Set.mem_univ x))
    exact ⟨U.1, hxU, U.2, by rw [toBase_preimage hq ⟨U.1, U.2⟩]; exact isAffineOpen_opensRange _⟩

end AffineHom

section Ideals

variable (F) (U : P.Opens) (I' : Ideal A)

def σT : A →+* T F U :=
  (algebraMap Γ(P, U) (T F U)).comp (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap

lemma σT_apply (a : A) : σT F U a = inl ((Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap a) := rfl

lemma algebraMap_smul_eq (a : A) (m : F.obj U) :
    (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap a • m = a • m := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  exact algebraMap_smul Γ(P, U) a m

lemma sections_smul_mem {m : F.obj U} (hm : m ∈ I' • (⊤ : Submodule A (F.obj U))) (r : Γ(P, U)) :
    r • m ∈ I' • (⊤ : Submodule A (F.obj U)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [smul_comm]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [smul_add]; exact Submodule.add_mem _ hx hy

lemma smul_mem_of_fst_mem {r : Γ(P, U)}
    (hr : r ∈ I'.map (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap) (m : F.obj U) :
    r • m ∈ I' • (⊤ : Submodule A (F.obj U)) := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [algebraMap_smul_eq]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [smul_eq_mul, mul_smul]; exact sections_smul_mem F U I' hx t

def J : Ideal (T F U) where
  carrier := {z | z.fst ∈ I'.map (Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap ∧
    z.snd ∈ I' • (⊤ : Submodule A (F.obj U))}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' {x y} hx hy := ⟨by rw [fst_add]; exact Ideal.add_mem _ hx.1 hy.1,
    by rw [snd_add]; exact Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' t z hz := by
    refine ⟨?_, ?_⟩
    · rw [smul_eq_mul, fst_mul]; exact Ideal.mul_mem_left _ _ hz.1
    · rw [smul_eq_mul, snd_mul, op_smul_eq_smul]
      exact Submodule.add_mem _ (sections_smul_mem F U I' hz.2 _) (smul_mem_of_fst_mem F U I' hz.1 _)

lemma map_σT_le : I'.map (σT F U) ≤ J F U I' := by
  refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
  refine ⟨?_, ?_⟩
  · rw [σT_apply, fst_inl]; exact Ideal.mem_map_of_mem _ ha
  · rw [σT_apply, snd_inl]; exact Submodule.zero_mem _

lemma snd_mem_of_mem_map_σT {z : T F U} (hz : z ∈ I'.map (σT F U)) :
    z.snd ∈ I' • (⊤ : Submodule A (F.obj U)) :=
  (map_σT_le F U I' hz).2

lemma inr_mem_map_σT {m : F.obj U} (hm : m ∈ I' • (⊤ : Submodule A (F.obj U))) :
    (inr m : T F U) ∈ I'.map (σT F U) := by
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [← algebraMap_smul_eq, ← inl_mul_inr, ← σT_apply]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  · rw [inr_add]; exact Ideal.add_mem _ hx hy

end Ideals

section Cech

variable [IsSeparated q]

abbrev Ks (_hq : F.IsQuasicoherent) (K : P.OrderedAffineCover) {i : ℕ} (s : K.Idx i) : P.AffineZariskiSite :=
  ⟨K.inter s, K.isAffineOpen_inter q s⟩

variable (hq : F.IsQuasicoherent) (K : P.OrderedAffineCover)

abbrev KY : (Y hq).OrderedAffineCover := K.comap (p hq)

abbrev toP {i : ℕ} (s : K.Idx i) : Γ(Y hq, (KY hq K).inter s) →+* Γ(Y hq, p hq ⁻¹ᵁ K.inter s) :=
  ((Y hq).presheaf.map (homOfLE (K.le_comap_inter (p hq) s)).op).hom

abbrev ofP {i : ℕ} (s : K.Idx i) : Γ(Y hq, p hq ⁻¹ᵁ K.inter s) →+* Γ(Y hq, (KY hq K).inter s) :=
  ((Y hq).presheaf.map (homOfLE (K.comap_inter_le (p hq) s)).op).hom

lemma Ymap_Ymap {U V W : (Y hq).Opens} (f : op U ⟶ op V) (g : op V ⟶ op W) (h : op U ⟶ op W) (x : Γ(Y hq, U)) :
    (Y hq).presheaf.map g ((Y hq).presheaf.map f x) = (Y hq).presheaf.map h x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (f ≫ g) h]

lemma Ymap_id {U : (Y hq).Opens} (f : op U ⟶ op U) (x : Γ(Y hq, U)) : (Y hq).presheaf.map f x = x := by
  rw [Subsingleton.elim f (𝟙 _), CategoryTheory.Functor.map_id]; rfl

lemma toP_ofP {i : ℕ} (s : K.Idx i) (x : Γ(Y hq, p hq ⁻¹ᵁ K.inter s)) : toP hq K s (ofP hq K s x) = x := by
  rw [toP, ofP, Ymap_Ymap hq _ _ (𝟙 _), Ymap_id]

lemma ofP_toP {i : ℕ} (s : K.Idx i) (x : Γ(Y hq, (KY hq K).inter s)) : ofP hq K s (toP hq K s x) = x := by
  rw [toP, ofP, Ymap_Ymap hq _ _ (𝟙 _), Ymap_id]

def eY {i : ℕ} (s : K.Idx i) : Γ(Y hq, (KY hq K).inter s) ≃+* T F (K.inter s) where
  toFun x := e hq (Ks hq K s) (toP hq K s x)
  invFun t := ofP hq K s ((e hq (Ks hq K s)).symm t)
  left_inv x := by
    change ofP hq K s ((e hq (Ks hq K s)).symm (e hq (Ks hq K s) (toP hq K s x))) = x
    rw [RingEquiv.symm_apply_apply, ofP_toP]
  right_inv t := by
    change e hq (Ks hq K s) (toP hq K s (ofP hq K s ((e hq (Ks hq K s)).symm t))) = t
    rw [toP_ofP, RingEquiv.apply_symm_apply]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add' x y := by rw [map_add, map_add]

lemma eY_apply {i : ℕ} (s : K.Idx i) (x : Γ(Y hq, (KY hq K).inter s)) :
    eY hq K s x = e hq (Ks hq K s) (toP hq K s x) := rfl

abbrev σY {i : ℕ} (s : K.Idx i) : A →+* Γ(Y hq, (KY hq K).inter s) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (p hq ≫ q).appLE ⊤ ((KY hq K).inter s) le_top).hom

lemma eY_σY {i : ℕ} (s : K.Idx i) (a : A) : eY hq K s (σY hq K s a) = σT F (K.inter s) a := by
  rw [eY_apply, σT_apply, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  change e hq (Ks hq K s) (((p hq ≫ q).appLE ⊤ ((KY hq K).inter s) le_top ≫
    (Y hq).presheaf.map (homOfLE (K.le_comap_inter (p hq) s)).op) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = _
  rw [Scheme.Hom.appLE_map, ← Scheme.Hom.appLE_comp_appLE (p hq) q ⊤ (K.inter s) (p hq ⁻¹ᵁ K.inter s) le_top le_rfl,
    CommRingCat.comp_apply]
  exact e_appLE hq (Ks hq K s) _

lemma eY_comp_σY {i : ℕ} (s : K.Idx i) : (eY hq K s).toRingHom.comp (σY hq K s) = σT F (K.inter s) :=
  RingHom.ext (eY_σY hq K s)

def Φ (i : ℕ) (c : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i) (s : K.Idx i) : T F (K.inter s) :=
  eY hq K s (c s)

def Ψ (i : ℕ) (c : ∀ s : K.Idx i, T F (K.inter s)) : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) i :=
  fun s => (eY hq K s).symm (c s)

lemma Φ_Ψ (i : ℕ) (c : ∀ s : K.Idx i, T F (K.inter s)) : Φ hq K i (Ψ hq K i c) = c := by
  funext s; exact (eY hq K s).apply_symm_apply (c s)

def dT (c : ∀ s : K.Idx 0, T F (K.inter s)) (s : K.Idx 1) : T F (K.inter s) :=
  ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • ρ F (K.inter_le_inter_face s j) (c (K.face s j))

lemma snd_dT (c : ∀ s : K.Idx 0, T F (K.inter s)) (s : K.Idx 1) :
    (dT K c s).snd = F.d K 0 (fun t => (c t).snd) s := by
  rw [OModulePresheaf.d_apply, dT, snd_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (snd_smul _ _).trans (by rw [snd_ρ])

lemma fst_dT_inr (w : ∀ s : K.Idx 0, F.obj (K.inter s)) (s : K.Idx 1) :
    (dT K (fun t => inr (w t)) s).fst = 0 := by
  rw [dT, fst_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact (fst_smul _ _).trans (by rw [fst_ρ, fst_inr, map_zero, smul_zero])

lemma snd_dT_inr (w : ∀ s : K.Idx 0, F.obj (K.inter s)) (s : K.Idx 1) :
    (dT K (fun t => inr (w t)) s).snd = F.d K 0 w s := by
  rw [snd_dT]; rfl

lemma dT_inr (w : ∀ s : K.Idx 0, F.obj (K.inter s)) (s : K.Idx 1) :
    dT K (fun t => inr (w t)) s = inr (F.d K 0 w s) :=
  TrivSqZeroExt.ext (by rw [fst_dT_inr, fst_inr]) (by rw [snd_dT_inr, snd_inr])

lemma Φ_d (c : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0) :
    Φ hq K 1 ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 c) = dT K (Φ hq K 0 c) := by
  funext s
  rw [Φ, OModulePresheaf.d_apply, dT]
  change eY hq K s (∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) •
    (Y hq).presheaf.map (homOfLE ((KY hq K).inter_le_inter_face s j)).op (c ((KY hq K).face s j))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  rw [Φ, eY_apply, eY_apply, ← e_map hq (U := Ks hq K (K.face s j)) (V := Ks hq K s) (K.inter_le_inter_face s j)]
  congr 1
  have hcommon : op ((KY hq K).inter ((KY hq K).face s j)) ⟶ op (p hq ⁻¹ᵁ K.inter s) :=
    (homOfLE (((p hq).preimage_mono (K.inter_le_inter_face s j)).trans (K.le_comap_inter (p hq) (K.face s j)))).op
  change (Y hq).presheaf.map _ ((Y hq).presheaf.map _ (c _)) = (Y hq).presheaf.map _ ((Y hq).presheaf.map _ (c _))
  exact (Ymap_Ymap hq _ _ hcommon _).trans (Ymap_Ymap hq _ _ hcommon _).symm

lemma mem_map_σY_iff {i : ℕ} (s : K.Idx i) (I' : Ideal A) (x : Γ(Y hq, (KY hq K).inter s)) :
    x ∈ I'.map (σY hq K s) ↔ eY hq K s x ∈ I'.map (σT F (K.inter s)) := by
  constructor
  · intro hx
    have := Ideal.mem_map_of_mem (eY hq K s).toRingHom hx
    rwa [Ideal.map_map, eY_comp_σY] at this
  · intro hy
    rw [← eY_comp_σY hq K s, ← Ideal.map_map] at hy
    have := Ideal.mem_map_of_mem (eY hq K s).symm.toRingHom hy
    rwa [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this

end Cech

theorem main [IsNoetherianRing A] (I : Ideal A) [IsProper q] (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K 0,
      (∀ s : K.Idx 1, F.d K 0 w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K 0,
        (∀ s : K.Idx 0, w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K 0 w' = F.d K 0 w := by
  haveI : IsFinite (p hq) := isFinite_p hq hc
  obtain ⟨c, hc'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper I (p hq ≫ q) (KY hq K) n
  refine ⟨c, fun w hw => ?_⟩
  let wY : (OModulePresheaf.unit (p hq ≫ q)).cochain (KY hq K) 0 := Ψ hq K 0 fun s => inr (w s)
  have hΦwY : Φ hq K 0 wY = fun s => inr (w s) := Φ_Ψ hq K 0 _
  have hdwY : ∀ s : K.Idx 1,
      eY hq K s ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 wY s) = inr (F.d K 0 w s) := by
    intro s
    have := congr_fun (Φ_d hq K wY) s
    rw [hΦwY, dT_inr] at this
    exact this
  obtain ⟨w'Y, hw'1, hw'2⟩ := hc' wY fun s =>
    (mem_map_σY_iff hq K s _ _).mpr (by rw [hdwY s]; exact inr_mem_map_σT F _ _ (hw s))
  refine ⟨fun s => (Φ hq K 0 w'Y s).snd, fun s => ?_, ?_⟩
  · exact snd_mem_of_mem_map_σT F _ _ ((mem_map_σY_iff hq K s _ _).mp (hw'1 s))
  · funext s
    calc F.d K 0 (fun t => (Φ hq K 0 w'Y t).snd) s
        = (dT K (Φ hq K 0 w'Y) s).snd := (snd_dT K _ s).symm
      _ = (Φ hq K 1 ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 w'Y) s).snd := by rw [Φ_d]
      _ = (Φ hq K 1 ((OModulePresheaf.unit (p hq ≫ q)).d (KY hq K) 0 wY) s).snd := by rw [hw'2]
      _ = (dT K (Φ hq K 0 wY) s).snd := by rw [Φ_d]
      _ = F.d K 0 w s := by rw [hΦwY, dT_inr, snd_inr]

end FormalGAGAFiniteSqZeroAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux"

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K 0,
      (∀ s : K.Idx 1, F.d K 0 w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K 0,
        (∀ s : K.Idx 0, w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K 0 w' = F.d K 0 w :=
  FormalGAGAFiniteSqZeroAux.main I hc hq K n

end S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper (solution)
