-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7b7108b4-0c22-5a35-8a8d-046bdcf92be3

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
import Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace RedC6bSol

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}

section FSide

variable (F : OModulePresheaf π)

theorem eq_of_forall_isLocalizedModule_eq {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M] [Module S M]
    {ι : Type*} [Fintype ι] (g : ι → S) (hg : Ideal.span (Set.range g) = ⊤)
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (f : ∀ i, M →ₗ[S] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)]
    (x y : M) (h : ∀ i, f i x = f i y) : x = y := by
  classical
  have hex : ∀ i, ∃ n : ℕ, g i ^ n • x = g i ^ n • y := fun i => by
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (g i)) (f i)).mp (h i)
    exact ⟨n, hn⟩
  choose n hn using hex
  let N := Finset.univ.sup n
  have hN : ∀ i, g i ^ N • x = g i ^ N • y := fun i => by
    have hle : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm, mul_smul, mul_smul, hn i]
  have hspan : Ideal.span (Set.range fun i => g i ^ N) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range g) hg N
    rw [← Set.range_comp] at this
    exact this
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hspan.symm ▸ Submodule.mem_top (x := (1 : S)))
  calc x = (1 : S) • x := (one_smul S x).symm
    _ = (∑ i, c i * g i ^ N) • x := by rw [hc]
    _ = ∑ i, c i • (g i ^ N • x) := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = ∑ i, c i • (g i ^ N • y) := by simp_rw [hN]
    _ = (∑ i, c i * g i ^ N) • y := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = y := by rw [hc, one_smul]

def FO (O : V.Opens) (W : V.Opens) (h : W ≤ O) : Type u := F.obj W

scoped instance instACG_FO (O W : V.Opens) (h : W ≤ O) : AddCommGroup (FO F O W h) :=
  inferInstanceAs (AddCommGroup (F.obj W))

scoped instance instMod_FO (O W : V.Opens) (h : W ≤ O) : Module Γ(V, O) (FO F O W h) :=
  Module.compHom (F.obj W) (V.presheaf.map (homOfLE h).op).hom

theorem FO_smul_def (O W : V.Opens) (h : W ≤ O) (a : Γ(V, O)) (x : FO F O W h) :
    a • x = (show FO F O W h from (V.presheaf.map (homOfLE h).op).hom a • (show F.obj W from x)) := rfl

def FresO (O : V.Opens) {W W' : V.Opens} (hW : W ≤ O) (hW' : W' ≤ O) (h : W' ≤ W) :
    FO F O W hW →ₗ[Γ(V, O)] FO F O W' hW' where
  toFun x := (show FO F O W' hW' from F.res h (show F.obj W from x))
  map_add' x y := map_add (F.res h) _ _
  map_smul' a x := by
    show F.res h ((V.presheaf.map (homOfLE hW).op).hom a • (show F.obj W from x)) =
      (V.presheaf.map (homOfLE hW').op).hom a • F.res h _
    rw [F.res_smul, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]
    rfl

theorem FresO_apply (O : V.Opens) {W W' : V.Opens} (hW : W ≤ O) (hW' : W' ≤ O) (h : W' ≤ W) (x : FO F O W hW) :
    FresO F O hW hW' h x = (show FO F O W' hW' from F.res h (show F.obj W from x)) := rfl

def Fres₀ (O : V.Opens) {W : V.Opens} (hW : W ≤ O) : F.obj O →ₗ[Γ(V, O)] FO F O W hW where
  toFun x := (show FO F O W hW from F.res hW x)
  map_add' x y := map_add (F.res hW) _ _
  map_smul' a x := F.res_smul hW a x

theorem Fres₀_apply (O : V.Opens) {W : V.Opens} (hW : W ≤ O) (x : F.obj O) :
    Fres₀ F O hW x = (show FO F O W hW from F.res hW x) := rfl

variable {F}

theorem isLocalizedModule_FresO (hF : F.IsQuasicoherent) (O : V.Opens) (W : V.affineOpens) (hW : W.1 ≤ O)
    (g : Γ(V, O)) :
    IsLocalizedModule (Submonoid.powers g)
      (FresO F O hW ((V.basicOpen_le _).trans hW)
        (V.basicOpen_le ((V.presheaf.map (homOfLE hW).op).hom g))) := by
  set gW := (V.presheaf.map (homOfLE hW).op).hom g with hgW
  have hq := hF W gW
  have hres : ∀ n : ℕ, (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) =
      (V.presheaf.map (homOfLE (V.basicOpen_le gW)).op).hom (gW ^ n) := fun n => by
    rw [hgW, ← map_pow, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl
  have hunit : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le gW)).op).hom gW) :=
    V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen gW
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n)) := by
      rw [hres, map_pow]; exact hunit.pow n
    have hb : Function.Bijective (fun y : F.obj (V.basicOpen gW) =>
        (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) • y) := hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  · intro y
    obtain ⟨n, x, hx⟩ := hq.1 y
    refine ⟨((show FO F O W.1 hW from x), ⟨g ^ n, n, rfl⟩), ?_⟩
    show (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) • (show F.obj _ from y) = F.res _ x
    rw [hres]; exact hx.symm
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le gW) ((show F.obj W.1 from x₁) - (show F.obj W.1 from x₂)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hq.2 _ h0
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show (V.presheaf.map (homOfLE hW).op).hom (g ^ n) • (show F.obj W.1 from x₁) =
      (V.presheaf.map (homOfLE hW).op).hom (g ^ n) • (show F.obj W.1 from x₂)
    rw [map_pow, ← hgW, ← sub_eq_zero, ← smul_sub, hn]

theorem isLocalizedModule_Fres₀ (hF : F.IsQuasicoherent) (U : V.affineOpens) (g : Γ(V, U.1)) :
    IsLocalizedModule (Submonoid.powers g) (Fres₀ F U.1 (V.basicOpen_le g)) := by
  have hq := hF U g
  have hunit : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom g) :=
    V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen g
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n)) := by
      rw [map_pow]; exact hunit.pow n
    have hb : Function.Bijective (fun y : F.obj (V.basicOpen g) =>
        (V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n) • y) := hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  · intro y
    obtain ⟨n, x, hx⟩ := hq.1 y
    exact ⟨(x, ⟨g ^ n, n, rfl⟩), hx.symm⟩
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le g) (x₁ - x₂) = 0 := by rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hq.2 _ h0
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show g ^ n • x₁ = g ^ n • x₂
    rw [← sub_eq_zero, ← smul_sub, hn]

theorem F_eq_of_forall_res_basicOpen_eq (hF : F.IsQuasicoherent) (U : V.affineOpens)
    {ι : Type*} [Fintype ι] (g : ι → Γ(V, U.1)) (hg : Ideal.span (Set.range g) = ⊤) (x y : F.obj U.1)
    (h : ∀ i, F.res (V.basicOpen_le (g i)) x = F.res (V.basicOpen_le (g i)) y) : x = y :=
  haveI := fun i => isLocalizedModule_Fres₀ hF U (g i)
  eq_of_forall_isLocalizedModule_eq g hg (fun i => Fres₀ F U.1 (V.basicOpen_le (g i))) x y h

theorem F_exists_of_forall_res_eq (hF : F.IsQuasicoherent) (U : V.affineOpens)
    {ι : Type u} [Fintype ι] (g : ι → Γ(V, U.1)) (hg : Ideal.span (Set.range g) = ⊤)
    (x : ∀ i, F.obj (V.basicOpen (g i)))
    (hx : ∀ i j, F.res (V.basicOpen_le ((V.presheaf.map (homOfLE (V.basicOpen_le (g i))).op).hom (g j))) (x i) =
      F.res (by rw [Scheme.basicOpen_res]; exact inf_le_right) (x j)) :
    ∃ m : F.obj U.1, ∀ i, F.res (V.basicOpen_le (g i)) m = x i := by
  haveI := fun i => isLocalizedModule_Fres₀ hF U (g i)
  let Ui : ι → V.affineOpens := fun i => ⟨V.basicOpen (g i), U.2.basicOpen (g i)⟩
  haveI := fun i j => isLocalizedModule_FresO hF U.1 (Ui i) (V.basicOpen_le (g i)) (g j)
  obtain ⟨m, hm⟩ := IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top g hg
    (fun i => Fres₀ F U.1 (V.basicOpen_le (g i)))
    (fun i j => FresO F U.1 (V.basicOpen_le (g i)) ((V.basicOpen_le _).trans (V.basicOpen_le (g i)))
      (V.basicOpen_le ((V.presheaf.map (homOfLE (V.basicOpen_le (g i))).op).hom (g j))))
    (fun i j => FresO F U.1 (V.basicOpen_le (g j)) ((V.basicOpen_le _).trans (V.basicOpen_le (g i)))
      (by rw [Scheme.basicOpen_res]; exact inf_le_right))
    (fun i j => LinearMap.ext fun m => by
      show F.res _ (F.res _ m) = F.res _ (F.res _ m)
      rw [F.res_res, F.res_res])
    (fun i => (show FO F U.1 _ _ from x i)) (fun i j => hx i j)
  exact ⟨m, hm⟩

end FSide

section Hom

variable {F₁ F₂ : OModulePresheaf π}

def appO (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) : F₁.obj U.1 →ₗ[Γ(V, U.1)] F₂.obj U.1 where
  toFun x := Φ.app U x
  map_add' x y := map_add _ x y
  map_smul' a x := Φ.app_smul U a x

theorem appO_apply (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (x : F₁.obj U.1) : appO Φ U x = Φ.app U x := rfl

abbrev bU (U : V.affineOpens) (g : Γ(V, U.1)) : V.affineOpens := ⟨V.basicOpen g, U.2.basicOpen g⟩

def appB (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (g : Γ(V, U.1)) :
    FO F₁ U.1 (V.basicOpen g) (V.basicOpen_le g) →ₗ[Γ(V, U.1)] FO F₂ U.1 (V.basicOpen g) (V.basicOpen_le g) where
  toFun x := (show FO F₂ U.1 _ _ from Φ.app (bU U g) (show F₁.obj (V.basicOpen g) from x))
  map_add' x y := map_add (Φ.app (bU U g)) _ _
  map_smul' a x := Φ.app_smul (bU U g) _ _

theorem appB_comp (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (g : Γ(V, U.1)) :
    appB Φ U g ∘ₗ Fres₀ F₁ U.1 (V.basicOpen_le g) = Fres₀ F₂ U.1 (V.basicOpen_le g) ∘ₗ appO Φ U := by
  refine LinearMap.ext fun x => ?_
  show Φ.app (bU U g) (F₁.res (V.basicOpen_le g) x) = F₂.res (V.basicOpen_le g) (Φ.app U x)
  have := Φ.naturality (U := bU U g) (U' := U) (V.basicOpen_le g)
  exact (LinearMap.congr_fun this x)

theorem map_eq_appB (hF₁ : F₁.IsQuasicoherent) (hF₂ : F₂.IsQuasicoherent)
    (Φ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens) (g : Γ(V, U.1)) :
    haveI := isLocalizedModule_Fres₀ hF₁ U g
    haveI := isLocalizedModule_Fres₀ hF₂ U g
    IsLocalizedModule.map (Submonoid.powers g) (Fres₀ F₁ U.1 (V.basicOpen_le g)) (Fres₀ F₂ U.1 (V.basicOpen_le g))
      (appO Φ U) = appB Φ U g := by
  haveI := isLocalizedModule_Fres₀ hF₁ U g
  haveI := isLocalizedModule_Fres₀ hF₂ U g
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers g) (Fres₀ F₁ U.1 (V.basicOpen_le g))
    (Fres₀ F₂ U.1 (V.basicOpen_le g))
  rw [IsLocalizedModule.map_comp, appB_comp]

theorem app_eq_of_forall_basicOpen (hF₂ : F₂.IsQuasicoherent) (Φ Ψ : OModulePresheaf.AffHom F₁ F₂) (U : V.affineOpens)
    (T : Finset Γ(V, U.1)) (hT : Ideal.span (T : Set Γ(V, U.1)) = ⊤)
    (h : ∀ g ∈ T, Φ.app (bU U g) = Ψ.app (bU U g)) (x : F₁.obj U.1) : Φ.app U x = Ψ.app U x := by
  classical
  have hrange : Set.range (fun g : ↥T => (g.1 : Γ(V, U.1))) = (T : Set Γ(V, U.1)) := by
    ext a; exact ⟨by rintro ⟨g, rfl⟩; exact g.2, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
  refine F_eq_of_forall_res_basicOpen_eq hF₂ U (fun g : ↥T => (g.1 : Γ(V, U.1))) (by rw [hrange]; exact hT) _ _ fun g => ?_
  show F₂.res (V.basicOpen_le g.1) (Φ.app U x) = F₂.res (V.basicOpen_le g.1) (Ψ.app U x)
  rw [← Φ.naturality_apply (U := bU U g.1) (U' := U) (V.basicOpen_le g.1) x,
    ← Ψ.naturality_apply (U := bU U g.1) (U' := U) (V.basicOpen_le g.1) x, h g.1 g.2]

end Hom

theorem exists_cover (B : Set V.affineOpens)
    (hdown : ∀ (W W' : V.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
    (hcov : ∀ x : V, ∃ W ∈ B, x ∈ W.1) (U : V.affineOpens) :
    ∃ T : Finset Γ(V, U.1), Ideal.span (T : Set Γ(V, U.1)) = ⊤ ∧ ∀ g ∈ T, bU U g ∈ B := by
  classical
  let s : Set Γ(V, U.1) := {g | bU U g ∈ B}
  have hs : Ideal.span s = ⊤ := by
    rw [← U.2.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => V.basicOpen_le _) ?_
    intro x hx
    obtain ⟨W, hWB, hxW⟩ := hcov x
    obtain ⟨f, hfW, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hxW⟩ hx
    have hf : f ∈ s := hdown W (bU U f) hfW hWB
    exact Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨T, hTs, hT⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hs)
  exact ⟨T, (Ideal.eq_top_iff_one _).mpr hT, fun g hg => hTs hg⟩

end RedC6bSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.RedC6bSol"

open RedC6bSol in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (α : OModulePresheaf.AffHom GK G) (β : OModulePresheaf.AffHom G GE)
      (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ U : P.affineOpens, LinearMap.range (α.app U) = LinearMap.ker (β.app U)) ∧
      (∀ U : P.affineOpens, Function.Surjective (β.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ k).app U ∘ₗ α.app U = (lam k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ε k).app U ∘ₗ (ψ k).app U = (ψE k).app U ∘ₗ β.app U) := by
  classical
  obtain ⟨B, hdown, hcov, M, i1, i2, i3, i4, res, res_smul, res_refl, res_comp, hqc, hfg, ϑ, θE, θF,
    hϑs, hθEs, hθFs, hϑn, hθEn, hθFn, hexact, hsurj, hc1, hc2, hc3⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
  letI := i1; letI := i2; letI := i3; letI := i4
  obtain ⟨G, e, hGc, hGq, he_smul, he_res, hout, hin⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis q B hdown hcov M res
      res_smul res_refl res_comp hqc hfg
  obtain ⟨α, hα, -⟩ := hin GK hGKq ϑ hϑs hϑn
  obtain ⟨β, hβ, -⟩ := hout GE hGEq θE hθEs hθEn
  choose ψ hψ using fun k => (hout (F k) (hFq k) (θF k) (hθFs k) (hθFn k)).exists

  have hβW : ∀ (W : ↥B) (x : G.obj W.1.1), β.app W.1 x = θE W (e W x) := hβ
  have hαW : ∀ (W : ↥B) (x : GK.obj W.1.1), α.app W.1 x = (e W).symm (ϑ W x) := fun W x => by
    rw [← hα W x, LinearEquiv.symm_apply_apply]
  refine ⟨G, α, β, ψ, hGc, hGq, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGKq U g.1
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGq U g.1
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGEq U g.1
    have hrange : Set.range (fun g : ↥T => (g.1 : Γ(P, U.1))) = (T : Set Γ(P, U.1)) := by
      ext a; exact ⟨by rintro ⟨g, rfl⟩; exact g.2, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
    have key : Function.Exact (appO α U) (appO β U) := by
      refine exact_of_isLocalized_span (T : Set Γ(P, U.1)) hT
        (fun g : ↥(T : Set Γ(P, U.1)) => FO GK U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ GK U.1 (P.basicOpen_le g.1))
        (fun g : ↥(T : Set Γ(P, U.1)) => FO G U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ G U.1 (P.basicOpen_le g.1))
        (fun g : ↥(T : Set Γ(P, U.1)) => FO GE U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ GE U.1 (P.basicOpen_le g.1))
        (appO α U) (appO β U) fun g => ?_
      rw [map_eq_appB hGKq hGq α U g.1, map_eq_appB hGq hGEq β U g.1]

      intro y
      let W : ↥B := ⟨bU U g.1, hB g.1 g.2⟩
      show β.app W.1 y = 0 ↔ y ∈ Set.range (fun x => α.app W.1 x)
      rw [hβW W, ← LinearMap.mem_ker, ← hexact W, LinearMap.mem_range]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        show α.app W.1 x = y
        rw [hαW W, hx, LinearEquiv.symm_apply_apply]
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        change α.app W.1 x = y at hx
        rw [← hx, hαW W, LinearEquiv.apply_symm_apply]
    have key' : Function.Exact (α.app U) (β.app U) := key
    exact (LinearMap.exact_iff.mp key').symm
  ·
    intro U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGq U g.1
    haveI := fun g : ↥T => isLocalizedModule_Fres₀ hGEq U g.1
    have key : Function.Surjective (appO β U) := by
      refine surjective_of_isLocalized_span (T : Set Γ(P, U.1)) hT
        (fun g : ↥(T : Set Γ(P, U.1)) => FO G U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ G U.1 (P.basicOpen_le g.1))
        (fun g : ↥(T : Set Γ(P, U.1)) => FO GE U.1 (P.basicOpen g.1) (P.basicOpen_le g.1))
        (fun g => Fres₀ GE U.1 (P.basicOpen_le g.1))
        (appO β U) fun g => ?_
      rw [map_eq_appB hGq hGEq β U g.1]
      intro z
      let W : ↥B := ⟨bU U g.1, hB g.1 g.2⟩
      obtain ⟨m, hm⟩ := hsurj W (show GE.obj W.1.1 from z)
      refine ⟨(show FO G U.1 _ _ from (e W).symm m), ?_⟩
      show β.app W.1 ((e W).symm m) = z
      rw [hβW W, LinearEquiv.apply_symm_apply, hm]
    exact key
  ·
    intro k U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    refine LinearMap.ext fun x => ?_
    show ((φ k).comp (ψ (k + 1))).app U x = (ψ k).app U x
    refine app_eq_of_forall_basicOpen (hFq k) _ _ U T hT (fun g hg => LinearMap.ext fun y => ?_) x
    let W : ↥B := ⟨bU U g, hB g hg⟩
    show (φ k).app W.1 ((ψ (k + 1)).app W.1 y) = (ψ k).app W.1 y
    rw [hψ (k + 1) W, hψ k W]
    exact LinearMap.congr_fun (hc1 k W) (e W y)
  ·
    intro k U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    refine LinearMap.ext fun x => ?_
    show ((ψ k).comp α).app U x = (lam k).app U x
    refine app_eq_of_forall_basicOpen (hFq k) _ _ U T hT (fun g hg => LinearMap.ext fun y => ?_) x
    let W : ↥B := ⟨bU U g, hB g hg⟩
    show (ψ k).app W.1 (α.app W.1 y) = (lam k).app W.1 y
    rw [hψ k W, hαW W, LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (hc2 k W) y
  ·
    intro k U
    obtain ⟨T, hT, hB⟩ := exists_cover B hdown hcov U
    refine LinearMap.ext fun x => ?_
    show ((ε k).comp (ψ k)).app U x = ((ψE k).comp β).app U x
    refine app_eq_of_forall_basicOpen (hEq k) _ _ U T hT (fun g hg => LinearMap.ext fun y => ?_) x
    let W : ↥B := ⟨bU U g, hB g hg⟩
    show (ε k).app W.1 ((ψ k).app W.1 y) = (ψE k).app W.1 (β.app W.1 y)
    rw [hψ k W, hβW W]
    exact LinearMap.congr_fun (hc3 k W) (e W y)

end S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete (solution)
