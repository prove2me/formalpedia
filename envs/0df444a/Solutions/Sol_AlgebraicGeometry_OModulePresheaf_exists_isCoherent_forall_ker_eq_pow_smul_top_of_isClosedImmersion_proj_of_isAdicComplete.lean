-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/57a76cd4-bd39-51dd-a8b6-9e188f3187ee

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mProjExistSol

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~coker"

section Generic

variable {A : Type*} [CommRing A]

theorem map_mem_smul_top {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (g : M →ₗ[A] M') {x : M} (hx : x ∈ J • (⊤ : Submodule A M)) :
    g x ∈ J • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := g) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem map_smul_top_of_surjective {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (J : Ideal A) (g : M →ₗ[A] M') (hg : Function.Surjective g) :
    (J • (⊤ : Submodule A M)).map g = J • (⊤ : Submodule A M') := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]

theorem pow_smul_top_eq_bot {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (g : M →ₗ[A] M') (hg : Function.Surjective g)
    (hk : LinearMap.ker g = J • (⊤ : Submodule A M)) : J • (⊤ : Submodule A M') = ⊥ := by
  rw [← map_smul_top_of_surjective J g hg, ← hk]
  exact le_bot_iff.mp (Submodule.map_le_iff_le_comap.mpr (by rw [Submodule.comap_bot]))

end Generic

theorem affHom_ext {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (a b : AffHom F G) (h : ∀ (W : V.affineOpens) (x : F.obj W.1), a.app W x = b.app W x) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have : a1 = b1 := funext fun W => LinearMap.ext (h W)
  subst this
  rfl

section Trunc

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} {q : P ⟶ Spec (.of A)}
variable (E : OModulePresheaf q)

def T (k : ℕ) (U : P.Opens) : Submodule A (E.obj U) := I ^ (k + 1) • ⊤

theorem T_def (k : ℕ) (U : P.Opens) : T I E k U = I ^ (k + 1) • (⊤ : Submodule A (E.obj U)) := rfl

theorem T_smul_mem (k : ℕ) (U : P.Opens) (a : Γ(P, U)) {x : E.obj U} (hx : x ∈ T I E k U) :
    a • x ∈ T I E k U := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  haveI : IsScalarTower A Γ(P, U) (E.obj U) := E.isScalarTower U
  refine Submodule.smul_induction_on hx (fun i hi y _ => ?_) (fun x y hx hy => ?_)
  · rw [T_def, smul_algebra_smul_comm i a y]
    exact Submodule.smul_mem_smul hi Submodule.mem_top
  · rw [smul_add]; exact add_mem hx hy

theorem T_res {U U' : P.Opens} (hle : U ≤ U') (k : ℕ) {x : E.obj U'} (hx : x ∈ T I E k U') :
    E.res hle x ∈ T I E k U :=
  map_mem_smul_top _ (E.res hle) hx

theorem T_anti (k : ℕ) (U : P.Opens) : T I E (k + 1) U ≤ T I E k U :=
  Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ _)) le_rfl

@[reducible] noncomputable def truncModuleSections (k : ℕ) (U : P.Opens) :
    Module Γ(P, U) (E.obj U ⧸ T I E k U) :=
  letI : SMul Γ(P, U) (E.obj U ⧸ T I E k U) :=
    ⟨fun a => Quotient.map' (a • ·) fun x y hxy => (Submodule.quotientRel_def _).mpr <| by
      rw [← smul_sub]; exact T_smul_mem I E k U a ((Submodule.quotientRel_def _).mp hxy)⟩
  Function.Surjective.module Γ(P, U) ⟨⟨Submodule.Quotient.mk, rfl⟩, fun _ _ => rfl⟩
    (Submodule.Quotient.mk_surjective _) (fun _ _ => rfl)

noncomputable def trunc (k : ℕ) : OModulePresheaf q where
  obj U := E.obj U ⧸ T I E k U
  module U := inferInstance
  moduleSections U := truncModuleSections I E k U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
    letI := truncModuleSections I E k U
    exact ⟨fun r a => Quotient.ind' fun x => congrArg Submodule.Quotient.mk (smul_assoc r a x)⟩
  res {U U'} hle := Submodule.mapQ _ _ (E.res hle) fun x hx => T_res I E hle k hx
  res_smul {U U'} hle a z := z.inductionOn' fun x => congrArg Submodule.Quotient.mk (E.res_smul hle a x)
  res_refl U := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (E.res_refl U) x)
  res_comp {U U' U''} hle hle' := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (E.res_comp hle hle') x)

theorem trunc_obj (k : ℕ) (U : P.Opens) : (trunc I E k).obj U = (E.obj U ⧸ T I E k U) := rfl

theorem trunc_res_mk (k : ℕ) {U U' : P.Opens} (hle : U ≤ U') (x : E.obj U') :
    (trunc I E k).res hle (Submodule.Quotient.mk x) = Submodule.Quotient.mk (E.res hle x) := rfl

theorem trunc_smul_mk (k : ℕ) (U : P.Opens) (a : Γ(P, U)) (x : E.obj U) :
    (a • (show (trunc I E k).obj U from Submodule.Quotient.mk x))
      = (show (trunc I E k).obj U from Submodule.Quotient.mk (a • x)) := rfl

noncomputable def truncπ (k : ℕ) : AffHom E (trunc I E k) where
  app U := (T I E k U.1).mkQ
  app_smul _ _ _ := rfl
  naturality _ := rfl

theorem truncπ_app (k : ℕ) (U : P.affineOpens) (x : E.obj U.1) :
    (truncπ I E k).app U x = (show (trunc I E k).obj U.1 from Submodule.Quotient.mk x) := rfl

theorem truncπ_surjective (k : ℕ) (U : P.affineOpens) : Function.Surjective ((truncπ I E k).app U) :=
  Submodule.mkQ_surjective _

theorem ker_truncπ (k : ℕ) (U : P.affineOpens) :
    LinearMap.ker ((truncπ I E k).app U) = I ^ (k + 1) • (⊤ : Submodule A (E.obj U.1)) :=
  Submodule.ker_mkQ _

noncomputable def truncτ (k : ℕ) : AffHom (trunc I E (k + 1)) (trunc I E k) where
  app U := Submodule.mapQ (T I E (k + 1) U.1) (T I E k U.1) LinearMap.id (T_anti I E k U.1)
  app_smul _ _ z := z.inductionOn' fun _ => rfl
  naturality _ := LinearMap.ext fun z => z.inductionOn' fun _ => rfl

theorem truncτ_app_mk (k : ℕ) (U : P.affineOpens) (x : E.obj U.1) :
    (truncτ I E k).app U (Submodule.Quotient.mk x) = (show (trunc I E k).obj U.1 from Submodule.Quotient.mk x) :=
  rfl

theorem truncτ_truncπ (k : ℕ) (U : P.affineOpens) (x : E.obj U.1) :
    (truncτ I E k).app U ((truncπ I E (k + 1)).app U x) = (truncπ I E k).app U x := rfl

theorem truncτ_comp_truncπ (k : ℕ) : (truncτ I E k).comp (truncπ I E (k + 1)) = truncπ I E k :=
  affHom_ext _ _ fun _ _ => rfl

theorem truncτ_surjective (k : ℕ) (U : P.affineOpens) : Function.Surjective ((truncτ I E k).app U) := by
  intro z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem ker_truncτ (k : ℕ) (U : P.affineOpens) :
    LinearMap.ker ((truncτ I E k).app U)
      = I ^ (k + 1) • (⊤ : Submodule A ((trunc I E (k + 1)).obj U.1)) := by

  have h1 : LinearMap.ker ((truncτ I E k).app U) = (T I E k U.1).map ((truncπ I E (k + 1)).app U) := by
    ext z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [LinearMap.mem_ker]
    change (Submodule.Quotient.mk x : E.obj U.1 ⧸ T I E k U.1) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hd : y - x ∈ T I E (k + 1) U.1 := (Submodule.Quotient.eq _).mp hyx
      have : x = y - (y - x) := by abel
      rw [this]
      exact sub_mem hy (T_anti I E k U.1 hd)
  rw [h1, T_def, map_smul_top_of_surjective _ _ (truncπ_surjective I E (k + 1) U)]

theorem isCoherent_trunc (hEc : E.IsCoherent) (k : ℕ) : (trunc I E k).IsCoherent := by
  intro U
  haveI := hEc U
  let f : E.obj U.1 →ₗ[Γ(P, U.1)] (trunc I E k).obj U.1 :=
    { toFun := Submodule.Quotient.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective f (Submodule.Quotient.mk_surjective _)

theorem isQuasicoherent_trunc (hEq : E.IsQuasicoherent) (k : ℕ) : (trunc I E k).IsQuasicoherent := by
  intro U f
  obtain ⟨hE1, hE2⟩ := hEq U f
  have hDf : IsAffineOpen (P.basicOpen f) := U.2.basicOpen f
  set D : P.affineOpens := ⟨P.basicOpen f, hDf⟩ with hD

  set fD : ℕ → Γ(P, P.basicOpen f) := fun n => (P.presheaf.map (homOfLE (P.basicOpen_le f)).op).hom (f ^ n)
    with hfD
  have hfD_add : ∀ a b, fD (a + b) = fD a * fD b := fun a b => by
    simp only [hfD, pow_add, map_mul]
  have hres_pow : ∀ (n : ℕ) (y : E.obj U.1),
      E.res (P.basicOpen_le f) ((f ^ n : Γ(P, U.1)) • y) = fD n • E.res (P.basicOpen_le f) y :=
    fun n y => E.res_smul _ _ _
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨n, y, hy⟩ := hE1 x
    refine ⟨n, Submodule.Quotient.mk y, ?_⟩
    show Submodule.Quotient.mk (E.res _ y) = Submodule.Quotient.mk (_ • x)
    rw [hy]
  · intro z hz
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hmem : E.res (P.basicOpen_le f) y ∈ T I E k (P.basicOpen f) :=
      (Submodule.Quotient.mk_eq_zero _).mp hz

    have key : ∀ x ∈ T I E k (P.basicOpen f),
        ∃ (n : ℕ) (w : E.obj U.1), w ∈ T I E k U.1 ∧ E.res (P.basicOpen_le f) w = fD n • x := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun i hi x _ => ?_) (fun x x' hx hx' => ?_)
      · obtain ⟨n, w, hw⟩ := hE1 x
        refine ⟨n, i • w, Submodule.smul_mem_smul hi Submodule.mem_top, ?_⟩
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q (P.basicOpen f)
        haveI : IsScalarTower A Γ(P, P.basicOpen f) (E.obj (P.basicOpen f)) := E.isScalarTower _
        rw [LinearMap.map_smul, hw]
        exact (smul_algebra_smul_comm i (fD n) x).symm
      · obtain ⟨n, w, hw, hwx⟩ := hx
        obtain ⟨n', w', hw', hwx'⟩ := hx'
        refine ⟨n + n', (f ^ n' : Γ(P, U.1)) • w + (f ^ n : Γ(P, U.1)) • w',
          add_mem (T_smul_mem I E k U.1 _ hw) (T_smul_mem I E k U.1 _ hw'), ?_⟩
        rw [map_add, hres_pow, hres_pow, hwx, hwx', smul_smul, smul_smul, ← hfD_add, ← hfD_add,
          Nat.add_comm n' n, smul_add]
    obtain ⟨n, w, hw, hwy⟩ := key _ hmem
    have h0 : E.res (P.basicOpen_le f) ((f ^ n : Γ(P, U.1)) • y - w) = 0 := by
      rw [map_sub, hres_pow, hwy, sub_self]
    obtain ⟨m, hm⟩ := hE2 _ h0
    refine ⟨m + n, ?_⟩
    show Submodule.Quotient.mk ((f ^ (m + n) : Γ(P, U.1)) • y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hm
    rw [hm]
    exact T_smul_mem I E k U.1 _ hw

end Trunc

section Card

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
  [IsClosedImmersion ι]

theorem main
    (F : ℕ → OModulePresheaf (ι ≫ ProjSpace.π A r)) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf (ι ≫ ProjSpace.π A r)) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by

  haveI : IsProper (ι ≫ ProjSpace.π A r) := inferInstance
  haveI : LocallyOfFiniteType (ι ≫ ProjSpace.π A r) := inferInstance

  obtain ⟨E, θ, hEc, hEq, hθs, hθc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion
      I ι rfl F hc hq φ hφs hφk

  have hFk : ∀ (k : ℕ) (U : P.affineOpens), I ^ (k + 1) • (⊤ : Submodule A ((F k).obj U.1)) = ⊥ :=
    fun k U => pow_smul_top_eq_bot _ ((φ k).app U) (hφs k U) (hφk k U)
  have hTθ : ∀ (k : ℕ) (U : P.affineOpens), T I E k U.1 ≤ LinearMap.ker ((θ k).app U) := by
    intro k U x hx
    rw [LinearMap.mem_ker, ← (Submodule.mem_bot A), ← hFk k U]
    exact map_mem_smul_top _ ((θ k).app U) hx
  let θb : ∀ k, AffHom (trunc I E k) (F k) := fun k =>
    { app := fun U => (T I E k U.1).liftQ ((θ k).app U) (hTθ k U)
      app_smul := fun U a z => z.inductionOn' fun x => (θ k).app_smul U a x
      naturality := fun {U U'} hle => LinearMap.ext fun z => z.inductionOn' fun x =>
        (θ k).naturality_apply hle x }
  have θb_mk : ∀ (k : ℕ) (U : P.affineOpens) (x : E.obj U.1),
      (θb k).app U ((truncπ I E k).app U x) = (θ k).app U x := fun _ _ _ => rfl
  have hθbs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θb k).app U) := by
    intro k U y
    obtain ⟨x, rfl⟩ := hθs k U y
    exact ⟨(truncπ I E k).app U x, rfl⟩
  have hθbc : ∀ (k : ℕ) (U : P.affineOpens),
      (φ k).app U ∘ₗ (θb (k + 1)).app U = (θb k).app U ∘ₗ (truncτ I E k).app U := by
    intro k U
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    show (φ k).app U ((θ (k + 1)).app U x) = (θ k).app U x
    rw [← LinearMap.comp_apply, hθc]

  obtain ⟨K, κ, j, hKc, hKq, hκs, hκk, hjc, hjr⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top I
      (fun k => trunc I E k) F (fun k => isCoherent_trunc I E hEc k) (fun k => isQuasicoherent_trunc I E hEq k)
      hc hq (fun k => truncτ I E k) (fun k => truncτ_surjective I E k) (fun k => ker_truncτ I E k)
      φ hφs hφk θb hθbs hθbc

  obtain ⟨H, lam, hHc, hHq, hls, hlc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion
      I ι rfl K hKc hKq κ hκs hκk
  let ψ' : ∀ n, AffHom H (trunc I E n) := fun n => (j n).comp (lam n)
  have hψ' : ∀ n, (truncτ I E n).comp (ψ' (n + 1)) = ψ' n := by
    intro n
    refine affHom_ext _ _ fun U x => ?_
    show ((truncτ I E n).app U ∘ₗ (j (n + 1)).app U) ((lam (n + 1)).app U x)
      = (j n).app U ((lam n).app U x)
    rw [hjc n U, LinearMap.comp_apply, ← LinearMap.comp_apply ((κ n).app U), hlc n U]
  obtain ⟨h, hh, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper I
      (ι ≫ ProjSpace.π A r) H E hHc hHq hEc hEq (fun n => trunc I E n) (fun n => truncτ I E n)
      (fun n => truncπ I E n) (fun n => truncπ_surjective I E n) (fun n => ker_truncπ I E n)
      (fun n => truncτ_comp_truncπ I E n) ψ' hψ'
  have hh_app : ∀ (n : ℕ) (U : P.affineOpens) (x : H.obj U.1),
      (truncπ I E n).app U (h.app U x) = (j n).app U ((lam n).app U x) := by
    intro n U x
    have := congrArg (fun (g : AffHom H (trunc I E n)) => g.app U x) (hh n)
    exact this

  have hker : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((θ k).app U)
        = LinearMap.range (h.app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A (E.obj U.1)) := by
    intro k U

    have hfac : (θ k).app U = (θb k).app U ∘ₗ (truncπ I E k).app U := LinearMap.ext fun _ => rfl

    have hkb : LinearMap.ker ((θb k).app U) = (LinearMap.range (h.app U)).map ((truncπ I E k).app U) := by
      rw [← hjr k U, ← LinearMap.range_comp]
      have hsurj : LinearMap.range ((j k).app U)
          = LinearMap.range ((j k).app U ∘ₗ (lam k).app U) := by
        rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr (hls k U), Submodule.map_top]
      rw [hsurj]
      congr 1
      exact LinearMap.ext fun x => (hh_app k U x).symm
    rw [hfac, LinearMap.ker_comp, hkb, Submodule.comap_map_eq, ker_truncπ, sup_comm]
  obtain ⟨G, ρ, ψ, hGc, hGq, -, -, -, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
      I hHq hEc hEq h F φ θ hθs hker hθc
  exact ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩

end Card

end P2mProjExistSol

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  subst hιq
  exact P2mProjExistSol.main I ι F hc hq φ hφs hφk

end S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete (solution)
