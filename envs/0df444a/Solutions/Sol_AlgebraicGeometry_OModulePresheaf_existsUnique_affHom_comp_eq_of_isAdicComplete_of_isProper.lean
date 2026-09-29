-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7eaa1790-a15e-57f9-99a3-7e1dd0ffbcd7

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique
import Theorems.Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace HomCompleteAux

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~zero"

section Generic

variable {A : Type*} [CommRing A]

theorem map_mem_smul_top {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (g : M →ₗ[A] M') {x : M} (hx : x ∈ J • (⊤ : Submodule A M)) :
    g x ∈ J • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := g) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem mem_smul_top_iff_of_linearEquiv {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (J : Ideal A) (e : M ≃ₗ[A] M') (x : M) :
    x ∈ J • (⊤ : Submodule A M) ↔ e x ∈ J • (⊤ : Submodule A M') := by
  constructor
  · intro hx
    exact map_mem_smul_top J e.toLinearMap hx
  · intro hx
    have h := map_mem_smul_top J e.symm.toLinearMap hx
    rwa [LinearEquiv.coe_coe, e.symm_apply_apply] at h

theorem pi_mem_smul_top {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] (J : Ideal A) (w : ∀ i, M i) (hw : ∀ i, w i ∈ J • (⊤ : Submodule A (M i))) :
    w ∈ J • (⊤ : Submodule A (∀ i, M i)) := by
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact map_mem_smul_top J (LinearMap.single A M i) (hw i)

theorem apply_mem_smul_top {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    (J : Ideal A) {w : ∀ i, M i} (hw : w ∈ J • (⊤ : Submodule A (∀ i, M i))) (i : ι) :
    w i ∈ J • (⊤ : Submodule A (M i)) :=
  map_mem_smul_top J (LinearMap.proj i) hw

theorem mem_smul_top_of_coe_mem {M : Type*} [AddCommGroup M] [Module A M] (J : Ideal A) (p : Submodule A M)
    (y : p) (hy : (y : M) ∈ J • p) : y ∈ J • (⊤ : Submodule A p) := by
  have h : (J • (⊤ : Submodule A p)).map p.subtype = J • p := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [← h] at hy
  obtain ⟨y', hy', hyy⟩ := Submodule.mem_map.mp hy
  have : y' = y := Subtype.ext hyy
  exact this ▸ hy'

theorem coe_mem_of_mem_smul_top {M : Type*} [AddCommGroup M] [Module A M] (J : Ideal A) (p : Submodule A M)
    (y : p) (hy : y ∈ J • (⊤ : Submodule A p)) : (y : M) ∈ J • (⊤ : Submodule A M) :=
  map_mem_smul_top J p.subtype hy

theorem affHom_ext {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (a b : AffHom F G) (h : ∀ (W : V.affineOpens) (x : F.obj W.1), a.app W x = b.app W x) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have : a1 = b1 := funext fun W => LinearMap.ext (h W)
  subst this
  rfl

theorem d_zero_apply {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (H : OModulePresheaf π)
    (K : V.OrderedAffineCover) (c : H.cochain K 0) (t : K.Idx 1) :
    H.d K 0 c t = H.res (K.inter_le_inter_face t 0) (c (K.face t 0)) -
      H.res (K.inter_le_inter_face t 1) (c (K.face t 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul]
  rw [sub_eq_add_neg]

theorem d_zero_res_eq_zero {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (H : OModulePresheaf π) (K : V.OrderedAffineCover) (x : H.obj ⊤) :
    H.d K 0 (fun s => H.res (le_top : K.inter s ≤ ⊤) x) = 0 := by
  funext t
  rw [d_zero_apply]
  change H.res _ (H.res _ x) - H.res _ (H.res _ x) = 0
  rw [H.res_res, H.res_res, sub_self]

def coverOfCompact (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Generic

structure Sys {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) where
  F : OModulePresheaf f
  G : OModulePresheaf f
  hFc : F.IsCoherent
  hFq : F.IsQuasicoherent
  hGc : G.IsCoherent
  hGq : G.IsQuasicoherent
  Gn : ℕ → OModulePresheaf f
  τ : ∀ n : ℕ, AffHom (Gn (n + 1)) (Gn n)
  ρ : ∀ n : ℕ, AffHom G (Gn n)
  hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U)
  hρk : ∀ (n : ℕ) (U : X.affineOpens), LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1))
  hρc : ∀ n : ℕ, (τ n).comp (ρ (n + 1)) = ρ n
  ψ : ∀ n : ℕ, AffHom F (Gn n)
  hψ : ∀ n : ℕ, (τ n).comp (ψ (n + 1)) = ψ n

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R]
  {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]

abbrev A (U : X.affineOpens) : Type u := X.presheaf.obj (op U.1)

namespace Sys

theorem isLN (S : Sys I f) : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f

theorem noeth (S : Sys I f) (U : X.affineOpens) : IsNoetherianRing (A U) := by
  haveI := S.isLN
  exact IsLocallyNoetherian.component_noetherian U

theorem compactSpace (S : Sys I f) : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f

def K (S : Sys I f) : X.OrderedAffineCover :=
  haveI := S.compactSpace
  coverOfCompact X

def IU (S : Sys I f) (U : X.affineOpens) : Ideal (A U) :=
  I.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U.1 le_top).hom

end Sys

variable (S : Sys I f)

namespace Sys

abbrev H : OModulePresheaf f := internalHom S.F S.G

theorem H_coh_qc : S.H.IsCoherent ∧ S.H.IsQuasicoherent := by
  haveI := S.isLN
  have h := AlgebraicGeometry.OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq f S.F S.G S.hFc S.hFq
    S.hGc S.hGq
  exact ⟨h.1, h.2.1⟩

theorem hρc_app (n : ℕ) (U : X.affineOpens) (y : S.G.obj U.1) :
    (S.τ n).app U ((S.ρ (n + 1)).app U y) = (S.ρ n).app U y := by
  rw [← AffHom.comp_app, S.hρc n]

theorem hψ_app (n : ℕ) (U : X.affineOpens) (x : S.F.obj U.1) :
    (S.τ n).app U ((S.ψ (n + 1)).app U x) = (S.ψ n).app U x := by
  rw [← AffHom.comp_app, S.hψ n]

theorem smul_Gn_eq_zero (n : ℕ) (U : X.affineOpens) (i : R) (hi : i ∈ I ^ (n + 1)) (y : (S.Gn n).obj U.1) :
    i • y = 0 := by
  obtain ⟨g, rfl⟩ := S.hρs n U y
  rw [← map_smul, ← LinearMap.mem_ker, S.hρk n U]
  exact Submodule.smul_mem_smul hi Submodule.mem_top

theorem sections_smul_mem (M : OModulePresheaf f) (U : X.Opens) (J : Ideal R) (a : Γ(X, U)) {y : M.obj U}
    (hy : y ∈ J • (⊤ : Submodule R (M.obj U))) : a • y ∈ J • (⊤ : Submodule R (M.obj U)) := by
  induction hy using Submodule.smul_induction_on' with
  | smul i hi m hm =>
    rw [← smul_comm_sections M U i a m]
    exact Submodule.smul_mem_smul hi Submodule.mem_top
  | add x hx y hy h₁ h₂ =>
    rw [smul_add]
    exact Submodule.add_mem _ h₁ h₂

theorem isQuasicoherent_Gn (n : ℕ) : (S.Gn n).IsQuasicoherent := by
  intro U r

  let D : X.affineOpens := ⟨X.basicOpen r, U.2.basicOpen r⟩
  have hD : D.1 ≤ U.1 := X.basicOpen_le r
  let rr : ℕ → A D := fun N => (X.presheaf.map (homOfLE hD).op).hom (r ^ N)
  have hrr : ∀ N, rr N = (rr 1) ^ N := fun N => by simp only [rr, pow_one, map_pow]
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨g, rfl⟩ := S.hρs n D x
    obtain ⟨N, y, hy⟩ := (S.hGq U r).1 g
    refine ⟨N, (S.ρ n).app U y, ?_⟩
    have nat := (S.ρ n).naturality_apply (U := D) (U' := U) hD y
    change (S.Gn n).res hD ((S.ρ n).app U y) = rr N • (S.ρ n).app D g
    rw [← nat, hy, (S.ρ n).app_smul]
  · obtain ⟨g, rfl⟩ := S.hρs n U y

    have hker : S.G.res hD g ∈ I ^ (n + 1) • (⊤ : Submodule R (S.G.obj D.1)) := by
      rw [← S.hρk n D, LinearMap.mem_ker, (S.ρ n).naturality_apply (U := D) (U' := U) hD g]
      exact hy

    have key : ∀ x ∈ I ^ (n + 1) • (⊤ : Submodule R (S.G.obj D.1)), ∃ (N : ℕ) (y₀ : S.G.obj U.1),
        y₀ ∈ I ^ (n + 1) • (⊤ : Submodule R (S.G.obj U.1)) ∧ S.G.res hD y₀ = rr N • x := by
      intro x hx
      induction hx using Submodule.smul_induction_on' with
      | smul i hi m hm =>
        obtain ⟨N, y₁, hy₁⟩ := (S.hGq U r).1 m
        refine ⟨N, i • y₁, Submodule.smul_mem_smul hi Submodule.mem_top, ?_⟩
        rw [map_smul, hy₁, smul_comm_sections S.G D.1 i (rr N) m]
      | add x hx y hy h₁ h₂ =>
        obtain ⟨N₁, y₁, hy₁, e₁⟩ := h₁
        obtain ⟨N₂, y₂, hy₂, e₂⟩ := h₂
        refine ⟨N₁ + N₂, (r ^ N₂) • y₁ + (r ^ N₁) • y₂,
          Submodule.add_mem _ (sections_smul_mem S.G U.1 _ _ hy₁) (sections_smul_mem S.G U.1 _ _ hy₂), ?_⟩
        rw [map_add, S.G.res_smul, S.G.res_smul, e₁, e₂, smul_add]
        change rr N₂ • rr N₁ • x + rr N₁ • rr N₂ • y = rr (N₁ + N₂) • x + rr (N₁ + N₂) • y
        rw [hrr N₁, hrr N₂, hrr (N₁ + N₂), smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm N₂ N₁]
    obtain ⟨N, y₀, hy₀, e₀⟩ := key _ hker

    have hz : S.G.res hD ((r ^ N) • g - y₀) = 0 := by
      rw [map_sub, S.G.res_smul, e₀, sub_self]
    obtain ⟨N', hN'⟩ := (S.hGq U r).2 _ hz
    refine ⟨N' + N, ?_⟩
    rw [← (S.ρ n).app_smul, ← LinearMap.mem_ker, S.hρk n U]
    have e : (r ^ (N' + N)) • g = (r ^ N') • y₀ := by
      rw [smul_sub, smul_smul, ← pow_add, sub_eq_zero] at hN'
      exact hN'
    rw [e]
    exact sections_smul_mem S.G U.1 _ _ hy₀

section Local

variable (U : X.affineOpens)

theorem mem_IU_pow_smul_top_iff (M : OModulePresheaf f) (k : ℕ) (x : M.obj U.1) :
    x ∈ S.IU U ^ k • (⊤ : Submodule (A U) (M.obj U.1)) ↔ x ∈ I ^ k • (⊤ : Submodule R (M.obj U.1)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U.1
  haveI := M.isScalarTower U.1
  have e : S.IU U = I.map (algebraMap R (A U)) := rfl
  rw [← Submodule.restrictScalars_mem R, e, ← Ideal.map_pow, Ideal.smul_restrictScalars,
    Submodule.restrictScalars_top]

abbrev HomU : Type u := S.F.obj U.1 →ₗ[A U] S.G.obj U.1

theorem res_refl_fun (a : A U) : (X.presheaf.map (homOfLE (le_refl U.1)).op).hom a = a := by
  rw [Subsingleton.elim (homOfLE (le_refl U.1)).op (𝟙 (op U.1)), X.presheaf.map_id]
  rfl

def evalA : S.H.obj U.1 →ₗ[A U] S.HomU U where
  toFun φ :=
    { toFun := fun x => φ.1 ⟨U, le_rfl⟩ x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => φ.2.1 ⟨U, le_rfl⟩ a x }
  map_add' φ ψ := rfl
  map_smul' a φ := by
    refine LinearMap.ext fun x => ?_
    change (a • φ).1 ⟨U, le_rfl⟩ x = a • φ.1 ⟨U, le_rfl⟩ x
    rw [internalHom_smul_apply]
    exact congrArg (· • φ.1 ⟨U, le_rfl⟩ x) (res_refl_fun U a)

theorem evalA_apply (φ : S.H.obj U.1) (x : S.F.obj U.1) : S.evalA U φ x = φ.1 ⟨U, le_rfl⟩ x := rfl

theorem evalA_bijective : Function.Bijective (S.evalA U) := by
  haveI := S.isLN
  constructor
  · intro φ ψ h
    exact AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq S.hFq S.hGq U φ ψ
      fun x => by rw [← evalA_apply, ← evalA_apply, h]
  · intro g
    obtain ⟨φ, hφ, -⟩ :=
      (AlgebraicGeometry.OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq f S.F S.G S.hFc S.hFq
        S.hGc S.hGq).2.2 U g
    exact ⟨φ, LinearMap.ext hφ⟩

def evalE : S.H.obj U.1 ≃ₗ[A U] S.HomU U := LinearEquiv.ofBijective (S.evalA U) (S.evalA_bijective U)

theorem evalE_apply (φ : S.H.obj U.1) (x : S.F.obj U.1) : S.evalE U φ x = φ.1 ⟨U, le_rfl⟩ x := rfl

theorem sub_mem_iff_evalE (k : ℕ) (φ φ' : S.H.obj U.1) :
    φ - φ' ∈ I ^ k • (⊤ : Submodule R (S.H.obj U.1)) ↔
      S.evalE U φ - S.evalE U φ' ∈ S.IU U ^ k • (⊤ : Submodule (A U) (S.HomU U)) := by
  rw [← S.mem_IU_pow_smul_top_iff U S.H k, mem_smul_top_iff_of_linearEquiv _ (S.evalE U), map_sub]

abbrev PU (n : ℕ) : Submodule (A U) (S.G.obj U.1) := S.IU U ^ (n + 1) • ⊤

theorem PU_eq_ker (n : ℕ) : S.PU U n = LinearMap.ker ((S.ρ n).appSections U) := by
  ext x
  rw [S.mem_IU_pow_smul_top_iff U S.G, LinearMap.mem_ker, AffHom.appSections_apply, ← LinearMap.mem_ker,
    S.hρk n U]

def eQ (n : ℕ) : (S.G.obj U.1 ⧸ S.PU U n) ≃ₗ[A U] (S.Gn n).obj U.1 :=
  (Submodule.quotEquivOfEq _ _ (S.PU_eq_ker U n)).trans
    (LinearMap.quotKerEquivOfSurjective ((S.ρ n).appSections U) (S.hρs n U))

theorem eQ_mk (n : ℕ) (y : S.G.obj U.1) : S.eQ U n (Submodule.Quotient.mk y) = (S.ρ n).app U y := by
  rw [eQ, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

theorem eQ_symm_apply (n : ℕ) (y : S.G.obj U.1) : (S.eQ U n).symm ((S.ρ n).app U y) = Submodule.Quotient.mk y := by
  rw [← eQ_mk, LinearEquiv.symm_apply_apply]

def psiT (n : ℕ) : S.F.obj U.1 →ₗ[A U] S.G.obj U.1 ⧸ S.PU U n :=
  (S.eQ U n).symm.toLinearMap ∘ₗ (S.ψ n).appSections U

theorem psiT_apply (n : ℕ) (x : S.F.obj U.1) : S.psiT U n x = (S.eQ U n).symm ((S.ψ n).app U x) := rfl

theorem PU_le (n : ℕ) : S.PU U (n + 1) ≤ S.PU U n :=
  show S.IU U ^ (n + 1 + 1) • (⊤ : Submodule (A U) (S.G.obj U.1)) ≤ S.IU U ^ (n + 1) • ⊤ from
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

theorem factor_psiT (n : ℕ) : Submodule.factor (S.PU_le U n) ∘ₗ S.psiT U (n + 1) = S.psiT U n := by
  refine LinearMap.ext fun x => (S.eQ U n).injective ?_
  rw [LinearMap.comp_apply, psiT_apply, psiT_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨y, hy⟩ := S.hρs (n + 1) U ((S.ψ (n + 1)).app U x)
  rw [← hy, eQ_symm_apply, ← Submodule.mkQ_apply, Submodule.factor_mk, Submodule.mkQ_apply, eQ_mk,
    ← S.hρc_app, hy, S.hψ_app]

theorem mkQ_comp_eq_psiT_iff (n : ℕ) (g : S.HomU U) :
    Submodule.mkQ (S.PU U n) ∘ₗ g = S.psiT U n ↔ ∀ x : S.F.obj U.1, (S.ρ n).app U (g x) = (S.ψ n).app U x := by
  constructor
  · intro h x
    have hx := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, psiT_apply] at hx
    have := congrArg (S.eQ U n) hx
    rwa [eQ_mk, LinearEquiv.apply_symm_apply] at this
  · intro h
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, psiT_apply, ← h x, eQ_symm_apply]

theorem hal :
    ∃! Φ : ∀ n : ℕ, S.HomU U ⧸ (S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.HomU U))),
      (∀ n : ℕ, Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
        (Φ (n + 1)) = Φ n) ∧
      (∀ (n : ℕ) (g : S.HomU U), Submodule.Quotient.mk g = Φ n →
        (Submodule.mkQ (S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.G.obj U.1)))) ∘ₗ g = S.psiT U n) := by
  haveI := S.noeth U
  haveI : Module.Finite (A U) (S.F.obj U.1) := S.hFc U
  haveI : Module.Finite (A U) (S.G.obj U.1) := S.hGc U
  exact Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq (S.IU U) (S.psiT U)
    (S.factor_psiT U)

def Phi : ∀ n : ℕ, S.HomU U ⧸ (S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.HomU U))) := (S.hal U).exists.choose

theorem Phi_compat (n : ℕ) :
    Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (S.Phi U (n + 1)) =
      S.Phi U n :=
  (S.hal U).exists.choose_spec.1 n

theorem Phi_alpha (n : ℕ) (g : S.HomU U) (hg : Submodule.Quotient.mk g = S.Phi U n) :
    ∀ x : S.F.obj U.1, (S.ρ n).app U (g x) = (S.ψ n).app U x :=
  (S.mkQ_comp_eq_psiT_iff U n g).mp ((S.hal U).exists.choose_spec.2 n g hg)

theorem Phi_unique (Φ' : ∀ n : ℕ, S.HomU U ⧸ (S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.HomU U))))
    (h1 : ∀ n : ℕ, Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
        (Φ' (n + 1)) = Φ' n)
    (h2 : ∀ (n : ℕ) (g : S.HomU U), Submodule.Quotient.mk g = Φ' n →
        ∀ x : S.F.obj U.1, (S.ρ n).app U (g x) = (S.ψ n).app U x) :
    Φ' = S.Phi U :=
  (S.hal U).unique ⟨h1, fun n g hg => (S.mkQ_comp_eq_psiT_iff U n g).mpr (h2 n g hg)⟩
    (S.hal U).exists.choose_spec

theorem classes_eq_Phi (h : ℕ → S.H.obj U.1)
    (hcomp : ∀ n : ℕ, h (n + 1) - h n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)))
    (halpha : ∀ (n : ℕ) (x : S.F.obj U.1), (S.ρ n).app U ((h n).1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x) :
    (fun n => Submodule.Quotient.mk (S.evalE U (h n))) = S.Phi U := by
  refine S.Phi_unique U _ (fun n => ?_) (fun n g hg x => ?_)
  · change Submodule.factor _ (Submodule.mkQ _ (S.evalE U (h (n + 1)))) = Submodule.mkQ _ (S.evalE U (h n))
    rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact (S.sub_mem_iff_evalE U (n + 1) _ _).mp (hcomp n)
  ·
    have hg' : g - S.evalE U (h n) ∈ S.IU U ^ (n + 1) • (⊤ : Submodule (A U) (S.HomU U)) :=
      (Submodule.Quotient.eq _).mp hg
    have hgx : g x - (h n).1 ⟨U, le_rfl⟩ x ∈ I ^ (n + 1) • (⊤ : Submodule R (S.G.obj U.1)) := by
      rw [← S.mem_IU_pow_smul_top_iff U S.G, ← evalE_apply, ← LinearMap.sub_apply]
      exact map_mem_smul_top _ (LinearMap.applyₗ x) hg'
    have hzero : (S.ρ n).app U (g x - (h n).1 ⟨U, le_rfl⟩ x) = 0 := by
      rw [← LinearMap.mem_ker, S.hρk n U]
      exact hgx
    rw [map_sub, sub_eq_zero] at hzero
    rw [hzero, halpha]

theorem alpha_of_class (n : ℕ) (h : S.H.obj U.1) (hh : Submodule.Quotient.mk (S.evalE U h) = S.Phi U n)
    (x : S.F.obj U.1) : (S.ρ n).app U (h.1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x :=
  S.Phi_alpha U n (S.evalE U h) hh x

def rep (n : ℕ) : S.H.obj U.1 :=
  (S.evalE U).symm (Submodule.Quotient.mk_surjective _ (S.Phi U n)).choose

theorem evalE_rep (n : ℕ) : S.evalE U (S.rep U n) = (Submodule.Quotient.mk_surjective _ (S.Phi U n)).choose :=
  LinearEquiv.apply_symm_apply _ _

theorem mk_evalE_rep (n : ℕ) : Submodule.Quotient.mk (S.evalE U (S.rep U n)) = S.Phi U n := by
  rw [evalE_rep]
  exact (Submodule.Quotient.mk_surjective _ (S.Phi U n)).choose_spec

theorem rep_alpha (n : ℕ) (x : S.F.obj U.1) : (S.ρ n).app U ((S.rep U n).1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x :=
  S.alpha_of_class U n (S.rep U n) (S.mk_evalE_rep U n) x

theorem rep_succ_sub_rep (n : ℕ) : S.rep U (n + 1) - S.rep U n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)) := by
  rw [S.sub_mem_iff_evalE U, ← Submodule.Quotient.eq]
  have h := S.Phi_compat U n
  rw [← mk_evalE_rep, ← mk_evalE_rep] at h
  change Submodule.factor _ (Submodule.mkQ _ (S.evalE U (S.rep U (n + 1)))) =
    Submodule.mkQ _ (S.evalE U (S.rep U n)) at h
  rw [Submodule.factor_mk] at h
  exact h

theorem rep_sub_rep_of_le {n m : ℕ} (hnm : n ≤ m) :
    S.rep U m - S.rep U n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)) := by
  induction m, hnm using Nat.le_induction with
  | base => rw [sub_self]; exact Submodule.zero_mem _
  | succ m hnm ih =>
    have e : S.rep U (m + 1) - S.rep U n = (S.rep U (m + 1) - S.rep U m) + (S.rep U m - S.rep U n) := by abel
    rw [e]
    have hle : n + 1 ≤ m + 1 := by omega
    exact Submodule.add_mem _
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right hle) (S.rep_succ_sub_rep U m)) ih

theorem sub_rep_mem_of_classes (h : ℕ → S.H.obj U.1)
    (hcomp : ∀ n : ℕ, h (n + 1) - h n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)))
    (halpha : ∀ (n : ℕ) (x : S.F.obj U.1), (S.ρ n).app U ((h n).1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x) (n : ℕ) :
    h n - S.rep U n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1)) := by
  rw [S.sub_mem_iff_evalE U, ← Submodule.Quotient.eq, mk_evalE_rep]
  exact congrFun (S.classes_eq_Phi U h hcomp halpha) n

theorem alpha_of_sub_rep_mem (n : ℕ) (h : S.H.obj U.1)
    (hh : h - S.rep U n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj U.1))) (x : S.F.obj U.1) :
    (S.ρ n).app U (h.1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x := by
  refine S.alpha_of_class U n h ?_ x
  rw [← mk_evalE_rep, Submodule.Quotient.eq]
  exact (S.sub_mem_iff_evalE U (n + 1) _ _).mp hh

end Local

def pushFam (n : ℕ) {U : X.Opens} (h : S.H.obj U) : (internalHom S.F (S.Gn n)).obj U :=
  ⟨fun W => (S.ρ n).app W.1 ∘ₗ h.1 W,
    ⟨fun W a x => by
      change (S.ρ n).app W.1 (h.1 W (a • x)) = a • (S.ρ n).app W.1 (h.1 W x)
      rw [h.2.1 W a x, (S.ρ n).app_smul],
    fun W W' hW x => by
      change (S.ρ n).app W.1 (h.1 W (S.F.res hW x)) = (S.Gn n).res hW ((S.ρ n).app W'.1 (h.1 W' x))
      rw [h.2.2 W W' hW x, (S.ρ n).naturality_apply (U := W.1) (U' := W'.1) hW]⟩⟩

theorem pushFam_apply (n : ℕ) {U : X.Opens} (h : S.H.obj U) (W : AffBelow U) (x : S.F.obj W.1.1) :
    (S.pushFam n h).1 W x = (S.ρ n).app W.1 (h.1 W x) := rfl

def psiFam (n : ℕ) (U : X.Opens) : (internalHom S.F (S.Gn n)).obj U :=
  (internalHom S.F (S.Gn n)).res (le_top : U ≤ ⊤) (internalHom.ofAffHom S.F (S.Gn n) (S.ψ n))

theorem psiFam_apply (n : ℕ) (U : X.Opens) (W : AffBelow U) (x : S.F.obj W.1.1) :
    (S.psiFam n U).1 W x = (S.ψ n).app W.1 x := rfl

theorem alpha_below (n : ℕ) (U : X.affineOpens) (h : S.H.obj U.1)
    (halpha : ∀ x : S.F.obj U.1, (S.ρ n).app U (h.1 ⟨U, le_rfl⟩ x) = (S.ψ n).app U x)
    (W : AffBelow U.1) (x : S.F.obj W.1.1) : (S.ρ n).app W.1 (h.1 W x) = (S.ψ n).app W.1 x := by
  have key : S.pushFam n h = S.psiFam n U.1 :=
    AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq S.hFq (S.isQuasicoherent_Gn n) U _ _
      fun x => halpha x
  have := congrArg (fun θ : (internalHom S.F (S.Gn n)).obj U.1 => θ.1 W x) key
  exact this

theorem res_rep_sub_rep_mem (U : X.affineOpens) (W : X.affineOpens) (hW : W.1 ≤ U.1) (n : ℕ) :
    S.H.res hW (S.rep U n) - S.rep W n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj W.1)) := by
  refine S.sub_rep_mem_of_classes W (fun n => S.H.res hW (S.rep U n)) (fun n => ?_) (fun n x => ?_) n
  · rw [← map_sub]
    exact map_mem_smul_top _ (S.H.res hW) (S.rep_succ_sub_rep U n)
  · exact S.alpha_below n U (S.rep U n) (S.rep_alpha U n) ⟨W, hW⟩ x

theorem res_rep_sub_res_rep_mem (U U' W : X.affineOpens) (hW : W.1 ≤ U.1) (hW' : W.1 ≤ U'.1) (n : ℕ) :
    S.H.res hW (S.rep U n) - S.H.res hW' (S.rep U' n) ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj W.1)) := by
  have e : S.H.res hW (S.rep U n) - S.H.res hW' (S.rep U' n) =
      (S.H.res hW (S.rep U n) - S.rep W n) - (S.H.res hW' (S.rep U' n) - S.rep W n) := by abel
  rw [e]
  exact Submodule.sub_mem _ (S.res_rep_sub_rep_mem U W hW n) (S.res_rep_sub_rep_mem U' W hW' n)

abbrev Us {i : ℕ} (s : S.K.Idx i) : X.affineOpens := S.K.affineInter f s

def hcoch (n : ℕ) : S.H.cochain S.K 0 := fun s => S.rep (S.Us s) n

theorem d_hcoch_mem (n : ℕ) (t : S.K.Idx 1) :
    S.H.d S.K 0 (S.hcoch n) t ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter t))) := by
  rw [d_zero_apply]
  exact S.res_rep_sub_res_rep_mem (S.Us (S.K.face t 0)) (S.Us (S.K.face t 1)) (S.Us t)
    (S.K.inter_le_inter_face t 0) (S.K.inter_le_inter_face t 1) n

theorem exists_cocycle (m : ℕ) :
    ∃ z : S.H.cochain S.K 0, S.H.d S.K 0 z = 0 ∧
      ∀ s : S.K.Idx 0, z s - S.rep (S.Us s) m ∈ I ^ (m + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) := by
  obtain ⟨c, hc⟩ := AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper I S.H
    S.H_coh_qc.1 S.H_coh_qc.2 S.K (m + 1)
  obtain ⟨w', hw'mem, hw'd⟩ := hc (S.hcoch (m + c)) fun t => by
    have e : m + 1 + c = m + c + 1 := by omega
    rw [e]
    exact S.d_hcoch_mem (m + c) t
  refine ⟨S.hcoch (m + c) - w', ?_, fun s => ?_⟩
  · rw [map_sub, hw'd, sub_self]
  · have e : (S.hcoch (m + c) - w') s - S.rep (S.Us s) m =
        (S.rep (S.Us s) (m + c) - S.rep (S.Us s) m) - w' s := by
      change (S.rep (S.Us s) (m + c) - w' s) - S.rep (S.Us s) m = _
      abel
    rw [e]
    exact Submodule.sub_mem _ (S.rep_sub_rep_of_le (S.Us s) (by omega)) (hw'mem s)

def zc (m : ℕ) : S.H.cochain S.K 0 := (S.exists_cocycle m).choose

theorem d_zc (m : ℕ) : S.H.d S.K 0 (S.zc m) = 0 := (S.exists_cocycle m).choose_spec.1

theorem zc_sub_rep (m : ℕ) (s : S.K.Idx 0) :
    S.zc m s - S.rep (S.Us s) m ∈ I ^ (m + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) :=
  (S.exists_cocycle m).choose_spec.2 s

theorem zc_mem_H0 (m : ℕ) : S.zc m ∈ S.H.H0 S.K := LinearMap.mem_ker.mpr (S.d_zc m)

theorem zc_succ_sub_zc_mem (m : ℕ) :
    S.zc (m + 1) - S.zc m ∈ S.H.H0 S.K ⊓ I ^ (m + 1) • (⊤ : Submodule R (S.H.cochain S.K 0)) := by
  refine ⟨Submodule.sub_mem _ (S.zc_mem_H0 (m + 1)) (S.zc_mem_H0 m), ?_⟩
  classical
  refine pi_mem_smul_top _ _ fun s => ?_
  have e : (S.zc (m + 1) - S.zc m) s = (S.zc (m + 1) s - S.rep (S.Us s) (m + 1)) +
      (S.rep (S.Us s) (m + 1) - S.rep (S.Us s) m) - (S.zc m s - S.rep (S.Us s) m) := by
    change S.zc (m + 1) s - S.zc m s = _
    abel
  rw [e]
  refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ (S.rep_succ_sub_rep (S.Us s) m)) (S.zc_sub_rep m s)
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (S.zc_sub_rep (m + 1) s)

def cAR (k : ℕ) : ℕ :=
  (AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper I f S.H S.H_coh_qc.1
    S.H_coh_qc.2 S.K k).choose

theorem cAR_spec (k : ℕ) :
    S.H.H0 S.K ⊓ I ^ (k + S.cAR k) • (⊤ : Submodule R (S.H.cochain S.K 0)) ≤ I ^ k • S.H.H0 S.K :=
  (AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper I f S.H S.H_coh_qc.1
    S.H_coh_qc.2 S.K k).choose_spec

def Nm (k : ℕ) : ℕ := (Finset.range (k + 1)).sup fun j => j + S.cAR j

theorem le_Nm (k : ℕ) : k + S.cAR k ≤ S.Nm k :=
  Finset.le_sup (f := fun j => j + S.cAR j) (Finset.mem_range.mpr (Nat.lt_succ_self k))

theorem Nm_mono : Monotone S.Nm := fun k l hkl =>
  Finset.sup_mono (Finset.range_subset_range.mpr (by omega))

theorem zc_sub_zc_mem (k a b : ℕ) (ha : S.Nm k ≤ a) (hab : a ≤ b) :
    S.zc b - S.zc a ∈ I ^ k • S.H.H0 S.K := by
  induction b, hab using Nat.le_induction with
  | base => rw [sub_self]; exact Submodule.zero_mem _
  | succ b hab ih =>
    have e : S.zc (b + 1) - S.zc a = (S.zc (b + 1) - S.zc b) + (S.zc b - S.zc a) := by abel
    rw [e]
    refine Submodule.add_mem _ (S.cAR_spec k ⟨(S.zc_succ_sub_zc_mem b).1, ?_⟩) ih
    have hle : k + S.cAR k ≤ b + 1 := by have := S.le_Nm k; omega
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hle) (S.zc_succ_sub_zc_mem b).2

def gseq (k : ℕ) : S.H.H0 S.K := ⟨S.zc (S.Nm k), S.zc_mem_H0 _⟩

theorem gseq_cauchy {k l : ℕ} (hkl : k ≤ l) :
    S.gseq k ≡ S.gseq l [SMOD I ^ k • (⊤ : Submodule R (S.H.H0 S.K))] := by
  rw [SModEq.sub_mem]
  have h : (S.gseq l - S.gseq k : S.H.H0 S.K) ∈ I ^ k • (⊤ : Submodule R (S.H.H0 S.K)) :=
    mem_smul_top_of_coe_mem _ _ _ (S.zc_sub_zc_mem k (S.Nm k) (S.Nm l) le_rfl (S.Nm_mono hkl))
  rw [← neg_sub]
  exact Submodule.neg_mem _ h

scoped instance finite_H0 : Module.Finite R (S.H.H0 S.K) :=
  (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper S.H S.H_coh_qc.1 S.H_coh_qc.2 S.K).1

scoped instance isAdicComplete_H0 : IsAdicComplete I (S.H.H0 S.K) :=
  IsAdicComplete.of_finite_of_isNoetherianRing I (S.H.H0 S.K)

theorem exists_limit :
    ∃ L : S.H.H0 S.K, ∀ k : ℕ, S.gseq k ≡ L [SMOD I ^ k • (⊤ : Submodule R (S.H.H0 S.K))] :=
  IsPrecomplete.prec' S.gseq fun {k l} hkl => S.gseq_cauchy hkl

def L : S.H.H0 S.K := S.exists_limit.choose

theorem gseq_sub_L (k : ℕ) : S.gseq k - S.L ∈ I ^ k • (⊤ : Submodule R (S.H.H0 S.K)) :=
  SModEq.sub_mem.mp (S.exists_limit.choose_spec k)

set_option maxHeartbeats 3200000 in

theorem L_sub_rep_mem (n : ℕ) (s : S.K.Idx 0) :
    (S.L : S.H.cochain S.K 0) s - S.rep (S.Us s) n ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) := by

  have h0 : ((S.gseq (n + 1) - S.L : S.H.H0 S.K) : S.H.cochain S.K 0) ∈
      I ^ (n + 1) • (⊤ : Submodule R (S.H.cochain S.K 0)) :=
    coe_mem_of_mem_smul_top (I ^ (n + 1)) (S.H.H0 S.K) _ (S.gseq_sub_L (n + 1))
  have h1 : ((S.gseq (n + 1) - S.L : S.H.H0 S.K) : S.H.cochain S.K 0) s ∈
      I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) :=
    apply_mem_smul_top (M := fun s : S.K.Idx 0 => S.H.obj (S.K.inter s)) (I ^ (n + 1)) h0 s
  have hN : n ≤ S.Nm (n + 1) := by have := S.le_Nm (n + 1); omega
  have h2 : S.zc (S.Nm (n + 1)) s - S.rep (S.Us s) (S.Nm (n + 1)) ∈
      I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (S.zc_sub_rep (S.Nm (n + 1)) s)
  have h3 := S.rep_sub_rep_of_le (S.Us s) hN
  have e : (S.L : S.H.cochain S.K 0) s - S.rep (S.Us s) n =
      -(((S.gseq (n + 1) - S.L : S.H.H0 S.K) : S.H.cochain S.K 0) s) +
        (S.zc (S.Nm (n + 1)) s - S.rep (S.Us s) (S.Nm (n + 1))) +
        (S.rep (S.Us s) (S.Nm (n + 1)) - S.rep (S.Us s) n) := by
    change (S.L : S.H.cochain S.K 0) s - S.rep (S.Us s) n =
      -((S.zc (S.Nm (n + 1)) s - (S.L : S.H.cochain S.K 0) s)) + _ + _
    abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ h1) h2) h3

theorem d_L : S.H.d S.K 0 (S.L : S.H.cochain S.K 0) = 0 := LinearMap.mem_ker.mp S.L.2

theorem exists_glued : ∃! Lt : S.H.obj ⊤, ∀ s : S.K.Idx 0, (S.L : S.H.cochain S.K 0) s = S.H.res le_top Lt :=
  (AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique S.hGq S.K _).mp S.d_L

def Lt : S.H.obj ⊤ := S.exists_glued.exists.choose

theorem res_Lt (s : S.K.Idx 0) : S.H.res (le_top : S.K.inter s ≤ ⊤) S.Lt = (S.L : S.H.cochain S.K 0) s :=
  (S.exists_glued.exists.choose_spec s).symm

theorem Lt_unique (M : S.H.obj ⊤) (hM : ∀ s : S.K.Idx 0, S.H.res (le_top : S.K.inter s ≤ ⊤) M =
    (S.L : S.H.cochain S.K 0) s) : M = S.Lt :=
  S.exists_glued.unique (fun s => (hM s).symm) S.exists_glued.exists.choose_spec

def phi : AffHom S.F S.G := internalHom.toAffHom S.F S.G S.Lt

theorem Lt_alpha (n : ℕ) (W : X.affineOpens) (x : S.F.obj W.1) :
    (S.ρ n).app W (S.Lt.1 ⟨W, le_top⟩ x) = (S.ψ n).app W x := by

  have hglue := (AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique
    (F := S.F) (S.isQuasicoherent_Gn n) S.K
    (fun s => (internalHom S.F (S.Gn n)).res (le_top : S.K.inter s ≤ ⊤) (S.psiFam n ⊤))).mp
    (d_zero_res_eq_zero (internalHom S.F (S.Gn n)) S.K (S.psiFam n ⊤))
  have key : S.pushFam n S.Lt = S.psiFam n ⊤ := by
    refine hglue.unique (fun s => ?_) (fun s => rfl)

    refine (AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq S.hFq (S.isQuasicoherent_Gn n)
      (S.Us s) _ _ fun y => ?_).symm
    change (S.ρ n).app (S.Us s) (S.Lt.1 ⟨S.Us s, le_top⟩ y) = (S.ψ n).app (S.Us s) y
    have e : S.Lt.1 ⟨S.Us s, le_top⟩ y = ((S.L : S.H.cochain S.K 0) s).1 ⟨S.Us s, le_rfl⟩ y := by
      rw [← S.res_Lt s]; rfl
    rw [e]
    exact S.alpha_of_sub_rep_mem (S.Us s) n _ (S.L_sub_rep_mem n s) y
  exact congrArg (fun θ : (internalHom S.F (S.Gn n)).obj ⊤ => θ.1 ⟨W, le_top⟩ x) key

theorem phi_spec (n : ℕ) : (S.ρ n).comp S.phi = S.ψ n :=
  affHom_ext _ _ fun W x => S.Lt_alpha n W x

theorem phi_unique (φ' : AffHom S.F S.G) (hφ' : ∀ n : ℕ, (S.ρ n).comp φ' = S.ψ n) : φ' = S.phi := by
  let M : S.H.obj ⊤ := internalHom.ofAffHom S.F S.G φ'

  let δ : S.H.cochain S.K 0 := fun s => S.H.res (le_top : S.K.inter s ≤ ⊤) M - (S.L : S.H.cochain S.K 0) s
  have hδmem : ∀ (n : ℕ) (s : S.K.Idx 0),
      δ s ∈ I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) := by
    intro n s
    have hM : S.H.res (le_top : S.K.inter s ≤ ⊤) M - S.rep (S.Us s) n ∈
        I ^ (n + 1) • (⊤ : Submodule R (S.H.obj (S.K.inter s))) := by
      refine S.sub_rep_mem_of_classes (S.Us s) (fun _ => S.H.res (le_top : S.K.inter s ≤ ⊤) M)
        (fun k => by rw [sub_self]; exact Submodule.zero_mem _) (fun k x => ?_) n
      change (S.ρ k).app (S.Us s) (φ'.app (S.Us s) x) = (S.ψ k).app (S.Us s) x
      rw [← AffHom.comp_app, hφ' k]
    have e : δ s = (S.H.res (le_top : S.K.inter s ≤ ⊤) M - S.rep (S.Us s) n) -
        ((S.L : S.H.cochain S.K 0) s - S.rep (S.Us s) n) := by
      change S.H.res le_top M - (S.L : S.H.cochain S.K 0) s = _
      abel
    rw [e]
    exact Submodule.sub_mem _ hM (S.L_sub_rep_mem n s)
  have hδ0 : S.H.d S.K 0 δ = 0 := by
    have e : δ = (fun s => S.H.res (le_top : S.K.inter s ≤ ⊤) M) - (S.L : S.H.cochain S.K 0) := rfl
    rw [e, map_sub, d_zero_res_eq_zero, S.d_L, sub_self]
  have hδ : δ = 0 := by
    refine AlgebraicGeometry.OModulePresheaf.eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper I S.H
      S.H_coh_qc.1 S.H_coh_qc.2 S.K δ hδ0 fun k s => ?_
    cases k with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    | succ n => exact hδmem n s
  have hM : M = S.Lt := S.Lt_unique M fun s => by
    have := congrFun hδ s
    rwa [Pi.zero_apply, sub_eq_zero] at this
  calc φ' = internalHom.toAffHom S.F S.G M := (internalHom.toAffHom_ofAffHom S.F S.G φ').symm
    _ = S.phi := by rw [hM]; rfl

theorem main :
    ∃ φ : AffHom S.F S.G, (∀ n : ℕ, (S.ρ n).comp φ = S.ψ n) ∧
      ∀ φ' : AffHom S.F S.G, (∀ n : ℕ, (S.ρ n).comp φ' = S.ψ n) → φ' = φ :=
  ⟨S.phi, S.phi_spec, S.phi_unique⟩

end Sys
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys"

end HomCompleteAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux"

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F G : OModulePresheaf f)
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (Gn : ℕ → OModulePresheaf f) (τ : ∀ n : ℕ, OModulePresheaf.AffHom (Gn (n + 1)) (Gn n))
    (ρ : ∀ n : ℕ, OModulePresheaf.AffHom G (Gn n))
    (hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U))
    (hρk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)))
    (hρc : ∀ n : ℕ, (τ n).comp (ρ (n + 1)) = ρ n)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (Gn n)) (hψ : ∀ n : ℕ, (τ n).comp (ψ (n + 1)) = ψ n) :
    ∃ φ : OModulePresheaf.AffHom F G, (∀ n : ℕ, (ρ n).comp φ = ψ n) ∧
      ∀ φ' : OModulePresheaf.AffHom F G, (∀ n : ℕ, (ρ n).comp φ' = ψ n) → φ' = φ :=
  HomCompleteAux.Sys.main
    { F := F, G := G, hFc := hFc, hFq := hFq, hGc := hGc, hGq := hGq, Gn := Gn, τ := τ, ρ := ρ,
      hρs := hρs, hρk := hρk, hρc := hρc, ψ := ψ, hψ := hψ }

end S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper (solution)
