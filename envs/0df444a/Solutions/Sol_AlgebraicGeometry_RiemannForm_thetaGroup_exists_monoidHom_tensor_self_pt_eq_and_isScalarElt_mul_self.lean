-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/faa2ffd8-67f4-504c-840e-f75b597a5259

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm"

noncomputable section

namespace TgEps
set_option backward.isDefEq.respectTransparency false

section core
variable {A : Scheme.{0}}

theorem fib_mapComp_inv_app (a b : A ⟶ A) (N : A.Modules) :
    (Scheme.Modules.fibration.mapComp b.op.toLoc a.op.toLoc).inv.toNatTrans.app N =
      (Scheme.Modules.pullbackComp a b).hom.app N := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]
  rfl

theorem fib_mapId_inv_app (N : A.Modules) :
    (Scheme.Modules.fibration.mapId ⟨Opposite.op A⟩).inv.toNatTrans.app N = (Scheme.Modules.pullbackId A).inv.app N := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]

theorem pullbackTensorObjIso_inv {X Y : Scheme.{0}} (b : X ⟶ Y) (L N : Y.Modules) :
    (Scheme.Modules.pullbackTensorObjIso b L N).inv = Functor.LaxMonoidal.μ (Scheme.Modules.pullback b) L N := rfl

theorem pullbackTensorObjIso_hom {X Y : Scheme.{0}} (b : X ⟶ Y) (L N : Y.Modules) :
    (Scheme.Modules.pullbackTensorObjIso b L N).hom = Functor.OplaxMonoidal.δ (Scheme.Modules.pullback b) L N := rfl

variable (M : A.Modules)

def epsFiber (b : A ⟶ A) (φ : M ⟶ (Scheme.Modules.pullback b).obj M) :
    M ⊗ M ⟶ (Scheme.Modules.pullback b).obj (M ⊗ M) :=
  (φ ⊗ₘ φ) ≫ (Scheme.Modules.pullbackTensorObjIso b M M).inv

theorem epsFiber_comp (b b' : A ⟶ A) (φ : M ⟶ (Scheme.Modules.pullback b).obj M)
    (ψ : M ⟶ (Scheme.Modules.pullback b').obj M) :
    epsFiber M (b ≫ b') (φ ≫ (Scheme.Modules.pullback b).map ψ ≫ (Scheme.Modules.pullbackComp b b').hom.app M) =
      epsFiber M b φ ≫ (Scheme.Modules.pullback b).map (epsFiber M b' ψ) ≫
        (Scheme.Modules.pullbackComp b b').hom.app (M ⊗ M) := by
  have hc : (Scheme.Modules.pullbackComp b b').hom.app (M ⊗ M) =
      (Scheme.Modules.pullback b).map (Scheme.Modules.pullbackTensorObjIso b' M M).hom ≫
        (Scheme.Modules.pullbackTensorObjIso b ((Scheme.Modules.pullback b').obj M) ((Scheme.Modules.pullback b').obj M)).hom ≫
        ((Scheme.Modules.pullbackComp b b').hom.app M ⊗ₘ (Scheme.Modules.pullbackComp b b').hom.app M) ≫
        (Scheme.Modules.pullbackTensorObjIso (b ≫ b') M M).inv := by
    rw [← Iso.app_hom, AlgebraicGeometry.Scheme.Modules.pullbackComp_app_tensorObj b b' M M]
    simp only [Iso.trans_hom, Functor.mapIso_hom, tensorIso_hom, Iso.symm_hom, Iso.app_hom]
  rw [hc]
  simp only [epsFiber, pullbackTensorObjIso_inv, pullbackTensorObjIso_hom, Functor.map_comp, Category.assoc,
    Functor.Monoidal.map_μ_δ_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_assoc]
  simp only [Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom_assoc]

scoped instance isIso_epsFiber (b : A ⟶ A) (φ : M ⟶ (Scheme.Modules.pullback b).obj M) [IsIso φ] :
    IsIso (epsFiber M b φ) := by
  unfold epsFiber
  infer_instance

def eps (u : modulePair (A := A) M ⟶ modulePair (A := A) M) :
    modulePair (A := A) (M ⊗ M) ⟶ modulePair (A := A) (M ⊗ M) :=
  Pseudofunctor.CoGrothendieck.homMk u.base (epsFiber M u.base u.fiber)

@[scoped simp] theorem eps_base (u : modulePair (A := A) M ⟶ modulePair (A := A) M) : (eps M u).base = u.base := rfl
@[scoped simp] theorem eps_fiber (u : modulePair (A := A) M ⟶ modulePair (A := A) M) :
    (eps M u).fiber = epsFiber M u.base u.fiber := rfl

theorem eps_comp (u v : modulePair (A := A) M ⟶ modulePair (A := A) M) :
    eps M (u ≫ v) = eps M u ≫ eps M v := by
  obtain ⟨b, φ⟩ := u
  obtain ⟨b', ψ⟩ := v
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by rfl) ?_
  simp only [eqToHom_refl, Category.comp_id, eps_fiber, Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber,
    Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, eps_base, modulePair_fiber,
    Scheme.Modules.fibration_map_toFunctor, fib_mapComp_inv_app]
  exact epsFiber_comp M b b' φ ψ

theorem id_fiber_eq (N : A.Modules) :
    (𝟙 (modulePair (A := A) N) : modulePair (A := A) N ⟶ modulePair (A := A) N).fiber =
      (Scheme.Modules.pullbackId A).inv.app N := by
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, modulePair_base, modulePair_fiber, fib_mapId_inv_app]

theorem eps_id : eps M (𝟙 (modulePair (A := A) M)) = 𝟙 _ := by
  have h2 : eps M (𝟙 _) ≫ eps M (𝟙 _) = 𝟙 _ ≫ eps M (𝟙 (modulePair (A := A) M)) := by
    rw [← eps_comp, Category.id_comp, Category.id_comp]
  have hφ : IsIso (𝟙 (modulePair (A := A) M) : modulePair (A := A) M ⟶ modulePair (A := A) M).fiber := by
    rw [id_fiber_eq]
    infer_instance
  have hb : Mono (𝟙 (modulePair (A := A) M) : modulePair (A := A) M ⟶ modulePair (A := A) M).base := by
    change Mono (𝟙 A)
    infer_instance
  haveI : Mono (eps M (𝟙 (modulePair (A := A) M))) := by
    unfold eps
    refine @Pseudofunctor.CoGrothendieck.mono_homMk _ _ _ (modulePair (A := A) (M ⊗ M)) (modulePair (A := A) (M ⊗ M)) _ hb
      (epsFiber M (𝟙 (modulePair (A := A) M) : modulePair (A := A) M ⟶ modulePair (A := A) M).base
        (𝟙 (modulePair (A := A) M) : modulePair (A := A) M ⟶ modulePair (A := A) M).fiber) ?_
    exact @isIso_epsFiber _ M _ _ hφ
  exact (cancel_mono _).1 h2

def epsAut (a : Aut (modulePair (A := A) M)) : Aut (modulePair (A := A) (M ⊗ M)) where
  hom := eps M a.hom
  inv := eps M a.inv
  hom_inv_id := by rw [← eps_comp, a.hom_inv_id, eps_id]
  inv_hom_id := by rw [← eps_comp, a.inv_hom_id, eps_id]

theorem epsAut_mul (a b : Aut (modulePair (A := A) M)) : epsAut M (a * b) = epsAut M a * epsAut M b :=
  Iso.ext (by
    change eps M (b.hom ≫ a.hom) = eps M b.hom ≫ eps M a.hom
    exact eps_comp M b.hom a.hom)

def rd (N : A.Modules) (u : modulePair (A := A) N ⟶ modulePair (A := A) N) (h : u.base = 𝟙 A) : N ⟶ N :=
  u.fiber ≫ (Scheme.Modules.pullbackCongr h).hom.app N ≫ (Scheme.Modules.pullbackId A).hom.app N

theorem rd_congr (N : A.Modules) {u v : modulePair (A := A) N ⟶ modulePair (A := A) N} (e : u = v)
    (h : u.base = 𝟙 A) (h' : v.base = 𝟙 A) : rd N u h = rd N v h' := by
  subst e
  rfl

theorem rd_id (N : A.Modules) (h : (𝟙 (modulePair (A := A) N) : modulePair (A := A) N ⟶ modulePair (A := A) N).base = 𝟙 A) :
    rd N (𝟙 _) h = 𝟙 N := by
  simp only [rd, Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, modulePair_fiber, modulePair_base, fib_mapId_inv_app,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp]
  exact (Scheme.Modules.pullbackId A).inv_hom_id_app N

def theta : M ⊗ M ⟶ M ⊗ M :=
  ((Scheme.Modules.pullbackId A).inv.app M ⊗ₘ (Scheme.Modules.pullbackId A).inv.app M) ≫
    (Scheme.Modules.pullbackTensorObjIso (𝟙 A) M M).inv ≫ (Scheme.Modules.pullbackId A).hom.app (M ⊗ M)

theorem rd_eps (u : modulePair (A := A) M ⟶ modulePair (A := A) M) (h : u.base = 𝟙 A) :
    rd (M ⊗ M) (eps M u) h = (rd M u h ⊗ₘ rd M u h) ≫ theta M := by
  obtain ⟨b, φ⟩ := u
  change b = 𝟙 A at h
  subst h
  simp only [rd, eps_fiber, epsFiber, theta, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]

theorem theta_eq_id : theta M = 𝟙 (M ⊗ M) := by
  have h1 : rd (M ⊗ M) (eps M (𝟙 _)) rfl = (rd M (𝟙 _) rfl ⊗ₘ rd M (𝟙 _) rfl) ≫ theta M := rd_eps M (𝟙 _) rfl
  rw [rd_id, id_tensorHom_id, Category.id_comp, rd_congr (M ⊗ M) (eps_id M) rfl rfl, rd_id] at h1
  exact h1.symm

end core

section thetaGroup
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
variable (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules)

def epsHom : thetaGroup f L hc M →* thetaGroup f L hc (M ⊗ M) :=
  MonoidHom.mk' (fun g => ⟨(epsAut M g.1.1, g.1.2), g.2⟩) (fun g h => Subtype.ext (Prod.ext (epsAut_mul M g.1.1 h.1.1) rfl))

theorem pt_epsHom (g : thetaGroup f L hc M) :
    thetaGroup.pt f L hc (M ⊗ M) (epsHom f L hc M g) = thetaGroup.pt f L hc M g := rfl

theorem isScalarElt_epsHom (g : thetaGroup f L hc M) (c : k) (hg : thetaGroup.IsScalarElt f L hc M g c) :
    thetaGroup.IsScalarElt f L hc (M ⊗ M) (epsHom f L hc M g) (c * c) := by
  obtain ⟨hpt, hσ⟩ := hg
  refine ⟨hpt, ?_⟩
  have hB := thetaGroup.base_eq_id_of_pt_eq_one f L hc M g hpt
  have key : thetaGroup.unitReading (M ⊗ M)
      (thetaGroup.base_eq_id_of_pt_eq_one f L hc (M ⊗ M) (epsHom f L hc M g) hpt) =
      thetaGroup.unitReading M hB ⊗ₘ thetaGroup.unitReading M hB := by
    change rd (M ⊗ M) (eps M g.1.1.hom) hB = (rd M g.1.1.hom hB ⊗ₘ rd M g.1.1.hom hB)
    rw [rd_eps, theta_eq_id, Category.comp_id]
  rw [key]
  exact AlgebraicGeometry.RiemannForm.isConstScalar_tensorHom k f _ _ c c hσ hσ

theorem main
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (M : A.Modules) :
    ∃ ε : thetaGroup f L hc M →* thetaGroup f L hc (M ⊗ M),
      (∀ g : thetaGroup f L hc M, thetaGroup.pt f L hc (M ⊗ M) (ε g) = thetaGroup.pt f L hc M g) ∧
      (∀ (g : thetaGroup f L hc M) (c : k), thetaGroup.IsScalarElt f L hc M g c →
        thetaGroup.IsScalarElt f L hc (M ⊗ M) (ε g) (c * c)) :=
  ⟨epsHom f L hc M, pt_epsHom f L hc M, isScalarElt_epsHom f L hc M⟩

end thetaGroup
end TgEps
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self.TgEps"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self.TgEps"

theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ ε : thetaGroup f L hc M →* thetaGroup f L hc (M ⊗ M),
      (∀ g : thetaGroup f L hc M, thetaGroup.pt f L hc (M ⊗ M) (ε g) = thetaGroup.pt f L hc M g) ∧
      (∀ (g : thetaGroup f L hc M) (c : k), thetaGroup.IsScalarElt f L hc M g c →
        thetaGroup.IsScalarElt f L hc (M ⊗ M) (ε g) (c * c)) :=
  TgEps.main k f L hc M

end S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self (solution)
