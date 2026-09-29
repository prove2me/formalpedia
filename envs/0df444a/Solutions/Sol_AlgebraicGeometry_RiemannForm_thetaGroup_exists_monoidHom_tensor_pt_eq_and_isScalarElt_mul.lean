-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9d9c8816-a154-5a38-95ea-fb09c4fa65c0

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

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm"

noncomputable section

namespace TgTens
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

variable (M N : A.Modules)

def tensFiber (b : A ⟶ A) (φ : M ⟶ (Scheme.Modules.pullback b).obj M) (ψ : N ⟶ (Scheme.Modules.pullback b).obj N) :
    M ⊗ N ⟶ (Scheme.Modules.pullback b).obj (M ⊗ N) :=
  (φ ⊗ₘ ψ) ≫ (Scheme.Modules.pullbackTensorObjIso b M N).inv

theorem tensFiber_comp (b b' : A ⟶ A) (φ : M ⟶ (Scheme.Modules.pullback b).obj M)
    (φ' : M ⟶ (Scheme.Modules.pullback b').obj M) (ψ : N ⟶ (Scheme.Modules.pullback b).obj N)
    (ψ' : N ⟶ (Scheme.Modules.pullback b').obj N) :
    tensFiber M N (b ≫ b') (φ ≫ (Scheme.Modules.pullback b).map φ' ≫ (Scheme.Modules.pullbackComp b b').hom.app M)
        (ψ ≫ (Scheme.Modules.pullback b).map ψ' ≫ (Scheme.Modules.pullbackComp b b').hom.app N) =
      tensFiber M N b φ ψ ≫ (Scheme.Modules.pullback b).map (tensFiber M N b' φ' ψ') ≫
        (Scheme.Modules.pullbackComp b b').hom.app (M ⊗ N) := by
  have hc : (Scheme.Modules.pullbackComp b b').hom.app (M ⊗ N) =
      (Scheme.Modules.pullback b).map (Scheme.Modules.pullbackTensorObjIso b' M N).hom ≫
        (Scheme.Modules.pullbackTensorObjIso b ((Scheme.Modules.pullback b').obj M) ((Scheme.Modules.pullback b').obj N)).hom ≫
        ((Scheme.Modules.pullbackComp b b').hom.app M ⊗ₘ (Scheme.Modules.pullbackComp b b').hom.app N) ≫
        (Scheme.Modules.pullbackTensorObjIso (b ≫ b') M N).inv := by
    rw [← Iso.app_hom, AlgebraicGeometry.Scheme.Modules.pullbackComp_app_tensorObj b b' M N]
    simp only [Iso.trans_hom, Functor.mapIso_hom, tensorIso_hom, Iso.symm_hom, Iso.app_hom]
  rw [hc]
  simp only [tensFiber, pullbackTensorObjIso_inv, pullbackTensorObjIso_hom, Functor.map_comp, Category.assoc,
    Functor.Monoidal.map_μ_δ_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_assoc]
  simp only [Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom_assoc]

scoped instance isIso_tensFiber (b : A ⟶ A) (φ : M ⟶ (Scheme.Modules.pullback b).obj M)
    (ψ : N ⟶ (Scheme.Modules.pullback b).obj N) [IsIso φ] [IsIso ψ] : IsIso (tensFiber M N b φ ψ) := by
  unfold tensFiber
  infer_instance

def tens (b : A ⟶ A) (u : modulePair (A := A) M ⟶ modulePair (A := A) M) (v : modulePair (A := A) N ⟶ modulePair (A := A) N)
    (hu : u.base = b) (hv : v.base = b) :
    modulePair (A := A) (M ⊗ N) ⟶ modulePair (A := A) (M ⊗ N) :=
  Pseudofunctor.CoGrothendieck.homMk b
    (tensFiber M N b (u.fiber ≫ (Scheme.Modules.pullbackCongr hu).hom.app M) (v.fiber ≫ (Scheme.Modules.pullbackCongr hv).hom.app N))

@[scoped simp] theorem tens_base (b : A ⟶ A) (u : modulePair (A := A) M ⟶ modulePair (A := A) M)
    (v : modulePair (A := A) N ⟶ modulePair (A := A) N) (hu : u.base = b) (hv : v.base = b) :
    (tens M N b u v hu hv).base = b := rfl

theorem tens_congr {b b' : A ⟶ A} {u u' : modulePair (A := A) M ⟶ modulePair (A := A) M}
    {v v' : modulePair (A := A) N ⟶ modulePair (A := A) N} (eb : b = b') (eu : u = u') (ev : v = v')
    (hu : u.base = b) (hv : v.base = b) (hu' : u'.base = b') (hv' : v'.base = b') :
    tens M N b u v hu hv = tens M N b' u' v' hu' hv' := by
  subst eb eu ev
  rfl

theorem tens_comp (b b' : A ⟶ A) (u u' : modulePair (A := A) M ⟶ modulePair (A := A) M)
    (v v' : modulePair (A := A) N ⟶ modulePair (A := A) N)
    (hu : u.base = b) (hv : v.base = b) (hu' : u'.base = b') (hv' : v'.base = b')
    (huu : (u ≫ u').base = b ≫ b') (hvv : (v ≫ v').base = b ≫ b') :
    tens M N (b ≫ b') (u ≫ u') (v ≫ v') huu hvv = tens M N b u v hu hv ≫ tens M N b' u' v' hu' hv' := by
  obtain ⟨bu, φ⟩ := u
  obtain ⟨bu', φ'⟩ := u'
  obtain ⟨bv, ψ⟩ := v
  obtain ⟨bv', ψ'⟩ := v'
  change bu = b at hu; change bv = b at hv; change bu' = b' at hu'; change bv' = b' at hv'
  subst hu hv hu' hv'
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by rfl) ?_
  simp only [tens, eqToHom_refl, Category.comp_id, Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber,
    Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, Pseudofunctor.CoGrothendieck.homMk_base,
    Pseudofunctor.CoGrothendieck.homMk_fiber, modulePair_fiber, Scheme.Modules.fibration_map_toFunctor, fib_mapComp_inv_app,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  repeat (erw [Category.comp_id])
  exact tensFiber_comp M N _ _ φ φ' ψ ψ'

theorem id_base_eq (K : A.Modules) :
    (𝟙 (modulePair (A := A) K) : modulePair (A := A) K ⟶ modulePair (A := A) K).base = 𝟙 A := rfl

theorem id_fiber_eq (K : A.Modules) :
    (𝟙 (modulePair (A := A) K) : modulePair (A := A) K ⟶ modulePair (A := A) K).fiber =
      (Scheme.Modules.pullbackId A).inv.app K := by
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, modulePair_base, modulePair_fiber, fib_mapId_inv_app]

theorem tens_id : tens M N (𝟙 A) (𝟙 (modulePair (A := A) M)) (𝟙 (modulePair (A := A) N)) rfl rfl = 𝟙 _ := by
  have h2 : tens M N (𝟙 A) (𝟙 _) (𝟙 _) rfl rfl ≫ tens M N (𝟙 A) (𝟙 _) (𝟙 _) rfl rfl =
      𝟙 _ ≫ tens M N (𝟙 A) (𝟙 (modulePair (A := A) M)) (𝟙 (modulePair (A := A) N)) rfl rfl := by
    rw [Category.id_comp, ← tens_comp M N (𝟙 A) (𝟙 A) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) rfl rfl rfl rfl rfl rfl]
    exact tens_congr M N (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) _ _ _ _
  have hφ : IsIso ((𝟙 (modulePair (A := A) M) : modulePair (A := A) M ⟶ modulePair (A := A) M).fiber ≫
      (Scheme.Modules.pullbackCongr (id_base_eq M)).hom.app M) := by
    rw [id_fiber_eq]
    infer_instance
  have hψ : IsIso ((𝟙 (modulePair (A := A) N) : modulePair (A := A) N ⟶ modulePair (A := A) N).fiber ≫
      (Scheme.Modules.pullbackCongr (id_base_eq N)).hom.app N) := by
    rw [id_fiber_eq]
    infer_instance
  haveI : Mono (tens M N (𝟙 A) (𝟙 (modulePair (A := A) M)) (𝟙 (modulePair (A := A) N)) rfl rfl) := by
    unfold tens
    refine @Pseudofunctor.CoGrothendieck.mono_homMk _ _ _ (modulePair (A := A) (M ⊗ N)) (modulePair (A := A) (M ⊗ N)) (𝟙 A)
      (by change Mono (𝟙 A); infer_instance) _ ?_
    exact @isIso_tensFiber _ M N _ _ _ hφ hψ
  exact (cancel_mono _).1 h2

def baseIso (K : A.Modules) (a : Aut (modulePair (A := A) K)) : A ≅ A where
  hom := a.hom.base
  inv := a.inv.base
  hom_inv_id := by
    rw [← Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, a.hom_inv_id]
    rfl
  inv_hom_id := by
    rw [← Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, a.inv_hom_id]
    rfl

theorem inv_base_eq (K : A.Modules) (a : Aut (modulePair (A := A) K)) (e : A ≅ A) (h : a.hom.base = e.hom) :
    a.inv.base = e.inv := by
  have h1 : e.hom ≫ a.inv.base = 𝟙 A := by
    rw [← h, ← Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, a.hom_inv_id]
    rfl
  rw [(Iso.eq_inv_comp e).mpr h1, Category.comp_id]

def tensAut (a : Aut (modulePair (A := A) M)) (a' : Aut (modulePair (A := A) N)) (h : a'.hom.base = a.hom.base) :
    Aut (modulePair (A := A) (M ⊗ N)) where
  hom := tens M N a.hom.base a.hom a'.hom rfl h
  inv := tens M N a.inv.base a.inv a'.inv rfl (inv_base_eq N a' (baseIso M a) h)
  hom_inv_id := by
    rw [← tens_comp M N a.hom.base a.inv.base a.hom a.inv a'.hom a'.inv rfl h rfl (inv_base_eq N a' (baseIso M a) h)
      rfl (by rw [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, h, inv_base_eq N a' (baseIso M a) h]; rfl),
      tens_congr M N (show a.hom.base ≫ a.inv.base = 𝟙 A from (baseIso M a).hom_inv_id) a.hom_inv_id a'.hom_inv_id _ _ rfl rfl]
    exact tens_id M N
  inv_hom_id := by
    rw [← tens_comp M N a.inv.base a.hom.base a.inv a.hom a'.inv a'.hom rfl (inv_base_eq N a' (baseIso M a) h) rfl h
      rfl (by rw [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, h, inv_base_eq N a' (baseIso M a) h]; rfl),
      tens_congr M N (show a.inv.base ≫ a.hom.base = 𝟙 A from (baseIso M a).inv_hom_id) a.inv_hom_id a'.inv_hom_id _ _ rfl rfl]
    exact tens_id M N

theorem tensAut_hom (a : Aut (modulePair (A := A) M)) (a' : Aut (modulePair (A := A) N)) (h : a'.hom.base = a.hom.base) :
    (tensAut M N a a' h).hom = tens M N a.hom.base a.hom a'.hom rfl h := rfl

theorem tensAut_mul (a₁ a₂ : Aut (modulePair (A := A) M)) (b₁ b₂ : Aut (modulePair (A := A) N))
    (h₁ : b₁.hom.base = a₁.hom.base) (h₂ : b₂.hom.base = a₂.hom.base) (h₁₂ : (b₁ * b₂).hom.base = (a₁ * a₂).hom.base) :
    tensAut M N (a₁ * a₂) (b₁ * b₂) h₁₂ = tensAut M N a₁ b₁ h₁ * tensAut M N a₂ b₂ h₂ :=
  Iso.ext (by
    change tens M N (a₂.hom ≫ a₁.hom).base (a₂.hom ≫ a₁.hom) (b₂.hom ≫ b₁.hom) rfl h₁₂ =
      tens M N a₂.hom.base a₂.hom b₂.hom rfl h₂ ≫ tens M N a₁.hom.base a₁.hom b₁.hom rfl h₁
    exact tens_comp M N a₂.hom.base a₁.hom.base a₂.hom a₁.hom b₂.hom b₁.hom rfl h₂ rfl h₁ rfl h₁₂)

def rd (K : A.Modules) (u : modulePair (A := A) K ⟶ modulePair (A := A) K) (h : u.base = 𝟙 A) : K ⟶ K :=
  u.fiber ≫ (Scheme.Modules.pullbackCongr h).hom.app K ≫ (Scheme.Modules.pullbackId A).hom.app K

theorem rd_congr (K : A.Modules) {u v : modulePair (A := A) K ⟶ modulePair (A := A) K} (e : u = v)
    (h : u.base = 𝟙 A) (h' : v.base = 𝟙 A) : rd K u h = rd K v h' := by
  subst e
  rfl

theorem rd_id (K : A.Modules) (h : (𝟙 (modulePair (A := A) K) : modulePair (A := A) K ⟶ modulePair (A := A) K).base = 𝟙 A) :
    rd K (𝟙 _) h = 𝟙 K := by
  simp only [rd, Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, modulePair_fiber, modulePair_base, fib_mapId_inv_app,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp]
  exact (Scheme.Modules.pullbackId A).inv_hom_id_app K

def theta : M ⊗ N ⟶ M ⊗ N :=
  ((Scheme.Modules.pullbackId A).inv.app M ⊗ₘ (Scheme.Modules.pullbackId A).inv.app N) ≫
    (Scheme.Modules.pullbackTensorObjIso (𝟙 A) M N).inv ≫ (Scheme.Modules.pullbackId A).hom.app (M ⊗ N)

theorem rd_tens (u : modulePair (A := A) M ⟶ modulePair (A := A) M) (v : modulePair (A := A) N ⟶ modulePair (A := A) N)
    (hv : v.base = u.base) (h : u.base = 𝟙 A) :
    rd (M ⊗ N) (tens M N u.base u v rfl hv) h = (rd M u h ⊗ₘ rd N v (hv.trans h)) ≫ theta M N := by
  obtain ⟨bu, φ⟩ := u
  obtain ⟨bv, ψ⟩ := v
  change bv = bu at hv
  change bu = 𝟙 A at h
  subst h
  subst hv
  simp only [rd, tens, tensFiber, theta, Pseudofunctor.CoGrothendieck.homMk_fiber, Scheme.Modules.pullbackCongr, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.assoc]
  repeat (erw [Category.id_comp])
  repeat (erw [Category.comp_id])
  try (rw [tensorHom_comp_tensorHom_assoc]; simp only [Category.assoc, Iso.hom_inv_id_app])
  repeat (erw [Category.comp_id])

theorem theta_eq_id : theta M N = 𝟙 (M ⊗ N) := by
  have h1 : rd (M ⊗ N) (tens M N (𝟙 A) (𝟙 (modulePair (A := A) M)) (𝟙 (modulePair (A := A) N)) rfl rfl) rfl =
      (rd M (𝟙 _) rfl ⊗ₘ rd N (𝟙 _) rfl) ≫ theta M N :=
    rd_tens M N (𝟙 _) (𝟙 _) rfl rfl
  rw [rd_id, rd_id, id_tensorHom_id, Category.id_comp, rd_congr (M ⊗ N) (tens_id M N) rfl rfl, rd_id] at h1
  exact h1.symm

end core

section thetaGroup
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
variable (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M N : A.Modules)

def fiberProd : Subgroup (thetaGroup f L hc M × thetaGroup f L hc N) :=
  ((thetaGroup.pt f L hc M).comp (MonoidHom.fst _ _)).eqLocus ((thetaGroup.pt f L hc N).comp (MonoidHom.snd _ _))

theorem mem_fiberProd (p : thetaGroup f L hc M × thetaGroup f L hc N) :
    p ∈ fiberProd f L hc M N ↔ thetaGroup.pt f L hc M p.1 = thetaGroup.pt f L hc N p.2 := Iff.rfl

theorem base_eq_base (g : thetaGroup f L hc M) (h : thetaGroup f L hc N)
    (e : thetaGroup.pt f L hc M g = thetaGroup.pt f L hc N h) : h.1.1.hom.base = g.1.1.hom.base := by
  have e' : h.1.2 = g.1.2 := by simpa only [thetaGroup.pt_apply] using e.symm
  rw [thetaGroup.base_eq f L hc N h, thetaGroup.base_eq f L hc M g, e']

def tau (p : fiberProd f L hc M N) : thetaGroup f L hc (M ⊗ N) :=
  ⟨(tensAut M N p.1.1.1.1 p.1.2.1.1 (base_eq_base f L hc M N p.1.1 p.1.2 p.2), p.1.1.1.2), p.1.1.2⟩

theorem tau_mul (p q : fiberProd f L hc M N) : tau f L hc M N (p * q) = tau f L hc M N p * tau f L hc M N q :=
  Subtype.ext (Prod.ext (tensAut_mul M N p.1.1.1.1 q.1.1.1.1 p.1.2.1.1 q.1.2.1.1 _ _ _) rfl)

def tauHom : fiberProd f L hc M N →* thetaGroup f L hc (M ⊗ N) :=
  MonoidHom.mk' (tau f L hc M N) (tau_mul f L hc M N)

theorem pt_tau (p : fiberProd f L hc M N) :
    thetaGroup.pt f L hc (M ⊗ N) (tau f L hc M N p) = thetaGroup.pt f L hc M p.1.1 := rfl

theorem pt_tau' (p : fiberProd f L hc M N) :
    thetaGroup.pt f L hc (M ⊗ N) (tau f L hc M N p) = thetaGroup.pt f L hc N p.1.2 := p.2

theorem isScalarElt_tau (p : fiberProd f L hc M N) (c d : k)
    (hg : thetaGroup.IsScalarElt f L hc M p.1.1 c) (hh : thetaGroup.IsScalarElt f L hc N p.1.2 d) :
    thetaGroup.IsScalarElt f L hc (M ⊗ N) (tau f L hc M N p) (c * d) := by
  obtain ⟨hpt, hσ⟩ := hg
  obtain ⟨hpt', hτ⟩ := hh
  refine ⟨hpt, ?_⟩
  have hB := thetaGroup.base_eq_id_of_pt_eq_one f L hc M p.1.1 hpt
  have hB' := thetaGroup.base_eq_id_of_pt_eq_one f L hc N p.1.2 hpt'
  have key : thetaGroup.unitReading (M ⊗ N)
      (thetaGroup.base_eq_id_of_pt_eq_one f L hc (M ⊗ N) (tau f L hc M N p) hpt) =
      thetaGroup.unitReading M hB ⊗ₘ thetaGroup.unitReading N hB' := by
    change rd (M ⊗ N) (tens M N p.1.1.1.1.hom.base p.1.1.1.1.hom p.1.2.1.1.hom rfl
      (base_eq_base f L hc M N p.1.1 p.1.2 p.2)) hB = rd M p.1.1.1.1.hom hB ⊗ₘ rd N p.1.2.1.1.hom hB'
    rw [rd_tens, theta_eq_id, Category.comp_id]
  rw [key]
  exact AlgebraicGeometry.RiemannForm.isConstScalar_tensorHom k f _ _ c d hσ hτ

end thetaGroup
end TgTens
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul.TgTens"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul.TgTens"

theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M₁ M₂ : A.Modules) :
    ∃ τ : MonoidHom.eqLocus
          ((thetaGroup.pt f L hc M₁).comp (MonoidHom.fst (thetaGroup f L hc M₁) (thetaGroup f L hc M₂)))
          ((thetaGroup.pt f L hc M₂).comp (MonoidHom.snd (thetaGroup f L hc M₁) (thetaGroup f L hc M₂))) →*
        thetaGroup f L hc (M₁ ⊗ M₂),
      (∀ p, thetaGroup.pt f L hc (M₁ ⊗ M₂) (τ p) = thetaGroup.pt f L hc M₁ p.1.1) ∧
      (∀ p (c₁ c₂ : k), thetaGroup.IsScalarElt f L hc M₁ p.1.1 c₁ → thetaGroup.IsScalarElt f L hc M₂ p.1.2 c₂ →
        thetaGroup.IsScalarElt f L hc (M₁ ⊗ M₂) (τ p) (c₁ * c₂)) :=
  ⟨TgTens.tauHom f L hc M₁ M₂, TgTens.pt_tau f L hc M₁ M₂, TgTens.isScalarElt_tau f L hc M₁ M₂⟩

end S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul (solution)
