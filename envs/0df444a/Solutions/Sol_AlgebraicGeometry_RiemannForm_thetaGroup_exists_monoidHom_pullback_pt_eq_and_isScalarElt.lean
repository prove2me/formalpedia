-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_pullback_pt_eq_and_isScalarElt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/db10d8ff-7d3f-591f-bf79-3acbedcae45d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_pullback_pt_eq_and_isScalarElt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

noncomputable section

namespace TgPull
set_option backward.isDefEq.respectTransparency false

section Geom

variable {k : Type} [Field k] {A B : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of k)} {g : B ⟶ Spec (CommRingCat.of k)}
variable (L : RelativeGroupLaw k f) (LB : RelativeGroupLaw k g) (φ : A ⟶ B) (hφ : φ ≫ g = f)
  (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
    CerednikDrinfeld.QM.mapPt φ hφ (L.mul t P Q) =
      LB.mul t (CerednikDrinfeld.QM.mapPt φ hφ P) (CerednikDrinfeld.QM.mapPt φ hφ Q))

include hφhom in
theorem translation_comp_eq_comp_translation (x : Pt f) :
    translation f L x ≫ φ = φ ≫ translation g LB (CerednikDrinfeld.QM.mapPt φ hφ x) := by
  have h1 : translation f L x ≫ φ =
      (CerednikDrinfeld.QM.mapPt φ hφ (L.mul f RelativeGroupLaw.idPoint (constPt f x))).1 := rfl
  have h2 : φ ≫ translation g LB (CerednikDrinfeld.QM.mapPt φ hφ x) =
      (schemeHomOverComp φ hφ (LB.mul g RelativeGroupLaw.idPoint (constPt g (CerednikDrinfeld.QM.mapPt φ hφ x)))).1 := rfl
  rw [h1, h2, hφhom, LB.mul_natural g f φ hφ]
  have e1 : CerednikDrinfeld.QM.mapPt φ hφ (RelativeGroupLaw.idPoint : SchemeHomOver f f) =
      schemeHomOverComp φ hφ (RelativeGroupLaw.idPoint : SchemeHomOver g g) :=
    Subtype.ext (by simp)
  have e2 : CerednikDrinfeld.QM.mapPt φ hφ (constPt f x) =
      schemeHomOverComp φ hφ (constPt g (CerednikDrinfeld.QM.mapPt φ hφ x)) := by
    apply Subtype.ext
    show (f ≫ x.1) ≫ φ = φ ≫ (g ≫ (x.1 ≫ φ))
    rw [← Category.assoc φ g, hφ, Category.assoc]
  rw [e1, e2]

end Geom

namespace ConstPullback

open Opposite

variable {X : Scheme.{0}}

def res (r : Γ(X, ⊤)) (U : (X.Opens)ᵒᵖ) : ↑(X.ringCatSheaf.obj.obj U) :=
  (X.ringCatSheaf.obj.map (homOfLE (le_top (a := U.unop))).op) (show ↑(X.ringCatSheaf.obj.obj (op ⊤)) from r)

theorem res_map (r : Γ(X, ⊤)) {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V) :
    X.ringCatSheaf.obj.map i (res r U) = res r V := by
  change (X.ringCatSheaf.obj.map (homOfLE (le_top (a := U.unop))).op ≫ X.ringCatSheaf.obj.map i) _ = _
  rw [← Functor.map_comp]
  rfl

theorem res_comm (r : Γ(X, ⊤)) (U : (X.Opens)ᵒᵖ) (a : ↑(X.ringCatSheaf.obj.obj U)) :
    res r U * a = a * res r U := by
  change (res r U : Γ(X, U.unop)) * (a : Γ(X, U.unop)) = (a : Γ(X, U.unop)) * (res r U : Γ(X, U.unop))
  exact @mul_comm Γ(X, U.unop) _ _ _

def homothety (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun s => (res r U) • s
          map_add' := fun a b => smul_add _ a b
          map_smul' := fun a s => by
            change res r U • (a • s) = a • (res r U • s)
            rw [smul_smul, smul_smul, res_comm] }
     naturality := fun {U V} i => by
        ext s
        change res r V • (M.val.map i s) = M.val.map i (res r U • s)
        rw [PresheafOfModules.map_smul, res_map] }⟩

def res' (r : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) := X.presheaf.map (homOfLE (le_top (a := U))).op r

theorem homothety_app (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (s : Γ(M, U)) :
    (homothety M r).app U s = res' r U • s := rfl

theorem homothety_comm {M N : X.Modules} (φ : M ⟶ N) (r : Γ(X, ⊤)) :
    φ ≫ homothety N r = homothety M r ≫ φ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change (homothety N r).app U (φ.app U s) = φ.app U ((homothety M r).app U s)
  rw [homothety_app, homothety_app, Scheme.Modules.Hom.app_smul]

variable {Y : Scheme.{0}} (g : X ⟶ Y)

theorem app_res' (r : Γ(Y, ⊤)) (U : Y.Opens) : g.app U (res' r U) = res' (g.appTop r) (g ⁻¹ᵁ U) := by
  change (Y.presheaf.map (homOfLE (le_top (a := U))).op ≫ g.app U) r = (g.appTop ≫ X.presheaf.map _) r
  rw [Scheme.Hom.naturality]
  rfl

theorem pushforward_map_homothety (N : X.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pushforward g).map (homothety N (g.appTop r)) =
      homothety ((Scheme.Modules.pushforward g).obj N) r := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  rw [Scheme.Modules.pushforward_map_app]
  change res' (g.appTop r) (g ⁻¹ᵁ U) • (show Γ(N, g ⁻¹ᵁ U) from s) =
    (homothety ((Scheme.Modules.pushforward g).obj N) r).app U s
  rw [← app_res']
  rfl

theorem pullback_map_homothety (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback g).map (homothety M r) =
      homothety ((Scheme.Modules.pullback g).obj M) (g.appTop r) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, pushforward_map_homothety]
  have h1 := adj.unit.naturality (homothety M r)
  dsimp at h1 ⊢
  rw [← h1]
  exact (homothety_comm (adj.unit.app M) r).symm

variable {k : Type} [Field k]

theorem isConstScalar_pullback {A B : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (g : B ⟶ Spec (CommRingCat.of k))
    (φ : A ⟶ B) (hφ : φ ≫ g = f) {M : B.Modules} {σ : M ⟶ M} {c : k} (hσ : IsConstScalar g σ c) :
    IsConstScalar f ((Scheme.Modules.pullback φ).map σ) c := by
  set r : Γ(B, ⊤) := g.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) with hr
  have hσeq : σ = homothety M r := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext s
    exact hσ U s
  have hgr : φ.appTop r = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
    change (g.appTop ≫ φ.appTop) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) = _
    rw [← Scheme.Hom.comp_appTop, hφ]
  rw [hσeq, pullback_map_homothety, hgr]
  intro U s
  exact homothety_app _ _ U s

end ConstPullback

section Core

variable {A B : Scheme.{0}} (φ : A ⟶ B) (M : B.Modules)

theorem fib_mapComp_inv_app {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (N : Z.Modules) :
    (Scheme.Modules.fibration.mapComp b.op.toLoc a.op.toLoc).inv.toNatTrans.app N =
      (Scheme.Modules.pullbackComp a b).hom.app N := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]
  rfl

theorem fib_mapId_inv_app {X : Scheme.{0}} (N : X.Modules) :
    (Scheme.Modules.fibration.mapId ⟨Opposite.op X⟩).inv.toNatTrans.app N = (Scheme.Modules.pullbackId X).inv.app N := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]

def PhiT : modulePair (A := A) ((Scheme.Modules.pullback φ).obj M) ⟶ modulePair (A := B) M :=
  Pseudofunctor.CoGrothendieck.homMk φ (𝟙 ((Scheme.Modules.pullback φ).obj M))

@[scoped simp] theorem PhiT_base : (PhiT φ M).base = φ := rfl
@[scoped simp] theorem PhiT_fiber : (PhiT φ M).fiber = 𝟙 ((Scheme.Modules.pullback φ).obj M) := rfl

def plFiber (b : A ⟶ A) (b' : B ⟶ B) (h : b ≫ φ = φ ≫ b') (ψ : M ⟶ (Scheme.Modules.pullback b').obj M) :
    (Scheme.Modules.pullback φ).obj M ⟶ (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback φ).obj M) :=
  (Scheme.Modules.pullback φ).map ψ ≫ (Scheme.Modules.pullbackComp φ b').hom.app M ≫
    (Scheme.Modules.pullbackCongr h).inv.app M ≫ (Scheme.Modules.pullbackComp b φ).inv.app M

def pl (b : A ⟶ A) (v : modulePair (A := B) M ⟶ modulePair (A := B) M) (h : b ≫ φ = φ ≫ v.base) :
    modulePair (A := A) ((Scheme.Modules.pullback φ).obj M) ⟶ modulePair (A := A) ((Scheme.Modules.pullback φ).obj M) :=
  Pseudofunctor.CoGrothendieck.homMk b (plFiber φ M b v.base h v.fiber)

@[scoped simp] theorem pl_base (b : A ⟶ A) (v : modulePair (A := B) M ⟶ modulePair (A := B) M) (h : b ≫ φ = φ ≫ v.base) :
    (pl φ M b v h).base = b := rfl

theorem comp_PhiT_fiber (u : modulePair (A := A) ((Scheme.Modules.pullback φ).obj M) ⟶
    modulePair (A := A) ((Scheme.Modules.pullback φ).obj M)) :
    (u ≫ PhiT φ M).fiber = u.fiber ≫ (Scheme.Modules.pullbackComp u.base φ).hom.app M := by
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber, PhiT_base, PhiT_fiber, modulePair_fiber,
    Scheme.Modules.fibration_map_toFunctor, fib_mapComp_inv_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

theorem PhiT_comp_fiber (v : modulePair (A := B) M ⟶ modulePair (A := B) M) :
    (PhiT φ M ≫ v).fiber = (Scheme.Modules.pullback φ).map v.fiber ≫ (Scheme.Modules.pullbackComp φ v.base).hom.app M := by
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber, PhiT_base, PhiT_fiber, modulePair_fiber,
    Scheme.Modules.fibration_map_toFunctor, fib_mapComp_inv_app, Category.id_comp]

theorem uniq (u u' : modulePair (A := A) ((Scheme.Modules.pullback φ).obj M) ⟶
      modulePair (A := A) ((Scheme.Modules.pullback φ).obj M))
    (hb : u.base = u'.base) (h : u ≫ PhiT φ M = u' ≫ PhiT φ M) : u = u' := by
  obtain ⟨b, ψ⟩ := u
  obtain ⟨b', ψ'⟩ := u'
  change b = b' at hb
  subst hb
  have hc := Pseudofunctor.CoGrothendieck.Hom.congr h
  rw [comp_PhiT_fiber, comp_PhiT_fiber] at hc
  simp only [eqToHom_refl, Category.comp_id] at hc
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  simp only [eqToHom_refl, Category.comp_id]
  exact (cancel_mono ((Scheme.Modules.pullbackComp b φ).hom.app M)).1 hc

set_option maxHeartbeats 6400000 in

theorem pl_sq (b : A ⟶ A) (v : modulePair (A := B) M ⟶ modulePair (A := B) M) (h : b ≫ φ = φ ≫ v.base) :
    pl φ M b v h ≫ PhiT φ M = PhiT φ M ≫ v := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (show b ≫ φ = φ ≫ v.base from h) ?_
  rw [comp_PhiT_fiber, PhiT_comp_fiber]
  simp only [pl, Pseudofunctor.CoGrothendieck.homMk_base, Pseudofunctor.CoGrothendieck.homMk_fiber, plFiber,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Scheme.Modules.pullbackCongr, eqToIso.inv, eqToHom_app]

theorem pl_sq_assoc (b : A ⟶ A) (v : modulePair (A := B) M ⟶ modulePair (A := B) M) (h : b ≫ φ = φ ≫ v.base)
    {Z : Pseudofunctor.CoGrothendieck Scheme.Modules.fibration} (w : modulePair (A := B) M ⟶ Z) :
    pl φ M b v h ≫ PhiT φ M ≫ w = PhiT φ M ≫ v ≫ w := by
  rw [← Category.assoc, pl_sq, Category.assoc]

end Core

section AutLevel

variable {A B : Scheme.{0}} (φ : A ⟶ B) (M : B.Modules)

def plAut (e : A ≅ A) (a : Aut (modulePair (A := B) M)) (h : e.hom ≫ φ = φ ≫ a.hom.base)
    (h' : e.inv ≫ φ = φ ≫ a.inv.base) : Aut (modulePair (A := A) ((Scheme.Modules.pullback φ).obj M)) where
  hom := pl φ M e.hom a.hom h
  inv := pl φ M e.inv a.inv h'
  hom_inv_id := by
    apply uniq φ M
    · exact e.hom_inv_id
    · simp only [Category.assoc, pl_sq, pl_sq_assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply uniq φ M
    · exact e.inv_hom_id
    · simp only [Category.assoc, pl_sq, pl_sq_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

theorem plAut_hom (e : A ≅ A) (a : Aut (modulePair (A := B) M)) (h : e.hom ≫ φ = φ ≫ a.hom.base)
    (h' : e.inv ≫ φ = φ ≫ a.inv.base) : (plAut φ M e a h h').hom = pl φ M e.hom a.hom h := rfl

def rd {X : Scheme.{0}} (N : X.Modules) (u : modulePair (A := X) N ⟶ modulePair (A := X) N) (h : u.base = 𝟙 X) :
    N ⟶ N :=
  u.fiber ≫ (Scheme.Modules.pullbackCongr h).hom.app N ≫ (Scheme.Modules.pullbackId X).hom.app N

theorem rd_congr {X : Scheme.{0}} (N : X.Modules) {u v : modulePair (A := X) N ⟶ modulePair (A := X) N} (e : u = v)
    (h : u.base = 𝟙 X) (h' : v.base = 𝟙 X) : rd N u h = rd N v h' := by
  subst e
  rfl

theorem rd_id {X : Scheme.{0}} (N : X.Modules)
    (h : (𝟙 (modulePair (A := X) N) : modulePair (A := X) N ⟶ modulePair (A := X) N).base = 𝟙 X) :
    rd N (𝟙 _) h = 𝟙 N := by
  simp only [rd, Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, modulePair_fiber, modulePair_base, fib_mapId_inv_app,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp]
  exact (Scheme.Modules.pullbackId X).inv_hom_id_app N

theorem h0 : 𝟙 A ≫ φ = φ ≫ 𝟙 B := by simp

def Theta : (Scheme.Modules.pullback φ).obj M ⟶ (Scheme.Modules.pullback φ).obj M :=
  (Scheme.Modules.pullback φ).map ((Scheme.Modules.pullbackId B).inv.app M) ≫
    (Scheme.Modules.pullbackComp φ (𝟙 B)).hom.app M ≫ (Scheme.Modules.pullbackCongr (h0 φ)).inv.app M ≫
    (Scheme.Modules.pullbackComp (𝟙 A) φ).inv.app M ≫ (Scheme.Modules.pullbackId A).hom.app ((Scheme.Modules.pullback φ).obj M)

theorem rd_pl (b : A ⟶ A) (v : modulePair (A := B) M ⟶ modulePair (A := B) M) (h : b ≫ φ = φ ≫ v.base)
    (hb : b = 𝟙 A) (hv : v.base = 𝟙 B) :
    rd ((Scheme.Modules.pullback φ).obj M) (pl φ M b v h) hb = (Scheme.Modules.pullback φ).map (rd M v hv) ≫ Theta φ M := by
  obtain ⟨bv, ψ⟩ := v
  change bv = 𝟙 B at hv
  subst hv
  subst hb
  have e1 : rd M ⟨𝟙 B, ψ⟩ rfl ≫ (Scheme.Modules.pullbackId B).inv.app M = ψ := by
    simp only [rd, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.assoc,
      Iso.hom_inv_id_app]
    erw [Category.id_comp, Category.comp_id]
  rw [Theta, ← CategoryTheory.Functor.map_comp_assoc, e1]
  simp only [rd, pl, plFiber, Pseudofunctor.CoGrothendieck.homMk_fiber, Category.assoc]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, eqToIso.inv, eqToIso.hom]
  erw [Category.id_comp]

end AutLevel

section Group

variable {k : Type} [Field k] {A B : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (g : B ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (LB : RelativeGroupLaw k g) (hcB : LB.IsCommutative)
  (φ : A ⟶ B) (hφ : φ ≫ g = f)
  (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
    CerednikDrinfeld.QM.mapPt φ hφ (L.mul t P Q) = LB.mul t (CerednikDrinfeld.QM.mapPt φ hφ P) (CerednikDrinfeld.QM.mapPt φ hφ Q))
  (φpt : Multiplicative (L.AlgPoints hc k) →* Multiplicative (LB.AlgPoints hcB k))
  (hφpt : ∀ z : Multiplicative (L.AlgPoints hc k),
    RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (φpt z)) =
      CerednikDrinfeld.QM.mapPt φ hφ (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd z)))
  (M : B.Modules)

abbrev H : Subgroup (thetaGroup g LB hcB M × Multiplicative (L.AlgPoints hc k)) :=
  MonoidHom.eqLocus
    ((thetaGroup.pt g LB hcB M).comp (MonoidHom.fst (thetaGroup g LB hcB M) (Multiplicative (L.AlgPoints hc k))))
    (φpt.comp (MonoidHom.snd (thetaGroup g LB hcB M) (Multiplicative (L.AlgPoints hc k))))

include hφhom hφpt in

theorem base_intertwine (q : thetaGroup g LB hcB M) (x : Multiplicative (L.AlgPoints hc k))
    (hq : thetaGroup.pt g LB hcB M q = φpt x) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd x)) ≫ φ = φ ≫ q.1.1.hom.base := by
  rw [thetaGroup.base_eq g LB hcB M q, ← thetaGroup.pt_apply g LB hcB M q, hq, hφpt,
    translation_comp_eq_comp_translation L LB φ hφ hφhom]

include hφhom hφpt in
theorem base_intertwine_inv (q : thetaGroup g LB hcB M) (x : Multiplicative (L.AlgPoints hc k))
    (hq : thetaGroup.pt g LB hcB M q = φpt x) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (-Multiplicative.toAdd x)) ≫ φ = φ ≫ q.1.1.inv.base := by
  have := base_intertwine f g L hc LB hcB φ hφ hφhom φpt hφpt M q⁻¹ x⁻¹ (by rw [map_inv, map_inv, hq])
  exact this

def psi (p : H f g L hc LB hcB φpt M) : thetaGroup f L hc ((Scheme.Modules.pullback φ).obj M) :=
  ⟨(plAut φ M (translationIso f L hc (Multiplicative.toAdd p.1.2)) p.1.1.1.1
      (base_intertwine f g L hc LB hcB φ hφ hφhom φpt hφpt M p.1.1 p.1.2 p.2)
      (base_intertwine_inv f g L hc LB hcB φ hφ hφhom φpt hφpt M p.1.1 p.1.2 p.2),
    p.1.2), rfl⟩

theorem psi_hom (p : H f g L hc LB hcB φpt M) :
    (psi f g L hc LB hcB φ hφ hφhom φpt hφpt M p).1.1.hom =
      pl φ M (translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd p.1.2))) p.1.1.1.1.hom
        (base_intertwine f g L hc LB hcB φ hφ hφhom φpt hφpt M p.1.1 p.1.2 p.2) := rfl

theorem psi_mul (p q : H f g L hc LB hcB φpt M) :
    psi f g L hc LB hcB φ hφ hφhom φpt hφpt M (p * q) =
      psi f g L hc LB hcB φ hφ hφhom φpt hφpt M p * psi f g L hc LB hcB φ hφ hφhom φpt hφpt M q := by
  refine Subtype.ext (Prod.ext (Iso.ext ?_) rfl)
  change pl φ M _ (q.1.1.1.1.hom ≫ p.1.1.1.1.hom) _ = pl φ M _ q.1.1.1.1.hom _ ≫ pl φ M _ p.1.1.1.1.hom _
  apply uniq φ M
  · change translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (p.1.2 * q.1.2))) =
      translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd q.1.2)) ≫
        translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd p.1.2))
    rw [toAdd_mul, add_comm, translation_toPoint_add f L hc]
  · simp only [Category.assoc, pl_sq, pl_sq_assoc]

def psiHom : H f g L hc LB hcB φpt M →* thetaGroup f L hc ((Scheme.Modules.pullback φ).obj M) :=
  MonoidHom.mk' (psi f g L hc LB hcB φ hφ hφhom φpt hφpt M) (psi_mul f g L hc LB hcB φ hφ hφhom φpt hφpt M)

theorem pt_psi (p : H f g L hc LB hcB φpt M) :
    thetaGroup.pt f L hc ((Scheme.Modules.pullback φ).obj M) (psi f g L hc LB hcB φ hφ hφhom φpt hφpt M p) = p.1.2 := rfl

include f g L hc LB hcB hφ hφhom φpt hφpt in
theorem theta_eq_id : Theta φ M = 𝟙 _ := by
  have h1 : psi f g L hc LB hcB φ hφ hφhom φpt hφpt M 1 = 1 := map_one (psiHom f g L hc LB hcB φ hφ hφhom φpt hφpt M)
  have hB : translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (1 : H f g L hc LB hcB φpt M).1.2)) = 𝟙 A := by
    rw [show (1 : H f g L hc LB hcB φpt M).1.2 = 1 from rfl, toAdd_one, translation_toPoint_zero]
  have e1 : rd ((Scheme.Modules.pullback φ).obj M) (psi f g L hc LB hcB φ hφ hφhom φpt hφpt M 1).1.1.hom hB = Theta φ M := by
    refine (rd_pl φ M _ _ _ hB rfl).trans ?_
    change (Scheme.Modules.pullback φ).map (rd M (𝟙 (modulePair (A := B) M)) rfl) ≫ Theta φ M = Theta φ M
    rw [rd_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have e2 : rd ((Scheme.Modules.pullback φ).obj M) (psi f g L hc LB hcB φ hφ hφhom φpt hφpt M 1).1.1.hom hB = 𝟙 _ := by
    rw [rd_congr _ (congrArg (fun q => q.1.1.hom) h1) hB rfl]
    exact rd_id _ _
  rw [← e1, e2]

theorem isScalarElt_psi (p : H f g L hc LB hcB φpt M) (c : k)
    (hsc : thetaGroup.IsScalarElt g LB hcB M p.1.1 c) (h1 : p.1.2 = 1) :
    thetaGroup.IsScalarElt f L hc ((Scheme.Modules.pullback φ).obj M) (psi f g L hc LB hcB φ hφ hφhom φpt hφpt M p) c := by
  obtain ⟨hpt, hσ⟩ := hsc
  have hpt' : thetaGroup.pt f L hc ((Scheme.Modules.pullback φ).obj M) (psi f g L hc LB hcB φ hφ hφhom φpt hφpt M p) = 1 := h1
  refine ⟨hpt', ?_⟩
  have hBv := thetaGroup.base_eq_id_of_pt_eq_one g LB hcB M p.1.1 hpt
  have key : thetaGroup.unitReading ((Scheme.Modules.pullback φ).obj M)
      (thetaGroup.base_eq_id_of_pt_eq_one f L hc ((Scheme.Modules.pullback φ).obj M)
        (psi f g L hc LB hcB φ hφ hφhom φpt hφpt M p) hpt') =
      (Scheme.Modules.pullback φ).map (thetaGroup.unitReading M hBv) := by
    change rd ((Scheme.Modules.pullback φ).obj M) (psi f g L hc LB hcB φ hφ hφhom φpt hφpt M p).1.1.hom _ =
      (Scheme.Modules.pullback φ).map (rd M p.1.1.1.1.hom hBv)
    refine (rd_pl φ M _ _ _ _ hBv).trans ?_
    rw [theta_eq_id f g L hc LB hcB φ hφ hφhom φpt hφpt M, Category.comp_id]
  rw [key]
  exact ConstPullback.isConstScalar_pullback f g φ hφ hσ

end Group
end TgPull
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_pullback_pt_eq_and_isScalarElt.TgPull"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_pullback_pt_eq_and_isScalarElt.TgPull"

theorem solution
    (k : Type) [Field k] {A B : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (g : B ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (LB : RelativeGroupLaw k g) (hcB : LB.IsCommutative)
    (φ : A ⟶ B) (hφ : φ ≫ g = f)
    (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      CerednikDrinfeld.QM.mapPt φ hφ (L.mul t P Q) = LB.mul t (CerednikDrinfeld.QM.mapPt φ hφ P) (CerednikDrinfeld.QM.mapPt φ hφ Q))
    (φpt : Multiplicative (L.AlgPoints hc k) →* Multiplicative (LB.AlgPoints hcB k))
    (hφpt : ∀ z : Multiplicative (L.AlgPoints hc k),
      RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (φpt z)) =
        CerednikDrinfeld.QM.mapPt φ hφ (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd z)))
    (M : B.Modules) :
    ∃ Ψ : MonoidHom.eqLocus
          ((thetaGroup.pt g LB hcB M).comp (MonoidHom.fst (thetaGroup g LB hcB M) (Multiplicative (L.AlgPoints hc k))))
          (φpt.comp (MonoidHom.snd (thetaGroup g LB hcB M) (Multiplicative (L.AlgPoints hc k)))) →*
        thetaGroup f L hc ((Scheme.Modules.pullback φ).obj M),
      (∀ p, thetaGroup.pt f L hc ((Scheme.Modules.pullback φ).obj M) (Ψ p) = p.1.2) ∧
      (∀ p (c : k), thetaGroup.IsScalarElt g LB hcB M p.1.1 c → p.1.2 = 1 →
        thetaGroup.IsScalarElt f L hc ((Scheme.Modules.pullback φ).obj M) (Ψ p) c) :=
  ⟨TgPull.psiHom f g L hc LB hcB φ hφ hφhom φpt hφpt M, TgPull.pt_psi f g L hc LB hcB φ hφ hφhom φpt hφpt M,
    TgPull.isScalarElt_psi f g L hc LB hcB φ hφ hφhom φpt hφpt M⟩

end S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_pullback_pt_eq_and_isScalarElt
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_pullback_pt_eq_and_isScalarElt (solution)
