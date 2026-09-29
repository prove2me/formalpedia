-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1dcda75e-b259-5c28-9187-800754954301

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace RFFunct29
namespace Geom

variable {k : Type} [Field k] {A B : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of k)} {g : B ⟶ Spec (CommRingCat.of k)}

theorem val_comp_schemeNsmul (L : RelativeGroupLaw k f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t f) (n : ℕ) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul t n x).1 := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint : SchemeHomOver f f) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  exact congrArg Subtype.val h

section Hom

variable (L : RelativeGroupLaw k f) (LB : RelativeGroupLaw k g) (φ : A ⟶ B) (hφ : φ ≫ g = f)
  (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
    CerednikDrinfeld.QM.mapPt φ hφ (L.mul t P Q) =
      LB.mul t (CerednikDrinfeld.QM.mapPt φ hφ P) (CerednikDrinfeld.QM.mapPt φ hφ Q))

include hφhom in

theorem mapPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) :
    CerednikDrinfeld.QM.mapPt φ hφ (L.one t) = LB.one t := by
  set a := CerednikDrinfeld.QM.mapPt φ hφ (L.one t) with ha
  have h : a = LB.mul t a a := by
    have := hφhom t (L.one t) (L.one t)
    rwa [L.one_mul] at this
  calc a = LB.mul t (LB.one t) a := (LB.one_mul t a).symm
    _ = LB.mul t (LB.mul t (LB.inv t a) a) a := by rw [LB.inv_mul_cancel]
    _ = LB.mul t (LB.inv t a) (LB.mul t a a) := LB.mul_assoc t _ _ _
    _ = LB.mul t (LB.inv t a) a := by rw [← h]
    _ = LB.one t := LB.inv_mul_cancel t a

include hφhom in

theorem mapPt_nsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (x : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt φ hφ (L.nsmul t n x) = LB.nsmul t n (CerednikDrinfeld.QM.mapPt φ hφ x) := by
  induction n with
  | zero => exact mapPt_one L LB φ hφ hφhom t
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hφhom, ih]

include hφhom in

theorem schemeNsmul_comp_eq_comp_schemeNsmul (n : ℕ) :
    L.schemeNsmul n ≫ φ = φ ≫ LB.schemeNsmul n := by
  have h1 : L.schemeNsmul n ≫ φ =
      (CerednikDrinfeld.QM.mapPt φ hφ (L.nsmul f n (RelativeGroupLaw.idPoint : SchemeHomOver f f))).1 := rfl
  have h2 : CerednikDrinfeld.QM.mapPt φ hφ (RelativeGroupLaw.idPoint : SchemeHomOver f f) = (⟨φ, hφ⟩ : SchemeHomOver f g) :=
    Subtype.ext (Category.id_comp _)
  rw [h1, mapPt_nsmul L LB φ hφ hφhom, h2, val_comp_schemeNsmul LB f ⟨φ, hφ⟩ n]

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

end Hom

theorem translation_comp_schemeNsmul (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (P : L.AlgPoints hc k) (n : ℕ) (hP : n • P = 0) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n :=
  AlgebraicGeometry.RiemannForm.translation_comp_schemeNsmul_of_nsmul_eq_zero k f L hc P n hP

theorem translation_toPoint_comp_eq_comp_translation (L : RelativeGroupLaw k f) (LB : RelativeGroupLaw k g)
    (φ : A ⟶ B) (hφ : φ ≫ g = f)
    (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      CerednikDrinfeld.QM.mapPt φ hφ (L.mul t P Q) =
        LB.mul t (CerednikDrinfeld.QM.mapPt φ hφ P) (CerednikDrinfeld.QM.mapPt φ hφ Q))
    (hc : L.IsCommutative) (P : L.AlgPoints hc k) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ φ =
      φ ≫ translation g LB (CerednikDrinfeld.QM.mapPt φ hφ (RelativeGroupLaw.AlgPoints.toPoint P)) :=
  translation_comp_eq_comp_translation L LB φ hφ hφhom _

section CardFrame

variable (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (LB : RelativeGroupLaw k g) (φ : A ⟶ B) (hφ : φ ≫ g = f)
  (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
    CerednikDrinfeld.QM.mapPt φ hφ (L.mul t P Q) =
      LB.mul t (CerednikDrinfeld.QM.mapPt φ hφ P) (CerednikDrinfeld.QM.mapPt φ hφ Q))

theorem hxA (n : ℕ) (P : L.AlgPoints hc k) (hP : n • P = 0) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n :=
  AlgebraicGeometry.RiemannForm.translation_comp_schemeNsmul_of_nsmul_eq_zero k f L hc P n hP

include hφhom in

theorem nsmul_comm (n : ℕ) : L.schemeNsmul n ≫ φ = φ ≫ LB.schemeNsmul n :=
  schemeNsmul_comp_eq_comp_schemeNsmul L LB φ hφ hφhom n

include hφhom in

theorem translation_comm (P : L.AlgPoints hc k) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ φ =
      φ ≫ translation g LB (CerednikDrinfeld.QM.mapPt φ hφ (RelativeGroupLaw.AlgPoints.toPoint P)) :=
  translation_comp_eq_comp_translation L LB φ hφ hφhom _

end CardFrame

end RFFunct29.Geom

noncomputable section

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

end ConstPullback

namespace RFFunct29
namespace Mod

open ConstPullback

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

theorem isConstScalar_conj {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) {M N : A.Modules} (e : M ≅ N)
    {σ : N ⟶ N} {c : k} (hσ : IsConstScalar f σ c) : IsConstScalar f (e.hom ≫ σ ≫ e.inv) c := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change e.inv.app U (σ.app U (e.hom.app U s)) = _
  rw [hσ U, Scheme.Modules.Hom.app_smul]
  change _ • (e.hom.app U ≫ e.inv.app U) s = _ • s
  rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

def D {X Y Z : Scheme.{0}} (u : X ⟶ Y) (v : Y ⟶ Z) (w : X ⟶ Z) (h : u ≫ v = w) :
    Scheme.Modules.pullback v ⋙ Scheme.Modules.pullback u ≅ Scheme.Modules.pullback w :=
  Scheme.Modules.pullbackComp u v ≪≫ Scheme.Modules.pullbackCongr h

theorem assoc_app {W X Y Z : Scheme.{0}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M =
      (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M := by
  have := congrArg (fun τ => NatTrans.app τ M) (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app] at this
  erw [Category.id_comp] at this
  exact this

theorem D_assoc {W X Y Z : Scheme.{0}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (h1 : fg ≫ h = fgh) (M : Z.Modules) :
    (Scheme.Modules.pullback f).map ((D g h gh hgh).hom.app M) ≫
      (D f gh fgh (by rw [← hgh, ← Category.assoc, hfg, h1])).hom.app M =
      (D f g fg hfg).hom.app ((Scheme.Modules.pullback h).obj M) ≫ (D fg h fgh h1).hom.app M := by
  subst hfg hgh h1
  simp only [D, Iso.trans_hom, NatTrans.comp_app, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, Functor.map_comp]
  have := assoc_app f g h M
  simp only [Scheme.Modules.pullbackCongr] at this
  rw [← this]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

def sq {X Y Y' Z : Scheme.{0}} {u : X ⟶ Y} {v : Y ⟶ Z} {u' : X ⟶ Y'} {v' : Y' ⟶ Z} (h : u ≫ v = u' ≫ v') :
    Scheme.Modules.pullback v ⋙ Scheme.Modules.pullback u ≅ Scheme.Modules.pullback v' ⋙ Scheme.Modules.pullback u' :=
  Scheme.Modules.pullbackComp u v ≪≫ Scheme.Modules.pullbackCongr h ≪≫ (Scheme.Modules.pullbackComp u' v').symm

def tr {X Y : Scheme.{0}} {T : X ⟶ X} {w : X ⟶ Y} (h : T ≫ w = w) :
    Scheme.Modules.pullback w ⋙ Scheme.Modules.pullback T ≅ Scheme.Modules.pullback w :=
  Scheme.Modules.pullbackComp T w ≪≫ Scheme.Modules.pullbackCongr h

theorem tr_eq_D {X Y : Scheme.{0}} {T : X ⟶ X} {w : X ⟶ Y} (h : T ≫ w = w) : tr h = D T w w h := rfl

theorem sq_hom_app {X Y Y' Z : Scheme.{0}} {u : X ⟶ Y} {v : Y ⟶ Z} {u' : X ⟶ Y'} {v' : Y' ⟶ Z} (h : u ≫ v = u' ≫ v')
    (M : Z.Modules) :
    (sq h).hom.app M = (D u v (u' ≫ v') h).hom.app M ≫ (D u' v' (u' ≫ v') rfl).inv.app M := by
  simp [sq, D, Scheme.Modules.pullbackCongr]

theorem sq_inv_app {X Y Y' Z : Scheme.{0}} {u : X ⟶ Y} {v : Y ⟶ Z} {u' : X ⟶ Y'} {v' : Y' ⟶ Z} (h : u ≫ v = u' ≫ v')
    (M : Z.Modules) :
    (sq h).inv.app M = (D u' v' (u' ≫ v') rfl).hom.app M ≫ (D u v (u' ≫ v') h).inv.app M := by
  simp [sq, D, Scheme.Modules.pullbackCongr]

theorem tr_app_pullback {A B : Scheme.{0}} {TA nA : A ⟶ A} {TB nB : B ⟶ B} {φ : A ⟶ B}
    (hA : TA ≫ nA = nA) (hB : TB ≫ nB = nB) (sN : nA ≫ φ = φ ≫ nB) (sT : TA ≫ φ = φ ≫ TB) (N : B.Modules) :
    (tr hA).app ((Scheme.Modules.pullback φ).obj N) =
      (Scheme.Modules.pullback TA).mapIso ((sq sN).app N) ≪≫ (sq sT).app ((Scheme.Modules.pullback nB).obj N) ≪≫
        (Scheme.Modules.pullback φ).mapIso ((tr hB).app N) ≪≫ ((sq sN).app N).symm := by
  have h1 : (φ ≫ TB) ≫ nB = φ ≫ nB := by rw [Category.assoc, hB]
  have I := D_assoc TA nA φ nA (φ ≫ nB) (φ ≫ nB) hA sN sN N
  have II := D_assoc TA φ nB (φ ≫ TB) (φ ≫ nB) (φ ≫ nB) sT rfl h1 N
  have III := D_assoc φ TB nB (φ ≫ TB) nB (φ ≫ nB) rfl hB h1 N
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, tr_eq_D, sq_hom_app, sq_inv_app,
    Functor.map_comp]
  dsimp only [Functor.comp_obj] at I II III ⊢
  simp only [Category.assoc]

  have k1 : ∀ {Z : A.Modules} (t : (Scheme.Modules.pullback (φ ≫ TB)).obj ((Scheme.Modules.pullback nB).obj N) ⟶ Z),
      (D φ TB (φ ≫ TB) rfl).inv.app ((Scheme.Modules.pullback nB).obj N) ≫
        (D φ TB (φ ≫ TB) rfl).hom.app ((Scheme.Modules.pullback nB).obj N) ≫ t = t :=
    fun t => Iso.inv_hom_id_app_assoc _ _ t
  have k2 : ∀ {Z : A.Modules} (t : (Scheme.Modules.pullback TA).obj ((Scheme.Modules.pullback (φ ≫ nB)).obj N) ⟶ Z),
      (Scheme.Modules.pullback TA).map ((D φ nB (φ ≫ nB) rfl).inv.app N) ≫
        (Scheme.Modules.pullback TA).map ((D φ nB (φ ≫ nB) rfl).hom.app N) ≫ t = t := by
    intro Z t
    rw [← Functor.map_comp_assoc]
    erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have k3 : (D nA φ (φ ≫ nB) sN).hom.app N ≫ (D nA φ (φ ≫ nB) sN).inv.app N = 𝟙 _ := Iso.hom_inv_id_app _ _
  dsimp only [Functor.comp_obj] at k1 k2 k3
  rw [reassoc_of% III, k1, ← reassoc_of% II, k2, reassoc_of% I, k3]
  erw [Category.comp_id]

theorem transportIso_eq {X : Scheme.{0}} {T w : X ⟶ X} (h : T ≫ w = w) (M : X.Modules) :
    transportIso (T := T) (g := w) h M = (tr h).app M := rfl

theorem tr_hom_app_pullback {A B : Scheme.{0}} {TA nA : A ⟶ A} {TB nB : B ⟶ B} {φ : A ⟶ B}
    (hA : TA ≫ nA = nA) (hB : TB ≫ nB = nB) (sN : nA ≫ φ = φ ≫ nB) (sT : TA ≫ φ = φ ≫ TB) (N : B.Modules) :
    (tr hA).hom.app ((Scheme.Modules.pullback φ).obj N) =
      (Scheme.Modules.pullback TA).map ((sq sN).hom.app N) ≫ (sq sT).hom.app ((Scheme.Modules.pullback nB).obj N) ≫
        (Scheme.Modules.pullback φ).map ((tr hB).hom.app N) ≫ (sq sN).inv.app N := by
  have := congrArg Iso.hom (tr_app_pullback hA hB sN sT N)
  simpa only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv] using this

theorem tr_inv_app_pullback {A B : Scheme.{0}} {TA nA : A ⟶ A} {TB nB : B ⟶ B} {φ : A ⟶ B}
    (hA : TA ≫ nA = nA) (hB : TB ≫ nB = nB) (sN : nA ≫ φ = φ ≫ nB) (sT : TA ≫ φ = φ ≫ TB) (N : B.Modules) :
    (tr hA).inv.app ((Scheme.Modules.pullback φ).obj N) =
      (sq sN).hom.app N ≫ (Scheme.Modules.pullback φ).map ((tr hB).inv.app N) ≫
        (sq sT).inv.app ((Scheme.Modules.pullback nB).obj N) ≫ (Scheme.Modules.pullback TA).map ((sq sN).inv.app N) := by
  have := congrArg Iso.inv (tr_app_pullback hA hB sN sT N)
  simpa only [Iso.app_inv, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_hom, Category.assoc] using this

end RFFunct29.Mod

namespace LevelAdjoint29

p2m_open "P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback.RFFunct29.Mod CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal"

variable {k : Type} [Field k] {A : Scheme.{0}}

def sig {T F : A ⟶ A} (hx : T ≫ F = F) {M M₀ : A.Modules}
    (β : (Scheme.Modules.pullback F).obj M ≅ (Scheme.Modules.pullback F).obj M₀) :
    (Scheme.Modules.pullback F).obj M₀ ≅ (Scheme.Modules.pullback F).obj M₀ :=
  β.symm ≪≫ (transportIso hx M).symm ≪≫ (Scheme.Modules.pullback T).mapIso β ≪≫ transportIso hx M₀

theorem sig_hom {T F : A ⟶ A} (hx : T ≫ F = F) {M M₀ : A.Modules}
    (β : (Scheme.Modules.pullback F).obj M ≅ (Scheme.Modules.pullback F).obj M₀) :
    (sig hx β).hom = β.inv ≫ (tr hx).inv.app M ≫ (Scheme.Modules.pullback T).map β.hom ≫ (tr hx).hom.app M₀ := by
  simp [sig, transportIso_eq]

theorem sig_conj_hom {T F : A ⟶ A} (hx : T ≫ F = F) {M M₀ M' M₀' : A.Modules}
    (β : (Scheme.Modules.pullback F).obj M ≅ (Scheme.Modules.pullback F).obj M₀) (γ : M' ≅ M) (γ₀ : M₀' ≅ M₀) :
    (sig hx ((Scheme.Modules.pullback F).mapIso γ ≪≫ β ≪≫ (Scheme.Modules.pullback F).mapIso γ₀.symm)).hom =
      (Scheme.Modules.pullback F).map γ₀.hom ≫ (sig hx β).hom ≫ (Scheme.Modules.pullback F).map γ₀.inv := by
  have n1 := (tr hx).inv.naturality γ.inv
  have n2 := (tr hx).hom.naturality γ₀.inv
  dsimp only [Functor.comp_obj, Functor.comp_map] at n1 n2
  simp only [sig_hom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj]
  try simp only [Category.assoc]
  rw [reassoc_of% n1, n2]
  have c : ∀ {Z' : A.Modules} (t : _ ⟶ Z'),
      (Scheme.Modules.pullback T).map ((Scheme.Modules.pullback F).map γ.inv) ≫
        (Scheme.Modules.pullback T).map ((Scheme.Modules.pullback F).map γ.hom) ≫ t = t := by
    intro Z' t
    rw [← Functor.map_comp_assoc, ← Functor.map_comp, γ.inv_hom_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [c]

theorem isConstScalar_sig_conj (f : A ⟶ Spec (CommRingCat.of k)) {T F : A ⟶ A} (hx : T ≫ F = F)
    {M M₀ M' M₀' : A.Modules}
    (β : (Scheme.Modules.pullback F).obj M ≅ (Scheme.Modules.pullback F).obj M₀) (γ : M' ≅ M) (γ₀ : M₀' ≅ M₀)
    {c : k} (h : IsConstScalar f (sig hx β).hom c) :
    IsConstScalar f (sig hx ((Scheme.Modules.pullback F).mapIso γ ≪≫ β ≪≫ (Scheme.Modules.pullback F).mapIso γ₀.symm)).hom c := by
  rw [sig_conj_hom]
  exact isConstScalar_conj f ((Scheme.Modules.pullback F).mapIso γ₀) h

theorem sig_pullback_hom {B : Scheme.{0}} (ψ : A ⟶ B) {TA nA : A ⟶ A} {TB nB : B ⟶ B}
    (hxA : TA ≫ nA = nA) (hxB : TB ≫ nB = nB) (sN : nA ≫ ψ = ψ ≫ nB) (sT : TA ≫ ψ = ψ ≫ TB)
    {M M₀ : B.Modules} (β : (Scheme.Modules.pullback nB).obj M ≅ (Scheme.Modules.pullback nB).obj M₀) :
    (sig hxA ((sq sN).app M ≪≫ (Scheme.Modules.pullback ψ).mapIso β ≪≫ ((sq sN).app M₀).symm)).hom =
      (sq sN).hom.app M₀ ≫ (Scheme.Modules.pullback ψ).map (sig hxB β).hom ≫ (sq sN).inv.app M₀ := by
  simp only [sig_hom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [tr_inv_app_pullback hxA hxB sN sT M, tr_hom_app_pullback hxA hxB sN sT M₀]
  try simp only [Category.assoc]
  have n3 := (sq sT).hom.naturality β.hom
  dsimp only [Functor.comp_obj, Functor.comp_map] at n3
  have c1 : ∀ {Z' : A.Modules} (t : _ ⟶ Z'),
      (sq sN).inv.app M ≫ (sq sN).hom.app M ≫ t = t := fun t => Iso.inv_hom_id_app_assoc (sq sN) M t
  have c2 : ∀ (X : B.Modules) {Z' : A.Modules} (t : _ ⟶ Z'),
      (Scheme.Modules.pullback TA).map ((sq sN).inv.app X) ≫ (Scheme.Modules.pullback TA).map ((sq sN).hom.app X) ≫ t = t := by
    intro X Z' t
    rw [← Functor.map_comp_assoc]
    erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have c3 : ∀ {Z' : A.Modules} (t : _ ⟶ Z'),
      (sq sT).inv.app ((Scheme.Modules.pullback nB).obj M) ≫ (sq sT).hom.app ((Scheme.Modules.pullback nB).obj M) ≫ t = t :=
    fun t => Iso.inv_hom_id_app_assoc (sq sT) _ t
  dsimp only [Functor.comp_obj] at c1 c2 c3 ⊢
  try simp only [Category.assoc]
  rw [c1, c2 M, c2 M₀, reassoc_of% n3, c3]

theorem isConstScalar_sig_pullback (f : A ⟶ Spec (CommRingCat.of k)) (ψ : A ⟶ A) (hψ : ψ ≫ f = f)
    {TA nA TB nB : A ⟶ A} (hxA : TA ≫ nA = nA) (hxB : TB ≫ nB = nB) (sN : nA ≫ ψ = ψ ≫ nB) (sT : TA ≫ ψ = ψ ≫ TB)
    {M M₀ : A.Modules} (β : (Scheme.Modules.pullback nB).obj M ≅ (Scheme.Modules.pullback nB).obj M₀)
    {c : k} (h : IsConstScalar f (sig hxB β).hom c) :
    IsConstScalar f (sig hxA ((sq sN).app M ≪≫ (Scheme.Modules.pullback ψ).mapIso β ≪≫ ((sq sN).app M₀).symm)).hom c := by
  rw [sig_pullback_hom ψ hxA hxB sN sT β]
  exact isConstScalar_conj f ((sq sN).app M₀) (isConstScalar_pullback f f ψ hψ h)

abbrev dd (F : A ⟶ A) (X Y : A.Modules) := Scheme.Modules.pullbackTensorObjIso F X Y

theorem tr_app_tensor {T F : A ⟶ A} (hx : T ≫ F = F) (X Y : A.Modules) :
    (tr hx).app (X ⊗ Y) =
      (Scheme.Modules.pullback T).mapIso (dd F X Y) ≪≫ dd T _ _ ≪≫ ((tr hx).app X ⊗ᵢ (tr hx).app Y) ≪≫ (dd F X Y).symm := by
  suffices H : ∀ (F' : A ⟶ A) (h : T ≫ F = F'), (D T F F' h).app (X ⊗ Y) =
      (Scheme.Modules.pullback T).mapIso (dd F X Y) ≪≫ dd T _ _ ≪≫ ((D T F F' h).app X ⊗ᵢ (D T F F' h).app Y) ≪≫
        (dd F' X Y).symm from H F hx
  intro F' h
  subst h
  have e : D T F (T ≫ F) rfl = Scheme.Modules.pullbackComp T F := by
    simp [D, Scheme.Modules.pullbackCongr]
  rw [e]
  exact Scheme.Modules.pullbackComp_app_tensorObj T F X Y

theorem tr_hom_app_tensor {T F : A ⟶ A} (hx : T ≫ F = F) (X Y : A.Modules) :
    (tr hx).hom.app (X ⊗ Y) =
      (Scheme.Modules.pullback T).map (dd F X Y).hom ≫ (dd T _ _).hom ≫ ((tr hx).hom.app X ⊗ₘ (tr hx).hom.app Y) ≫
        (dd F X Y).inv := by
  have := congrArg Iso.hom (tr_app_tensor hx X Y)
  simpa only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, tensorIso_hom] using this

theorem tr_inv_app_tensor {T F : A ⟶ A} (hx : T ≫ F = F) (X Y : A.Modules) :
    (tr hx).inv.app (X ⊗ Y) =
      (dd F X Y).hom ≫ ((tr hx).inv.app X ⊗ₘ (tr hx).inv.app Y) ≫ (dd T _ _).inv ≫
        (Scheme.Modules.pullback T).map (dd F X Y).inv := by
  have := congrArg Iso.inv (tr_app_tensor hx X Y)
  simpa only [Iso.app_inv, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, tensorIso_inv, Category.assoc] using this

def tensorBeta (F : A ⟶ A) {M M₀ : A.Modules}
    (β : (Scheme.Modules.pullback F).obj M ≅ (Scheme.Modules.pullback F).obj M₀) (K : A.Modules) :
    (Scheme.Modules.pullback F).obj (M ⊗ K) ≅ (Scheme.Modules.pullback F).obj (M₀ ⊗ K) :=
  dd F M K ≪≫ (β ⊗ᵢ Iso.refl _) ≪≫ (dd F M₀ K).symm

theorem sig_tensor_hom {T F : A ⟶ A} (hx : T ≫ F = F) {M M₀ : A.Modules}
    (β : (Scheme.Modules.pullback F).obj M ≅ (Scheme.Modules.pullback F).obj M₀) (K : A.Modules) :
    (sig hx (tensorBeta F β K)).hom = (dd F M₀ K).hom ≫ ((sig hx β).hom ▷ _) ≫ (dd F M₀ K).inv := by
  simp only [sig_hom, tensorBeta, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, tensorIso_hom,
    tensorIso_inv, Iso.refl_hom, Iso.refl_inv, Functor.map_comp, Category.assoc,
    tr_inv_app_tensor hx M K, tr_hom_app_tensor hx M₀ K]
  dsimp only [Functor.comp_obj]
  try simp only [Category.assoc]
  try simp only [Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]
  have nat : (dd T ((Scheme.Modules.pullback F).obj M) ((Scheme.Modules.pullback F).obj K)).inv ≫
      (Scheme.Modules.pullback T).map (β.hom ⊗ₘ 𝟙 _) ≫
        (dd T ((Scheme.Modules.pullback F).obj M₀) ((Scheme.Modules.pullback F).obj K)).hom =
      ((Scheme.Modules.pullback T).map β.hom ⊗ₘ 𝟙 _) := by
    simp only [dd, Scheme.Modules.pullbackTensorObjIso, Iso.symm_inv, Iso.symm_hom, μIso_hom, μIso_inv]
    rw [← reassoc_of% (μ_natural (Scheme.Modules.pullback T) β.hom
      (𝟙 ((Scheme.Modules.pullback F).obj K)))]
    simp
  erw [reassoc_of% nat]
  simp only [← tensorHom_id]
  simp only [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  erw [Iso.inv_hom_id_app]

theorem isConstScalar_sig_tensor (f : A ⟶ Spec (CommRingCat.of k)) {T F : A ⟶ A} (hx : T ≫ F = F) {M M₀ : A.Modules}
    (β : (Scheme.Modules.pullback F).obj M ≅ (Scheme.Modules.pullback F).obj M₀) (K : A.Modules)
    {c : k} (h : IsConstScalar f (sig hx β).hom c) :
    IsConstScalar f (sig hx (tensorBeta F β K)).hom c := by
  rw [sig_tensor_hom]
  exact isConstScalar_conj f (dd F M₀ K)
    (AlgebraicGeometry.RiemannForm.isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2 k f _ c h _).1

end LevelAdjoint29

p2m_open "P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback.LevelAdjoint29 P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback.RFFunct29.Mod CategoryTheory.MonoidalCategory AlgebraicGeometry.Polarisation CerednikDrinfeld.QM"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ψ : A ⟶ A) (hψ : ψ ≫ f = f)
    (hψhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt ψ hψ (L.mul t P Q) = L.mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))
    (n : ℕ) (hn : (n : k) ≠ 0) (P Q Q' : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (hQ' : n • Q' = 0)
    (hiso : Nonempty
      ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q'))).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛 ≅
        (Scheme.Modules.pullback ψ).obj
          ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛)))
    (c : k)
    (h : IsLevelPairingValue f L 𝓛 n (pushPt ψ hψ (RelativeGroupLaw.AlgPoints.toPoint P)) (RelativeGroupLaw.AlgPoints.toPoint Q) c) :
    IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q') c := by

  have hxP : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n :=
    RFFunct29.Geom.hxA L hc n P hP
  have sN : L.schemeNsmul n ≫ ψ = ψ ≫ L.schemeNsmul n := RFFunct29.Geom.nsmul_comm L L ψ hψ hψhom n
  have sP : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ ψ =
      ψ ≫ translation f L (pushPt ψ hψ (RelativeGroupLaw.AlgPoints.toPoint P)) :=
    RFFunct29.Geom.translation_comm L hc L ψ hψ hψhom P
  obtain ⟨hxB, βB, hσB⟩ := h
  change IsConstScalar f (sig hxB βB).hom c at hσB

  obtain ⟨e⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛).2
  obtain ⟨ι⟩ := hiso

  have h₁ := isConstScalar_sig_tensor f hxB βB (Scheme.Modules.dual 𝓛) hσB

  have h₂ := isConstScalar_sig_conj f hxB (tensorBeta _ βB (Scheme.Modules.dual 𝓛)) (Iso.refl _) e.symm h₁

  have h₃ := isConstScalar_sig_pullback f ψ hψ hxP hxB sN sP _ h₂

  have h₄ := isConstScalar_sig_conj f hxP _ ι (Scheme.Modules.pullbackTensorUnitObjIso ψ).symm h₃

  have h₅ := isConstScalar_sig_tensor f hxP _ 𝓛 h₄

  have h₆ := isConstScalar_sig_conj f hxP _
    ((ρ_ _).symm ≪≫ whiskerLeftIso _ ((β_ (Scheme.Modules.dual 𝓛) 𝓛) ≪≫ e).symm ≪≫ (α_ _ _ _).symm)
    (λ_ 𝓛).symm h₅
  exact ⟨hxP, _, h₆⟩

end
end S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback (solution)
