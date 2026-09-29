-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.isLevelPairingValue_mul_of_isLevelPairingValue_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5720a73b-213f-5c6e-be19-f0ce5bca8e7c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_RiemannForm_schemeNsmul_mul_and_translation_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_isLevelPairingValue_nsmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace RFCompatE165
universe u
set_option backward.isDefEq.respectTransparency false

section assoc
variable {X Y Z T' : Scheme.{u}}

theorem assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T') (M : T'.Modules)
    (p : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj M = (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj M) :
    (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M = eqToHom p := by
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at this
  exact this

@[reassoc]
theorem assoc_app₁ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T') (M : T'.Modules)
    (p : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj M = (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj M) :
    (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) =
      eqToHom p ≫ (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M := by
  rw [← assoc_app f g h M p]
  simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

theorem assoc_app₂ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T') (M : T'.Modules)
    (q : (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj M = (Scheme.Modules.pullback (f ≫ g ≫ h)).obj M) :
    (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M ≫
        (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) =
      eqToHom q ≫ (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) := by
  have e := assoc_app f g h M q.symm
  have : eqToHom q ≫ (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) =
      eqToHom q ≫ ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M ≫
        (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  rw [this, e, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end assoc

section congr
variable {X Y Z : Scheme.{u}}

@[reassoc]
theorem congr_left_inv {a b : X ⟶ Y} (hab : a = b) (g : Y ⟶ Z) (M : Z.Modules)
    (pa : (Scheme.Modules.pullback (a ≫ g)).obj M = (Scheme.Modules.pullback (b ≫ g)).obj M)
    (pb : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj M)) :
    (Scheme.Modules.pullbackComp a g).inv.app M ≫ eqToHom pb =
      eqToHom pa ≫ (Scheme.Modules.pullbackComp b g).inv.app M := by
  subst hab
  simp

@[reassoc]
theorem congr_right_hom_inv (a : X ⟶ Y) {g g' : Y ⟶ Z} (hg : g = g') (M : Z.Modules)
    (p1 : (Scheme.Modules.pullback (a ≫ g)).obj M = (Scheme.Modules.pullback (a ≫ g')).obj M)
    (p2 : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g').obj M)) :
    (Scheme.Modules.pullbackComp a g).hom.app M ≫ eqToHom p1 ≫ (Scheme.Modules.pullbackComp a g').inv.app M =
      eqToHom p2 := by
  subst hg
  simp

end congr

section heart
variable {A : Scheme.{0}}

noncomputable def iota (Mm N W : A ⟶ A) (hW : W = Mm ≫ N) (M : A.Modules) :
    (Scheme.Modules.pullback W).obj M ≅ (Scheme.Modules.pullback Mm).obj ((Scheme.Modules.pullback N).obj M) :=
  (Scheme.Modules.pullbackCongr hW).app M ≪≫ ((Scheme.Modules.pullbackComp Mm N).app M).symm

noncomputable def kappa (T T₁ Mm : A ⟶ A) (hT : T ≫ Mm = Mm ≫ T₁) :
    Scheme.Modules.pullback Mm ⋙ Scheme.Modules.pullback T ≅ Scheme.Modules.pullback T₁ ⋙ Scheme.Modules.pullback Mm :=
  Scheme.Modules.pullbackComp T Mm ≪≫ Scheme.Modules.pullbackCongr hT ≪≫ (Scheme.Modules.pullbackComp Mm T₁).symm

theorem heart (T T₁ Mm N W : A ⟶ A) (hW : W = Mm ≫ N) (hT : T ≫ Mm = Mm ≫ T₁)
    (hx₁ : T₁ ≫ N = N) (hx : T ≫ W = W) (M : A.Modules) :
    (iota Mm N W hW M).inv ≫ (transportIso hx M).inv ≫ (Scheme.Modules.pullback T).map (iota Mm N W hW M).hom ≫
        (kappa T T₁ Mm hT).hom.app ((Scheme.Modules.pullback N).obj M) =
      (Scheme.Modules.pullback Mm).map (transportIso hx₁ M).inv := by
  subst hW
  simp only [iota, kappa, transportIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToIso.inv, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.comp_app, NatTrans.id_app, eqToHom_app, eqToHom_map, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [assoc_app₁_assoc T Mm N M (by simp only [Category.assoc])]
  rw [congr_left_inv_assoc hT N M (by rw [hT])]
  rw [assoc_app₂ Mm T₁ N M (by simp only [Category.assoc])]
  simp only [eqToHom_trans_assoc]
  rw [congr_right_hom_inv_assoc Mm hx₁.symm M _ (by rw [hx₁])]

@[reassoc]
theorem heart' (T T₁ Mm N W : A ⟶ A) (hW : W = Mm ≫ N) (hT : T ≫ Mm = Mm ≫ T₁)
    (hx₁ : T₁ ≫ N = N) (hx : T ≫ W = W) (M : A.Modules) :
    (iota Mm N W hW M).inv ≫ (transportIso hx M).inv ≫ (Scheme.Modules.pullback T).map (iota Mm N W hW M).hom =
      (Scheme.Modules.pullback Mm).map (transportIso hx₁ M).inv ≫
        (kappa T T₁ Mm hT).inv.app ((Scheme.Modules.pullback N).obj M) := by
  rw [← heart T T₁ Mm N W hW hT hx₁ hx M]
  simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

theorem heart'' (T T₁ Mm N W : A ⟶ A) (hW : W = Mm ≫ N) (hT : T ≫ Mm = Mm ≫ T₁)
    (hx₁ : T₁ ≫ N = N) (hx : T ≫ W = W) (M : A.Modules) :
    (Scheme.Modules.pullback T).map (iota Mm N W hW M).inv ≫ (transportIso hx M).hom ≫ (iota Mm N W hW M).hom =
      (kappa T T₁ Mm hT).hom.app ((Scheme.Modules.pullback N).obj M) ≫
        (Scheme.Modules.pullback Mm).map (transportIso hx₁ M).hom := by
  let Φ : (Scheme.Modules.pullback Mm).obj ((Scheme.Modules.pullback N).obj M) ≅
      (Scheme.Modules.pullback T).obj ((Scheme.Modules.pullback Mm).obj ((Scheme.Modules.pullback N).obj M)) :=
    (iota Mm N W hW M).symm ≪≫ (transportIso hx M).symm ≪≫ (Scheme.Modules.pullback T).mapIso (iota Mm N W hW M)
  have e : Φ ≪≫ (kappa T T₁ Mm hT).app ((Scheme.Modules.pullback N).obj M) =
      (Scheme.Modules.pullback Mm).mapIso (transportIso hx₁ M).symm := by
    apply Iso.ext
    simp only [Φ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
    exact heart T T₁ Mm N W hW hT hx₁ hx M
  have := congrArg Iso.inv e
  simp only [Φ, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at this
  rw [← this, Iso.hom_inv_id_app_assoc]

@[reassoc]
theorem kappa_conj (T T₁ Mm : A ⟶ A) (hT : T ≫ Mm = Mm ≫ T₁) {X Y : A.Modules} (φ : X ⟶ Y) :
    (kappa T T₁ Mm hT).inv.app X ≫ (Scheme.Modules.pullback T).map ((Scheme.Modules.pullback Mm).map φ) ≫
        (kappa T T₁ Mm hT).hom.app Y =
      (Scheme.Modules.pullback Mm).map ((Scheme.Modules.pullback T₁).map φ) := by
  have h := (kappa T T₁ Mm hT).inv.naturality φ
  simp only [Functor.comp_map] at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id]

noncomputable def betaW (Mm N W : A ⟶ A) (hW : W = Mm ≫ N) {M₀ M₁ : A.Modules}
    (β₁ : (Scheme.Modules.pullback N).obj M₀ ≅ (Scheme.Modules.pullback N).obj M₁) :
    (Scheme.Modules.pullback W).obj M₀ ≅ (Scheme.Modules.pullback W).obj M₁ :=
  iota Mm N W hW M₀ ≪≫ (Scheme.Modules.pullback Mm).mapIso β₁ ≪≫ (iota Mm N W hW M₁).symm

theorem assembly (T T₁ Mm N W : A ⟶ A) (hW : W = Mm ≫ N) (hT : T ≫ Mm = Mm ≫ T₁)
    (hx₁ : T₁ ≫ N = N) (hx : T ≫ W = W) {M₀ M₁ : A.Modules}
    (β₁ : (Scheme.Modules.pullback N).obj M₀ ≅ (Scheme.Modules.pullback N).obj M₁) :
    ((betaW Mm N W hW β₁).symm ≪≫ (transportIso hx M₀).symm ≪≫
        (Scheme.Modules.pullback T).mapIso (betaW Mm N W hW β₁) ≪≫ transportIso hx M₁).hom =
      (iota Mm N W hW M₁).hom ≫
        (Scheme.Modules.pullback Mm).map
          (β₁.symm ≪≫ (transportIso hx₁ M₀).symm ≪≫ (Scheme.Modules.pullback T₁).mapIso β₁ ≪≫ transportIso hx₁ M₁).hom ≫
        (iota Mm N W hW M₁).inv := by
  rw [← cancel_mono (iota Mm N W hW M₁).hom]
  simp only [betaW, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [heart'_assoc T T₁ Mm N W hW hT hx₁ hx M₀, heart'' T T₁ Mm N W hW hT hx₁ hx M₁,
    kappa_conj_assoc T T₁ Mm hT]

end heart

section solution
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

theorem isConstScalar_conj {M N : A.Modules} (e : M ≅ N) {σ : N ⟶ N} {c : k}
    (hσ : IsConstScalar f σ c) : IsConstScalar f (e.hom ≫ σ ≫ e.inv) c := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change e.inv.app U (σ.app U (e.hom.app U s)) = _
  rw [hσ U, Scheme.Modules.Hom.app_smul]
  change _ • (e.hom.app U ≫ e.inv.app U) s = _
  rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

theorem compat (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (𝓛 : A.Modules) (n m : ℕ) (P Q : L.AlgPoints hc k) (c : k)
    (h₁ : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint (m • P)) (RelativeGroupLaw.AlgPoints.toPoint Q) c) :
    IsLevelPairingValue f L 𝓛 (n * m) (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c := by
  obtain ⟨hx₁, β₁, hσ₁⟩ := h₁
  obtain ⟨hW, hT⟩ :=
    AlgebraicGeometry.RiemannForm.schemeNsmul_mul_and_translation_comp_schemeNsmul k f L hc n m P
  have hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul (n * m) = L.schemeNsmul (n * m) := by
    rw [hW, ← Category.assoc, hT, Category.assoc, hx₁]
  refine ⟨hx, betaW (L.schemeNsmul m) (L.schemeNsmul n) (L.schemeNsmul (n * m)) hW β₁, ?_⟩
  rw [assembly _ _ (L.schemeNsmul m) (L.schemeNsmul n) (L.schemeNsmul (n * m)) hW hT hx₁ hx β₁]
  exact isConstScalar_conj f _
    (AlgebraicGeometry.RiemannForm.isConstScalar_pullback_map k f (L.schemeNsmul m) (L.schemeNsmul_over m) hσ₁)

end solution

end RFCompatE165

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (n m : ℕ) (hnm : ((n * m : ℕ) : k) ≠ 0) (P Q : L.AlgPoints hc k) (hP : (n * m) • P = 0) (hQ : n • Q = 0) (c : k)
    (h₁ : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint (m • P)) (RelativeGroupLaw.AlgPoints.toPoint Q) c) :
    IsLevelPairingValue f L 𝓛 (n * m) (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint Q) c := by
  exact RFCompatE165.compat f L hc 𝓛 n m P Q c h₁

end S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_isLevelPairingValue_nsmul
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_isLevelPairingValue_nsmul (solution)
