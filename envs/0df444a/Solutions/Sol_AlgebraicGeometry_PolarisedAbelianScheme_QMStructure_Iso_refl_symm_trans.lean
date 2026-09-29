-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.refl_symm_trans
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/80c18fac-a96e-5f2f-ae06-f3f24376e7b3

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_refl_symm_trans

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

namespace G2QMIso

variable {S : Type} [CommRing S] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (e : A ≅ A') (he : e.hom ≫ f' = f)

include he in
theorem inv_over : e.inv ≫ f = f' := by rw [← he, Iso.inv_hom_id_assoc]

def ePt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f') : SchemeHomOver t f :=
  ⟨P.1 ≫ e.inv, by rw [Category.assoc, inv_over e he]; exact P.2⟩

@[scoped simp] theorem ePt_val {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f') :
    (ePt e he P).1 = P.1 ≫ e.inv := rfl

def hPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨P.1 ≫ e.hom, by rw [Category.assoc, he]; exact P.2⟩

@[scoped simp] theorem hPt_val {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    (hPt e he P).1 = P.1 ≫ e.hom := rfl

@[scoped simp] theorem hPt_ePt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f') :
    hPt e he (ePt e he P) = P := Subtype.ext (by simp)

@[scoped simp] theorem ePt_hPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    ePt e he (hPt e he P) = P := Subtype.ext (by simp)

variable (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f),
      (L.mul t x y).1 ≫ e.hom =
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)

include hmul in
theorem hPt_mul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f) :
    hPt e he (L.mul t x y) = L'.mul t (hPt e he x) (hPt e he y) :=
  Subtype.ext (hmul t x y)

include hmul in

theorem ePt_mul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f') :
    ePt e he (L'.mul t P Q) = L.mul t (ePt e he P) (ePt e he Q) := by
  have h := hPt_mul L L' e he hmul t (ePt e he P) (ePt e he Q)
  rw [hPt_ePt, hPt_ePt] at h
  rw [← h, ePt_hPt]

include hmul in

theorem hPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : hPt e he (L.one t) = L'.one t := by
  letI := L'.pointGroup t
  have h := hPt_mul L L' e he hmul t (L.one t) (L.one t)
  rw [L.one_mul] at h
  have h2 : hPt e he (L.one t) * hPt e he (L.one t) = hPt e he (L.one t) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

include hmul in
theorem ePt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : ePt e he (L'.one t) = L.one t := by
  rw [← hPt_one L L' e he hmul, ePt_hPt]

omit L L' he in

noncomputable def pullbackInvHomIso (P' : A'.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj P') ≅ P' :=
  (Scheme.Modules.pullbackComp e.inv e.hom).app P' ≪≫ (Scheme.Modules.pullbackCongr e.inv_hom_id).app P' ≪≫
    (Scheme.Modules.pullbackId A').app P'

omit L' e he in
theorem mul_val_congr {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) {P P' Q Q' : SchemeHomOver t f}
    (hP : P = P') (hQ : Q = Q') : (L.mul t P Q).1 = (L.mul t P' Q').1 := by subst hP hQ; rfl

omit L L' e he in

theorem locIso_of_iso {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S)) {M M' : X.Modules} (i : M ≅ M') :
    LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso i⟩⟩

end G2QMIso
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_refl_symm_trans.G2QMIso"

open G2QMIso in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ}
    {d m : ℕ} {S : Type} [CommRing S] :
    (∀ (X : PolarisedAbelianScheme 2 d m S) (t : QMStructure Λ star β X), QMStructure.Iso t t) ∧
    (∀ (X Y : PolarisedAbelianScheme 2 d m S) (t : QMStructure Λ star β X) (u : QMStructure Λ star β Y),
      QMStructure.Iso t u → QMStructure.Iso u t) ∧
    (∀ (X Y W : PolarisedAbelianScheme 2 d m S) (t : QMStructure Λ star β X) (u : QMStructure Λ star β Y)
      (w : QMStructure Λ star β W), QMStructure.Iso t u → QMStructure.Iso u w → QMStructure.Iso t w) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    intro X t
    refine ⟨Iso.refl _, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro T s x y
      exact (Category.comp_id _).trans
        (mul_val_congr X.L s (Subtype.ext (Category.comp_id _).symm) (Subtype.ext (Category.comp_id _).symm))
    · intro i; simp
    · exact locIso_of_iso X.f ((Scheme.Modules.pullbackId X.A).app X.pol)
    · intro x; simp
    · simp
  ·
    intro X Y t u h
    obtain ⟨e, he, hmul, hlev, hpol, hact, hP⟩ := h
    have hinv : e.inv ≫ X.f = Y.f := inv_over e he
    refine ⟨e.symm, hinv, ?_, ?_, ?_, ?_, ?_⟩
    · intro T s x y
      exact congrArg Subtype.val (ePt_mul X.L Y.L e he hmul s x y)
    · intro i
      show (Y.P i).1 ≫ e.inv = (X.P i).1
      rw [← hlev i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    ·
      show LocIsoOnBase Y.f ((Scheme.Modules.pullback e.inv).obj X.pol) Y.pol
      have hcomm : e.inv ≫ X.f = Y.f ≫ 𝟙 (Spec (CommRingCat.of S)) := by rw [Category.comp_id, hinv]
      have h2 := LocIsoOnBase.pullback_of_comp_eq Y.f e.inv (𝟙 _) hcomm hpol
      have E := LocIsoOnBase.equivalence Y.f
      exact E.trans (E.symm h2) (locIso_of_iso Y.f (pullbackInvHomIso e Y.pol))
    · intro x
      show u.act x ≫ e.inv = e.inv ≫ t.act x
      rw [(Iso.eq_inv_comp e).mpr (hact x).symm, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · show u.P.1 ≫ e.inv = t.P.1
      rw [← hP, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ·
    intro X Y W t u w h₁ h₂
    obtain ⟨e₁, he₁, hmul₁, hlev₁, hpol₁, hact₁, hP₁⟩ := h₁
    obtain ⟨e₂, he₂, hmul₂, hlev₂, hpol₂, hact₂, hP₂⟩ := h₂
    have he : (e₁ ≪≫ e₂).hom ≫ W.f = X.f := by rw [Iso.trans_hom, Category.assoc, he₂, he₁]
    refine ⟨e₁ ≪≫ e₂, he, ?_, ?_, ?_, ?_, ?_⟩
    · intro T s x y
      calc (X.L.mul s x y).1 ≫ (e₁ ≪≫ e₂).hom = ((X.L.mul s x y).1 ≫ e₁.hom) ≫ e₂.hom := (Category.assoc _ _ _).symm
        _ = _ := by rw [hmul₁]
        _ = _ := hmul₂ s _ _
        _ = _ := mul_val_congr W.L s (Subtype.ext (Category.assoc _ _ _)) (Subtype.ext (Category.assoc _ _ _))
    · intro i
      rw [Iso.trans_hom, ← Category.assoc, hlev₁ i, hlev₂ i]
    · show LocIsoOnBase X.f ((Scheme.Modules.pullback (e₁.hom ≫ e₂.hom)).obj W.pol) X.pol
      have hcomm : e₁.hom ≫ Y.f = X.f ≫ 𝟙 (Spec (CommRingCat.of S)) := by rw [Category.comp_id, he₁]
      have h2 := LocIsoOnBase.pullback_of_comp_eq X.f e₁.hom (𝟙 _) hcomm hpol₂
      have E := LocIsoOnBase.equivalence X.f
      exact E.trans (E.trans (locIso_of_iso X.f ((Scheme.Modules.pullbackComp e₁.hom e₂.hom).app W.pol).symm) h2) hpol₁
    · intro x
      rw [Iso.trans_hom, ← Category.assoc, hact₁ x, Category.assoc, hact₂ x, Category.assoc]
    · rw [Iso.trans_hom, ← Category.assoc, hP₁, hP₂]

end S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_refl_symm_trans
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_refl_symm_trans (solution)
