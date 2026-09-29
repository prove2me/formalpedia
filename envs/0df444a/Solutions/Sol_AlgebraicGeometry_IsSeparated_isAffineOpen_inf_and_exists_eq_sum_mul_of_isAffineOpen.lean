-- Prove2me | solution 1 for AlgebraicGeometry.IsSeparated.isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/cefd99dd-ca53-5a08-b643-264f5eb0278d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsSeparated_isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

namespace IntSurj28

theorem opHom_eq {X : Scheme.{u}} {A B : X.Opens} (i j : op A ⟶ op B) : i = j :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem topIso_hom_homOfLE_appTop {X : Scheme.{u}} {U W : X.Opens} (e : W ≤ U) (a : Γ(X, U)) :
    W.topIso.hom ((X.homOfLE e).appTop (U.topIso.inv a)) = X.presheaf.map (homOfLE e).op a := by
  rw [Scheme.homOfLE_appTop]
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  change (X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _) a = _
  rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  exact congrArg (fun i => X.presheaf.map i a) (opHom_eq _ _)

theorem exists_eq_specMap {A R : CommRingCat.{u}} (g : Spec A ⟶ Spec R) :
    ∃ θ : R ⟶ A, Spec.map θ = g := by
  refine ⟨(Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso A).hom, ?_⟩
  have h := Scheme.toSpecΓ_naturality g
  rw [← SpecMap_ΓSpecIso_hom, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp] at h
  rw [Spec.map_comp, ← h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

section Main

theorem main {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [IsAffine Y]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) ∧
    ∀ c : Γ(X, U ⊓ V), ∃ (n : ℕ) (a : Fin n → Γ(X, U)) (b : Fin n → Γ(X, V)),
      c = ∑ i : Fin n, X.presheaf.map (homOfLE inf_le_left).op (a i) *
        X.presheaf.map (homOfLE inf_le_right).op (b i) := by
  classical

  set R : CommRingCat.{u} := Γ(Y, ⊤) with hR
  set A : CommRingCat.{u} := Γ(X, U) with hA
  set B : CommRingCat.{u} := Γ(X, V) with hB
  set f' : X ⟶ Spec R := f ≫ Y.isoSpec.hom with hf'
  haveI : IsSeparated f' := inferInstance

  obtain ⟨θU, hθU⟩ := exists_eq_specMap (hU.fromSpec ≫ f')
  obtain ⟨θV, hθV⟩ := exists_eq_specMap (hV.fromSpec ≫ f')
  letI algA : Algebra R A := θU.hom.toAlgebra
  letI algB : Algebra R B := θV.hom.toAlgebra
  have eU : hU.fromSpec ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← hθU]; rfl
  have eV : hV.fromSpec ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← hθV]; rfl

  have hP : IsPullback (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ hU.isoSpec.hom)
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ hV.isoSpec.hom) hU.fromSpec hV.fromSpec :=
    (isPullback_opens_inf U V).of_iso (Iso.refl _) hU.isoSpec hV.isoSpec (Iso.refl _)
      (by simp) (by simp) (by simp [IsAffineOpen.isoSpec_hom]) (by simp [IsAffineOpen.isoSpec_hom])

  set ψ := pullback.mapDesc hU.fromSpec hV.fromSpec f' with hψ
  haveI : IsClosedImmersion ψ := inferInstance
  set F : ↑(U ⊓ V) ⟶ Spec (.of (A ⊗[R] B)) :=
    hP.isoPullback.hom ≫ ψ ≫ (pullback.congrHom eU eV).hom ≫ (pullbackSpecIso R A B).hom with hF
  haveI hFci : IsClosedImmersion F := inferInstance
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine F
  refine ⟨hAff, ?_⟩

  have hF1 : F ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      X.homOfLE inf_le_left ≫ hU.isoSpec.hom := by
    rw [hF, hψ]
    simp only [Category.assoc, pullbackSpecIso_hom_fst, pullback.congrHom_hom,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, IsPullback.isoPullback_hom_fst]
  have hF2 : F ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : B →+* A ⊗[R] B)) =
      X.homOfLE inf_le_right ≫ hV.isoSpec.hom := by
    rw [hF, hψ]
    simp only [Category.assoc, pullbackSpecIso_hom_snd, pullback.congrHom_hom,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id, IsPullback.isoPullback_hom_snd]

  set Φ : A ⊗[R] B →+* Γ(X, U ⊓ V) :=
    ((Scheme.ΓSpecIso (.of (A ⊗[R] B))).inv ≫ F.appTop ≫ (U ⊓ V).topIso.hom).hom with hΦ
  have hΦU : ∀ a : A, Φ (a ⊗ₜ[R] (1 : B)) = X.presheaf.map (homOfLE inf_le_left).op a := by
    intro a
    have h1 : (Scheme.ΓSpecIso (.of (A ⊗[R] B))).inv (a ⊗ₜ[R] (1 : B)) =
        (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).appTop
          ((Scheme.ΓSpecIso A).inv a) := by
      rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso A).inv, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      rfl
    have h2 : F.appTop ((Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).appTop
          ((Scheme.ΓSpecIso A).inv a)) = (X.homOfLE inf_le_left).appTop (hU.isoSpec.hom.appTop ((Scheme.ΓSpecIso A).inv a)) := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hF1, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply]
    have h3 : hU.isoSpec.hom.appTop ((Scheme.ΓSpecIso A).inv a) = U.topIso.inv a := by
      rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply (Scheme.ΓSpecIso A).inv,
        Iso.inv_hom_id, CommRingCat.id_apply]
    simp only [hΦ, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [h1, h2, h3]
    exact topIso_hom_homOfLE_appTop _ a
  have hΦV : ∀ b : B, Φ ((1 : A) ⊗ₜ[R] b) = X.presheaf.map (homOfLE inf_le_right).op b := by
    intro b
    have h1 : (Scheme.ΓSpecIso (.of (A ⊗[R] B))).inv ((1 : A) ⊗ₜ[R] b) =
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : B →+* A ⊗[R] B))).appTop
          ((Scheme.ΓSpecIso B).inv b) := by
      rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso B).inv, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      rfl
    have h2 : F.appTop ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : B →+* A ⊗[R] B))).appTop
          ((Scheme.ΓSpecIso B).inv b)) = (X.homOfLE inf_le_right).appTop (hV.isoSpec.hom.appTop ((Scheme.ΓSpecIso B).inv b)) := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hF2, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply]
    have h3 : hV.isoSpec.hom.appTop ((Scheme.ΓSpecIso B).inv b) = V.topIso.inv b := by
      rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply (Scheme.ΓSpecIso B).inv,
        Iso.inv_hom_id, CommRingCat.id_apply]
    simp only [hΦ, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [h1, h2, h3]
    exact topIso_hom_homOfLE_appTop _ b

  intro c
  obtain ⟨s, hs⟩ := hsurj ((U ⊓ V).topIso.inv c)
  set t : A ⊗[R] B := (Scheme.ΓSpecIso (.of (A ⊗[R] B))).hom s with ht
  have hc : Φ t = c := by
    simp only [hΦ, ht, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply, hs,
      ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset t
  refine ⟨S.card, fun i => (S.equivFin.symm i).1.1, fun i => (S.equivFin.symm i).1.2, ?_⟩
  rw [← hc, hS, map_sum]
  rw [← Finset.sum_coe_sort S]
  rw [← Fintype.sum_equiv S.equivFin.symm
    (fun i => X.presheaf.map (homOfLE inf_le_left).op (S.equivFin.symm i).1.1 *
      X.presheaf.map (homOfLE inf_le_right).op (S.equivFin.symm i).1.2)
    (fun p => Φ (p.1.1 ⊗ₜ[R] p.1.2)) ?_]
  intro i
  dsimp only
  rw [← hΦU, ← hΦV, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Main

end IntSurj28

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [IsAffine Y]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) ∧
    ∀ c : Γ(X, U ⊓ V), ∃ (n : ℕ) (a : Fin n → Γ(X, U)) (b : Fin n → Γ(X, V)),
      c = ∑ i : Fin n, X.presheaf.map (homOfLE inf_le_left).op (a i) * X.presheaf.map (homOfLE inf_le_right).op (b i) :=
  IntSurj28.main f U V hU hV

end S_AlgebraicGeometry_IsSeparated_isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_IsSeparated_isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen (solution)
