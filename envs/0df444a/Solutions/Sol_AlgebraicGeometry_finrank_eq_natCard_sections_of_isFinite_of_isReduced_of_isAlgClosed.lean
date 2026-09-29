-- Prove2me | solution 1 for AlgebraicGeometry.finrank_eq_natCard_sections_of_isFinite_of_isReduced_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/61c9c1f2-cbb4-5ba8-b242-7fcf8c8e3bd7

import Mathlib
import Theorems.Thm_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finrank_eq_natCard_sections_of_isFinite_of_isReduced_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace LEVRED

variable {k : Type u} [Field k]

theorem finrank_sections_eq {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] [Flat z] [IsAffine C]
    (n : ℕ) (hrank : ∀ s : ↥(Spec (CommRingCat.of k)), z.finrank s = n) :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Module.Finite k Γ(C, ⊤) ∧ Module.finrank k Γ(C, ⊤) = n := by
  set φ : CommRingCat.of k ⟶ Γ(C, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop with hφ
  letI alg : Algebra k Γ(C, ⊤) := φ.hom.toAlgebra
  have hbij : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  have hFin : φ.hom.Finite := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Finite
    exact z.finite_appTop.comp (RingHom.Finite.of_surjective _ hbij.surjective)
  have hFlat : φ.hom.Flat := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Flat
    exact (RingHom.Flat.of_bijective hbij).comp z.flat_appTop
  have hfin : Module.Finite k Γ(C, ⊤) := hFin
  refine ⟨hfin, ?_⟩

  have hz : z = C.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  haveI : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).2 hFin
  haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hFlat

  obtain ⟨s⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of k)))
  have h1 := hrank s
  rw [hz, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hFin hFlat] at h1

  have h2 : φ.hom.finrank s = Module.finrank k Γ(C, ⊤) := by
    have : φ.hom = algebraMap k Γ(C, ⊤) := rfl
    rw [this, RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, h1]

theorem finite_algHom (B : Type u) [CommRing B] [Algebra k B] [Module.Finite k B] : Finite (B →ₐ[k] k) := by
  classical
  haveI : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let F : (B →ₐ[k] k) → MaximalSpectrum B := fun φ =>
    ⟨RingHom.ker φ.toRingHom, RingHom.ker_isMaximal_of_surjective φ.toRingHom (fun x => ⟨algebraMap k B x, by simp⟩)⟩
  refine Finite.of_injective F ?_
  intro φ ψ h
  have hker : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom := congrArg MaximalSpectrum.asIdeal h
  apply AlgHom.ext
  intro x

  have h1 : x - algebraMap k B (φ x) ∈ RingHom.ker φ.toRingHom := by simp [RingHom.mem_ker]
  rw [hker] at h1
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, AlgHom.commutes] at h1
  exact (sub_eq_zero.1 h1).symm

theorem natCard_algHom_ge {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsAffine C]
    (hfin : letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra; Module.Finite k Γ(C, ⊤))
    (ι : Type) (e : ι ↪ {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _}) [Finite ι] :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Nat.card ι ≤ Nat.card (Γ(C, ⊤) →ₐ[k] k) := by
  letI alg : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  haveI := hfin
  haveI : Finite (Γ(C, ⊤) →ₐ[k] k) := finite_algHom Γ(C, ⊤)

  let Φ : {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} → (Γ(C, ⊤) →ₐ[k] k) := fun x =>
    { toRingHom := (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
      commutes' := by
        intro c
        change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop ≫ x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
        rw [← Scheme.Hom.comp_appTop_assoc, x.2]
        simp }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have happ : x.1.appTop = y.1.appTop := by
      have := congrArg (fun φ : Γ(C, ⊤) →ₐ[k] k => φ.toRingHom) hxy
      have h2 : (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) = (y.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) := by
        ext1; exact this
      simpa [← Iso.eq_comp_inv] using h2
    apply Subtype.ext
    have hx := Scheme.isoSpec_hom_naturality x.1
    have hy := Scheme.isoSpec_hom_naturality y.1
    rw [happ] at hx
    rw [← cancel_mono C.isoSpec.hom, ← hx, hy]
  calc Nat.card ι ≤ Nat.card {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} := by
          haveI : Finite {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} := Finite.of_injective Φ hΦ
          exact Nat.card_le_card_of_injective e e.injective
    _ ≤ Nat.card (Γ(C, ⊤) →ₐ[k] k) := Nat.card_le_card_of_injective Φ hΦ

end LEVRED

namespace RANKFIN

variable {k : Type u} [Field k]

theorem flat_of_field {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] : Flat z := by
  haveI : IsAffine C := isAffine_of_isAffineHom z
  set φ : CommRingCat.of k ⟶ Γ(C, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop with hφ
  have hFlat : φ.hom.Flat := by
    letI : Algebra k Γ(C, ⊤) := φ.hom.toAlgebra
    have : Module.Flat k Γ(C, ⊤) := inferInstance
    exact this
  have hz : z = C.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hFlat
  rw [hz]; infer_instance

theorem natCard_sections_eq_natCard_algHom {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsAffine C] :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Nat.card {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} = Nat.card (Γ(C, ⊤) →ₐ[k] k) := by
  letI alg : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  let Φ : {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} → (Γ(C, ⊤) →ₐ[k] k) := fun x =>
    { toRingHom := (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
      commutes' := by
        intro c
        change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop ≫ x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
        rw [← Scheme.Hom.comp_appTop_assoc, x.2]
        simp }
  apply Nat.card_eq_of_bijective Φ
  constructor
  · intro x y hxy
    have happ : x.1.appTop = y.1.appTop := by
      have := congrArg (fun φ : Γ(C, ⊤) →ₐ[k] k => φ.toRingHom) hxy
      have h2 : (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) = (y.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) := by
        ext1; exact this
      simpa [← Iso.eq_comp_inv] using h2
    apply Subtype.ext
    have hx := Scheme.isoSpec_hom_naturality x.1
    have hy := Scheme.isoSpec_hom_naturality y.1
    rw [happ] at hx
    rw [← cancel_mono C.isoSpec.hom, ← hx, hy]
  · intro ψ

    let x : Spec (CommRingCat.of k) ⟶ C := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ C.isoSpec.inv
    have hz : z = C.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop) := by
      rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
    have hcomp : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop) ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 _ := by
      ext c
      exact ψ.commutes c
    have hx : x ≫ z = 𝟙 _ := by
      rw [hz]
      simp only [x, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Spec.map_comp, hcomp, Spec.map_id]
    refine ⟨⟨x, hx⟩, ?_⟩
    apply AlgHom.ext
    intro c
    change ((x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) c = ψ c
    have hx' : x.appTop = C.isoSpec.inv.appTop ≫ (Spec.map (CommRingCat.ofHom ψ.toRingHom)).appTop := by
      simp [x]
    have hinv : C.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(C, ⊤)).inv := by
      have h := congrArg Scheme.Hom.appTop C.isoSpec.inv_hom_id
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
      have hh : C.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(C, ⊤)).hom := Scheme.toSpecΓ_appTop C
      rw [hh] at h

      rw [← Iso.eq_inv_comp, Category.comp_id] at h
      exact h
    rw [hx', hinv, Category.assoc, Scheme.ΓSpecIso_naturality]
    change ((Scheme.ΓSpecIso Γ(C, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(C, ⊤)).hom ≫ CommRingCat.ofHom ψ.toRingHom).hom c = ψ c
    rw [Iso.inv_hom_id_assoc]; rfl

end RANKFIN

namespace RANKFIN

theorem finrank_eq_natCard_sections {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] [IsReduced C] (s : ↥(Spec (CommRingCat.of k))) :
    z.finrank s = Nat.card {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} := by
  haveI : IsAffine C := isAffine_of_isAffineHom z
  haveI : Flat z := flat_of_field z
  have hconst : ∀ s' : ↥(Spec (CommRingCat.of k)), z.finrank s' = z.finrank s := by
    intro s'; congr 1; exact Subsingleton.elim _ _
  obtain ⟨hfin, hrank⟩ := LEVRED.finrank_sections_eq z (z.finrank s) hconst
  letI alg : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  haveI := hfin
  haveI : _root_.IsReduced Γ(C, ⊤) := IsReduced.component_reduced ⊤
  rw [← hrank, ← AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed k Γ(C, ⊤), natCard_sections_eq_natCard_algHom z]

end RANKFIN

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsFinite f] [IsReduced X] (s : ↥(Spec (CommRingCat.of k))) :
    f.finrank s = Nat.card {x : Spec (CommRingCat.of k) ⟶ X // x ≫ f = 𝟙 (Spec (CommRingCat.of k))} := by
  exact RANKFIN.finrank_eq_natCard_sections f s

end S_AlgebraicGeometry_finrank_eq_natCard_sections_of_isFinite_of_isReduced_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_finrank_eq_natCard_sections_of_isFinite_of_isReduced_of_isAlgClosed (solution)
