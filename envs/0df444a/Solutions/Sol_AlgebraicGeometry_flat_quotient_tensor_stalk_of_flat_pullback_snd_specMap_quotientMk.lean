-- Prove2me | solution 1 for AlgebraicGeometry.flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6d4c49a7-1dc7-5d17-ba07-5f7aff0bef84

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace TruncStalk

theorem flat_tensor_sections
    {R : Type u} [CommRing R] (J : Ideal R) {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of R))
    [Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))]
    {U : Z.Opens} (hU : IsAffineOpen U) :
    letI : Algebra R ↑Γ(Z, U) := (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top).hom).toAlgebra
    Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] ↑Γ(Z, U)) := by
  letI algS : Algebra R ↑Γ(Z, U) := (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top).hom).toAlgebra
  set T := R ⧸ J with hT
  set ι : Spec (CommRingCat.of (R ⧸ J)) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) with hι

  haveI : Flat (pullback.snd (hU.fromSpec ≫ f) ι) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd f ι hU.fromSpec]
    infer_instance

  have hident : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R ↑Γ(Z, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec f (U := ⊤) (isAffineOpen_top (Spec (CommRingCat.of R))) hU le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
    rw [← h]
    rfl
  haveI hflat2 : Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R ↑Γ(Z, U))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T)))) := by
    rw [← hident]; exact this

  haveI : Flat (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↑Γ(Z, U)) (B := T) : T →+* ↑Γ(Z, U) ⊗[R] T))) := by
    rw [← pullbackSpecIso_inv_snd R (↑Γ(Z, U)) T]
    infer_instance
  have hR : (Algebra.TensorProduct.includeRight (R := R) (A := ↑Γ(Z, U)) (B := T) : T →+* ↑Γ(Z, U) ⊗[R] T).Flat :=
    (Flat.SpecMap_iff).mp this

  have hL : (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := T) (B := ↑Γ(Z, U))).Flat := by
    have hcomp : (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := T) (B := ↑Γ(Z, U))) =
        (Algebra.TensorProduct.comm R (↑Γ(Z, U)) T).toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := ↑Γ(Z, U)) (B := T) : T →+* ↑Γ(Z, U) ⊗[R] T) := by
      ext t
      simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.includeRight_apply]
    rw [hcomp]
    exact RingHom.Flat.comp hR (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R (↑Γ(Z, U)) T).bijective)
  have halg : algebraMap T (T ⊗[R] ↑Γ(Z, U)) = Algebra.TensorProduct.includeLeftRingHom := by
    ext t; rfl
  rw [← RingHom.flat_algebraMap_iff, halg]
  exact hL

end TruncStalk

open TruncStalk in
theorem solution
    {R : Type u} [CommRing R] (J : Ideal R) {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of R))
    [Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))] (z : ↥Z) :
    letI : Algebra R ↑(Z.presheaf.stalk z) :=
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ Z.presheaf.germ ⊤ z trivial).hom).toAlgebra
    Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] ↑(Z.presheaf.stalk z)) := by
  classical
  letI algz : Algebra R ↑(Z.presheaf.stalk z) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ Z.presheaf.germ ⊤ z trivial).hom).toAlgebra

  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  letI algS : Algebra R ↑Γ(Z, U) := (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top).hom).toAlgebra
  letI aU : Algebra ↑Γ(Z, U) ↑(Z.presheaf.stalk z) := Z.presheaf.algebra_section_stalk ⟨z, hzU⟩
  haveI hloc : IsLocalization.AtPrime ↑(Z.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  haveI : IsScalarTower R ↑Γ(Z, U) ↑(Z.presheaf.stalk z) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change (Z.presheaf.germ ⊤ z trivial).hom ((f.app ⊤).hom (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r)) =
      (Z.presheaf.germ U z hzU).hom ((Z.presheaf.map (homOfLE (le_top : U ≤ f ⁻¹ᵁ ⊤)).op).hom
        ((f.app ⊤).hom (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r)))
    exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE (le_top : U ≤ f ⁻¹ᵁ ⊤)) z hzU _).symm

  letI algB : Algebra ((R ⧸ J) ⊗[R] ↑Γ(Z, U)) ((R ⧸ J) ⊗[R] ↑(Z.presheaf.stalk z)) :=
    (Algebra.TensorProduct.map (AlgHom.id R (R ⧸ J)) (IsScalarTower.toAlgHom R ↑Γ(Z, U) ↑(Z.presheaf.stalk z))).toAlgebra
  haveI hst : IsScalarTower (R ⧸ J) ((R ⧸ J) ⊗[R] ↑Γ(Z, U)) ((R ⧸ J) ⊗[R] ↑(Z.presheaf.stalk z)) :=
    @IsScalarTower.of_algebraMap_eq (R ⧸ J) ((R ⧸ J) ⊗[R] ↑Γ(Z, U)) ((R ⧸ J) ⊗[R] ↑(Z.presheaf.stalk z)) _ _ _ _ algB _
      (fun x => by simp [algB, RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply])
  haveI hlocT : IsLocalization (((hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl).map (Algebra.TensorProduct.includeRight (R := R) (A := R ⧸ J))) ((R ⧸ J) ⊗[R] ↑(Z.presheaf.stalk z)) :=
    IsLocalization.tensorProduct_tensorProduct_right R (R ⧸ J) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl ↑(Z.presheaf.stalk z)
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  have h1 : Module.Flat ((R ⧸ J) ⊗[R] ↑Γ(Z, U)) ((R ⧸ J) ⊗[R] ↑(Z.presheaf.stalk z)) :=
    IsLocalization.flat _ (((hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl).map (Algebra.TensorProduct.includeRight (R := R) (A := R ⧸ J)))
  have h2 : Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] ↑Γ(Z, U)) := flat_tensor_sections J f hU
  exact Module.Flat.trans (R ⧸ J) ((R ⧸ J) ⊗[R] ↑Γ(Z, U)) ((R ⧸ J) ⊗[R] ↑(Z.presheaf.stalk z))

end S_AlgebraicGeometry_flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk
end P2MW
export P2MW.S_AlgebraicGeometry_flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk (solution)
