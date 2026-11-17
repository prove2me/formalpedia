-- Prove2me | solution 1 for AlgebraicGeometry.finite_flat_sigma_desc
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:13.57845+00:00
-- url     : https://prove2.me/submissions/dbad112b-0ac0-4e44-91f4-00ea6305663d

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Limits

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite disjoint union of finite-flat schemes over an affine base is finite flat.
Finiteness follows from the finite product of the corresponding finite modules. -/
theorem _root_.solution
    (R : Type u) [CommRing R] {ι : Type u} [Finite ι]
    (X : ι → Scheme.{u})
    (f : ∀ i, X i ⟶ Spec (CommRingCat.of R))
    [∀ i, IsFinite (f i)] [∀ i, Flat (f i)] :
    IsFinite (Sigma.desc f) ∧ Flat (Sigma.desc f) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let S := Spec (CommRingCat.of R)
  letI : ∀ i, IsAffine (X i) := fun i => isAffine_of_isAffineHom (f i)
  let K := Γ(S, ⊤)
  let A : ι → Type u := fun i => Γ(X i, ⊤)
  letI : ∀ i, Algebra K (A i) := fun i => (f i).appTop.hom.toAlgebra
  haveI : ∀ i, Module.Finite K (A i) := fun i =>
    RingHom.finite_algebraMap.mp (f i).finite_appTop
  let φ : K →+* (∀ i, A i) := algebraMap K (∀ i, A i)
  have hφ : RingHom.Finite φ := RingHom.finite_algebraMap.mpr inferInstance
  let e : (∐ X) ≅ Spec (CommRingCat.of (∀ i, A i)) :=
    (Sigma.mapIso (fun i => (X i).isoSpec)) ≪≫
      asIso (sigmaSpec (fun i => CommRingCat.of (A i)))
  have he : Sigma.desc f ≫ S.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    apply Sigma.hom_ext
    intro i
    simp only [Category.assoc, Sigma.ι_desc_assoc]
    rw [← Scheme.isoSpec_hom_naturality (f i)]
    change (X i).isoSpec.hom ≫ Spec.map (f i).appTop =
      Sigma.ι X i ≫ CategoryTheory.Limits.Sigma.map (fun j => (X j).isoSpec.hom) ≫
        sigmaSpec (fun j => CommRingCat.of (A j)) ≫ Spec.map (CommRingCat.ofHom φ)
    simp only [Sigma.ι_map_assoc]
    change (X i).isoSpec.hom ≫ Spec.map (f i).appTop =
      (X i).isoSpec.hom ≫ Sigma.ι (fun j => Spec (CommRingCat.of (A j))) i ≫
        sigmaSpec (fun j => CommRingCat.of (A j)) ≫ Spec.map (CommRingCat.ofHom φ)
    rw [ι_sigmaSpec_assoc]
    rw [← Spec.map_comp]
    congr 1
  haveI : IsFinite (Spec.map (CommRingCat.ofHom φ)) :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom φ)).mpr hφ
  haveI : IsFinite (Sigma.desc f ≫ S.isoSpec.hom) := by
    rw [he]
    infer_instance
  exact ⟨(IsFinite.comp_iff (f := Sigma.desc f) (g := S.isoSpec.hom)).mp inferInstance,
    inferInstance⟩

end AlgebraicGeometry
