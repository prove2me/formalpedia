-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_sections_injective_of_tensorProduct_algEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/70bc286d-bb84-5e56-8ee7-5585f50e9ea4

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi

set_option autoImplicit false

universe u

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi.AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi.AlgebraicGeometry.SmoothProperCurve NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage Spec Spec.map Scheme Spec.map_injective IsClosedImmersion Spec.preimage"
namespace SmoothProperCurve
p2m_export "AlgebraicGeometry.SmoothProperCurve" "specMap baseChange"
namespace SplitSectionsImpl
p2m_open "AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry"

section Ring

variable {R₀ R' B : Type u} [CommRing R₀] [CommRing R'] [CommRing B] [Algebra R₀ B] [Algebra R₀ R']
  {d : ℕ} (φ : (R' ⊗[R₀] B) ≃ₐ[R'] (Fin d → R'))

noncomputable def proj (m : Fin d) : (R' ⊗[R₀] B) →ₐ[R'] R' :=
  (Pi.evalAlgHom R' (fun _ : Fin d => R') m).comp (φ : (R' ⊗[R₀] B) →ₐ[R'] (Fin d → R'))

theorem proj_apply (m : Fin d) (z : R' ⊗[R₀] B) : proj φ m z = φ z m := rfl

noncomputable def coord (m : Fin d) : B →+* R' :=
  (proj φ m).toRingHom.comp (Algebra.TensorProduct.includeRight (R := R₀) (A := R') (B := B)).toRingHom

theorem coord_apply (m : Fin d) (b : B) : coord φ m b = φ (1 ⊗ₜ[R₀] b) m := rfl

theorem proj_tmul (m : Fin d) (a : R') (b : B) : proj φ m (a ⊗ₜ[R₀] b) = a * coord φ m b := by
  rw [coord_apply, proj_apply]
  have h : a ⊗ₜ[R₀] b = algebraMap R' (R' ⊗[R₀] B) a * (1 ⊗ₜ[R₀] b) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  rw [h, map_mul, AlgEquiv.commutes, Pi.mul_apply, Pi.algebraMap_apply]
  rfl

theorem coord_algebraMap (m : Fin d) (x : R₀) : coord φ m (algebraMap R₀ B x) = algebraMap R₀ R' x := by
  rw [coord_apply, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have h : (algebraMap R₀ R' x) ⊗ₜ[R₀] (1 : B) = algebraMap R' (R' ⊗[R₀] B) (algebraMap R₀ R' x) := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [h, AlgEquiv.commutes, Pi.algebraMap_apply]
  rfl

theorem coord_comp_algebraMap (m : Fin d) : (coord φ m).comp (algebraMap R₀ B) = algebraMap R₀ R' :=
  RingHom.ext fun x => coord_algebraMap φ m x

theorem eq_of_apply_coord_eq {T : Type u} [CommRing T] [Nontrivial T] (t : R' →+* T) {i j : Fin d}
    (h : ∀ b : B, t (coord φ i b) = t (coord φ j b)) : i = j := by
  by_contra hij
  have key : ∀ z : R' ⊗[R₀] B, t (proj φ i z) = t (proj φ j z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [proj_tmul, proj_tmul, map_mul, map_mul, h b]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have h1 := key (φ.symm (Pi.single i 1))
  rw [proj_apply, proj_apply, AlgEquiv.apply_symm_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hij), map_one, map_zero] at h1
  exact one_ne_zero h1

end Ring

section Scheme

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  {R₀ : Type u} [CommRing R₀] [Algebra R R₀] {B : Type u} [CommRing B] [Algebra R₀ B]
  (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀))
  (hι : ι ≫ baseChange R c R₀ = specMap R₀ B)
  {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra R₀ R'] [IsScalarTower R R₀ R']
  {d : ℕ} (φ : (R' ⊗[R₀] B) ≃ₐ[R'] (Fin d → R'))

noncomputable abbrev specCoord (m : Fin d) : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (coord φ m))

theorem specCoord_comp_specMap (m : Fin d) : specCoord φ m ≫ specMap R₀ B = specMap R₀ R' := by
  show Spec.map (CommRingCat.ofHom (coord φ m)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) =
    Spec.map (CommRingCat.ofHom (algebraMap R₀ R'))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, coord_comp_algebraMap]

noncomputable def secTop (m : Fin d) : Spec (CommRingCat.of R') ⟶ C :=
  specCoord φ m ≫ ι ≫ pullback.fst c (specMap R R₀)

include hι in
theorem secTop_comp (m : Fin d) : secTop c ι φ m ≫ c = specMap R R' := by
  have hι' : ι ≫ pullback.snd c (specMap R R₀) = specMap R₀ B := hι
  simp only [secTop, Category.assoc]
  rw [pullback.condition, ← Category.assoc ι, hι', ← Category.assoc, specCoord_comp_specMap φ m]

  show Spec.map (CommRingCat.ofHom (algebraMap R₀ R')) ≫ Spec.map (CommRingCat.ofHom (algebraMap R R₀)) =
    Spec.map (CommRingCat.ofHom (algebraMap R R'))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R R₀ R']

noncomputable def sec (m : Fin d) : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R') :=
  ⟨pullback.lift (secTop c ι φ m) (𝟙 _) (by rw [secTop_comp c ι hι φ m, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

theorem sec_fst (m : Fin d) : (sec c ι hι φ m).1 ≫ pullback.fst c (specMap R R') = secTop c ι φ m :=
  pullback.lift_fst _ _ _

theorem sec_injective [IsClosedImmersion ι] (k : Type u) [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')) :
    Function.Injective fun m => s ≫ (sec c ι hι φ m).1 := by
  intro i j h
  have hι' : ι ≫ pullback.snd c (specMap R R₀) = specMap R₀ B := hι

  have h1 : s ≫ secTop c ι φ i = s ≫ secTop c ι φ j := by
    have := congrArg (· ≫ pullback.fst c (specMap R R')) h
    simpa only [Category.assoc, sec_fst] using this
  have h2 : (s ≫ specCoord φ i) ≫ ι = (s ≫ specCoord φ j) ≫ ι := by
    apply pullback.hom_ext
    · simpa only [secTop, Category.assoc] using h1
    · simp only [Category.assoc, hι', specCoord_comp_specMap φ]

  have h3 : s ≫ specCoord φ i = s ≫ specCoord φ j := (cancel_mono ι).mp h2
  obtain ⟨θ, rfl⟩ : ∃ θ, Spec.map θ = s := ⟨Spec.preimage s, Spec.map_preimage s⟩
  rw [← Spec.map_comp, ← Spec.map_comp] at h3
  have h4 := Spec.map_injective h3
  have E : ∀ b : B, θ.hom (coord φ i b) = θ.hom (coord φ j b) := fun b => by
    have := congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of k => f.hom b) h4
    simpa using this

  exact eq_of_apply_coord_eq φ θ.hom E

end Scheme

end AlgebraicGeometry.SmoothProperCurve.SplitSectionsImpl

open AlgebraicGeometry.SmoothProperCurve.SplitSectionsImpl in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R₀ : Type u) [CommRing R₀] [Algebra R R₀]
    (B : Type u) [CommRing B] [Algebra R₀ B]
    (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀)) [IsClosedImmersion ι]
    (hι : ι ≫ baseChange R c R₀ = specMap R₀ B)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R₀ R'] [IsScalarTower R R₀ R']
    (d : ℕ) (φ : (R' ⊗[R₀] B) ≃ₐ[R'] (Fin d → R')) :
    ∃ σ : Fin d → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R'),
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')),
        Function.Injective fun i => s ≫ (σ i).1 :=
  ⟨fun m => sec c ι hι φ m, fun k _ s => sec_injective c ι hι φ k s⟩

end S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi (solution)
