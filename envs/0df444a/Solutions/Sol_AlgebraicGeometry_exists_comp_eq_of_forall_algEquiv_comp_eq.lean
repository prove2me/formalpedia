-- Prove2me | solution 1 for AlgebraicGeometry.exists_comp_eq_of_forall_algEquiv_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f10786d6-0b0c-53df-a459-b45933f52879

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_comp_eq_of_forall_algEquiv_comp_eq
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (hfix : ∀ x : L, (∀ σ : L ≃ₐ[K] L, σ x = x) → ∃ a : K, algebraMap K L a = x)
    {Y : Scheme.{u}} (y : Spec (.of L) ⟶ Y)
    (hy : ∀ σ : L ≃ₐ[K] L, Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ y = y) :
    ∃ y₀ : Spec (.of K) ⟶ Y, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ y₀ = y := by
  classical
  obtain ⟨⟨x, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L Y).symm.surjective y

  have hψ : ∀ σ : L ≃ₐ[K] L, ψ ≫ CommRingCat.ofHom (σ : L →+* L) = ψ := by
    intro σ
    have h : (Scheme.SpecToEquivOfField L Y).symm ⟨x, ψ ≫ CommRingCat.ofHom (σ : L →+* L)⟩ =
        (Scheme.SpecToEquivOfField L Y).symm ⟨x, ψ⟩ := by
      change Spec.map (ψ ≫ _) ≫ Y.fromSpecResidueField x =
        Spec.map ψ ≫ Y.fromSpecResidueField x
      rw [Spec.map_comp, Category.assoc]
      exact hy σ
    exact eq_of_heq (Sigma.mk.inj ((Scheme.SpecToEquivOfField L Y).symm.injective h)).2

  have hfix' : ∀ a, ∃ b : K, algebraMap K L b = ψ.hom a := fun a =>
    hfix _ fun σ => by
      have := congrArg (fun φ : Y.residueField x ⟶ CommRingCat.of L => φ.hom a) (hψ σ)
      simpa using this
  choose q hq using hfix'
  have hinj := (algebraMap K L).injective
  let ψ₀ : Y.residueField x →+* K :=
    { toFun := q
      map_one' := hinj (by rw [hq, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hq, map_mul, map_mul, hq, hq])
      map_zero' := hinj (by rw [hq, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hq, map_add, map_add, hq, hq]) }
  have hψ₀ : CommRingCat.ofHom ψ₀ ≫ CommRingCat.ofHom (algebraMap K L) = ψ := by
    ext a
    simp [ψ₀, hq]
  refine ⟨Spec.map (CommRingCat.ofHom ψ₀) ≫ Y.fromSpecResidueField x, ?_⟩
  change _ = Spec.map ψ ≫ Y.fromSpecResidueField x
  rw [← hψ₀, Spec.map_comp, Category.assoc]

end S_AlgebraicGeometry_exists_comp_eq_of_forall_algEquiv_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_comp_eq_of_forall_algEquiv_comp_eq (solution)
