-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.existsUnique_section_of_map_i1_eq_map_i2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1fcc66b7-9f5a-5866-9bbb-ce27e96b3a12

import Mathlib
import Definitions.Def_Algebra_DescentCofaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry Algebra.TensorProduct Algebra.DescentCofaces
open scoped TensorProduct

theorem solution
    (E : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1})
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A]
    (e : ToType (E.obj.obj (op (Spec (.of A)))))
    (he : E.obj.map (Spec.map (i₁ R A)).op e = E.obj.map (Spec.map (i₂ R A)).op e) :
    ∃! e₀ : ToType (E.obj.obj (op (Spec (.of R)))),
      E.obj.map (Spec.map (CommRingCat.ofHom (algebraMap R A))).op e₀ = e := by
  classical

  have he' : E.obj.map (Spec.map (CommRingCat.ofHom (includeLeftRingHom : A →+* A ⊗[R] A))).op e =
      E.obj.map (Spec.map (CommRingCat.ofHom ↑(includeRight : A →ₐ[R] A ⊗[R] A))).op e := by
    simpa only [i₁, i₂, AlgHom.toRingHom_eq_coe] using he

  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := A)⟩

  have hcov : Sieve.generate (Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ∈
      Scheme.fppfTopology (Spec (.of R)) :=
    Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage _)

  have hsh : Presheaf.IsSheaf Scheme.fppfTopology (E.obj ⋙ forget AddCommGrpCat) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ E.obj (forget _)).mp E.cond
  have hsf : Presieve.IsSheafFor (E.obj ⋙ forget AddCommGrpCat)
      (Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hsh.isSheafFor _ hcov
  rw [Presieve.isSheafFor_singleton] at hsf
  refine hsf e ?_

  intro Z p₁ p₂ hp
  change E.obj.map p₁.op e = E.obj.map p₂.op e
  set q : Z ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := Limits.pullback.lift p₁ p₂ hp with hq
  have h1 : p₁ = q ≫ (pullbackSpecIso R A A).hom ≫ Spec.map (CommRingCat.ofHom includeLeftRingHom) := by
    rw [pullbackSpecIso_hom_fst, hq, Limits.pullback.lift_fst]
  have h2 : p₂ = q ≫ (pullbackSpecIso R A A).hom ≫ Spec.map (CommRingCat.ofHom ↑(includeRight : A →ₐ[R] A ⊗[R] A)) := by
    rw [pullbackSpecIso_hom_snd, hq, Limits.pullback.lift_snd]
  rw [h1, h2]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  rw [he']

end S_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2 (solution)
