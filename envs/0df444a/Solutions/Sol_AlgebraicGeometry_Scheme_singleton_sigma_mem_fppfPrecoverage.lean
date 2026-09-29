-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.singleton_sigma_mem_fppfPrecoverage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/085c2403-7ec6-5ab0-bd6b-e5f673b0e5bf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : CommRingCat.{u}} {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u}) (φ : ∀ i, R ⟶ A i)
    (h : Presieve.ofArrows (fun i => Spec (A i)) (fun i => Spec.map (φ i)) ∈ Scheme.fppfPrecoverage (Spec R)) :
    Presieve.singleton (Spec.map (CommRingCat.ofHom (RingHom.pi fun i => (φ i).hom))) ∈
      Scheme.fppfPrecoverage (Spec R) := by
  classical
  change Presieve.ofArrows _ _ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) (Spec R) at h
  rw [Scheme.ofArrows_mem_precoverage_iff] at h
  obtain ⟨hsurj, hP⟩ := h
  set F : Spec (CommRingCat.of (Π i, A i)) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (RingHom.pi fun i => (φ i).hom)) with hF

  have hcomp : sigmaSpec A ≫ F = Sigma.desc (fun i => Spec.map (φ i)) := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [ι_sigmaSpec_assoc, Sigma.ι_desc, hF, ← Spec.map_comp]
    rfl
  change Presieve.singleton F ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) (Spec R)
  rw [Scheme.singleton_mem_precoverage_iff]
  refine ⟨fun s => ?_, ?_, ?_⟩
  · obtain ⟨i, y, rfl⟩ := hsurj s
    refine ⟨(Sigma.ι (fun i => Spec (A i)) i ≫ sigmaSpec A).base y, ?_⟩
    change ((Sigma.ι (fun i => Spec (A i)) i ≫ sigmaSpec A) ≫ F).base y = _
    rw [Category.assoc, hcomp, Sigma.ι_desc]
  · have : Flat (Sigma.desc fun i => Spec.map (φ i)) := IsZariskiLocalAtSource.sigmaDesc fun i => (hP i).1
    rw [← hcomp] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @Flat (sigmaSpec A) F).mp this
  · have : LocallyOfFinitePresentation (Sigma.desc fun i => Spec.map (φ i)) :=
      IsZariskiLocalAtSource.sigmaDesc fun i => (hP i).2
    rw [← hcomp] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFinitePresentation (sigmaSpec A) F).mp this

end S_AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage (solution)
