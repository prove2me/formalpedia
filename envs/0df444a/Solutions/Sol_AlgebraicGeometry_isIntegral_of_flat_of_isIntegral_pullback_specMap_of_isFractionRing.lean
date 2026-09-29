-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c2350abb-290e-5e1d-b92e-5b3bd7eb3448

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] [IsDomain A] (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f]
    [IsIntegral ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap A L))))] :
    IsIntegral X := by
  classical
  set g := Spec.map (CommRingCat.ofHom (algebraMap A L)) with hg
  set pr := pullback.fst f g with hpr

  haveI : QuasiCompact g := inferInstance
  haveI : IsDominant g := by
    refine ⟨?_⟩
    show DenseRange (PrimeSpectrum.comap (algebraMap A L))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro a ha
    rw [RingHom.mem_ker] at ha
    have : a = 0 := (IsFractionRing.injective A L) (by rw [ha, map_zero])
    rw [this]; exact Ideal.zero_mem _
  haveI : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isDominant g

  haveI : IsSchemeTheoreticallyDominant pr := IsSchemeTheoreticallyDominant.pullbackFst f g
  haveI : QuasiCompact pr := inferInstance
  haveI : IsDominant pr := inferInstance

  haveI : IsReduced X := IsSchemeTheoreticallyDominant.isReduced pr

  haveI : IrreducibleSpace X := by
    have hirr : IsIrreducible (Set.range pr.base) := by
      have := (IrreducibleSpace.isIrreducible_univ (↑(pullback f g))).image pr.base pr.base.hom.continuous.continuousOn
      rwa [Set.image_univ] at this
    have hcl : closure (Set.range pr.base) = Set.univ := pr.denseRange.closure_range
    have := hirr.closure
    rw [hcl] at this
    exact (irreducibleSpace_def _).mpr this
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end S_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing (solution)
