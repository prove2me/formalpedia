-- Prove2me | solution 1 for AlgebraicGeometry.IsFinite.of_isProper_of_finite_preimage_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/16eeef9d-b7f0-5da0-a2a9-05eb54be92d6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsFinite_of_isProper_of_finite_preimage_closedPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hfin : (f.base ⁻¹' {(IsLocalRing.closedPoint R : PrimeSpectrum R)}).Finite) :
    IsFinite f := by
  classical

  have hqf : ∀ x : X, f.base x = IsLocalRing.closedPoint R → f.QuasiFiniteAt x := by
    intro x hx
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    haveI : Finite ↥(f.fiber (f.base x)) := by
      haveI : Finite ↥(f.base ⁻¹' {f.base x}) := by rw [hx]; exact hfin.to_subtype
      exact Finite.of_equiv _ (f.fiberHomeo (f.base x)).toEquiv.symm
    haveI : LocallyOfFiniteType (f.fiberToSpecResidueField (f.base x)) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    haveI hg : LocallyQuasiFinite (f.fiberToSpecResidueField (f.base x)) :=
      LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => Set.toFinite _
    have hd := (f.fiberToSpecResidueField (f.base x)).isDiscrete_preimage_singleton
      ((f.fiberToSpecResidueField (f.base x)).base (f.asFiber x))
    have huniv : (f.fiberToSpecResidueField (f.base x)).base ⁻¹'
        {(f.fiberToSpecResidueField (f.base x)).base (f.asFiber x)} = Set.univ :=
      Set.eq_univ_of_forall fun z => Subsingleton.elim _ _
    rw [huniv, isDiscrete_univ_iff] at hd
    exact isOpen_discrete _

  have htop : f.quasiFiniteLocus = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_contra hxU
    have hZ : IsClosed ((f.quasiFiniteLocus : Set X)ᶜ) := f.quasiFiniteLocus.2.isClosed_compl
    have hfZ : IsClosed (f.base '' (f.quasiFiniteLocus : Set X)ᶜ) := f.isClosedMap _ hZ
    have hmem : f.base x ∈ f.base '' (f.quasiFiniteLocus : Set X)ᶜ := ⟨x, hxU, rfl⟩
    have hcl : IsLocalRing.closedPoint R ∈ f.base '' (f.quasiFiniteLocus : Set X)ᶜ :=
      (IsLocalRing.specializes_closedPoint (f.base x)).mem_closed hfZ hmem
    obtain ⟨z, hz, hzc⟩ := hcl
    exact hz (hqf z hzc)
  haveI : LocallyQuasiFinite f := (Scheme.Hom.quasiFiniteLocus_eq_top_iff f).mp htop
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end S_AlgebraicGeometry_IsFinite_of_isProper_of_finite_preimage_closedPoint
end P2MW
export P2MW.S_AlgebraicGeometry_IsFinite_of_isProper_of_finite_preimage_closedPoint (solution)
