-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_ideal_le_primeIdealOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:29.637017+00:00
-- url     : https://prove2.me/submissions/58604fc9-229e-4526-b943-0bccc98d699f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
private theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (g : Γ(X, U)) :
    x ∈ X.basicOpen g ↔ g ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : hU.fromSpec ⁻¹ᵁ (X.basicOpen g) = PrimeSpectrum.basicOpen g :=
    hU.fromSpec_preimage_basicOpen g
  constructor
  · intro h
    rw [← h1] at h
    have h3 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ (X.basicOpen g) := h
    rw [h2] at h3
    exact (PrimeSpectrum.mem_basicOpen g _).mp h3
  · intro h
    have h3 : hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen g :=
      (PrimeSpectrum.mem_basicOpen g _).mpr h
    rw [← h2] at h3
    have h4 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen g := h3
    rwa [h1] at h4
end AlgebraicGeometry.Scheme.IdealSheafData
namespace FunctorialResolution.Blowup
end FunctorialResolution.Blowup
namespace AlgebraicGeometry.Scheme.IdealSheafData
end AlgebraicGeometry.Scheme.IdealSheafData
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    x ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hx,
    Scheme.mem_zeroLocus_iff]
  constructor
  · intro h
    rw [SetLike.le_def]
    intro f hf
    have hb := h f hf
    rw [mem_basicOpen_iff_notMem_primeIdealOf hU hx f] at hb
    exact not_not.mp hb
  · intro h f hf
    rw [mem_basicOpen_iff_notMem_primeIdealOf hU hx f]
    exact not_not.mpr (h hf)
end AlgebraicGeometry.Scheme.IdealSheafData
