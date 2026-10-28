-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.smoothOfRelativeDimension_of_fiber_dimension_of_preconnectedSpace
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T04:04:18.415454+00:00
-- url     : https://prove2.me/submissions/94f2a3df-5d2c-432a-bfb7-53b7f882c520

import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace

universe u
noncomputable section
set_option linter.style.haveILetI false


set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponIntegralDimension

lemma ring_dimension_le_of_integral {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsIntegral R S := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro I J h
  exact Ideal.IsIntegral.comap_lt_comap (R := R) h

lemma dimension_eq_iSup_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [show topologicalKrullDim X = Order.krullDim X from
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  simp_rw [Order.krullDim_eq_iSup_coheight, ringKrullDim_stalk_eq_coheight]

lemma stalk_dimension_le {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [dimension_eq_iSup_stalk]
  exact le_iSup (fun x : X => ringKrullDim (X.presheaf.stalk x)) x


end PhilipponIntegralDimension


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponSmoothRelativeDimension

lemma dimension_eq_of_smoothOfRelativeDimension
    (K : Type u) [Field K] {X : Scheme.{u}} [Nonempty X]
    (f : X ⟶ Spec (.of K)) (d : ℕ) [SmoothOfRelativeDimension d f] :
    topologicalKrullDim X = (d : WithBot ℕ∞) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth d f
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, _hx, hclosed⟩ := nonempty_inter_closedPoints
    (X := X) Set.univ_nonempty isOpen_univ.isLocallyClosed
  apply le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le f d)
  calc
    (d : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) :=
      (SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed K f d x hclosed).symm
    _ ≤ topologicalKrullDim X := PhilipponIntegralDimension.stalk_dimension_le x

/-- On a preconnected smooth source, the dimension of any one nonempty
actual fibre determines the relative dimension of the whole morphism. -/
theorem smoothOfRelativeDimension_of_fiber_dimension
    {X Y : Scheme.{u}} [PreconnectedSpace X] (f : X ⟶ Y) [Smooth f]
    (y : Y) [Nonempty (f.fiber y)] (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞)) :
    SmoothOfRelativeDimension d f := by
  obtain ⟨n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace f
  letI : SmoothOfRelativeDimension n f := hn
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  letI : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd f (Y.fromSpecResidueField y) inferInstance
  have hF := dimension_eq_of_smoothOfRelativeDimension
    (Y.residueField y) (f.fiberToSpecResidueField y) n
  have he : (n : WithBot ℕ∞) = (d : WithBot ℕ∞) := hF.symm.trans hdim
  have hnd : n = d := by exact_mod_cast he
  cases hnd
  exact hn

end PhilipponSmoothRelativeDimension

theorem solution
    {X Y : Scheme.{u}} [PreconnectedSpace X] (f : X ⟶ Y) [Smooth f]
    (y : Y) [Nonempty (f.fiber y)] (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞)) :
    SmoothOfRelativeDimension d f := by
  exact PhilipponSmoothRelativeDimension.smoothOfRelativeDimension_of_fiber_dimension f y d hdim
