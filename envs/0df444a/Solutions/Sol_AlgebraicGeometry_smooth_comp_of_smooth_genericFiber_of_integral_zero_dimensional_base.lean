-- Prove2me | solution 1 for AlgebraicGeometry.smooth_comp_of_smooth_genericFiber_of_integral_zero_dimensional_base
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T01:52:59.423904+00:00
-- url     : https://prove2.me/submissions/3eb184ff-7331-4581-bfe7-d6cfe395283c

import Mathlib

universe u
noncomputable section
set_option linter.style.haveILetI false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponAlterationBaseCases

lemma isIso_of_integral_subsingleton_over_algClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    [IsIntegral X] [Subsingleton X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    IsIso π := by
  letI : IsFinite π := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  let f : Spec Γ(X, ⊤) ⟶ Spec (.of K) := X.isoSpec.inv ≫ π
  let r := Spec.preimage f
  have hfinite : r.hom.Finite := (IsFinite.SpecMap_iff r).mp (by
    rw [Spec.map_preimage]
    infer_instance)
  letI := r.hom.toAlgebra
  letI : Module.Finite K Γ(X, ⊤) := hfinite
  have hbij : Function.Bijective r :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
  letI : IsIso r := (ConcreteCategory.isIso_iff_bijective r).mpr hbij
  have : IsIso f := by
    rw [← Spec.map_preimage f]
    infer_instance
  have hπ : π = X.isoSpec.hom ≫ f := by simp [f]
  rw [hπ]
  infer_instance

lemma subsingleton_of_dimension_le_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 0) : Subsingleton X := by
  letI : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  letI : DiscreteTopology X := inferInstance
  have hcl : closure ({genericPoint X} : Set X) = {genericPoint X} :=
    (isClosed_discrete _).closure_eq
  have hall : ({genericPoint X} : Set X) = Set.univ := hcl.symm.trans (genericPoint_spec X)
  refine ⟨fun x y => ?_⟩
  have hx : x = genericPoint X := by
    exact Set.mem_singleton_iff.mp (hall.symm ▸ Set.mem_univ x)
  have hy : y = genericPoint X := by
    exact Set.mem_singleton_iff.mp (hall.symm ▸ Set.mem_univ y)
  exact hx.trans hy.symm


end PhilipponAlterationBaseCases


set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponFieldModelProperties

lemma fpqc_fieldMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  haveI : Surjective b := by
    constructor
    intro x
    exact ⟨(⊥ : PrimeSpectrum K), Subsingleton.elim _ _⟩
  haveI : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩


end PhilipponFieldModelProperties


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponZeroDimensionalBaseSmooth

/-- Over an integral zero-dimensional finite-type base over an algebraically
closed field, smoothness of the actual generic fibre is global smoothness. -/
theorem smooth_of_genericFiber_of_base_dimension_le_zero
    (K : Type u) [Field K] [IsAlgClosed K] {N G : Scheme.{u}} [IsIntegral N]
    (πN : N ⟶ Spec (.of K)) [LocallyOfFiniteType πN]
    (f : G ⟶ N) (hN : topologicalKrullDim N ≤ 0)
    (hs : Smooth (f.fiberToSpecResidueField (genericPoint N))) : Smooth (f ≫ πN) := by
  letI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian πN
  letI : Subsingleton N := PhilipponAlterationBaseCases.subsingleton_of_dimension_le_zero hN
  letI : IsIso πN := PhilipponAlterationBaseCases.isIso_of_integral_subsingleton_over_algClosed πN
  let b := N.fromSpecResidueField (genericPoint N)
  let γ := Spec.preimage (b ≫ πN)
  letI : Algebra K (N.residueField (genericPoint N)) := γ.hom.toAlgebra
  have hfield := PhilipponFieldModelProperties.fpqc_fieldMap K (N.residueField (genericPoint N))
  change (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (Spec.map γ) at hfield
  rw [Spec.map_preimage] at hfield
  have hb : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) b :=
    (MorphismProperty.cancel_right_of_respectsIso
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) b πN).mp hfield
  haveI : Smooth f := MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback f b).flip hb hs
  infer_instance


end PhilipponZeroDimensionalBaseSmooth

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {N G : Scheme.{u}} [IsIntegral N]
    (πN : N ⟶ Spec (.of K)) [LocallyOfFiniteType πN]
    (f : G ⟶ N) (hN : topologicalKrullDim N ≤ 0)
    (hs : Smooth (f.fiberToSpecResidueField (genericPoint N))) : Smooth (f ≫ πN) := by
  exact PhilipponZeroDimensionalBaseSmooth.smooth_of_genericFiber_of_base_dimension_le_zero K πN f hN hs
