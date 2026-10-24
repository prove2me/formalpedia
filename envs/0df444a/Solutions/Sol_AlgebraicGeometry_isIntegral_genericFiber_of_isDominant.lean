-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_genericFiber_of_isDominant
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T20:31:00.935965+00:00
-- url     : https://prove2.me/submissions/ace12766-2187-4727-9ef0-352511cfe7b6

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace PhilipponAlterationProjection

/-- A preimmersion into a field spectrum has reduced source, including the empty source. -/
lemma isReduced_of_preimmersion_to_field
    (K : Type u) [Field K] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of K)) [IsPreimmersion f] : IsReduced Z := by
  haveI (z : Z) : _root_.IsReduced (Z.presheaf.stalk z) := by
    have hfield : IsField ((Spec (.of K)).presheaf.stalk (f z)) :=
      isField_stalk_of_closure_mem_irreducibleComponents (Spec (.of K)) (f z) (by
        rw [Subsingleton.elim (f z) (genericPoint (Spec (.of K)))]
        simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
        exact genericPoint_spec (Spec (.of K)))
    letI : Field ((Spec (.of K)).presheaf.stalk (f z)) := hfield.toField
    let e := RingEquiv.ofBijective (f.stalkMap z).hom
      ⟨(f.stalkMap z).hom.injective, f.stalkMap_surjective z⟩
    exact isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_isReduced_stalk Z

/-- Preimmersions have geometrically reduced fibres. -/
lemma geometricallyReduced_of_preimmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] : GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  haveI : IsPreimmersion snd :=
    MorphismProperty.of_isPullback h (inferInstance : IsPreimmersion f)
  exact isReduced_of_preimmersion_to_field K snd

/-- The canonical map from a local spectrum is flat. -/
lemma flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
  dsimp only [IsAffineOpen.fromSpecStalk]
  haveI : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    apply Flat.SpecMap_iff.mpr
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    letI := hU.isLocalization_stalk ⟨x, hx⟩
    change (algebraMap Γ(X, U) (X.presheaf.stalk x)).Flat
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
  infer_instance

/-- The generic-point residue-field inclusion into an integral scheme is flat. -/
lemma flat_fromSpecResidueField_genericPoint (Y : Scheme.{u}) [IsIntegral Y] :
    Flat (Y.fromSpecResidueField (genericPoint Y)) := by
  have hbij : Function.Bijective (Y.residue (genericPoint Y)) :=
    ⟨(Y.residue (genericPoint Y)).hom.injective, Y.residue_surjective _⟩
  letI : IsIso (Y.residue (genericPoint Y)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI := flat_fromSpecStalk Y (genericPoint Y)
  dsimp only [Scheme.fromSpecResidueField]
  infer_instance

/-- The generic fibre of a morphism between integral schemes is reduced. -/
lemma isReduced_genericFiber
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (f : X ⟶ Y) : IsReduced (f.fiber (genericPoint Y)) := by
  letI : Flat (Y.fromSpecResidueField (genericPoint Y)) := flat_fromSpecResidueField_genericPoint Y
  letI : GeometricallyReduced (Y.fromSpecResidueField (genericPoint Y)) :=
    geometricallyReduced_of_preimmersion (Y.fromSpecResidueField (genericPoint Y))
  haveI : Flat (f.fiberι (genericPoint Y)) := by
    dsimp only [Scheme.Hom.fiberι]
    exact MorphismProperty.pullback_fst f (Y.fromSpecResidueField (genericPoint Y))
      (flat_fromSpecResidueField_genericPoint Y)
  haveI : GeometricallyReduced (f.fiberι (genericPoint Y)) := by
    dsimp only [Scheme.Hom.fiberι]
    exact MorphismProperty.pullback_fst f (Y.fromSpecResidueField (genericPoint Y))
      (geometricallyReduced_of_preimmersion (Y.fromSpecResidueField (genericPoint Y)))
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (f.fiberι (genericPoint Y))

/-- A dominant morphism maps the generic point of an integral source to that of its target. -/
lemma genericPoint_eq_of_dominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  have hg : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using h
  exact hg.eq (genericPoint_spec Y)

/-- The generic fibre of a dominant morphism of integral schemes is irreducible. -/
lemma irreducibleSpace_genericFiber
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IrreducibleSpace (f.fiber (genericPoint Y)) := by
  let z : f.fiber (genericPoint Y) :=
    (f.fiberHomeo (genericPoint Y)).symm
      ⟨genericPoint X, genericPoint_eq_of_dominant f⟩
  have hz : f.fiberι (genericPoint Y) z = genericPoint X :=
    f.fiberι_fiberHomeo_symm (genericPoint Y) _
  have hgen : IsGenericPoint z (Set.univ : Set (f.fiber (genericPoint Y))) := by
    rw [isGenericPoint_iff_specializes]
    intro w
    simp only [Set.mem_univ, iff_true]
    apply (f.fiberι (genericPoint Y)).isEmbedding.isInducing.specializes_iff.mp
    rw [hz]
    exact genericPoint_specializes _
  exact (irreducibleSpace_def _).mpr hgen.isIrreducible

/-- The generic fibre of a dominant morphism of integral schemes is integral. -/
lemma isIntegral_genericFiber
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsIntegral (f.fiber (genericPoint Y)) := by
  letI := isReduced_genericFiber f
  letI := irreducibleSpace_genericFiber f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PhilipponAlterationProjection


theorem solution
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsIntegral (f.fiber (genericPoint Y)) := by
  exact PhilipponAlterationProjection.isIntegral_genericFiber f
