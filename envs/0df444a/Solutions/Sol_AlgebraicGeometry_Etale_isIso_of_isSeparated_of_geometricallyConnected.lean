-- Prove2me | solution 1 for AlgebraicGeometry.Etale.isIso_of_isSeparated_of_geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T16:16:07.036756+00:00
-- url     : https://prove2.me/submissions/5f69db3b-4a6f-4941-a80d-ef9480a282e7

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace PhilipponEtaleConnectedIso

/-- A section with open and closed image fills every connected fibre. -/
lemma surjective_section_of_isClopen_range
    {X Y : Scheme.{u}} (p : X ⟶ Y) [GeometricallyConnected p]
    (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) (hc : IsClopen (Set.range s)) :
    Surjective s := by
  constructor
  intro x
  have hne : ((p ⁻¹' {p x}) ∩ Set.range s).Nonempty := by
    refine ⟨s (p x), ?_, ⟨p x, rfl⟩⟩
    change p (s (p x)) = p x
    change (s ≫ p) (p x) = p x
    rw [hs]
    rfl
  exact (p.isConnected_preimage_singleton (p x)).isPreconnected.subset_isClopen hc hne
    (show x ∈ p ⁻¹' {p x} by rfl)

/-- Separated étale morphisms with geometrically connected fibres are isomorphisms. -/
theorem isIso_of_etale_separated_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    [GeometricallyConnected f] : IsIso f := by
  let d := pullback.diagonal f
  let p := pullback.snd f f
  have hc : IsClopen (Set.range d) :=
    ⟨d.isClosedEmbedding.isClosed_range, d.isOpenEmbedding.isOpen_range⟩
  haveI : Surjective d := surjective_section_of_isClopen_range p d
    (pullback.diagonal_snd f) hc
  haveI : IsIso d := (isIso_iff_isOpenImmersion_and_surjective d).mpr
    ⟨inferInstance, inferInstance⟩
  haveI : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  haveI : IsOpenImmersion f := IsOpenImmersion.of_flat_of_mono f
  exact (isIso_iff_isOpenImmersion_and_surjective f).mpr ⟨inferInstance, inferInstance⟩

/-- The relative-dimension-zero branch of a proper geometrically connected smooth family. -/
theorem isIso_of_smoothOfRelativeDimension_zero_proper_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 0 f] [IsProper f]
    [GeometricallyConnected f] : IsIso f := by
  haveI : Etale f := (Etale.iff_smoothOfRelativeDimension_zero f).mpr inferInstance
  exact isIso_of_etale_separated_geometricallyConnected f

end PhilipponEtaleConnectedIso

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    [GeometricallyConnected f] : IsIso f := by
  exact PhilipponEtaleConnectedIso.isIso_of_etale_separated_geometricallyConnected f
