-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_isOpen_isIrreducible_nhd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/670f762b-3f5f-50f9-a143-cd020067bf1a

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_isOpen_isIrreducible_nhd
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SmoothUnibranchAux

theorem isOpen_connectedComponent_of_noetherianSpace {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  classical

  let F : Set (Set α) := {Z ∈ irreducibleComponents α | Disjoint Z (connectedComponent x)}
  have hF : F.Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
  have hcl : IsClosed (⋃ Z ∈ F, Z) :=
    hF.isClosed_biUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  have hcompl : (connectedComponent x)ᶜ = ⋃ Z ∈ F, Z := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    constructor
    · intro hz
      refine ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩, mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro w hwZ hwx
      apply hz
      have hsub : irreducibleComponent z ⊆ connectedComponent w :=
        (isIrreducible_irreducibleComponent.isConnected.isPreconnected).subset_connectedComponent hwZ
      rw [connectedComponent_eq hwx]
      exact hsub mem_irreducibleComponent
    · rintro ⟨Z, ⟨-, hZd⟩, hzZ⟩ hzx
      exact Set.disjoint_left.1 hZd hzZ hzx
  rw [← isClosed_compl_iff, hcompl]
  exact hcl

end SmoothUnibranchAux

open SmoothUnibranchAux in
theorem solution
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f] (y : ↥Y) :
    ∃ Ω : Y.Opens, y ∈ Ω ∧ IsIrreducible (Ω : Set ↥Y) := by

  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f

  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace ↥(U : Scheme.{u}) := noetherianSpace_of_isAffineOpen U hU

  let y' : ↥(U : Scheme.{u}) := ⟨y, hyU⟩

  let V : (U : Scheme.{u}).Opens := ⟨connectedComponent y', isOpen_connectedComponent_of_noetherianSpace y'⟩
  haveI : PreconnectedSpace ↥(V : Scheme.{u}) := Subtype.preconnectedSpace isPreconnected_connectedComponent
  haveI : Nonempty ↥(V : Scheme.{u}) := ⟨⟨y', mem_connectedComponent⟩⟩
  haveI : Smooth (V.ι ≫ U.ι ≫ f) := inferInstance
  haveI : IsIntegral (V : Scheme.{u}) := isIntegral_of_smooth_of_preconnectedSpace (V.ι ≫ U.ι ≫ f)

  refine ⟨U.ι ''ᵁ V, ⟨y', mem_connectedComponent, rfl⟩, ?_⟩
  show IsIrreducible (U.ι.base '' (V : Set ↥(U : Scheme.{u})))
  have hV : IsIrreducible (V : Set ↥(U : Scheme.{u})) := by
    have h := (IrreducibleSpace.isIrreducible_univ (X := ↥(V : Scheme.{u}))).image V.ι.base V.ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at h
  exact hV.image _ U.ι.continuous.continuousOn

end S_AlgebraicGeometry_Smooth_exists_isOpen_isIrreducible_nhd
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_isOpen_isIrreducible_nhd (solution)
