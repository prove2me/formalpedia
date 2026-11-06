-- Prove2me | Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_GeckLattice_Torus_3c5676c66e
-- name    : TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_GeckLattice_Torus_3c5676c66e
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:24:34.64471+00:00
-- url     : https://prove2.me/theorems/c0120493-bc2f-4716-8f83-f40141042d08
-- title:
--   TauCeti: LinearAlgebra / RootSystem / SimplyConnectedRootDatum / GeckLattice / Torus
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Torus for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/GeckLattice/Torus.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Scheme_ToralClosure_Torus_77a686f2a5
public import Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_GeckLattice_GroupScheme_122e608608
public import Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_GeckLattice_WeightSpan_5551871195
import Definitions.Def_TC433_CategoryTheory_Comma_Over_f656a0be87

/-!
# The split torus in the Geck carrier

The represented Geck lattice of a valid Dynkin type `t` gives a morphism from the split torus
of rank `t.rank` into the explicit Kostant toral-closure carrier
`TauCeti.DynkinType.geckGroupScheme`. This file proves that the morphism is a closed immersion
whenever the Geck weights span the full character lattice.

The proof is deliberately conditional in the general case. The Geck weights generate exactly the
root lattice, which is usually a proper sublattice of the weight lattice used by the simply
connected root datum. Consequently the represented torus need not embed in the Geck carrier for
an arbitrary Dynkin type. The spanning condition is known for the three unimodular exceptional
types `E₈`, `F₄`, and `G₂`, where the root and weight lattices coincide, and this file records
the resulting closed immersions explicitly.

This supplies the intended closed split-torus component of a future pinning for those
three types. Proving that it is maximal, constructing a compatible Borel, identifying the carrier
as split reductive with the stated root datum, and constructing full-weight admissible lattices for
the remaining types are separate Layer 9 steps in the ReductiveGroups roadmap. The resulting
completed carriers are consumed by milestone L0 of the CFSGStatement roadmap.

## Main declarations

* `TauCeti.DynkinType.isClosedImmersion_geckWeightTorus_of_span_eq_top`: the Geck weight torus is
  a closed immersion under the exact character-spanning hypothesis.
* `TauCeti.DynkinType.geckWeightTorusClosedSubgroup`: the corresponding closed subgroup scheme of
  the Geck carrier.
* `TauCeti.DynkinType.isClosedImmersion_geckWeightTorus_E8`, and the analogous `F4` and `G2`
  instances: the spanning hypothesis holds for the three unimodular exceptional types.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.1 and 8.2.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- Reindexing the Geck coordinates by a finite ordinal does not change the integral span of their
weights. This relates the intrinsic `GeckIndex`-indexed weight calculation to the finite basis
used to represent the group scheme in `GL`. -/
private theorem span_range_geckWeightFin_eq_span_range_geckWeight :
    Submodule.span ℤ (Set.range (t.geckWeightFin ht)) =
      Submodule.span ℤ (Set.range (t.geckWeight ht)) := by
  exact congrArg (Submodule.span ℤ)
    ((Fintype.equivFin (t.GeckIndex ht)).symm.surjective.range_comp (t.geckWeight ht))

/-- **Full character span makes the represented Geck torus a closed subgroup of the Geck
carrier.** The hypothesis is exact: it says that the characters occurring in the Geck lattice
generate the character lattice of the source split torus. -/
theorem isClosedImmersion_geckWeightTorus_of_span_eq_top
    (hwt : Submodule.span ℤ (Set.range (t.geckWeight ht)) = ⊤) :
    IsClosedImmersion (t.geckWeightTorus ht).hom.hom.left := by
  have hwtFin : Submodule.span ℤ (Set.range (t.geckWeightFin ht)) = ⊤ := by
    rw [t.span_range_geckWeightFin_eq_span_range_geckWeight ht]
    exact hwt
  let c :=
    (UniversalEnvelopingAlgebra.kostantWeightTorusToToral
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)).hom.hom.left
  let e := (eqToHom (t.geckGroupScheme_def ht).symm).hom.hom.left
  have hc : IsClosedImmersion c :=
    UniversalEnvelopingAlgebra.isClosedImmersion_kostantWeightTorusToToral
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) hwtFin
  have hce : IsClosedImmersion (c ≫ e) :=
    (MorphismProperty.cancel_right_of_respectsIso _ c e).2 hc
  rw [geckWeightTorus_def]
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  exact hce

/-- The closed split torus in the Geck carrier supplied by a full character-spanning family of
Geck weights. No maximality or reductivity statement is part of this definition. -/
def geckWeightTorusClosedSubgroup
    (hwt : Submodule.span ℤ (Set.range (t.geckWeight ht)) = ⊤) :
    ClosedSubgroupScheme (t.geckGroupScheme ht) :=
  have _ := t.isClosedImmersion_geckWeightTorus_of_span_eq_top ht hwt
  ClosedSubgroupScheme.mk (t.geckWeightTorus ht)

/-- The underlying subobject of the closed Geck weight torus is represented by the defining
weight-torus morphism. -/
@[simp]
theorem coe_geckWeightTorusClosedSubgroup
    (hwt : Submodule.span ℤ (Set.range (t.geckWeight ht)) = ⊤) :
    let _ := t.isClosedImmersion_geckWeightTorus_of_span_eq_top ht hwt
    (t.geckWeightTorusClosedSubgroup ht hwt).1 = Subobject.mk (t.geckWeightTorus ht) := by
  have _ := t.isClosedImmersion_geckWeightTorus_of_span_eq_top ht hwt
  rw [geckWeightTorusClosedSubgroup]
  exact ClosedSubgroupScheme.coe_mk _

/-! ## The unimodular exceptional types -/

/-- **The represented Geck weight torus of type `E₈` is a closed immersion.** The type `E₈` roots
span the full weight lattice because its Cartan matrix is unimodular. -/
instance isClosedImmersion_geckWeightTorus_E8 (ht : E8.Valid) :
    IsClosedImmersion (E8.geckWeightTorus ht).hom.hom.left := by
  exact E8.isClosedImmersion_geckWeightTorus_of_span_eq_top ht
    (span_range_geckWeight_E8_eq_top ht)

/-- **The represented Geck weight torus of type `F₄` is a closed immersion.** -/
instance isClosedImmersion_geckWeightTorus_F4 (ht : F4.Valid) :
    IsClosedImmersion (F4.geckWeightTorus ht).hom.hom.left := by
  exact F4.isClosedImmersion_geckWeightTorus_of_span_eq_top ht
    (span_range_geckWeight_F4_eq_top ht)

/-- **The represented Geck weight torus of type `G₂` is a closed immersion.** -/
instance isClosedImmersion_geckWeightTorus_G2 (ht : G2.Valid) :
    IsClosedImmersion (G2.geckWeightTorus ht).hom.hom.left := by
  exact G2.isClosedImmersion_geckWeightTorus_of_span_eq_top ht
    (span_range_geckWeight_G2_eq_top ht)

end

end TauCeti.DynkinType


