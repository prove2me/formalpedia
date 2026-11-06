-- Prove2me | Definitions.Def_TC433_Algebra_Lie_E6_DoubledMinuscule_PointsFunctor_e543f1f956
-- name    : TC433_Algebra_Lie_E6_DoubledMinuscule_PointsFunctor_e543f1f956
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:10:10.398985+00:00
-- url     : https://prove2.me/theorems/c7725045-f0fd-4c7b-b752-4f31cc6e028b
-- title:
--   TauCeti: Algebra / Lie / E6 / DoubledMinuscule / PointsFunctor
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.E6.DoubledMinuscule.PointsFunctor for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/E6/DoubledMinuscule/PointsFunctor.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Scheme_ToralClosure_Points_0f7296c48f
public import Definitions.Def_TC433_Algebra_Lie_E6_DoubledMinuscule_GroupScheme_7f2fc5f8f4

/-!
# Presented points of the doubled minuscule E₆ carrier

`TauCeti.E6DoubledMinuscule.pointsPresentation` presents the carrier's matrix points by its defining
integral Hopf ideal. The shared `GeneralLinear.IntegralPointsPresentation` API supplies maps
of value rings, their functoriality, and the representing equivalence with quotient-algebra
points. This file proves that those maps preserve the pinned root subgroups and weight torus.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  Sections 1.15 and 1.17.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2, for the doubled minuscule realization.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.E6DoubledMinuscule

universe v v'

noncomputable section

/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    TauCeti.GeneralLinear.IntegralPointsPresentation 54 definingIdeal A where
  val := points A
  property := points_def A

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem map_rootSubgroupPoints (f : A →+* B) (k : Fin 6 ⊕ Fin 6)
    (u : Multiplicative A) :
    (pointsPresentation A).map (pointsPresentation B) f (rootSubgroupPoints k A u) =
      rootSubgroupPoints k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  have hh := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralRootSubgroupPoints
      (e := TauCeti.serreRootGenerator (Matrix.transpose (CartanMatrix.E 6)))
      (h := TauCeti.serreH ℚ (Matrix.transpose (CartanMatrix.E 6))) (ρ := rep)
      (M := lattice.toAddSubgroup) (hM := rep_kostantForm_mem_lattice)
      (hnil := isNilpotent_rep_serreRootGenerator) (b := matrixBasis)
      (wt := matrixWeight) f k u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at hh
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints] using hh

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin 6 → Aˣ) :
    (pointsPresentation A).map (pointsPresentation B) f (weightTorusPoints A s) =
      weightTorusPoints B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  have hh := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralWeightTorusPoints
      (e := TauCeti.serreRootGenerator (Matrix.transpose (CartanMatrix.E 6)))
      (h := TauCeti.serreH ℚ (Matrix.transpose (CartanMatrix.E 6))) (ρ := rep)
      (M := lattice.toAddSubgroup) (hM := rep_kostantForm_mem_lattice)
      (hnil := isNilpotent_rep_serreRootGenerator) (b := matrixBasis)
      (wt := matrixWeight) f s)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at hh
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints] using hh

end

end TauCeti.E6DoubledMinuscule


