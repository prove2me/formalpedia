-- Prove2me | Definitions.Def_TC433_Algebra_Lie_E7_Minuscule_PointsFunctor_dbbea450d7
-- name    : TC433_Algebra_Lie_E7_Minuscule_PointsFunctor_dbbea450d7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:09:50.84654+00:00
-- url     : https://prove2.me/theorems/3ad6b388-55ea-4c1a-bd15-b8e36b64cc80
-- title:
--   TauCeti: Algebra / Lie / E7 / Minuscule / PointsFunctor
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.E7.Minuscule.PointsFunctor for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/E7/Minuscule/PointsFunctor.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Scheme_ToralClosure_Points_0f7296c48f
public import Definitions.Def_TC433_Algebra_Lie_E7_Minuscule_Carrier_84b7a3afcf

/-!
# Presented points of the minuscule E₇ carrier

`TauCeti.E7Minuscule.pointsPresentation` presents the carrier's matrix points by its defining
integral Hopf ideal. The shared `GeneralLinear.IntegralPointsPresentation` API supplies maps
of value rings, their functoriality, and the representing equivalence with quotient-algebra
points. This file proves that those maps preserve the pinned root subgroups and weight torus.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  Sections 1.15 and 1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.E7Minuscule

universe v v'

noncomputable section

/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    TauCeti.GeneralLinear.IntegralPointsPresentation 56 definingIdeal A where
  val := points A
  property := points_def A

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem map_rootSubgroupPoints (f : A →+* B) (k : Fin 7 ⊕ Fin 7)
    (u : Multiplicative A) :
    (pointsPresentation A).map (pointsPresentation B) f (rootSubgroupPoints k A u) =
      rootSubgroupPoints k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralRootSubgroupPoints
      (e := TauCeti.serreRootGenerator (CartanMatrix.E 7))
      (h := TauCeti.serreH ℚ (CartanMatrix.E 7)) (ρ := rep) (M := lattice.toAddSubgroup)
      (hM := rep_kostantForm_mem_lattice) (hnil := isNilpotent_rep_serreRootGenerator)
      (b := latticeBasis) (wt := TauCeti.DynkinType.e7MinusculeWeight) f k u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints] using h

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin 7 → Aˣ) :
    (pointsPresentation A).map (pointsPresentation B) f (weightTorusPoints A s) =
      weightTorusPoints B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralWeightTorusPoints
      (e := TauCeti.serreRootGenerator (CartanMatrix.E 7))
      (h := TauCeti.serreH ℚ (CartanMatrix.E 7)) (ρ := rep) (M := lattice.toAddSubgroup)
      (hM := rep_kostantForm_mem_lattice) (hnil := isNilpotent_rep_serreRootGenerator)
      (b := latticeBasis) (wt := TauCeti.DynkinType.e7MinusculeWeight) f s)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints] using h

end

end TauCeti.E7Minuscule


