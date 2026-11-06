-- Prove2me | Definitions.Def_TC433_Algebra_HopfAlgebra_GroupLike_FiniteGeneration_ec094f887e
-- name    : TC433_Algebra_HopfAlgebra_GroupLike_FiniteGeneration_ec094f887e
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:22:23.878184+00:00
-- url     : https://prove2.me/theorems/a9def95a-3d26-48a8-9cb5-790d492ff5a0
-- title:
--   TauCeti: Algebra / HopfAlgebra / GroupLike / FiniteGeneration
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.HopfAlgebra.GroupLike.FiniteGeneration for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/HopfAlgebra/GroupLike/FiniteGeneration.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Definitions.Def_TC433_Algebra_Coalgebra_Subcoalgebra_GroupLike_8c2f7fbf8f

import Definitions.Def_TC433_Algebra_Bialgebra_GroupLike_Evaluation_5e43193f37

/-!
# Finite generation of group-like elements

If a finite-type Hopf algebra over a nontrivial commutative ring is spanned by linearly independent
group-like elements, then its group of group-like elements is finitely generated. Indeed,
evaluation identifies the group algebra on the group-like elements with the original Hopf algebra.
Finite type transports across this equivalence, and a group algebra over a nontrivial commutative
ring is of finite type exactly when its indexing group is finitely generated.

The result does not require the Hopf algebra to be commutative. Over a domain, linear independence
is automatic when the carrier is torsion-free.

## Main declarations

* `TauCeti.GroupLike.fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top`: finite
  generation when the group-like elements are linearly independent and span.
* `TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top`: the domain specialization for
  a torsion-free carrier.

## References

See Milne, *Algebraic Groups*, Proposition 4.23 and Theorems 12.8--12.9.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

universe u v

namespace GroupLike

/-- The linearly independent group-like elements spanning a finite-type Hopf algebra over a
nontrivial commutative ring form a finitely generated group.

The spanning hypothesis is expressed intrinsically through the subcoalgebra spanned by all
group-like elements. -/
theorem fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top
    (R : Type u) (H : Type v) [CommRing R] [Nontrivial R] [Semiring H] [HopfAlgebra R H]
    (hfinite : Algebra.FiniteType R H)
    (hlinear : LinearIndependent R (_root_.GroupLike.val (R := R) (A := H)))
    (hspan : Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ = ⊤) :
    Group.FG (_root_.GroupLike R H) := by
  have hlinearSpan :
      Submodule.span R
          (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤ :=
    (evaluationBialgHom_surjective_iff_span_eq_top R H).1
      ((evaluationBialgHom_surjective_iff_groupLikeSetSpan_eq_top R H).2 hspan)
  apply (MonoidAlgebra.finiteType_iff_group_fg
    (R := R) (G := _root_.GroupLike R H)).1
  exact Algebra.FiniteType.equiv hfinite
    (evaluationBialgEquivOfLinearIndependentOfSpanEqTop R H
      hlinear hlinearSpan).toAlgEquiv.symm

/-- The group-like elements spanning a finite-type Hopf algebra over a domain form a finitely
generated group, provided the carrier is torsion-free over the base. -/
theorem fg_of_finiteType_of_groupLikeSetSpan_eq_top
    (R : Type u) (H : Type v) [CommRing R] [IsDomain R] [Ring H] [HopfAlgebra R H]
    [Module.IsTorsionFree R H] (hfinite : Algebra.FiniteType R H)
    (hspan : Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ = ⊤) :
    Group.FG (_root_.GroupLike R H) :=
  fg_of_finiteType_of_linearIndependent_of_groupLikeSetSpan_eq_top R H hfinite
    (linearIndep_groupLikeVal (R := R) (A := H)) hspan

end GroupLike

end TauCeti


