-- Prove2me | Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_LieAlgebra_Killing_4db8fcb848
-- name    : TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_LieAlgebra_Killing_4db8fcb848
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:28:57.31165+00:00
-- url     : https://prove2.me/theorems/85e273d6-d890-482c-9f60-c1fa06be70a5
-- title:
--   TauCeti: LinearAlgebra / RootSystem / SimplyConnectedRootDatum / LieAlgebra / Killing
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Killing for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/LieAlgebra/Killing.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_Killing_BaseChange_6e95eef19e
public import Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_LieAlgebra_BaseChange_76443a8a61

/-!
# The Killing form of the pinned Dynkin-type Lie algebra

For a valid Dynkin type `t`, `TauCeti.DynkinType.lieAlgebra t ht` is the explicit rational
matrix Lie algebra obtained by applying Geck's construction to
`TauCeti.DynkinType.simplyConnectedRootDatum t ht`. This file proves that its Killing form is
nondegenerate.

Mathlib proves that Geck's Lie algebra has trivial solvable radical over an algebraically closed
field, hence has nondegenerate Killing form in characteristic zero. The rational carrier itself
does not satisfy the algebraic-closure hypothesis. We therefore extend scalars to
`AlgebraicClosure ℚ`, identify that scalar extension with Geck's construction over the extended
root system via `TauCeti.DynkinType.lieAlgebraBaseChangeEquiv`, and descend nondegeneracy along
`ℚ → AlgebraicClosure ℚ` using `TauCeti.isKilling_of_isKilling_baseChange`.

The result is installed as an instance because the root-space and Chevalley-system APIs take
`LieAlgebra.IsKilling` as a typeclass assumption. The final instance transports it to
`TauCeti.DynkinType.lieAlgebraBaseChange t ht K` over every integral domain carrying a rational
algebra structure; algebraic closedness is needed only once, in the descent argument over `ℚ`.

## Main declarations

* `TauCeti.DynkinType.instIsKillingLieAlgebra`: the rational pinned Dynkin-type Lie algebra has
  nondegenerate Killing form.
* `TauCeti.DynkinType.instIsKillingLieAlgebraBaseChange`: its explicit Geck realization after
  extension to any rational integral domain also has nondegenerate Killing form.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247, Lemma 4.3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §5.1.

-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.DynkinType

open LieAlgebra
open scoped TensorProduct

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **The pinned rational Lie algebra of a valid Dynkin type has nondegenerate Killing form.** -/
instance instIsKillingLieAlgebra : IsKilling ℚ (t.lieAlgebra ht) := by
  let K := AlgebraicClosure ℚ
  let e : (K ⊗[ℚ] t.lieAlgebra ht) ≃ₗ⁅K⁆ t.lieAlgebraBaseChange ht K :=
    t.lieAlgebraBaseChangeEquiv ht K
  have hradical : HasTrivialRadical K (t.lieAlgebraBaseChange ht K) := by
    rw [lieAlgebraBaseChange_def]
    infer_instance
  let _ : HasTrivialRadical K (t.lieAlgebraBaseChange ht K) := hradical
  have hbase : IsKilling K (t.lieAlgebraBaseChange ht K) := inferInstance
  let _ : IsKilling K (t.lieAlgebraBaseChange ht K) := hbase
  have hscalar : IsKilling K (K ⊗[ℚ] t.lieAlgebra ht) := e.symm.isKilling
  let _ : IsKilling K (K ⊗[ℚ] t.lieAlgebra ht) := hscalar
  exact TauCeti.isKilling_of_isKilling_baseChange ℚ K (t.lieAlgebra ht)

/-- **Every characteristic-zero scalar extension of the pinned Dynkin-type Lie algebra has
nondegenerate Killing form.** This is stated for the explicit Geck realization over `K`, rather
than for the tensor product, using `TauCeti.DynkinType.lieAlgebraBaseChangeEquiv`. -/
instance instIsKillingLieAlgebraBaseChange (K : Type*) [CommRing K] [IsDomain K] [Algebra ℚ K] :
    IsKilling K (t.lieAlgebraBaseChange ht K) := by
  let e : (K ⊗[ℚ] t.lieAlgebra ht) ≃ₗ⁅K⁆ t.lieAlgebraBaseChange ht K :=
    t.lieAlgebraBaseChangeEquiv ht K
  have hscalar : IsKilling K (K ⊗[ℚ] t.lieAlgebra ht) :=
    (TauCeti.isKilling_baseChange_iff ℚ K (t.lieAlgebra ht)).2
      (instIsKillingLieAlgebra t ht)
  let _ : IsKilling K (K ⊗[ℚ] t.lieAlgebra ht) := hscalar
  exact e.isKilling

end

end TauCeti.DynkinType


