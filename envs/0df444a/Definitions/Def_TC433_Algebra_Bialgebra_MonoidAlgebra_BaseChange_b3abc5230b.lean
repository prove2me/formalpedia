-- Prove2me | Definitions.Def_TC433_Algebra_Bialgebra_MonoidAlgebra_BaseChange_b3abc5230b
-- name    : TC433_Algebra_Bialgebra_MonoidAlgebra_BaseChange_b3abc5230b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:13:23.403997+00:00
-- url     : https://prove2.me/theorems/927d8494-deb2-40b2-b732-09b0759e8172
-- title:
--   TauCeti: Algebra / Bialgebra / MonoidAlgebra / BaseChange
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Bialgebra.MonoidAlgebra.BaseChange for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Bialgebra/MonoidAlgebra/BaseChange.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Base change of monoid bialgebras

For a commutative semiring extension `k → K` and a commutative monoid `G`, scalar extension of
the monoid bialgebra `k[G]` is canonically the monoid bialgebra `K[G]`:

```text
K ⊗[k] k[G] ≃ₐc[K] K[G].
```

Mathlib supplies the underlying algebra equivalence as `MonoidAlgebra.scalarTensorEquiv`. This
file records that it preserves the counit and comultiplication, hence promotes it to a bialgebra
equivalence. The equivalence is natural in `G`. When `G` is a group, both sides carry their
standard Hopf structures, so this is the coordinate-ring base-change identification for the
diagonalizable group `D(G)`.

This is the base-change input for the ReductiveGroups roadmap's Layer 4 development of groups of
multiplicative type and non-split tori: after extension of the base field, a diagonalizable
coordinate Hopf algebra remains the group algebra of the same character group.

## Main declarations

* `TauCeti.MonoidAlgebra.scalarTensorBialgEquiv`: base change of a monoid bialgebra is the monoid
  bialgebra over the extended scalars.
* `TauCeti.MonoidAlgebra.mapDomainBialgHom_comp_scalarTensorBialgEquiv`: the equivalence is natural
  in the indexing monoid.

## References

The underlying algebra equivalence is Mathlib's `MonoidAlgebra.scalarTensorEquiv` from
`Mathlib.RingTheory.TensorProduct.MonoidAlgebra`; the bialgebra structures are from
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra` and
`Mathlib.RingTheory.Bialgebra.TensorProduct`.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

namespace TauCeti.MonoidAlgebra

universe u v w w'

variable (k : Type u) (K : Type v) [CommSemiring k] [CommSemiring K] [Algebra k K]
variable {G : Type w} {G' : Type w'} [CommMonoid G] [CommMonoid G']

/-- **Monoid bialgebras commute with base change.**

This is Mathlib's algebra equivalence `MonoidAlgebra.scalarTensorEquiv`, promoted using the
standard tensor-product and monoid-algebra coalgebra structures. For a group `G`, the standard
Hopf structures on source and target make this the coordinate-ring base-change equivalence
`K ⊗[k] k[G] ≃ K[G]` for the diagonalizable group `D(G)`. -/
noncomputable def scalarTensorBialgEquiv :
    K ⊗[k] _root_.MonoidAlgebra k G ≃ₐc[K] _root_.MonoidAlgebra K G :=
  BialgEquiv.ofAlgEquiv (_root_.MonoidAlgebra.scalarTensorEquiv k K)
    (by
      ext s
      simp)
    (by
      ext s
      simp)

/-- On a pure tensor, base change applies the scalar and maps the coefficients of the monoid
algebra along `k → K`. -/
@[simp]
theorem scalarTensorBialgEquiv_tmul (s : K) (p : _root_.MonoidAlgebra k G) :
    scalarTensorBialgEquiv k K (s ⊗ₜ[k] p) =
      s • _root_.MonoidAlgebra.mapAlgHom G (Algebra.ofId k K) p := by
  rw [scalarTensorBialgEquiv, _root_.BialgEquiv.ofAlgEquiv_apply]
  exact _root_.MonoidAlgebra.scalarTensorEquiv_tmul s p

/-- The inverse base-change equivalence sends a monomial over `K` to the corresponding pure
tensor. -/
@[simp]
theorem scalarTensorBialgEquiv_symm_single (g : G) (s : K) :
    (scalarTensorBialgEquiv k K).symm (_root_.MonoidAlgebra.single g s) =
      s ⊗ₜ[k] _root_.MonoidAlgebra.single g (1 : k) := by
  apply_fun scalarTensorBialgEquiv k K
  rw [scalarTensorBialgEquiv_tmul]
  simp

/-- Base change of monoid bialgebras is natural in the indexing monoid. Mapping the indices
before base change gives the same bialgebra morphism as mapping them afterwards. -/
theorem mapDomainBialgHom_comp_scalarTensorBialgEquiv (φ : G →* G') :
    (_root_.MonoidAlgebra.mapDomainBialgHom K φ).comp
        (scalarTensorBialgEquiv k K (G := G) :
          K ⊗[k] _root_.MonoidAlgebra k G →ₐc[K] _root_.MonoidAlgebra K G) =
      (scalarTensorBialgEquiv k K (G := G') :
          K ⊗[k] _root_.MonoidAlgebra k G' →ₐc[K] _root_.MonoidAlgebra K G').comp
        (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K)
          (_root_.MonoidAlgebra.mapDomainBialgHom k φ)) := by
  apply _root_.BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext
  · ext
  · apply _root_.MonoidAlgebra.algHom_ext
    · intro g
      simp
    · ext

end TauCeti.MonoidAlgebra


