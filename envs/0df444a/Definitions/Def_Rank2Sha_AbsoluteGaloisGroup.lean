-- Prove2me | Definitions.Def_Rank2Sha_AbsoluteGaloisGroup
-- name    : Rank2Sha_AbsoluteGaloisGroup
-- status  : Definition
-- author  : @barindersbanwait
-- created : 2026-11-25T00:56:17.669949+00:00
-- url     : https://prove2.me/theorems/0534aa95-2e76-44a1-b439-ea16881b495d
-- title:
--   Restriction maps between absolute Galois groups
-- statement:
--   Let $K$ and $L$ be fields and write $G_K = \mathrm{Aut}(\overline{K}/K)$ for the absolute Galois group of $K$, with the Krull topology, where $\overline{K}$ is a fixed algebraic closure.
--
--   A field homomorphism $f : K \to L$ extends to a homomorphism $\overline{K} \to \overline{L}$ of algebraic closures. Restricting an automorphism of $\overline{L}$ over $L$ along this extension gives a continuous group homomorphism
--
--   $$
--   G_L \longrightarrow G_K .
--   $$
--
--   This file defines that homomorphism, first for a given commuting square of fields and algebraic closures (`Field.absoluteGaloisGroup.mapOfAlgebra`) and then for a field homomorphism $f$ with the extension to algebraic closures chosen arbitrarily (`Field.absoluteGaloisGroup.map`). A different choice of extension changes the map by conjugation in $G_K$.
--
--   These maps are the restriction maps from a global Galois group to the Galois group of a completion. They are used to state local conditions in Galois cohomology.
--
--   **Formalization Note** The code is copied without change from formal-conjectures, which copied it from Mathlib pull request 41415; the declarations are absent from the Mathlib revision of this environment.
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/6bc2f7490a49cc0258406ffb675483f4318a04b5/FormalConjecturesForMathlib/FieldTheory/AbsoluteGaloisGroup.lean ; Mathlib pull request https://github.com/leanprover-community/mathlib4/pull/41415 (Mathlib.FieldTheory.AbsoluteGaloisGroup)

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-
The copied Mathlib source carries the following attribution:
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# Restriction maps of absolute Galois groups

These definitions were introduced in Mathlib by Thomas Browning's
[pull request #41415](https://github.com/leanprover-community/mathlib4/pull/41415).
They are absent from this repository's Mathlib `v4.33.1` dependency. The added code is copied
verbatim from `Mathlib.FieldTheory.AbsoluteGaloisGroup` at the merged commit
`7e604dbff1442ed4b05a0b9a4b15c5207584f116`.
-/

noncomputable section

namespace Field

variable (K L : Type*) [Field K] [Field L]

local notation "G_K" => absoluteGaloisGroup

section

variable [Algebra K L] [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

open IntermediateField in
/-- A commuting square of two fields and their algebraic closures induces a continuous homomorphism
of their absolute Galois groups. -/
@[simps!]
noncomputable def absoluteGaloisGroup.mapOfAlgebra : G_K L →ₜ* G_K K :=
  letI F : G_K L →* G_K K := (AlgEquiv.restrictNormalHom _).comp (AlgEquiv.restrictScalarsHom K)
  { __ := F
    continuous_toFun := by
      classical
      let f := IsScalarTower.toAlgHom K (AlgebraicClosure K) (AlgebraicClosure L)
      apply continuous_of_continuousAt_one F
      rw [ContinuousAt, map_one]
      refine ((galGroupBasis L (AlgebraicClosure L)).nhds_one_hasBasis.tendsto_iff
        (galGroupBasis K (AlgebraicClosure K)).nhds_one_hasBasis).mpr ?_
      rintro _ ⟨_, ⟨F, hF : FiniteDimensional _ _, rfl⟩, rfl⟩
      refine ⟨_, ⟨_, ⟨adjoin L (F.map f), ?_, rfl⟩, rfl⟩, fun σ hσ x ↦ ?_⟩
      · suffices Algebra.EssFiniteType L (adjoin L (F.map f : Set (AlgebraicClosure L))) by
          apply Algebra.finite_of_essFiniteType_of_isAlgebraic
        replace hF : Algebra.EssFiniteType K F := inferInstance
        rw [essFiniteType_iff] at hF ⊢
        obtain ⟨s, rfl⟩ := hF
        use s.image f
        rw [adjoin_map, adjoin_adjoin_right, Finset.coe_image]
      · exact f.injective <| ((σ.restrictScalarsHom K).restrictNormal_commutes
          (AlgebraicClosure K) x).trans <| hσ ⟨f x, subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩ }

end

variable {K L} in
/-- An embedding of fields induces a continuous homomorphism of absolute Galois groups.
Note that this depends on an arbitrary choice of embedding of the algebraic closures. -/
@[simps!]
noncomputable def absoluteGaloisGroup.map (f : K →+* L) : G_K L →ₜ* G_K K :=
  letI : Algebra K L := f.toAlgebra
  letI g : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := g.toAlgebra
  absoluteGaloisGroup.mapOfAlgebra K L

end Field


