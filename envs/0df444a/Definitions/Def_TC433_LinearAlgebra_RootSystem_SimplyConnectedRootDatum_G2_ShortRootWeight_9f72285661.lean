-- Prove2me | Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_G2_ShortRootWeight_9f72285661
-- name    : TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_G2_ShortRootWeight_9f72285661
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:15:59.712208+00:00
-- url     : https://prove2.me/theorems/a5fd257a-da6c-4f08-853e-fca19ec45be8
-- title:
--   TauCeti: LinearAlgebra / RootSystem / SimplyConnectedRootDatum / G2 / ShortRootWeight
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.ShortRootWeight for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/G2/ShortRootWeight.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_LinearAlgebra_RootSystem_SimplyConnectedRootDatum_G2_Length_ccd06b0788

/-!
# The short-root weight diagram of type G2

This file records the seven weights of the fundamental type-`G₂` module `V(ϖ₁)` in
fundamental-weight coordinates. They are the six short roots and zero, ordered from the highest
weight to its negative. The table is root-datum data used by the integral representation in
`TauCeti.Algebra.Lie.G2.ShortRoot.Basic`.

The numbering and coordinates follow N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IX. The weight diagram follows J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §19.3 (the `G₂` algebra) and §21.3 (weight strings and diagrams).
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.G2ShortRoot

open TauCeti.DynkinType

/-- The seven weights of the fundamental module `V(ϖ₁)` of type `G₂` in fundamental-weight
coordinates: the six short roots and zero, ordered as
`2α₁ + α₂, α₁ + α₂, α₁, 0, -α₁, -(α₁ + α₂), -(2α₁ + α₂)`. -/
@[expose] def weight : Fin 7 → Fin 2 → ℤ :=
  ![![1, 0], ![-1, 1], ![2, -1], ![0, 0], ![-2, 1], ![1, -1], ![-1, 0]]

/-- The entrywise definition of the short-root weight table. -/
@[simp] theorem weight_apply (a : Fin 7) (i : Fin 2) : weight a i =
    ![![1, 0], ![-1, 1], ![2, -1], ![0, 0], ![-2, 1], ![1, -1], ![-1, 0]] a i := by
  rw [weight]

/-- The first listed weight is the highest weight `ϖ₁`. -/
theorem weight_zero : weight 0 = Pi.single 0 1 := by decide

/-- The middle listed weight is zero. -/
theorem weight_three : weight 3 = 0 := by decide

/-- The first two listed weights sum to the second fundamental weight. -/
theorem weight_zero_add_weight_one : weight 0 + weight 1 = Pi.single 1 1 := by decide +kernel

/-- The seven weights are injective in their index. -/
theorem weight_injective : Function.Injective weight := by decide

/-- **The weight diagram is symmetric about the origin.** Reversing the index negates the weight,
the middle index being the fixed point of that symmetry. Nothing is claimed here about a pairing
carrying that symmetry. -/
@[simp]
theorem weight_rev (a : Fin 7) : weight a.rev = -weight a := by
  revert a
  decide +kernel

/-- **The weights sum to zero.** -/
theorem sum_weight : ∑ a, weight a = 0 := by decide +kernel

/-- **The weights are the short roots and zero.** The nonzero weights are exactly the roots of the
pinned type-`G₂` datum of squared length one. -/
theorem range_weight :
    Set.range weight = insert 0 (g2Root '' {k | g2Length k = 1}) := by
  ext v
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Set.mem_ofPred_eq, g2Length_apply,
    g2Root_apply]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a
    · exact Or.inr ⟨3, by decide, by decide⟩
    · exact Or.inr ⟨2, by decide, by decide⟩
    · exact Or.inr ⟨0, by decide, by decide⟩
    · exact Or.inl (by decide)
    · exact Or.inr ⟨6, by decide, by decide⟩
    · exact Or.inr ⟨8, by decide, by decide⟩
    · exact Or.inr ⟨9, by decide, by decide⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨3, by decide⟩
    · fin_cases k
      · exact ⟨2, by decide⟩
      · exact absurd hk (by decide)
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact absurd hk (by decide)
      · exact absurd hk (by decide)
      · exact ⟨4, by decide⟩
      · exact absurd hk (by decide)
      · exact ⟨5, by decide⟩
      · exact ⟨6, by decide⟩
      · exact absurd hk (by decide)
      · exact absurd hk (by decide)

/-- **The weights span the full character lattice.** The highest weight is the first fundamental
weight, and it and the next weight sum to the second. -/
theorem span_range_weight_eq_top : Submodule.span ℤ (Set.range weight) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 2)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  let S := Submodule.span ℤ (Set.range weight)
  have h (a : Fin 7) : weight a ∈ S := Submodule.subset_span (Set.mem_range_self a)
  fin_cases i
  · simpa only [Fin.zero_eta, SetLike.mem_coe, ← weight_zero] using h 0
  · simpa only [Fin.mk_one, SetLike.mem_coe, ← weight_zero_add_weight_one] using
      S.add_mem (h 0) (h 1)

end TauCeti.G2ShortRoot


