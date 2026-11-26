-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Localization_Pi
-- name    : ProEtale_Mathlib_RingTheory_Localization_Pi
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:12.424492+00:00
-- url     : https://prove2.me/theorems/7994bcf0-624a-597b-80b1-ef657cc32307
-- title:
--   A product of total rings of fractions is the total ring of fractions of the product
-- statement:
--   For a commutative ring $V$, let $V^{\circ}$ be its monoid of non-zero-divisors; a $V$-algebra $L$ is a localization at $V^{\circ}$ (the total ring of fractions) if it satisfies the universal property of $V[(V^{\circ})^{-1}]$.
--
--   **Theorem.** Let $(V_i)_{i \in \iota}$ and $(L_i)_{i \in \iota}$ be families of commutative rings, indexed by an arbitrary type $\iota$. Suppose that each $L_i$ is a $V_i$-algebra which is a localization of $V_i$ at $V_i^{\circ}$. Suppose also that $\prod_i L_i$ carries a $\prod_i V_i$-algebra structure which is componentwise, i.e. $(s \cdot 1)_i = \mathrm{algebraMap}_{V_i \to L_i}(s_i)$ for all $s \in \prod_i V_i$ and all $i$. Then
--   $$\prod_i L_i \ \text{ is the localization of } \ \prod_i V_i \ \text{ at } \ \Big(\prod_i V_i\Big)^{\circ}.$$
--
--   This result computes total rings of fractions of products, for example of the rings of functions on finite disjoint unions.
--
--   **Formalization Note** The theorem is `IsLocalization.pi`. The componentwise algebra structure is not built in; it is an explicit hypothesis `halg` on an arbitrary instance `Algebra (Π i, V i) (Π i, L i)`. No finiteness assumption is made on $\iota$.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Localization/Pi.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Jingting Wang
-/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.RingTheory.Localization.Defs
import Definitions.Def_ProEtale_Mathlib_Algebra_GroupWithZero_NonZeroDivisors

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Localization of a product at its non-zero-divisors

A product of localizations at the non-zero-divisors is the localization of the product at its
non-zero-divisors.

## Main results

- `IsLocalization.pi`: if each `L i` is the localization of `V i` at its non-zero-divisors, then
  `Π i, L i` is the localization of `Π i, V i` at its non-zero-divisors.
-/

/-- If each `L i` is the localization of `V i` at its non-zero-divisors, then `Π i, L i` is the
localization of `Π i, V i` at its non-zero-divisors.

The algebra structure on `Π i, L i` over `Π i, V i` is assumed to be componentwise, expressed by
`halg`. -/
theorem IsLocalization.pi {ι : Type*} {V : ι → Type*} {L : ι → Type*}
    [∀ i, CommRing (V i)] [∀ i, CommRing (L i)] [∀ i, Algebra (V i) (L i)]
    [∀ i, IsLocalization (nonZeroDivisors (V i)) (L i)] [Algebra (Π i, V i) (Π i, L i)]
    (halg : ∀ (s : Π i, V i) (i : ι),
      algebraMap (Π i, V i) (Π i, L i) s i = algebraMap (V i) (L i) (s i)) :
    IsLocalization (nonZeroDivisors (Π i, V i)) (Π i, L i) := by
  refine ⟨fun ⟨s, hs⟩ ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · rw [Pi.isUnit_iff]
    intro i
    rw [halg]
    exact IsLocalization.map_units (L i) ⟨s i, Pi.mem_nonZeroDivisors_iff.mp hs i⟩
  · choose p hp using fun i : ι ↦ IsLocalization.surj (nonZeroDivisors (V i)) (z i)
    refine ⟨⟨fun i ↦ (p i).1, ⟨fun i ↦ (p i).2,
      Pi.mem_nonZeroDivisors_iff.mpr fun i ↦ (p i).2.2⟩⟩, funext fun i ↦ ?_⟩
    simp only [Pi.mul_apply, halg]
    exact hp i
  · obtain rfl : a = b := by
      funext i
      refine IsLocalization.injective (S := L i) le_rfl ?_
      have hi := congrFun h i
      rwa [halg, halg] at hi
    rfl


