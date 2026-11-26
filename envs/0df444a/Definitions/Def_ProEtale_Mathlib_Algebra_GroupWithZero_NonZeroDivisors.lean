-- Prove2me | Definitions.Def_ProEtale_Mathlib_Algebra_GroupWithZero_NonZeroDivisors
-- name    : ProEtale_Mathlib_Algebra_GroupWithZero_NonZeroDivisors
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:56:39.974737+00:00
-- url     : https://prove2.me/theorems/f0e6022a-0eda-52a5-91d3-95d716d3e8c8
-- title:
--   Non-zero-divisors of a product are exactly the componentwise non-zero-divisors
-- statement:
--   Let $(R_i)_{i \in I}$ be a family of monoids with zero and $s \in \prod_i R_i$. The file proves
--   $$s \in \operatorname{nzd}\Big(\prod_i R_i\Big) \iff \forall i,\ s_i \in \operatorname{nzd}(R_i).$$
--   Here $\operatorname{nzd}(M)$ denotes the submonoid of non-zero-divisors: elements $s$ such that $zs = 0 \Rightarrow z = 0$ and $sz = 0 \Rightarrow z = 0$.
--
--   This is used for localizations and total rings of fractions of finite products of rings.
--
--   **Formalization Note** The theorem is `Pi.mem_nonZeroDivisors_iff`, for an arbitrary index type and `[∀ i, MonoidWithZero (R i)]`. Mathlib's `nonZeroDivisors` is used, which in a non-commutative setting asks for both left and right cancellation of zero.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Jingting Wang
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Notation.Pi.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Non-zero-divisors of a product

We characterize the non-zero-divisors of a product of monoids with zero componentwise.

## Main results

- `Pi.mem_nonZeroDivisors_iff`: an element of a product `Π i, R i` is a non-zero-divisor if and
  only if each of its components is a non-zero-divisor.
-/

/-- An element of a product `Π i, R i` is a non-zero-divisor if and only if each of its
components is a non-zero-divisor. -/
theorem Pi.mem_nonZeroDivisors_iff {ι : Type*} {R : ι → Type*} [∀ i, MonoidWithZero (R i)]
    {s : Π i, R i} :
    s ∈ nonZeroDivisors (Π i, R i) ↔ ∀ i, s i ∈ nonZeroDivisors (R i) := by
  classical
  simp only [_root_.mem_nonZeroDivisors_iff]
  constructor
  · rintro ⟨hl, hr⟩ i
    refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
    · have hs : s * Pi.single i z = 0 := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simpa using hz
        · simp [Pi.single_eq_of_ne hj]
      simpa using congrFun (hl _ hs) i
    · have hs : Pi.single i z * s = 0 := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simpa using hz
        · simp [Pi.single_eq_of_ne hj]
      simpa using congrFun (hr _ hs) i
  · intro h
    refine ⟨fun t ht ↦ funext fun i ↦ (h i).1 (t i) (congrFun ht i),
      fun t ht ↦ funext fun i ↦ (h i).2 (t i) (congrFun ht i)⟩


