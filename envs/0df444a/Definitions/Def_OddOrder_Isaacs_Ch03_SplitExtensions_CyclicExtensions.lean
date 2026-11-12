-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_CyclicExtensions
-- name    : OddOrder_Isaacs_Ch03_SplitExtensions_CyclicExtensions
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:01:03.648235+00:00
-- url     : https://prove2.me/theorems/74267e2f-f75f-4433-9868-e48faf653ebe
-- title:
--   Isaacs §3F: cyclic quotient extensions
-- statement:
--   The cluster for Isaacs, *Finite Group Theory*, §3F (pp. 105–112): Thm 3.35 (extension uniqueness) and Thm 3.36 (existence of cyclic extensions via the construction $(N\rtimes_\sigma\mathbb{Z})/\langle(a^{-1},m)\rangle$).
--
--   The main definition is `cyclicExtPhi`, the twist homomorphism $\mathrm{Multiplicative}\,\mathbb{Z}\to\mathrm{Aut}(N)$ sending $k\mapsto\sigma^k$.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch03_SplitExtensions/CyclicExtensions.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/CyclicExtensions.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Theorem315
import Definitions.Def_OddOrder_Mathlib_SemidirectProduct

namespace OddOrder.Isaacs.Ch03

section

variable {G : Type*} [Group G]

/-- Twist hom: `Multiplicative ℤ →* MulAut N` sending `ofAdd k ↦ σ^k`. -/
private noncomputable def cyclicExtPhi {N : Type*} [Group N] (σ : MulAut N) :
    Multiplicative ℤ →* MulAut N :=
  zpowersHom (MulAut N) σ

@[simp] private lemma cyclicExtPhi_apply {N : Type*} [Group N] (σ : MulAut N)
    (k : Multiplicative ℤ) : cyclicExtPhi σ k = σ ^ k.toAdd := rfl

end

end OddOrder.Isaacs.Ch03


