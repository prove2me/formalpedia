-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
-- name    : OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:49:57.970353+00:00
-- url     : https://prove2.me/theorems/d9c4553b-b510-4bb5-9d7b-73e4728b6bc3
-- title:
--   Isaacs FGT Ch. 7: the normal-$J$ theorem, closing steps (Thm 7.6)
-- statement:
--   Isaacs, *Finite Group Theory*, Chapter 7, Theorem 7.6, pp. 209-214: Steps 4-8 of the normal-$J$ argument and the unconditional `normal_J`, covering the centralizing bridges, the count $|\bar A|=p$, the Step-8 action setup and the final assembly.
--
--   The bundle's definition is `subgroupConjActionOnNormal`, the conjugation action of a subgroup on a normal subgroup.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The conjugation `MulDistribMulAction` of `↥Q` on the normal subgroup `↥N`
of `K`, via `MulAut.conjNormal ∘ Q.subtype`.  Under this action,
`a • n = ⟨↑a * ↑n * (↑a)⁻¹⟩`.  Used in Step 5 with `Q = Ā`, `N = L̄`. -/
@[reducible]
noncomputable def subgroupConjActionOnNormal
    {K : Type*} [Group K] (Q N : Subgroup K) [N.Normal] :
    MulDistribMulAction ↥Q ↥N :=
  MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp Q.subtype)

end OddOrder.Isaacs.Ch07


