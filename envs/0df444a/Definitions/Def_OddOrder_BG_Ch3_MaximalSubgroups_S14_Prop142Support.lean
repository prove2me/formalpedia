-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S14_Prop142Support
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S14_Prop142Support
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:56:42.882986+00:00
-- url     : https://prove2.me/theorems/4fefd7f5-1704-4706-b502-544fa56fee07
-- title:
--   BG §14: support lemmas for Proposition 14.2 ($\kappa$-free)
-- statement:
--   Generic, $\kappa$-free utilities used by Proposition 14.2 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §14 (`typeP_structure`) to transport the prime action and the $M_\sigma$-centralizer witness across $M$-conjugacy.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S14_Prop142Support.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S14_Prop142Support.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeAction

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Conjugation transport for an element centralizer**: `C_G(a)^m = C_G(m a m⁻¹)`. -/
theorem smul_centralizer_singleton (m a : G) :
    MulAut.conj m • Subgroup.centralizer ({a} : Set G)
      = Subgroup.centralizer ({m * a * m⁻¹} : Set G) := by
  have himg : ({m * a * m⁻¹} : Set G) = (MulAut.conj m).toMonoidHom '' ({a} : Set G) := by
    simp [MulAut.conj_apply]
  rw [himg]
  exact Subgroup.map_centralizer_eq_of_bijective ({a} : Set G)
    (MulAut.conj m).toMonoidHom (MulAut.conj m).bijective

/-- **Conjugation transport for a subgroup centralizer**: `C_G(X)^m = C_G(X^m)`. -/
theorem smul_centralizer_subgroup (m : G) (X : Subgroup G) :
    MulAut.conj m • Subgroup.centralizer (X : Set G)
      = Subgroup.centralizer ((MulAut.conj m • X : Subgroup G) : Set G) :=
  Subgroup.map_centralizer_eq_of_bijective (X : Set G) (MulAut.conj m).toMonoidHom
    (MulAut.conj m).bijective

end OddOrder.BG.Ch3.S13


