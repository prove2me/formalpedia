-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
-- name    : OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:19.599518+00:00
-- url     : https://prove2.me/theorems/1d0d7d2f-1052-4f78-967e-2d8c8e940aa0
-- title:
--   Peterfalvi (14.6): the $S$-side Galois-field model
-- statement:
--   Formalizes the $S$-side Galois-field model of Peterfalvi (14.6): case (9.7.b) identifies the chief factor with the additive group of $GF(p^q)$. The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SSideGaloisFieldModel.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SSideGaloisFieldModel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_GaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

section

/-- The named complement `U` normalizes the Fitting kernel `P = S_F`.

Indeed `U ≤ S'`, while `S` normalizes its maximum nilpotent normal Hall subgroup. -/
theorem Hypothesis.U_le_normalizer_P (hyp : Hypothesis (G := G)) :
    hyp.U ≤ Subgroup.normalizer hyp.P := by
  have hU_le_deriv : hyp.U ≤ derivedInG hyp.S := by
    rw [hyp.S_deriv_eq_PU]
    exact le_sup_right
  have hderiv_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hS_le_norm : hyp.S ≤ Subgroup.normalizer hyp.P := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  exact (hU_le_deriv.trans hderiv_le_S).trans hS_le_norm

/-- Conjugation by the named complement `U` preserves the named kernel `P`. -/
theorem Hypothesis.conj_mem_P (hyp : Hypothesis (G := G))
    (v : ↥hyp.U) (x : ↥hyp.P) :
    (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.P := by
  have hv : (v : G) ∈ Subgroup.normalizer hyp.P := hyp.U_le_normalizer_P v.2
  exact (Subgroup.mem_normalizer_iff.mp hv (x : G)).mp x.2

end

end OddOrder.Peterfalvi.S15


