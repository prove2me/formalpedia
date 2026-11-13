-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
-- name    : OddOrder_Peterfalvi_S15_SAndTDefs
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:03:27.784486+00:00
-- url     : https://prove2.me/theorems/1047f182-a28a-4cd2-a198-4ffef3b48fda
-- title:
--   Peterfalvi (13.17): the $S$ and $T$ definitions (type I over a normalizer)
-- statement:
--   Defines the carrier `TypeIOverNormalizerData` for Peterfalvi (13.17), a type I maximal subgroup over a normalizer.
--
--   Main declarations: `TypeIOverNormalizerData` (Carrier for Peterfalvi (13.17), the type-I maximal subgroup over `N_G(U)`).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTDefs.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTDefs.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedTransport
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroupQuotient

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Carrier for Peterfalvi (13.17), the type-I maximal subgroup over
`N_G(U)`. -/
structure TypeIOverNormalizerData (hyp : Hypothesis (G := G)) where
  L : Subgroup G
  H : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  H_eq_LF : H = maxNilpotentNormalHall L
  normalizer_U_le_L : Subgroup.normalizer (hyp.U : Set G) ≤ L
  frobenius : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L
  U_le_H : hyp.U ≤ H
  /-- **Peterfalvi (13.17.c)/(14.5)**: the Frobenius complement has order `p q` (the `W₁W₂^y`
  alternative; the `W₁` alternative of (13.17.c) is ruled out by (14.5)). -/
  complement_card_eq_pq : Nat.card ↥frobenius.complement = hyp.p * hyp.q
  /-- **Peterfalvi (13.17.c)/(14.5)**: a conjugate `W₂^y` (`y ∈ Q`) lies in the Frobenius
  complement `W₁W₂^y` of `L`. -/
  exists_y_W2_conj_le_complement :
    ∃ y ∈ hyp.Q, (MulAut.conj y • hyp.W2 : Subgroup G) ≤
      frobenius.complement.map L.subtype

/-- **Peterfalvi (14.11)**, base-derived: `|W| = p q`.  `W = W₁ ⊔ W₂` (`W_eq_join`) is the internal
direct product of the elementwise-commuting (`W1_commutes_W2`), trivially-intersecting
(`W1_inf_W2_eq_bot`) cyclic factors `W₁` (order `q`) and `W₂` (order `p`), so
`|W| = |W₁| · |W₂| = q p = p q` via the disjoint-normalizer product formula. Supplies the
`card_W_eq`
field of `MHypothesis`, de-gating it from a §13-14 σ-prerequisite to a base consequence. -/
theorem card_W_eq_pq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.W = hyp.p * hyp.q := by
  -- `W₁` normalizes `W₂`: each `x ∈ W₁` centralizes `W₂`, hence fixes it under conjugation.
  have hconj : ∀ x ∈ hyp.W1, ∀ a ∈ hyp.W2, x * a * x⁻¹ ∈ hyp.W2 := by
    intro x hx a ha
    have hc : Commute x a := hyp.W1_commutes_W2 x hx a ha
    have hxa : x * a * x⁻¹ = a := by rw [hc.eq]; group
    rw [hxa]; exact ha
  have hW1norm : hyp.W1 ≤ Subgroup.normalizer (hyp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconj x hx a ha, fun ha => ?_⟩
    have hb := hconj x⁻¹ (hyp.W1.inv_mem hx) (x * a * x⁻¹) ha
    simpa [mul_assoc] using hb
  rw [hyp.W_eq_join,
    OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hW1norm hyp.W1_inf_W2_eq_bot,
    ← hyp.q_eq_card_W1, ← hyp.p_eq_card_W2]
  exact mul_comm hyp.q hyp.p

end OddOrder.Peterfalvi.S15


