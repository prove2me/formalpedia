-- Prove2me | Definitions.Def_OddOrder_FeitThompsonSetup
-- name    : OddOrder_FeitThompsonSetup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:43:48.59029+00:00
-- url     : https://prove2.me/theorems/602078a3-2714-4320-b6f9-107715fd92b1
-- title:
--   Feit–Thompson Section 16: character-grid setup
-- statement:
--   Formalizes the alignment API for the canonical type $P$ maximal pair and its $S$/$T$ character grids (Peterfalvi §§3-13, pp. 5-68).
--
--   Main declarations: `kstar_le_S` (`mp.Kstar ≤ mp.S` (it lies in `S ∩ T = K ⊔ K`)); `k_le_T` (`mp.K ≤ mp.T` (it lies in `S ∩ T = K ⊔ K`)); `tpW_subgroupOf_T_eq` (The key subgroup identity (T-side)); `gridEquivE_T` (The `W`-identification equiv (T-side) `↥tp.W ≃ ↥(certainTypeT.sdiff.W)`).
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonSetup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/FeitThompsonSetup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_FeitThompsonSection16Core

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

/-- `W₁` of `certainTypeS` is `mp.K.subgroupOf mp.S` (the κ-Hall factor of `S`). -/
theorem certainTypeS_W1_eq : (mp.certainTypeS hG).W1 = mp.K.subgroupOf mp.S := by
  unfold Section16MaximalPair.certainTypeS certainTypeHypothesis_of_typeP_kappaHall; rfl

/-- `W₂` of `certainTypeS` is `mp.Kstar.subgroupOf mp.S` (the dual factor of `S`). -/
theorem certainTypeS_W2_eq : (mp.certainTypeS hG).W2 = mp.Kstar.subgroupOf mp.S := by
  unfold Section16MaximalPair.certainTypeS certainTypeHypothesis_of_typeP_kappaHall; rfl

include hG in
/-- `mp.Kstar ≤ mp.S` (it lies in `S ∩ T = K ⊔ K*`). -/
theorem kstar_le_S : mp.Kstar ≤ mp.S := by
  obtain ⟨hWjoin, -, -, -⟩ := mp.W_structure hG
  have : mp.Kstar ≤ mp.S ⊓ mp.T := by rw [hWjoin]; exact le_sup_right
  exact this.trans inf_le_left

variable (tp : Section16TypePStructure mp)

/-- `|certainTypeS.W₁| = tp.q` (both are `|mp.K|`). -/
theorem cardCertainTypeS_W1 : Nat.card ↥(mp.certainTypeS hG).W1 = tp.q := by
  rw [certainTypeS_W1_eq hG mp, Nat.card_congr (Subgroup.subgroupOfEquivOfLe mp.K_le_S).toEquiv,
    ← tp.W1_eq_K hG, ← tp.q_eq_card_W1]

/-- `|certainTypeS.W₂| = tp.p` (both are `|mp.Kstar|`). -/
theorem cardCertainTypeS_W2 : Nat.card ↥(mp.certainTypeS hG).W2 = tp.p := by
  rw [certainTypeS_W2_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (kstar_le_S hG mp)).toEquiv,
    ← tp.W2_eq_Kstar hG, ← tp.p_eq_card_W2]

/-- `W₁` of `certainTypeT` is `mp.Kstar.subgroupOf mp.T` (the κ-Hall factor of `T`; the roles of the
two factors swap for the partner). -/
theorem certainTypeT_W1_eq : (mp.certainTypeT hG).W1 = mp.Kstar.subgroupOf mp.T := by
  unfold Section16MaximalPair.certainTypeT certainTypeHypothesis_of_typeP_kappaHall; rfl

/-- `W₂` of `certainTypeT` is `mp.K.subgroupOf mp.T` (the dual factor of `T`). -/
theorem certainTypeT_W2_eq : (mp.certainTypeT hG).W2 = mp.K.subgroupOf mp.T := by
  unfold Section16MaximalPair.certainTypeT certainTypeHypothesis_of_typeP_kappaHall; rfl

include hG in
/-- `mp.K ≤ mp.T` (it lies in `S ∩ T = K ⊔ K*`). -/
theorem k_le_T : mp.K ≤ mp.T := by
  obtain ⟨hWjoin, -, -, -⟩ := mp.W_structure hG
  have : mp.K ≤ mp.S ⊓ mp.T := by rw [hWjoin]; exact le_sup_left
  exact this.trans inf_le_right

include hG in
/-- The key subgroup identity (T-side): `tp.W.subgroupOf mp.T = certainTypeT.sdiff.W`.  Both equal
`(mp.Kstar ⊔ mp.K).subgroupOf mp.T` (`tp.W = mp.K ⊔ mp.Kstar` and
`certainTypeT.sdiff.W = W₁ ⊔ W₂`). -/
theorem tpW_subgroupOf_T_eq :
    tp.W.subgroupOf mp.T = (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
  change tp.W.subgroupOf mp.T = (mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2
  rw [certainTypeT_W1_eq hG mp, certainTypeT_W2_eq hG mp,
    ← Subgroup.subgroupOf_sup mp.Kstar_le_T (k_le_T hG mp), sup_comm, ← tp.W_eq_kappa_join hG]

/-- The `W`-identification equiv (T-side) `↥tp.W ≃* ↥(certainTypeT.sdiff.W)`: `tp.W ≃
tp.W.subgroupOf
mp.T` then transported along `tpW_subgroupOf_T_eq`.  Mirrors `gridEquivE` with `inf_le_right`. -/
noncomputable def gridEquivE_T :
    ↥tp.W ≃* ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W :=
  (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_right)).symm.trans
    (MulEquiv.subgroupCongr (tpW_subgroupOf_T_eq hG mp tp))

/-- **`gridEquivE_T` preserves the underlying `G`-element** (composite of the element-preserving
`subgroupOfEquivOfLe` and `subgroupCongr`). -/
theorem gridEquivE_T_coe (w : ↥tp.W) :
    (((gridEquivE_T hG mp tp w : ↥(mp.certainTypeT hG).sdiffTICyclicHypothesis.W) :
        ↥mp.T) : G) = (w : G) := rfl

/-- A `tp.W`-element lying in `mp.Kstar` transports under `gridEquivE_T` into `certainTypeT.W1`
(`= mp.Kstar.subgroupOf mp.T`). -/
theorem gridEquivE_T_mem_W1 (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    gridEquivE_T hG mp tp w ∈ ((mp.certainTypeT hG).W1).subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeT_W1_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_T_coe]
  exact hw

/-- A `tp.W`-element lying in `mp.K` transports under `gridEquivE_T` into `certainTypeT.W2`
(`= mp.K.subgroupOf mp.T`). -/
theorem gridEquivE_T_mem_W2 (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    gridEquivE_T hG mp tp w ∈ ((mp.certainTypeT hG).W2).subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeT_W2_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_T_coe]
  exact hw

/-- `Fin tp.q ≃ Fin |certainTypeS.W₁|`, fixing `0 ↦ 0` (so the (13.1.e) anchor `⟨0, q_prime.pos⟩`
matches `chiColumn`'s distinguished base index). -/
noncomputable def eqQ : Fin tp.q ≃ Fin (Nat.card ↥(mp.certainTypeS hG).W1) :=
  finCongr (cardCertainTypeS_W1 hG mp tp).symm

/-- The base `W₂`-column enumeration `Fin tp.p ≃ Ŵ₂` (Pontryagin: `|Ŵ₂| = |W₂| = tp.p`).  Stated in
the `sdiffTICyclicHypothesis.W₂/W` forms (defeq to `certainTypeS.W₂` / `W₁ ⊔ W₂`) so that both
`chiColumn` and `card_charGroup_subgroupOf` consume it directly. An arbitrary bijection; the
column-`0`
normalization is applied in `chi2enum`. -/
theorem cardChi2CharGroup :
    Nat.card (((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ) = tp.p := by
  rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.card_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W]
  exact cardCertainTypeS_W2 hG mp tp

/-- The `W₂`-column enumeration `Fin tp.p ≃ Ŵ₂`, realized as the **power enumeration** `j ↦ γ^j`
of a fixed generator `γ` of the cyclic dual (`S05.isCyclic_charGroup_subgroupOf` +
`cardCertainTypeS_W2`: `|Ŵ₂| = |W₂| = p`), mirroring the `w1CharEquiv` convention: column `0` is
the trivial character (`chi2enum_zero`, the `j = 0` base of the `nu_definition` T-side
difference), and column negation is character inversion (`chi2enum_finNeg`) — the honest (3.9.a)
grid pairing (issue 3002).  The `muS_definition` proof fixes the column `j` and is invariant
under the choice of column enumeration. -/
noncomputable def chi2enum :
    Fin tp.p ≃ (((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ) := by
  haveI := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  exact OddOrder.Peterfalvi.S06.cyclicPowEnum (cardChi2CharGroup hG mp tp)

/-- The normalized column enumeration sends column `0` to the trivial character (Peterfalvi's
column-`0` convention; the `j = 0` base of `nu_definition`). -/
@[simp] theorem chi2enum_zero : chi2enum hG mp tp ⟨0, tp.p_prime.pos⟩ = 1 := by
  have := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  rw [chi2enum, OddOrder.Peterfalvi.S06.cyclicPowEnum_apply]
  simp

include hG in
/-- The key subgroup identity: `tp.W.subgroupOf mp.S = certainTypeS.sdiff.W`.  Both equal
`(mp.K ⊔ mp.Kstar).subgroupOf mp.S` (`tp.W = mp.K ⊔ mp.Kstar` and
`certainTypeS.sdiff.W = W₁ ⊔ W₂`). -/
theorem tpW_subgroupOf_eq :
    tp.W.subgroupOf mp.S = (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
  change tp.W.subgroupOf mp.S = (mp.certainTypeS hG).W1 ⊔ (mp.certainTypeS hG).W2
  rw [certainTypeS_W1_eq hG mp, certainTypeS_W2_eq hG mp,
    ← Subgroup.subgroupOf_sup mp.K_le_S (kstar_le_S hG mp), tp.W_eq_kappa_join hG]

/-- The `W`-identification equiv `↥tp.W ≃* ↥(certainTypeS.sdiff.W)`: `tp.W ≃ tp.W.subgroupOf mp.S`
then transported along `tpW_subgroupOf_eq`.  The `≤` proof is the *same term* as in
`Section16CharacterData.mu_definition`. -/
noncomputable def gridEquivE :
    ↥tp.W ≃* ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W :=
  (Subgroup.subgroupOfEquivOfLe ((le_of_eq tp.W_eq_inter).trans inf_le_left)).symm.trans
    (MulEquiv.subgroupCongr (tpW_subgroupOf_eq hG mp tp))

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

/-- S-side `ω`-grid: the `certainTypeS` `chiColumn` transported to `↥tp.W`. -/
noncomputable def omegaS (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥tp.W ℂ :=
  ClassFunction.compHom (gridEquivE hG mp tp).toMonoidHom
    ((mp.certainTypeS hG).chiColumn (chi2enum hG mp tp j) (eqQ hG mp tp i) :
      ClassFunction ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W ℂ)

/-- S-side `μ`-grid: the (4.3.b) certain-type characters of `certainTypeS`. -/
noncomputable def muS (i : Fin tp.q) (j : Fin tp.p) : ClassFunction ↥mp.S ℂ :=
  (((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).mu (eqQ hG mp tp i) :
    ClassFunction ↥mp.S ℂ)

/-- S-side signs `δ`. -/
noncomputable def deltaS (j : Fin tp.p) : ℤ :=
  ((mp.certainTypeS hG).columnFamily (chi2enum hG mp tp j)).sign

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- **`gridEquivE` preserves the underlying `G`-element.**  It is the composite of the
element-preserving subgroup equivs `subgroupOfEquivOfLe` and `subgroupCongr`, so transporting
`w : ↥tp.W` into `certainTypeS`'s `W` does not move the ambient group element. -/
theorem gridEquivE_coe (w : ↥tp.W) :
    (((gridEquivE hG mp tp w : ↥(mp.certainTypeS hG).sdiffTICyclicHypothesis.W) :
        ↥mp.S) : G) = (w : G) := rfl

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- A `tp.W`-element lying in `mp.K` transports under `gridEquivE` into `certainTypeS.W1`
(`= mp.K.subgroupOf mp.S`). -/
theorem gridEquivE_mem_W1 (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    gridEquivE hG mp tp w ∈ ((mp.certainTypeS hG).W1).subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeS_W1_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_coe]
  exact hw

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- A `tp.W`-element lying in `mp.Kstar` transports under `gridEquivE` into `certainTypeS.W2`
(`= mp.Kstar.subgroupOf mp.S`). -/
theorem gridEquivE_mem_W2 (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    gridEquivE hG mp tp w ∈ ((mp.certainTypeS hG).W2).subgroupOf
      (mp.certainTypeS hG).sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf, certainTypeS_W2_eq hG mp, Subgroup.mem_subgroupOf, gridEquivE_coe]
  exact hw

end Section16CharacterData

end

end OddOrder


