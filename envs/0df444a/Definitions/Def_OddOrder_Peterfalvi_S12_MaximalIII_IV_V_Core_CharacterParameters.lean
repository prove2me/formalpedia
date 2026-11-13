-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
-- name    : OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:26:39.470811+00:00
-- url     : https://prove2.me/theorems/efc08952-98bf-4581-8e59-113bcafb5f37
-- title:
--   Peterfalvi (10.2)–(10.4): character parameters and coherent extension
-- statement:
--   Formalizes the character-parameter side of Peterfalvi (10.2)–(10.4): normalization, orthogonality and irreducibility of the $\mu$-grid entries and the column signs $\delta_j$.
--
--   Main declarations: `Hypothesis.muColumnSign_eq_one_or_neg_one` (Peterfalvi (10.3), the sign `δ_j ∈ {±1}`); `Hypothesis.muGrid_inner_self` (§10 μ-grid normalization); `Hypothesis.muGrid_inner_cross_column` (§10 μ-grid cross-column orthogonality); `Hypothesis.muGrid_inner_within_column` (§10 μ-grid within-column orthogonality).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/CharacterParameters.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/CharacterParameters.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_MuGridConstruction

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Peterfalvi (10.3), the sign `δ_j ∈ {±1}`**: every column sign `δ_j = muColumnSign j` is a unit
(`±1`).  Immediate from the §6 certain-type `columnFamily`'s `.sign_eq` (the Pontryagin sign of a
linear character is `±1`).  Combined with the `(10.3)` `δ_j`-independence and `δ_j = δ` (the
`muColumnSign j = δ` returned by `exists_charParamArith`), this gives the `δ = ±1` (`hδpm`) input to
the (10.6) Dade-value lemmas `tau1_values_and_norm_bound` / `zeta_tau1_norm_ge_one`. -/
theorem Hypothesis.muColumnSign_eq_one_or_neg_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) :
    hyp.muColumnSign hG hodd j = 1 ∨ hyp.muColumnSign hG hodd j = -1 := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have esign : hyp.muColumnSign hG hodd j
      = (h.columnFamily (finCardEquivCharacterGroup _
          (finCongr hcardW2sub.symm j))).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [esign]
  exact (h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).sign_eq

open scoped FiniteInduce in
/-- **§10 μ-grid normalization** (Peterfalvi (4.1)/(4.3.b)): each materialized certain-type
character `μ_{ij}` is an irreducible character of `M`, hence has norm one, `(μ_{ij}, μ_{ij}) = 1`.
Read off the §6 `columnFamily` (whose `mu` are irreducible) through the `muGrid` reconstruction. -/
theorem Hypothesis.muGrid_inner_self [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i j) = 1 := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [emj, OddOrder.RepresentationTheory.irreducibleCharacter_inner, if_pos rfl]

open scoped FiniteInduce in
/-- **§10 μ-grid cross-column orthogonality** (Peterfalvi (4.3.b)): certain-type characters from
*different* `W₂`-columns are orthogonal, `(μ_{ij}, μ_{i'j'}) = 0` for `j ≠ j'` (any rows `i, i'`).
The §6 `columnFamily_cross_products_zero` (via (4.1)), read through `muGrid`, with a case split on
which rows are `0`.  In particular `(μ_{ij}, μ_{i0}) = 0` for `0 < j`, the cross term in the
norm `‖α_{ij}‖² = 2 + n²` of the (10.5) Dade-image argument. -/
theorem Hypothesis.muGrid_inner_cross_column [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i i' : Fin hyp.w1) {j j' : Fin hyp.w2} (hjj' : j ≠ j') :
    ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i' j') = 0 := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- The two `W₂`-duals differ (different columns).
  have hχne : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm j)
      ≠ finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2)) (finCongr hcardW2sub.symm j') :=
    fun heq => hjj' ((finCongr hcardW2sub.symm).injective
      ((finCardEquivCharacterGroup _).injective heq))
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have emj' : hyp.muGrid hG hodd i' j'
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j'))).mu
          (finCongr hcardW1.symm i') : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [emj, emj']
  have hz : (⟨1, h.one_lt_card_W1⟩ : Fin (Nat.card h.W1)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  rcases eq_or_ne (finCongr hcardW1.symm i) 0 with hi | hi <;>
    rcases eq_or_ne (finCongr hcardW1.symm i') 0 with hi' | hi'
  · rw [hi, hi']; exact (h.columnFamily_cross_products_zero hχne hz hz).2.2.2
  · rw [hi]; exact (h.columnFamily_cross_products_zero hχne hz hi').2.2.1
  · rw [hi']; exact (h.columnFamily_cross_products_zero hχne hi hz).2.1
  · exact (h.columnFamily_cross_products_zero hχne hi hi').1

open scoped FiniteInduce in
/-- **§10 μ-grid within-column orthogonality** (Peterfalvi (4.3.b)): distinct rows of the same
`W₂`-column give orthogonal certain-type characters, `(μ_{ij}, μ_{i'j}) = 0` for `i ≠ i'`.  The
§6 `columnFamily` `mu` are distinct irreducibles (`irreducibleCharacter_inner` + the family's
`injective` field), read through `muGrid`.  With `muGrid_inner_self` this completes the
orthonormality of the full `μ`-grid. -/
theorem Hypothesis.muGrid_inner_within_column [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i i' : Fin hyp.w1} (j : Fin hyp.w2) (hii' : i ≠ i') :
    ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i' j) = 0 := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hrowne : (finCongr hcardW1.symm i) ≠ (finCongr hcardW1.symm i') :=
    fun heq => hii' ((finCongr hcardW1.symm).injective heq)
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have emj' : hyp.muGrid hG hodd i' j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i') : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [emj, emj', OddOrder.RepresentationTheory.irreducibleCharacter_inner,
    if_neg (fun heq => hrowne ((h.columnFamily _).injective heq))]

open scoped FiniteInduce in
/-- **§10 μ-grid entries are irreducible** (Peterfalvi (4.3.b)): each `μ_{ij}` is an irreducible
character of `M`, being the §6 certain-type character `(columnFamily χ₂).mu i` (an
`IrreducibleCharacter`).  This is the `μ_{ij} ∈ ℤ[Irr M]` input that makes `α_{ij}^τ` a virtual
character of `G`, hence the inner products of the (10.5) `a = 0` argument integers. -/
theorem Hypothesis.muGrid_isIrreducible [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1)
    (j : Fin hyp.w2) :
    IsIrreducibleCharacter (hyp.muGrid hG hodd i j) := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  rw [show hyp.muGrid hG hodd i j
    = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
        (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) from by unfold Hypothesis.muGrid; rfl]
  exact OddOrder.RepresentationTheory.IrreducibleCharacter.isIrreducible _

open scoped FiniteInduce in
/-- **§10 column sum is induced from `M'`, hence vanishes off `M'`** (Peterfalvi (10.5)/(4.5.a)):
the `W₂`-column sum `μ_k = ∑_{0≤i<w₁} μ_{ik}` equals the induced character
`Ind_{M'}^M (Res_{M'} μ_{0k})`
(`induce_restrict_certainType_eq`), so it vanishes on every `x ∉ M' = [M,M]`.

This is the structural fact making `μ_k − dζ̄` `A_0`-supported in the (10.5) `a = 0` argument (both
`μ_k` and `ζ̄` vanish off `M'`, and the degrees cancel) — so the Dade isometry `τ` transfers it
(`tau_inner_eq_of_supported`), with no Dade–coherence adjunction needed. -/
theorem Hypothesis.muGrid_column_sum_vanishes_off_derived [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    {x : ↥M} (hx : x ∉ (derivedInG M).subgroupOf M) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) x = 0 := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- The column sum is the induced character `Ind_{M'}^M (Res_{M'} μ_{0k})` (`induce_restrict`).
  have hsum : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      = ClassFunction.induce h.K
          (ClassFunction.restrict h.K
            ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu 0
              : ClassFunction ↥M ℂ)) := by
    rw [h.induce_restrict_certainType_eq, ← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu i'
        : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  rw [hsum]
  -- `K = M' = [M,M]` is normal, so the induced character vanishes off it.
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have : h.K.Normal := hKnormal
  exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hx

open scoped FiniteInduce in
/-- **§10 column sum lies in the family `S`** (Peterfalvi (10.5)/(4.5.a)): for `0 < k < w₂`, the
`W₂`-column sum `μ_k = ∑_{i} μ_{ik}` is the induced character `Ind_{M'}^M θ` of a *non-trivial*
irreducible `θ` of `M'` (`exists_irreducible_restrict_certainType`), hence lies in
`S = inducedFamily M`.  Non-triviality follows from the degree: `θ(1) = (Res_{M'} μ_{0k})(1) =
μ_{0k}(1) ≠ 1` (the caller supplies `μ_{0k}(1) = d > 1` from (10.3)).

This is the `μ_k ∈ ℤ[S]` input that the coherent extension `τ₁` consumes: it lets `μ_k^{τ₁}`
participate in the isometry (`‖μ_k^{τ₁}‖² = ‖μ_k‖² = w₁`) and the `(μ_k − dζ̄)^τ = μ_k^{τ₁} −
dζ̄^{τ₁}` split of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGrid_column_sum_mem_inducedFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) ∈ inducedFamily M := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨θ, hθeq, hind⟩ :=
    h.exists_irreducible_restrict_certainType
      (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))
  -- row-0 entry equals the certain-type character `μ_{0k}` (`finCongr` fixes `0`).
  have hrow0 : hyp.muGrid hG hodd 0 k
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu 0
          : ClassFunction ↥M ℂ) := by
    have hfc : (finCongr hcardW1.symm (0 : Fin hyp.w1)) = (0 : Fin (Nat.card h.W1)) := by simp
    rw [show hyp.muGrid hG hodd 0 k
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu
          (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) from by unfold Hypothesis.muGrid; rfl,
      hfc]
  -- `θ ≠ 1`: else `μ_{0k}(1) = θ(1) = 1`, contradicting `hdk1`.
  have hθne : θ ≠ trivialIrreducibleCharacter ↥h.K := by
    intro htriv
    apply hdk1
    rw [hrow0]
    have h2 : (ClassFunction.restrict h.K
        ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu 0
          : ClassFunction ↥M ℂ)) (1 : ↥h.K) = (θ : ClassFunction ↥h.K ℂ) (1 : ↥h.K) := by
      rw [hθeq]
    rw [ClassFunction.restrict_apply] at h2
    rw [htriv] at h2
    simpa using h2
  -- The column sum is `Ind_{M'}^M θ`, so it lies in `S`.
  refine ⟨θ, hθne, ?_⟩
  change (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
    = ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ)
  rw [hind, ← Equiv.sum_comp (finCongr hcardW1.symm)
    (fun i' => ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm k))).mu i'
      : ClassFunction ↥M ℂ))]
  exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)

open scoped FiniteInduce in
/-- **§10 column-sum norm** (Peterfalvi (10.5)/(10.6), `‖μ_k‖² = w₁`): the `W₂`-column sum
`μ_k = ∑_{0≤i<w₁} μ_{ik}` has squared norm `w₁`, since its `w₁` summands are orthonormal
(`muGrid_inner_self` on the diagonal, `muGrid_inner_within_column` off it).  This is the
`‖μ_k^{τ₁}‖² = w₁` factor in the Cauchy–Schwarz bound of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGrid_column_sum_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (j : Fin hyp.w2) :
    ClassFunction.inner (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
        (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j) = (hyp.w1 : ℂ) := by
  have := hyp.finiteG
  classical
  -- per-pair inner products: `1` on the diagonal, `0` off it.
  have hpair : ∀ i i' : Fin hyp.w1, ClassFunction.inner (hyp.muGrid hG hodd i j)
      (hyp.muGrid hG hodd i' j) = (if i' = i then 1 else 0) := by
    intro i i'
    by_cases h : i' = i
    · subst h; rw [if_pos rfl]; exact hyp.muGrid_inner_self hG hodd i' j
    · rw [if_neg h]; exact hyp.muGrid_inner_within_column hG hodd j (Ne.symm h)
  have hrow : ∀ i : Fin hyp.w1, ClassFunction.inner (hyp.muGrid hG hodd i j)
      (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) = 1 := by
    intro i
    rw [OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_congr rfl (fun i' _ => hpair i i'), Finset.sum_ite_eq' Finset.univ i]
    simp
  rw [OddOrder.RepresentationTheory.inner_sum_left,
    Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

open scoped FiniteInduce in
/-- **§10 μ-grid ⊥ a degree-distinct irreducible** (Peterfalvi (10.5), `(μ_{ij}, ζ) = 0`): the
certain-type character `μ_{ij}` is orthogonal to any irreducible character `χ` of a *different*
degree.  Both are irreducible, so `(μ_{ij}, χ) ∈ {0, 1}` and equals `1` only if `μ_{ij} = χ`; a
degree mismatch `μ_{ij}(1) ≠ χ(1)` rules that out.

This is the orthogonality `(μ_{ij}, ζ) = 0` (and `(μ_{ij}, ζ̄) = 0`) to the degree-`w₁` member
`ζ ∈ S` in the norm `‖α_{ij}‖² = 2 + n²` of the (10.5) `a = 0` argument: the caller supplies the
degree mismatch (`μ_{i0}(1) = 1 ≠ w₁`, and `μ_{ij}(1) = d ≠ w₁` since `n·w₁ = d − δ`, `d > 1`,
`w₁ > 1`).  It needs no Clifford theory — only orthonormality of irreducibles. -/
theorem Hypothesis.muGrid_inner_eq_zero_of_apply_one_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {χ : ClassFunction ↥M ℂ} (hχirr : IsIrreducibleCharacter χ)
    (hne : hyp.muGrid hG hodd i j 1 ≠ χ 1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j) χ = 0 := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have hμirr : IsIrreducibleCharacter (hyp.muGrid hG hodd i j) := by
    rw [emj]; exact OddOrder.RepresentationTheory.IrreducibleCharacter.isIrreducible _
  rw [OddOrder.RepresentationTheory.irr_cf_inner hμirr hχirr,
    if_neg (fun heq => hne (by rw [heq]))]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖α_{ij}‖² = 2 + n²`**: the squared norm of the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ`.  The triple `{μ_{ij}, μ_{i0}, ζ}` is orthonormal — `μ_{ij}` and
`μ_{i0}` are orthonormal certain-type characters (`muGrid_inner_self` / `muGrid_inner_cross_column`,
`j ≠ 0`), and both are orthogonal to the degree-distinct irreducible `ζ`
(`muGrid_inner_eq_zero_of_apply_one_ne`, from the degree mismatches `hdζ`/`h0ζ`) — so
`‖α‖² = 1 + δ² + n² = 2 + n²` (`δ² = 1`).  The reversed inner products use `inner_conj_symm`.

This is the `‖α_{ij}^τ‖²` input to the Cauchy–Schwarz bound of the (10.5) `a = 0` argument (the
Dade isometry `τ` preserves the norm).  The caller supplies the degree mismatches
`μ_{i0}(1) = 1 ≠ w₁` and `μ_{ij}(1) = d ≠ w₁` (from `n·w₁ = d − δ`, `d > 1`, `w₁ > 1`). -/
theorem Hypothesis.muGridAlpha_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = 2 + (n : ℂ) ^ 2 := by
  have := hyp.finiteG
  classical
  have hA := hyp.muGrid_inner_self hG hodd i j
  have hB := hyp.muGrid_inner_self hG hodd i 0
  have hZ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hP := hyp.muGrid_inner_cross_column hG hodd i i hj0
  have hP' := hyp.muGrid_inner_cross_column hG hodd i i (Ne.symm hj0)
  have hQ := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hR := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hQ' : ClassFunction.inner ζ (hyp.muGrid hG hodd i j) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i j) ζ, hQ, star_zero]
  have hR' : ClassFunction.inner ζ (hyp.muGrid hG hodd i 0) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i 0) ζ, hR, star_zero]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
    hA, hB, hZ, hP, hP', hQ, hQ', hR, hR', star_intCast, star_natCast,
    mul_zero, sub_zero, zero_sub, mul_one]
  rcases hδpm with h | h <;> subst h <;> push_cast <;> ring

open scoped FiniteInduce in
/-- **§10 `W₁`-vanishing of the column difference** (Peterfalvi (10.5), first step, via (4.3.c) +
(4.4)): on `W₁^#`, the materialized character `μ_{ij}` equals `δ_j` times the column-`0` character
`μ_{i0}`.  Indeed `x ∈ W₁^# ⊆ V = W − W₂`, so (4.3.c) gives `μ_{ij}(x) = δ_j·ω_{ij}(x)` and
`μ_{i0}(x) = δ_0·ω_{i0}(x) = ω_{i0}(x)` (`δ_0 = 1` by (4.4)); on `W₁` the linear characters `ω_{ij}`
and `ω_{i0}` agree (the `W₂`-dual is trivial on `W₁`, `wSnd = 1`), so `μ_{ij}(x) = δ_j·μ_{i0}(x)`.
This is the `μ`-grid form of the (10.5) claim that `α_{ij}` vanishes on `W₁`. -/
theorem Hypothesis.muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {x : ↥M} (hxW1 : (x : G) ∈ hyp.typeP.W1) (hx1 : x ≠ 1) :
    hyp.muGrid hG hodd i j x
      = (hyp.muColumnSign hG hodd j : ℂ) * hyp.muGrid hG hodd i 0 x := by
  have := hyp.finiteG
  classical
  -- Reconstruct the §6 host and instances exactly as in `Hypothesis.muGrid`/`muColumnSign`
  -- (instances synthesized, *not* provided explicitly, to match the def's `unfold; rfl`).
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- `x` as an element of `h.W1` and of `sdiff.V = W − W₂`.
  have hxhW1 : x ∈ h.W1 := Subgroup.mem_subgroupOf.mpr hxW1
  have hxV : x ∈ h.sdiffTICyclicHypothesis.V := by
    refine ⟨(le_sup_left : h.W1 ≤ _) hxhW1, fun hxW2 => hx1 ?_⟩
    exact Subgroup.mem_bot.mp (h.W_disjoint.le_bot (Subgroup.mem_inf.mpr ⟨hxhW1, hxW2⟩))
  -- The generic `W₁`-collapse: `(columnFamily χ).mu k x = δ_χ · (columnFamily 1).mu k x`.
  have keyW1 : ∀ (χ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : Fin (Nat.card h.W1)),
      ((h.columnFamily χ).mu k : ClassFunction ↥M ℂ) x
        = ((h.columnFamily χ).sign : ℂ) * ((h.columnFamily 1).mu k : ClassFunction ↥M ℂ) x := by
    intro χ k
    have hwsub : (⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ : ↥h.sdiffTICyclicHypothesis.W)
        ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr hxhW1
    have hwsnd : h.sdiffTICyclicHypothesis.wSnd
        ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ = 1 :=
      h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hwsub
    -- chiColumn value formula (inline, valid for the bare `Hypothesis`).
    have hchiform : ∀ (χ' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
        (h.chiColumn χ' k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
            ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩
          = ((h.w1CharEquiv k) (h.sdiffTICyclicHypothesis.wFst
              ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂ)
            * (χ' (h.sdiffTICyclicHypothesis.wSnd
              ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂ) := by
      intro χ'
      rw [OddOrder.Peterfalvi.S06.Hypothesis.chiColumn, h.sdiffTICyclicHypothesis.omega_apply]
      change (((h.w1CharEquiv k) (h.sdiffTICyclicHypothesis.wFst _)
          * χ' (h.sdiffTICyclicHypothesis.wSnd _) : ℂˣ) : ℂ) = _
      rw [Units.val_mul]
    -- the `W₂`-dual factor is trivial on `W₁` (`wSnd = 1`), so the value is `χ`-independent.
    have hsnd1 : ∀ (χ' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
        (χ' (h.sdiffTICyclicHypothesis.wSnd ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂˣ)
          = 1 := fun χ' => by rw [hwsnd]; exact map_one χ'
    have hchieq : (h.chiColumn χ k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩
        = (h.chiColumn 1 k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ := by
      rw [hchiform χ, hchiform 1, hsnd1 χ, hsnd1 1]
    rw [h.certainType_apply_eq_of_mem_V χ k hxV, h.certainType_apply_eq_of_mem_V 1 k hxV,
      h.certainType_zero_column_anchor.1, hchieq, Int.cast_one, one_mul]
  -- Evaluate `muGrid`/`muColumnSign` in `columnFamily` terms (the `unfold; rfl` idiom of the
  -- producer's `hmg`), then apply `keyW1` (column `0` is the trivial dual).
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have emj : hyp.muGrid hG hodd i j
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have em0 : hyp.muGrid hG hodd i 0
      = ((h.columnFamily (finCardEquivCharacterGroup _
          (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu
          (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  have esign : hyp.muColumnSign hG hodd j
      = (h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [emj, em0, esign, hdual0]
  exact keyW1 _ _

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **§10 reconciliation on `V`** (the M-side ↔ σ-side link of (10.5)): for `v ∈ V = typePV`,
`μ_{ij}(v) = δ_j · ω_{ij}^σ(v)` where `ω^σ = alignedOmegaSigmaGrid`.  Both sides reduce to the §6
column character `chiColumn χ₂ i` evaluated at `v`: the M-side by (4.3.c)
(`certainType_apply_eq_of_mem_V`, giving `μ_{ij}(v) = δ_j·chiColumn(v)`), the σ-side because
`alignedOmegaSigma` is `σ_∫` of the transported `chiColumn`, restored on `V` by
`sigmaIntegral_apply_of_mem_V`; the `W ≤ M ≤ G` isomorphism `e` carries `v` to itself, so the two
`chiColumn` arguments agree.  This is the alignment that makes the (10.5) Dade-image identity hold
(impossible with the independently-indexed `omegaSigmaGrid`). -/
theorem Hypothesis.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {v : G} (hv : v ∈ typePV M hyp.typeP) (hvM : v ∈ M) :
    hyp.muGrid hG hodd i j ⟨v, hvM⟩
      = (hyp.muColumnSign hG hodd j : ℂ) * hyp.alignedOmegaSigmaGrid hG hodd i j v := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  set χ₂ := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2)) (finCongr hcardW2sub.symm j)
    with hχ₂
  have hvtic : v ∈ tic.V := hv
  have hWeq : h.W1 ⊔ h.W2 = hyp.typeP.W.subgroupOf M := typePData_sup_subgroupOf_eq hyp.typeP
  have hvW : (⟨v, hvM⟩ : ↥M) ∈ h.W1 ⊔ h.W2 := by
    rw [hWeq, Subgroup.mem_subgroupOf]; exact hv.1
  -- `⟨v, hvM⟩ ∈ sdiff.V = W − W₂` (`v ∈ typePV = W − (W₁ ∪ W₂) ⊆ W − W₂`).
  have hvsdiffV : (⟨v, hvM⟩ : ↥M) ∈ h.sdiffTICyclicHypothesis.V := by
    refine ⟨hvW, ?_⟩
    intro hvW2
    exact hv.2 (Or.inr (Subgroup.mem_subgroupOf.mp hvW2))
  -- the transport `e` carries `v` to itself (same underlying `G`-element).
  have he_coe : ((e ⟨v, tic.V_subset_W hvtic⟩ : ↥(h.W1 ⊔ h.W2)) : ↥M) = ⟨v, hvM⟩ := by
    apply Subtype.ext
    change ((MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm
        ((Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm
          ⟨v, tic.V_subset_W hvtic⟩) : ↥M) : G) = v
    rw [MulEquiv.subgroupCongr_apply]; rfl
  -- the two `chiColumn` arguments (from (4.3.c) and from `e`) agree.
  have harg : (⟨⟨v, hvM⟩, h.sdiffTICyclicHypothesis.V_subset_W hvsdiffV⟩
        : ↥h.sdiffTICyclicHypothesis.W)
      = e ⟨v, tic.V_subset_W hvtic⟩ := by
    apply Subtype.ext; rw [he_coe]
  -- unfold `alignedOmegaSigma` to `chiColumn (e ⟨v⟩)` on `V`.
  have eaos : hyp.alignedOmegaSigmaGrid hG hodd i j v
      = (h.chiColumn χ₂ (finCongr hcardW1.symm i) : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          (e ⟨v, tic.V_subset_W hvtic⟩) := by
    unfold Hypothesis.alignedOmegaSigmaGrid
    rw [tic.sigmaIntegral_apply_of_mem_V rfl app _ hvtic, ClassFunction.compHom_apply]
    rfl
  -- unfold `muGrid`/`muColumnSign` and apply (4.3.c); the two `chiColumn` arguments agree.
  have emj : hyp.muGrid hG hodd i j = (h.columnFamily χ₂).mu (finCongr hcardW1.symm i) := by
    unfold Hypothesis.muGrid; rfl
  have esign : hyp.muColumnSign hG hodd j = (h.columnFamily χ₂).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [emj, esign, eaos,
    h.certainType_apply_eq_of_mem_V χ₂ (finCongr hcardW1.symm i) hvsdiffV, harg]

open scoped FiniteInduce in
/-- **§10 column-`0` degree** (Peterfalvi (4.4)): `μ_{i0}(1) = 1`.  The column-`0` character is
`K`-trivial (`μ_{00} = 1_L` by the (4.4) anchor), of degree `1`; by within-column degree constancy
(`muGrid_apply_one_within_column`) every `μ_{i0}` has the same degree. -/
theorem Hypothesis.muGrid_zero_column_apply_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) :
    hyp.muGrid hG hodd i 0 1 = 1 := by
  have := hyp.finiteG
  classical
  rw [hyp.muGrid_apply_one_within_column hG hodd i 0]
  -- Reconstruct the §6 host, as in `Hypothesis.muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have hrow0 : (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 := by apply Fin.ext; simp
  have e00 : hyp.muGrid hG hodd 0 0
      = ((h.columnFamily (finCardEquivCharacterGroup _
          (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu
          (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [e00, hdual0, hrow0, h.certainType_zero_column_anchor.2,
    OddOrder.RepresentationTheory.trivialClassFunction_apply]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), support half**: the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` (for `ζ` induced from `M'`, the materialized degrees `d`, sign
`δ_j = δ`, and `n` with `n·w₁ = d − δ`) is supported on `A_0(M)`.

This is the **dade0-free** half of (10.5), following Peterfalvi's argument verbatim:
* `α_{ij}` vanishes at `1` (by `n·w₁ = d − δ` and `μ_{i0}(1) = 1`) and on `W₁^#`
  (`muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1` and `ζ` vanishing off `M'`);
* `ζ`, being induced from the normal `M'`, vanishes off `M'`, so a support point `z ∉ M'` is, by
  (2.1) (`mem_compl_conj_into_W`), `M`-conjugate to `x·y` with `x ∈ W₁^#`, `y ∈ W₂`; `y ≠ 1` (else
  `z` is conjugate into `W₁^#`, where `α` vanishes), so `x·y ∈ V` and `z ∈ V^M`;
* a support point `z ∈ M'` lies in `(M')^# ⊆ A(M)` (it centralizes itself).

Hence `Supp(α_{ij}) ⊆ A(M) ∪ V^M = A_0(M)`. -/
theorem Hypothesis.muGrid_alpha_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {i : Fin hyp.w1} {j : Fin hyp.w2} (_hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) :
    (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ).support ⊆ hyp.A0 := by
  have := hyp.finiteG
  classical
  -- `ζ` is induced from the normal `M'`, hence vanishes off `M'`.
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  -- the §6 host (for (2.1)) and the abbreviation `α`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  set α : ClassFunction ↥M ℂ :=
    hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ with hαdef
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `α(1) = 0`, hence `z ≠ 1`.
  have hα1 : α 1 = 0 := by
    rw [hαdef, ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.smul_apply,
      ClassFunction.smul_apply, hdeg, hμ0, hζ1, mul_one]
    have hnfC : (n : ℂ) * (hyp.w1 : ℂ) = (d : ℂ) - (δ : ℂ) := by exact_mod_cast hnf
    rw [hnfC]; ring
  have hz1 : z ≠ 1 := fun h0 => hz (h0 ▸ hα1)
  change (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  by_cases hzM' : (z : G) ∈ derivedInG M
  · -- `z ∈ M'`: lands in `A(M)` (it centralizes itself).
    left
    exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
      ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  · -- `z ∉ M'`: use (2.1) to conjugate into `W`, landing in `V^M`.
    right
    have hzK : z ∉ h.K := fun hk => hzM' (Subgroup.mem_subgroupOf.mp hk)
    obtain ⟨c, x, hxW1, hx1, y, hyW2, hconj⟩ := h.mem_compl_conj_into_W hzK
    have hxG : (x : G) ∈ hyp.typeP.W1 := Subgroup.mem_subgroupOf.mp hxW1
    have hyG : (y : G) ∈ hyp.typeP.W2 := Subgroup.mem_subgroupOf.mp hyW2
    -- `α` is conjugation-invariant, so `α z = α (x·y)`.
    have hconjα : α z = α (x * y) := by
      rw [← hconj]
      have hce := α.conj_eq z c⁻¹
      rw [inv_inv] at hce
      exact hce.symm
    -- `x ∉ M'` (`W₁ ∩ M' = 1`, `M_complement`), so `ζ` also vanishes at `x`.
    have hxK : x ∉ h.K := fun hk =>
      hx1 ((Subgroup.disjoint_def.mp h.isComplement.disjoint) hk hxW1)
    -- `y ≠ 1`: otherwise `α z = α x = 0`, contradicting `z ∈ Supp(α)`.
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hz
      rw [hconjα, mul_one, hαdef, ClassFunction.sub_apply, ClassFunction.sub_apply,
        ClassFunction.smul_apply, ClassFunction.smul_apply,
        hyp.muGrid_apply_eq_columnSign_mul_zeroColumn_of_mem_W1 hG hodd i j hxG hx1, hδj,
        hζvanish hxK]
      ring
    -- `x·y ∈ V`, so `z ∈ V^M` (the conjugator `c` lies in `M`).
    rw [OddOrder.GroupTheory.mem_conjClassSetIn]
    refine ⟨(x : G) * (y : G), ?_, (c : G), c.2, ?_⟩
    · -- `(x:G)·(y:G) ∈ typePV`
      have hxyW : (x : G) * (y : G) ∈ hyp.typeP.W := by
        rw [hyp.typeP.W_eq]; exact mul_mem (Subgroup.mem_sup_left hxG) (Subgroup.mem_sup_right hyG)
      simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or]
      refine ⟨hxyW, ?_, ?_⟩
      · intro hmem
        apply hy1
        have hyW1 : (y : G) ∈ hyp.typeP.W1 := by
          have heq : (y : G) = (x : G)⁻¹ * ((x : G) * (y : G)) := by group
          rw [heq]; exact mul_mem (inv_mem hxG) hmem
        have := (typePData_disjoint_W1_W2 hyp.typeP).le_bot (Subgroup.mem_inf.mpr ⟨hyW1, hyG⟩)
        rw [Subgroup.mem_bot] at this
        exact Subtype.ext this
      · intro hmem
        apply hx1
        have hxW2 : (x : G) ∈ hyp.typeP.W2 := by
          have heq : (x : G) = ((x : G) * (y : G)) * (y : G)⁻¹ := by group
          rw [heq]; exact mul_mem hmem (inv_mem hyG)
        have := (typePData_disjoint_W1_W2 hyp.typeP).le_bot (Subgroup.mem_inf.mpr ⟨hxG, hxW2⟩)
        rw [Subgroup.mem_bot] at this
        exact Subtype.ext this
    · -- `(c:G)·((x:G)·(y:G))·(c:G)⁻¹ = (z:G)`
      have hconjG : (c : G)⁻¹ * (z : G) * (c : G) = (x : G) * (y : G) := by
        have := congrArg (M.subtype) hconj
        rwa [map_mul, map_mul, map_inv] at this
      rw [← hconjG]; group

/-- The character parameters obtained in Peterfalvi (10.2)--(10.3).

The arithmetic fields are now de-opaqued to genuine identities: `degree_independent` is the
degree constancy `μ_{ij}(1) = d` (4.5.a), `n_formula` is `n·w₁ = d − δ`, and `alpha` is the
genuine virtual character `μ_{ij} − δ·μ_{i0} − n·ζ` (10.5).  The `δ_j`-independence (10.3) is now a
genuine clause of `w2_prime_and_parameter_independence` (via `Hypothesis.muColumnSign`), no longer a
placeholder field. -/
structure CharacterParameters {M : Subgroup G} (hyp : Hypothesis M) where
  zeta : ClassFunction ↥M ℂ
  zeta_mem_S : zeta ∈ hyp.Sset
  /-- (10.2): `ζ` is irreducible.  De-opaqued from a placeholder `Prop` to the genuine
  irreducibility predicate, now that `exists_zeta_in_inducedFamily_degree_w1` constructs such a
  `ζ`. -/
  zeta_irreducible : IsIrreducibleCharacter zeta
  d : ℕ
  delta : ℤ
  n : ℕ
  w2_prime : hyp.w2.Prime
  d_gt_one : 1 < d
  mu : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ
  omegaSigma : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ
  /-- (10.3) degree independence (4.5.a): `d = μ_{ij}(1)` is independent of the indices, for
  `0 ≤ i < w₁` and `0 < j < w₂`.  De-opaqued from a placeholder `Prop` to the genuine degree
  identity. -/
  degree_independent : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → mu i j 1 = (d : ℂ)
  /-- (10.3) the index relation `n = (d − δ)/w₁ ∈ ℕ`, in the cleared form `n·w₁ = d − δ`.
  De-opaqued from a placeholder `Prop`. -/
  n_formula : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - delta
  /-- (10.3) the parity input: `n` is even and positive, so `n ≥ 2`.  `d = μ_{ij}(1)` divides the
  odd `|M|` (a character degree), hence is odd; with `δ = ±1`, `w₁` odd and `n·w₁ = d − δ`, `n` is
  even, and `d > 1` forces `n > 0`.  This is the (10.3) fact used by (10.5)'s Cauchy–Schwarz
  (`n < 2` contradiction); de-opaqued (no longer a carried hypothesis of the §10 (10.5)
  endpoint). -/
  two_le_n : 2 ≤ n
  /-- (10.5): `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ`.  De-opaqued from a free field + placeholder
  formula to the genuine definition in terms of the `μ`-grid, `δ`, `n` and `ζ`. -/
  alpha : Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ :=
    fun i j => mu i j - (delta : ℂ) • mu i 0 - (n : ℂ) • zeta
  alpha_def : ∀ i j, alpha i j = mu i j - (delta : ℂ) • mu i 0 - (n : ℂ) • zeta := by
    intro i j; rfl
  /-- (10.5), support half: for `0 < j < w₂`, `α_{ij}` is supported on `A_0(M)`.  De-opaqued (and
  dade0-free) — materialized in the producer from `Hypothesis.muGrid_alpha_support`. -/
  alpha_support : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → (alpha i j).support ⊆ hyp.A0

/-- **Peterfalvi (10.4)**: the coherent-extension hypothesis for the family of
characters in (10.1).

De-opaqued: instead of an unconstrained `tau1` field plus an opaque `tau1_extends_tau_on_S : Prop`,
this carries the *genuine* coherence datum `IsCoherent hyp.tau hyp.Sset hyp.A0` (Peterfalvi (5.1)).
Its bundled `extension` is Peterfalvi's `τ₁`, exposed as `CoherentHypothesis.tau1`: a lattice
isometry on `ℤ[S]` (`coherent.extension_inner_eq`) extending `τ` on the supported lattice
`ℤ[S, A₀]` (`coherent.extends_on_supported`).  This is exactly the content of (10.4.b) ("`S` is
coherent and `τ₁` is an extension of `τ` to `ℤ[S]`"), no longer a free map + placeholder `Prop`. -/
structure CoherentHypothesis {M : Subgroup G} [Fintype G] [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis M) (params : CharacterParameters hyp) where
  /-- (10.4.b): the family `S` is coherent; the bundled `extension` is Peterfalvi's `τ₁`. -/
  coherent : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0

namespace CoherentHypothesis

/-- **Peterfalvi's `τ₁`** (10.4.b): the coherent extension of the Dade isometry `τ` to `ℤ[S]`,
projected out of the bundled `IsCoherent` datum.  It is a lattice isometry on `ℤ[S]` and agrees
with `τ` on the supported lattice `ℤ[S, A₀(M)]`. -/
noncomputable def tau1 {M : Subgroup G} [Fintype G] [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params) : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
  coh.coherent.extension

end CoherentHypothesis

/-- **Peterfalvi (8.8) for `M`, used at the start of (10.3)**: there is a maximal subgroup `S` of
`G`
of **Type II** such that `|S : [S,S]| = w₂`.

This is exactly the opening sentence of the proof of (10.3) ("By Theorem (8.8), there is a maximal
subgroup `S` of `G` of Type II such that `|S:[S,S]| = w₂`"): the type-`P` maximal `M` of (10.1)
participates in the case-(b) configuration of Theorem (8.8), one of whose two maximal subgroups is
of Type II and shares the cyclic factor order `w₂`.  Tying the generic case-(b) datum
(`theorem88_caseB_holds`) to the *given* `M` is the content of (8.8)/(8.13) applied to `M`; it goes
through the BG §16 partner-existence behind `theorem88_caseB_holds`. -/
theorem Hypothesis.exists_typeII_maximal_with_w2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ S : Subgroup G, S ∈ maximalSubgroups G ∧ IsTypeII S ∧
      ((derivedInG S).subgroupOf S).index = hyp.w2 := by
  -- The `M`-specific (8.8) partner now lives in §8 (`S10.exists_typeII_maximal_with_w2_of_typeP`),
  -- stated on the bare `TypePData`; here `hyp.w2 = |W₂(hyp.typeP)|`.
  simpa only [Hypothesis.w2, Hypothesis.W2] using
    OddOrder.Peterfalvi.S10.exists_typeII_maximal_with_w2_of_typeP hG hyp.typeP hyp.maximal
      hyp.type_alt

/-- **Peterfalvi (10.3), first clause**: `w₂` is prime.

By Theorem (8.8) there is a Type-II maximal subgroup `S` with `|S:[S,S]| = w₂`
(`exists_typeII_maximal_with_w2`); a Type-II maximal's cyclic factor `W₁(S)` has prime order
(Peterfalvi (8.6.a), carried by `TypePNontrivialCore`) and equals `|S:[S,S]|`
(`card_W1_eq_derived_index`), so `w₂` is prime.

This follows Peterfalvi's own proof of (10.3) verbatim and is **non-circular**: it does *not* route
through `no_typeV_maximal` (the way a generic case-(b) datum would, since `TypeVData` carries no
prime-order field), so it may be used to populate `CharacterParameters.w2_prime` *upstream* of the
(10.10) Type-V elimination — which is what unblocks the (10.2)/(10.3) producer below. -/
theorem Hypothesis.w2_prime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) : (hyp.w2).Prime := by
  obtain ⟨S, -, hSII, hindex⟩ := hyp.exists_typeII_maximal_with_w2 hG
  obtain ⟨dataII⟩ := hSII
  have hcard : Nat.card ↥dataII.typeP.W1 = hyp.w2 := by
    rw [dataII.typeP.card_W1_eq_derived_index]; exact hindex
  rw [← hcard]
  exact dataII.common.2.1

open scoped FiniteInduce in
/-- **Peterfalvi (10.3), arithmetic data**: the common nontrivial-column degree `d`, the sign
`δ`, and the integer `n = (d − δ)/w₁`, materialized from the §6 column family.

We pick a nontrivial column `j₀` (which exists because `w₂` is prime, hence `≥ 2`) and read off
`d = μ_{0 j₀}(1)` as a natural number (the degree of an irreducible character,
`exists_natDegree_characterDegree_dvd_card`).  `d > 1` is Peterfalvi (4.4): if `μ_{0 j₀}` had degree
`1` it would be linear, hence `K`-trivial, hence a column-`0` character — contradicting `χ₂ ≠ 1`
(`columnFamily_mu_ne`); this mirrors the crux of `exists_zeta_in_inducedFamily_degree_w1`. `δ` is
the
column sign; and the congruence `μ_{0 j₀}(1) ≡ δ (mod w₁)` (Peterfalvi (4.3.d),
`certainType_degree_modEq`) gives `n` with `n·w₁ = d − δ`.  The degree independence
`μ_{ij}(1) = d` for all `i` and all nontrivial `j` is the materialized (10.3) constancy
`muGrid_apply_one_eq`. -/
theorem Hypothesis.exists_charParamArith [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    ∃ (d : ℕ) (delta : ℤ) (n : ℕ), 1 < d ∧ (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - delta ∧ 2 ≤ n ∧
      (∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → hyp.muGrid hG hodd i j 1 = (d : ℂ)) ∧
      (∀ (j : Fin hyp.w2), j ≠ 0 → hyp.muColumnSign hG hodd j = delta) := by
  have := hyp.finiteG
  classical
  have hw2 := hyp.w2_prime hG
  have hw2ge : 2 ≤ hyp.w2 := hw2.two_le
  -- a nontrivial column index `j₀`
  let j₀ : Fin hyp.w2 := ⟨1, by omega⟩
  have hj₀ : j₀ ≠ 0 := Fin.ne_of_val_ne (by simp [j₀])
  -- Reconstruct the §6 host and instances exactly as in `Hypothesis.muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j₀)
  let k₀ : Fin (Nat.card h.W1) := finCongr hcardW1.symm 0
  -- `χ₂` is a nontrivial dual (the column-`0` dual is the trivial one).
  have hχ₂ne : χ₂ ≠ 1 := by
    intro heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hk0 : finCongr hcardW2sub.symm j₀ = 0 := (finCardEquivCharacterGroup _).injective heq
    have : (j₀ : ℕ) = 0 := by simpa using congrArg Fin.val hk0
    exact hj₀ (Fin.ext this)
  -- `muGrid 0 j₀ = (h.columnFamily χ₂).mu k₀` definitionally.
  have hmg : hyp.muGrid hG hodd 0 j₀ = ((h.columnFamily χ₂).mu k₀ : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid
    rfl
  -- `h.K = commutator ↥M` (so (4.4) applies).
  have hKeq : h.K = (derivedInG M).subgroupOf M := rfl
  have hKcomm : h.K = commutator ↥M := by
    rw [hKeq, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- `d := μ_{0 j₀}(1) ∈ ℕ`, with `d ∣ |M|` (a character degree divides the group order).
  obtain ⟨d, hd0, hdeg, hdvd⟩ :=
    OddOrder.Peterfalvi.S03.exists_natDegree_characterDegree_dvd_card
      ((h.columnFamily χ₂).mu k₀)
  rw [OddOrder.Peterfalvi.S03.characterDegree_def] at hdeg
  -- `d > 1` by (4.4): a nontrivial column is not linear (mirrors the `exists_zeta` crux).
  have hne1 : ((h.columnFamily χ₂).mu k₀ : ClassFunction ↥M ℂ) 1 ≠ 1 := by
    intro hmu1
    have hker : (h.K : Set ↥M) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        ((h.columnFamily χ₂).mu k₀ : ClassFunction ↥M ℂ) := by
      intro x hx
      have hx1 := ((h.columnFamily χ₂).mu k₀).isIrreducible
        |>.apply_eq_one_of_mem_commutator_of_apply_one_eq_one hmu1 (hKcomm ▸ hx)
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel, hx1,
        OddOrder.Peterfalvi.S03.characterDegree_def, hmu1]
    obtain ⟨i, hi⟩ := h.exists_certainType_zero_column_eq_of_subset_characterKernel _ hker
    exact h.columnFamily_mu_ne hχ₂ne k₀ i hi.symm
  have hd1 : 1 < d := by
    rw [hdeg] at hne1
    have : d ≠ 1 := fun hd => hne1 (by rw [hd]; norm_num)
    omega
  -- (4.3.d): `μ_{0 j₀}(1) = δ + w₁·a`.
  obtain ⟨a, ha⟩ := h.certainType_degree_modEq χ₂ k₀
  have hcardW1c : (Nat.card ↥h.W1 : ℂ) = (hyp.w1 : ℂ) := by exact_mod_cast hcardW1
  have hcombine : (d : ℂ) = ((h.columnFamily χ₂).sign : ℂ) + (hyp.w1 : ℂ) * (a : ℂ) := by
    rw [← hdeg, ha, hcardW1c]
  have hZ : (d : ℤ) = (h.columnFamily χ₂).sign + (hyp.w1 : ℤ) * a := by exact_mod_cast hcombine
  -- `a ≥ 0` (so `n := a.toNat` realizes `n·w₁ = d − δ`).
  have hw1posN : 0 < hyp.w1 := Nat.pos_of_ne_zero (NeZero.ne hyp.w1)
  have hw1pos : (0 : ℤ) < (hyp.w1 : ℤ) := by exact_mod_cast hw1posN
  have hdsign : (0 : ℤ) < (d : ℤ) - (h.columnFamily χ₂).sign := by
    rcases (h.columnFamily χ₂).sign_eq with hs | hs <;> rw [hs] <;> omega
  have hapos : 0 ≤ a := by
    by_contra hlt
    push Not at hlt
    have hwa : (hyp.w1 : ℤ) * a < 0 := mul_neg_of_pos_of_neg hw1pos hlt
    linarith [hZ, hdsign, hwa]
  -- (10.3): `n = a` is even (hence `≥ 2`).  `d = μ_{0 j₀}(1)` divides the odd `|M|` (a character
  -- degree), so `d` is odd; with `δ = ±1` and `w₁` odd, `n·w₁ = d − δ` is even, forcing `n` even;
  -- and `n > 0` (from `d > 1`), so `n ≥ 2`.  This is the parity input of (10.5)'s Cauchy–Schwarz.
  have hModd : Odd (Nat.card ↥M) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hdodd : Odd (d : ℤ) := by exact_mod_cast hModd.of_dvd_nat hdvd
  have hw1odd : Odd (hyp.w1 : ℤ) := by
    exact_mod_cast hModd.of_dvd_nat (Subgroup.card_dvd_of_le hyp.typeP.W1_le)
  have hδodd : Odd ((h.columnFamily χ₂).sign) := by
    rcases (h.columnFamily χ₂).sign_eq with hs | hs <;> rw [hs] <;> decide
  have hwa : (hyp.w1 : ℤ) * a = (d : ℤ) - (h.columnFamily χ₂).sign := by linarith [hZ]
  have haeven : Even a := by
    have heven : Even ((hyp.w1 : ℤ) * a) := by rw [hwa]; exact hdodd.sub_odd hδodd
    rcases Int.even_mul.mp heven with hcon | h
    · obtain ⟨k, hk⟩ := hw1odd; obtain ⟨m, hm⟩ := hcon; omega
    · exact h
  have ha2 : 2 ≤ a := by
    have hwapos : 0 < (hyp.w1 : ℤ) * a := by rw [hwa]; exact hdsign
    have hapos' : 0 < a := by
      rcases eq_or_lt_of_le hapos with h | h
      · rw [← h, mul_zero] at hwapos; exact absurd hwapos (lt_irrefl 0)
      · exact h
    obtain ⟨b, hb⟩ := haeven
    omega
  have hn2 : 2 ≤ a.toNat := by omega
  -- degree independence (the materialized (10.3) constancy).
  have hdi : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
      hyp.muGrid hG hodd i j 1 = (d : ℂ) := by
    intro i j hj
    rw [hyp.muGrid_apply_one_eq hG hodd hw2 i 0 hj hj₀, hmg]
    exact hdeg
  refine ⟨d, (h.columnFamily χ₂).sign, a.toNat, hd1, ?_, hn2, hdi, ?_⟩
  · rw [Int.toNat_of_nonneg hapos, mul_comm]
    linarith [hZ]
  · -- `δ_k = δ_{j₀} = δ` for every nontrivial column `k` (the (10.3) sign-independence).
    intro k hk
    refine (hyp.muColumnSign_eq_of_ne hG hodd hw2 hk hj₀).trans ?_
    unfold Hypothesis.muColumnSign
    rfl

open scoped FiniteInduce in
/-- **Peterfalvi (10.2)+(10.3), the character parameters of (10.4)**: assemble a genuine
`CharacterParameters` for the §10 Hypothesis from the materialized §6 data.

`ζ` is the degree-`w₁` irreducible of (10.2) (`exists_zeta_in_inducedFamily_degree_w1`), the `μ`-
and
`ω^σ`-grids are `muGrid`/`omegaSigmaGrid`, `w₂` is prime by the non-circular (10.3) first clause
(`Hypothesis.w2_prime`), and the degree data `d > 1`, `n·w₁ = d − δ`, `μ_{ij}(1) = d` come from
`exists_charParamArith`.  The `δ_j`-independence `δ_j = δ_{j'}` (10.3) is the genuine
`muColumnSign_eq_of_ne`.  Only the `τ₁`-level `Prop` placeholders remain trivial, pending the
(10.5)/(10.6) Dade calculations. -/
theorem Hypothesis.exists_charParameters [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      (params.zeta ∈ hyp.Sset ∧ IsIrreducibleCharacter params.zeta ∧
          params.zeta 1 = ((hyp.w1 : ℕ) : ℂ)) ∧
        (1 < params.d ∧
          (∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → params.mu i j 1 = (params.d : ℂ)) ∧
          (∀ (j j' : Fin hyp.w2), j ≠ 0 → j' ≠ 0 →
              hyp.muColumnSign hG hG.odd j = hyp.muColumnSign hG hG.odd j') ∧
          ((params.n : ℤ) * (hyp.w1 : ℤ) = (params.d : ℤ) - params.delta)) := by
  have := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  obtain ⟨ζ, hζS, hζirr, hζdeg⟩ := exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hodd
    (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
  obtain ⟨d, delta, n, hd1, hnf, hn2, hdi, hδindep⟩ := hyp.exists_charParamArith hG hodd
  exact ⟨{ zeta := ζ
           zeta_mem_S := hζS
           zeta_irreducible := hζirr
           d := d
           delta := delta
           n := n
           w2_prime := hyp.w2_prime hG
           d_gt_one := hd1
           mu := hyp.muGrid hG hodd
           omegaSigma := hyp.alignedOmegaSigmaGrid hG hodd
           degree_independent := hdi
           n_formula := hnf
           two_le_n := hn2
           alpha_support := fun i j hj =>
             hyp.muGrid_alpha_support hG hodd hj hζS (hdi i j hj)
               (hyp.muGrid_zero_column_apply_one hG hodd i) hζdeg hnf (hδindep j hj) },
    ⟨hζS, hζirr, hζdeg⟩, hd1, hdi,
    (fun _ _ hj hj' => hyp.muColumnSign_eq_of_ne hG hG.odd (hyp.w2_prime hG) hj hj'), hnf⟩

/-- **Peterfalvi (10.3)**: `w_2` is prime and the parameters `d`, `delta`, and
`n = (d - delta) / w_1` are well-defined and independent of the indices. -/
theorem w2_prime_and_parameter_independence [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      hyp.w2.Prime ∧ 1 < params.d ∧
        (∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 → params.mu i j 1 = (params.d : ℂ)) ∧
        (∀ (j j' : Fin hyp.w2), j ≠ 0 → j' ≠ 0 →
            hyp.muColumnSign hG hG.odd j = hyp.muColumnSign hG hG.odd j') ∧
        ((params.n : ℤ) * (hyp.w1 : ℤ) = (params.d : ℤ) - params.delta) := by
  obtain ⟨params, -, h2⟩ := hyp.exists_charParameters hG
  exact ⟨params, hyp.w2_prime hG, h2⟩

/-- **Every degree-`w₁` irreducible of `M` is non-real (`χ̄ ≠ χ`), Peterfalvi (1.1)**.  A
degree-`w₁`
irreducible character `χ` of the *odd-order* group `M` is *nontrivial* (`χ(1) = w₁ > 1`), so by
`not_isReal_of_ne_trivial_of_odd_card'` (the only self-conjugate irreducible of an odd group is the
trivial one) `χ` is not real, i.e. `χ.conj ≠ χ`.  No induced-character / orbit argument is needed.
This is the general form feeding both `zeta_conj_ne` and the `S(HC)` `τ₁`-vanishing arguments (each
`S(HC)` member `λ` — a degree-`w₁` irreducible — is non-real, so `λ^{τ₁}` vanishes on `V`). -/
theorem Hypothesis.inducedFamily_degree_w1_conj_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ} (hχirr : IsIrreducibleCharacter χ) (hχ1 : χ 1 = (hyp.w1 : ℂ)) :
    χ.conj ≠ χ := by
  have := hyp.finiteG
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hne : (⟨χ, hχirr⟩ : IrreducibleCharacter ↥M) ≠ trivialIrreducibleCharacter ↥M := by
    intro h
    have hz : χ 1 = (1 : ℂ) := by
      have hcoe := congrArg (fun c : IrreducibleCharacter ↥M => (c : ClassFunction ↥M ℂ) 1) h
      simpa using hcoe
    rw [hχ1] at hz
    have : hyp.w1 = 1 := by exact_mod_cast hz
    omega
  exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hModd hne

/-- **`ζ` is non-real (`ζ̄ ≠ ζ`)** — the `hzconj` input to the (10.6.b) Dade-value lemmas,
**directly
from Peterfalvi (1.1)**.  Thin `CharacterParameters` specialisation of
`inducedFamily_degree_w1_conj_ne` at `χ = params.zeta`. -/
theorem Hypothesis.zeta_conj_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {params : CharacterParameters hyp} (hz1 : params.zeta 1 = (hyp.w1 : ℂ)) :
    (params.zeta).conj ≠ params.zeta :=
  hyp.inducedFamily_degree_w1_conj_ne hG params.zeta_irreducible hz1

/-- **Parameter package with all (10.6.b) hypotheses** (the `tau1_values_and_norm_bound` /
`zeta_tau1_norm_ge_one` inputs).  Strengthens `exists_charParameters` to also expose the seven
conditions those Dade-value lemmas require, now that each is establishable: `mu`/`omegaSigma` are
the
materialized grids (`rfl`), `ζ ∈ S` and `ζ(1) = w₁` come from `(10.2)`, `δ_j = δ` from
`exists_charParamArith`, `δ = ±1` from `muColumnSign_eq_one_or_neg_one`, and `ζ̄ ≠ ζ` from
`zeta_conj_ne` (Peterfalvi (1.1)).  This is the single producer the `(10.8)` line-83 step consumes
(via the re-wrapped coherence `⟨coh.coherent⟩` for this `params`). -/
theorem Hypothesis.exists_charParameters_full [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    ∃ params : CharacterParameters hyp,
      params.mu = hyp.muGrid hG hG.odd ∧
      params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd ∧
      params.zeta ∈ inducedFamily M ∧ params.zeta 1 = (hyp.w1 : ℂ) ∧
      params.zeta.conj ≠ params.zeta ∧
      (params.delta = 1 ∨ params.delta = -1) ∧
      (∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) := by
  have := hyp.finiteG
  classical
  obtain ⟨ζ, hζS, hζirr, hζdeg⟩ := exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd
    (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
  obtain ⟨d, delta, n, hd1, hnf, hn2, hdi, hδindep⟩ := hyp.exists_charParamArith hG hG.odd
  refine ⟨{ zeta := ζ
            zeta_mem_S := hζS
            zeta_irreducible := hζirr
            d := d
            delta := delta
            n := n
            w2_prime := hyp.w2_prime hG
            d_gt_one := hd1
            mu := hyp.muGrid hG hG.odd
            omegaSigma := hyp.alignedOmegaSigmaGrid hG hG.odd
            degree_independent := hdi
            n_formula := hnf
            two_le_n := hn2
            alpha_support := fun i j hj =>
              hyp.muGrid_alpha_support hG hG.odd hj hζS (hdi i j hj)
                (hyp.muGrid_zero_column_apply_one hG hG.odd i) hζdeg hnf (hδindep j hj) },
    rfl, rfl, hζS, hζdeg, ?_, ?_, hδindep⟩
  · exact hyp.zeta_conj_ne hG hζdeg
  · have hw2 : 2 ≤ hyp.w2 := (hyp.w2_prime hG).two_le
    have hj : (⟨1, by omega⟩ : Fin hyp.w2) ≠ 0 := by simp [Fin.ext_iff]
    have hde := hδindep ⟨1, by omega⟩ hj
    have hs := hyp.muColumnSign_eq_one_or_neg_one hG hG.odd ⟨1, by omega⟩
    rw [hde] at hs
    exact hs

/-- **(10.2)/(10.3) character parameters built around a *given* `ζ`** — the `∀ ζ` form of
`exists_charParameters_full`.

`exists_charParameters_full` picks its own `ζ` via `exists_zeta_in_inducedFamily_degree_w1`; the
consumers that state a property "for every `ζ ∈ S` of degree `w₁`" (Peterfalvi (11.8)/(11.9), whose
book form quantifies over `ζ ∈ S(HC)`) need the parameters assembled around a `ζ` handed to them.

Nothing but the three `ζ`-fields depends on the choice: `d`, `δ`, `n`, `μ`, `ω^σ` and the arithmetic
come from `exists_charParamArith`, and the only field coupling `ζ` to the grid is
`alpha_support` (`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` supported on `A₀`), whose producer
`muGrid_alpha_support` is **already `ζ`-generic** — it takes exactly `hζS` and `hζdeg : ζ(1) = w₁`
(these are what make `α_{ij}` vanish at `1`, via `n·w₁ = d − δ` and `μ_{i0}(1) = 1`).  So the
degree condition is not a repo artefact: it is precisely what `α`'s support demands. -/
theorem Hypothesis.exists_charParameters_full_of_zeta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζdeg : ζ 1 = (hyp.w1 : ℂ)) :
    ∃ params : CharacterParameters hyp,
      params.zeta = ζ ∧
      params.mu = hyp.muGrid hG hG.odd ∧
      params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd ∧
      params.zeta ∈ inducedFamily M ∧ params.zeta 1 = (hyp.w1 : ℂ) ∧
      params.zeta.conj ≠ params.zeta ∧
      (params.delta = 1 ∨ params.delta = -1) ∧
      (∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) := by
  have := hyp.finiteG
  classical
  obtain ⟨d, delta, n, hd1, hnf, hn2, hdi, hδindep⟩ := hyp.exists_charParamArith hG hG.odd
  refine ⟨{ zeta := ζ
            zeta_mem_S := hζS
            zeta_irreducible := hζirr
            d := d
            delta := delta
            n := n
            w2_prime := hyp.w2_prime hG
            d_gt_one := hd1
            mu := hyp.muGrid hG hG.odd
            omegaSigma := hyp.alignedOmegaSigmaGrid hG hG.odd
            degree_independent := hdi
            n_formula := hnf
            two_le_n := hn2
            alpha_support := fun i j hj =>
              hyp.muGrid_alpha_support hG hG.odd hj hζS (hdi i j hj)
                (hyp.muGrid_zero_column_apply_one hG hG.odd i) hζdeg hnf (hδindep j hj) },
    rfl, rfl, rfl, hζS, hζdeg, ?_, ?_, hδindep⟩
  · exact hyp.zeta_conj_ne hG hζdeg
  · have hw2 : 2 ≤ hyp.w2 := (hyp.w2_prime hG).two_le
    have hj : (⟨1, by omega⟩ : Fin hyp.w2) ≠ 0 := by simp [Fin.ext_iff]
    have hde := hδindep ⟨1, by omega⟩ hj
    have hs := hyp.muColumnSign_eq_one_or_neg_one hG hG.odd ⟨1, by omega⟩
    rw [hde] at hs
    exact hs

end OddOrder.Peterfalvi.S12


