-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIGridTranspose
-- name    : OddOrder_Peterfalvi_S12_TypeIIGridTranspose
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:18:12.58676+00:00
-- url     : https://prove2.me/theorems/b1f3f705-19b9-483f-b20a-25709fefee7b
-- title:
--   Peterfalvi (8.8)/(10.7): $\sigma$-agreement for the type $P$ pair grid transpose
-- statement:
--   Formalizes the $\sigma$-agreement bridge for the transpose of the type $P$ pair grid, used in (8.8) and (10.7) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §8 (8.8), §10 (10.7)).
--
--   Main declarations: `section16_pair_tic_W_eq` (The canonical pair shares its ambient `W`); `section16_pair_tic_W1_eq_W2` (The canonical pair swaps the first factor); `section16_pair_tic_W2_eq_W1` (The canonical pair swaps the second factor); `section16_pair_tic_V_eq` (The canonical pair shares its TI-set `V`).
--
--   The bundle also proves 13 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_TypeIIGridTranspose.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_TypeIIGridTranspose.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIColumnPin
import Definitions.Def_OddOrder_Peterfalvi_S12_TICyclicSigmaBridge
import Definitions.Def_OddOrder_Peterfalvi_S13_Section16PairData

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

open scoped IsMulCommutative

variable {G : Type*} [Group G]

section PairPackaging

open OddOrder.GroupTheory

open scoped Pointwise

open scoped FiniteInduce in
@[simp] theorem typePData_toTICyclicHypothesis_W [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    (typePData_toTICyclicHypothesis data hodd).W = data.W := rfl

open scoped FiniteInduce in
@[simp] theorem typePData_toTICyclicHypothesis_W1 [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    (typePData_toTICyclicHypothesis data hodd).W1 = data.W1 := rfl

open scoped FiniteInduce in
@[simp] theorem typePData_toTICyclicHypothesis_W2 [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    (typePData_toTICyclicHypothesis data hodd).W2 = data.W2 := rfl

open scoped FiniteInduce in
@[simp] theorem typePData_toTICyclicHypothesis_V [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    (typePData_toTICyclicHypothesis data hodd).V = typePV M data := rfl

/-- **The (8.4.b) centralizer law pins the partner's dual factor**: a `TypePData` on the
canonical partner `mp.T` whose cyclic factor `W₁` is the pair's dual κ-Hall `mp.Kstar`
automatically has `W₂ = mp.K`.  Both are the `T'`-centralizer of any `x ∈ K*#`: `data.W₂`
by the `centralizer_W1` field, `mp.K` by BG Theorem A(5)
(`typeP_derivedInG_inf_centralizer_kappaElement_eq` with the pairing `mp.K_eq`). -/
theorem section16_partner_typePData_W2_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPairCore G}
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    dataT.W2 = mp.K := by
  -- a nonidentity element of the dual κ-Hall `K* ≠ ⊥`
  have hKstarne : mp.Kstar ≠ ⊥ := fun hbot =>
    OddOrder.BG.Ch4.S14.card_kappaHall_ne_one mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
      (Subgroup.card_eq_one.mpr hbot)
  have := (Subgroup.nontrivial_iff_ne_bot mp.Kstar).mpr hKstarne
  obtain ⟨⟨x, hxK⟩, hxne⟩ := exists_ne (1 : ↥mp.Kstar)
  have hxne' : x ≠ 1 := fun h => hxne (Subtype.ext h)
  have hcen := dataT.centralizer_W1 x (hTW1.symm ▸ hxK) hxne'
  have hkstar := OddOrder.BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq hG
    mp.T_maximal mp.T_typeP mp.Kstar_le_T mp.Kstar_hall mp.K_eq x hxK hxne'
  exact hcen.symm.trans hkstar

/-- A `W₁`-reconciled partner `TypePData` has the pair's full cyclic factor:
`dataT.W = K ⊔ K*` (from `W = W₁ ⊔ W₂`, `W₁ = K*`, `W₂ = K`, and commutativity of `⊔`). -/
theorem section16_partner_typePData_W_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPairCore G}
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    dataT.W = mp.K ⊔ mp.Kstar := by
  rw [dataT.W_eq, hTW1, section16_partner_typePData_W2_eq hG dataT hTW1, sup_comm]

/-- **The (8.4.b) centralizer law pins the member's dual factor** (`S`-side mirror of
`section16_partner_typePData_W2_eq`): a `TypePData` on the pair's type-II member `mp.S`
whose cyclic factor `W₁` is the κ-Hall `mp.K` automatically has `W₂ = mp.K*`.  Both are
the `S'`-centralizer of any `x ∈ K^#`: `data.W₂` by the `centralizer_W1` field, `mp.K*` by
BG Theorem A(5) (`typeP_derivedInG_inf_centralizer_kappaElement_eq` with the pairing
`mp.Kstar_eq`). -/
theorem section16_S_typePData_W2_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPairCore G}
    (dataS : TypePData mp.S) (hSW1 : dataS.W1 = mp.K) :
    dataS.W2 = mp.Kstar := by
  have hKne : mp.K ≠ ⊥ := fun hbot =>
    OddOrder.BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall
      (Subgroup.card_eq_one.mpr hbot)
  have := (Subgroup.nontrivial_iff_ne_bot mp.K).mpr hKne
  obtain ⟨⟨x, hxK⟩, hxne⟩ := exists_ne (1 : ↥mp.K)
  have hxne' : x ≠ 1 := fun h => hxne (Subtype.ext h)
  have hcen := dataS.centralizer_W1 x (hSW1.symm ▸ hxK) hxne'
  have hkstar := OddOrder.BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq hG
    mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall mp.Kstar_eq x hxK hxne'
  exact hcen.symm.trans hkstar

open scoped FiniteInduce in
/-- **The canonical pair shares its ambient `W`** (Peterfalvi (8.8), `S ∩ T = W`): a
`(K, K*)`-reconciled `S`-side datum and a `W₁`-reconciled `T`-side datum give
`TICyclicHypothesis`s with the same `W = K ⊔ K*` — the `T`-side by
`section16_partner_typePData_W_eq`.  (The `S`-side reconciliations hold e.g. for `tp.Sdata`
via `Sdata_W1_eq`/`Sdata_W2_eq` + `W1_eq_K_and_W2_eq_Kstar`, and transfer to any
`TypesIIIIIIVSetup` datum equal to it.)  This is the `hW` input of the per-index σ-grid
identification (`ticyclic_sigma_omega_eq_of_V_eq`). -/
theorem section16_pair_tic_W_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPairCore G}
    (hodd : Odd (Nat.card G))
    {dataS : TypePData mp.S} (hSW1 : dataS.W1 = mp.K) (hSW2 : dataS.W2 = mp.Kstar)
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    (typePData_toTICyclicHypothesis dataS hodd).W
      = (typePData_toTICyclicHypothesis dataT hodd).W := by
  rw [typePData_toTICyclicHypothesis_W, typePData_toTICyclicHypothesis_W, dataS.W_eq,
    hSW1, hSW2, section16_partner_typePData_W_eq hG dataT hTW1]

open scoped FiniteInduce in
/-- **The canonical pair swaps the first factor**: the `S`-side `W₁` is the `T`-side `W₂`
(both are the κ-Hall `mp.K` — Peterfalvi (8.8), the role swap of the pair). -/
theorem section16_pair_tic_W1_eq_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPairCore G}
    (hodd : Odd (Nat.card G))
    {dataS : TypePData mp.S} (hSW1 : dataS.W1 = mp.K)
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    (typePData_toTICyclicHypothesis dataS hodd).W1
      = (typePData_toTICyclicHypothesis dataT hodd).W2 := by
  have hTW2 : dataT.W2 = mp.K := section16_partner_typePData_W2_eq hG dataT hTW1
  rw [typePData_toTICyclicHypothesis_W1, typePData_toTICyclicHypothesis_W2, hSW1, hTW2]

open scoped FiniteInduce in
/-- **The canonical pair swaps the second factor**: the `S`-side `W₂` is the `T`-side `W₁`
(both are the dual κ-Hall `mp.Kstar`). -/
theorem section16_pair_tic_W2_eq_W1 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPairCore G}
    (hodd : Odd (Nat.card G))
    {dataS : TypePData mp.S} (hSW2 : dataS.W2 = mp.Kstar)
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    (typePData_toTICyclicHypothesis dataS hodd).W2
      = (typePData_toTICyclicHypothesis dataT hodd).W1 := by
  rw [typePData_toTICyclicHypothesis_W2, typePData_toTICyclicHypothesis_W1, hSW2, hTW1]

open scoped FiniteInduce in
/-- **The canonical pair shares its TI-set `V`** (Peterfalvi (8.8) for the §10 → §5
bridges): a `(K, K*)`-reconciled `S`-side datum and a `W₁`-reconciled `T`-side datum
give `TICyclicHypothesis`s with the *same* `V = W ∖ (K ∪ K*)` — the `W`-blocks agree up to
the role swap `W₁ ↔ W₂` (`S`-side `(K, K*)`, `T`-side `(K*, K)`), and `V` is
swap-invariant (`ticyclic_V_eq_of_swap`). -/
theorem section16_pair_tic_V_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPairCore G}
    (hodd : Odd (Nat.card G))
    {dataS : TypePData mp.S} (hSW1 : dataS.W1 = mp.K) (hSW2 : dataS.W2 = mp.Kstar)
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar) :
    (typePData_toTICyclicHypothesis dataS hodd).V
      = (typePData_toTICyclicHypothesis dataT hodd).V :=
  ticyclic_V_eq_of_swap _ _ rfl rfl
    (section16_pair_tic_W_eq hG hodd hSW1 hSW2 dataT hTW1)
    (section16_pair_tic_W1_eq_W2 hG hodd hSW1 dataT hTW1)
    (section16_pair_tic_W2_eq_W1 hG hodd hSW2 dataT hTW1)

open scoped Classical FiniteInduce in
/-- **The (5.8) column sum of the `S`-side grid is a row sum of the `T`-side grid**
(issue 9079 item 4 at the canonical pair): the full `S`-grid column at `kcol` — the shape
of the dichotomy `typeII_nu_tau2_dichotomy` (whose `ticVdiff` setup *is* the `S`-side
bridge, `ticVdiff_typeIIHypothesis46_eq`) — equals the full `T`-grid row at the transported
index.  Pair instance of `ticyclic_chiFam_columnSum_transpose` over the shared `V`/`W` and
the role swap. -/
theorem section16_pair_chiFam_columnSum_transpose [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPairCore G}
    (hodd : Odd (Nat.card G))
    {dataS : TypePData mp.S} (hSW1 : dataS.W1 = mp.K) (hSW2 : dataS.W2 = mp.Kstar)
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar)
    (appS : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis dataS hodd))
    (appT : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis dataT hodd))
    (kcol : ((typePData_toTICyclicHypothesis dataS hodd).W2.subgroupOf
      (typePData_toTICyclicHypothesis dataS hodd).W) →* ℂˣ) :
    ∑ p : ((typePData_toTICyclicHypothesis dataS hodd).W1.subgroupOf
        (typePData_toTICyclicHypothesis dataS hodd).W) →* ℂˣ,
      (typePData_toTICyclicHypothesis dataS hodd).chiFam rfl appS (p, kcol)
      = ∑ q : ((typePData_toTICyclicHypothesis dataT hodd).W2.subgroupOf
          (typePData_toTICyclicHypothesis dataT hodd).W) →* ℂˣ,
        (typePData_toTICyclicHypothesis dataT hodd).chiFam rfl appT
          (kcol.comp (subgroupOfTransport
            (section16_pair_tic_W_eq hG hodd hSW1 hSW2 dataT hTW1).ge
            (section16_pair_tic_W2_eq_W1 hG hodd hSW2 dataT hTW1).ge), q) :=
  ticyclic_chiFam_columnSum_transpose _ _ rfl rfl
    (section16_pair_tic_V_eq hG hodd hSW1 hSW2 dataT hTW1)
    (section16_pair_tic_W_eq hG hodd hSW1 hSW2 dataT hTW1)
    (section16_pair_tic_W1_eq_W2 hG hodd hSW1 dataT hTW1)
    (section16_pair_tic_W2_eq_W1 hG hodd hSW2 dataT hTW1) appS appT kcol

open scoped Classical FiniteInduce in
/-- **The per-index grid transpose at the canonical pair, `T`-side → `S`-side** (Coq `etaC`
in the consumption direction): each `T = M`-side grid vector **is** an `S`-side grid vector
at the transported swapped index.  Pair instance of `ticyclic_chiFam_transpose` with the
roles read from the `T`-side (the swap equalities reversed).  This is what reduces an
`M`-side aligned-grid orthogonality claim ((5.3.b) `lam_ortho_grid`) to a pure `S`-side
grid computation. -/
theorem section16_pair_chiFam_transpose_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {mp : Section16MaximalPairCore G}
    (hodd : Odd (Nat.card G))
    {dataS : TypePData mp.S} (hSW1 : dataS.W1 = mp.K) (hSW2 : dataS.W2 = mp.Kstar)
    (dataT : TypePData mp.T) (hTW1 : dataT.W1 = mp.Kstar)
    (appS : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis dataS hodd))
    (appT : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (typePData_toTICyclicHypothesis dataT hodd))
    (P : ((typePData_toTICyclicHypothesis dataT hodd).W1.subgroupOf
        (typePData_toTICyclicHypothesis dataT hodd).W →* ℂˣ) ×
      ((typePData_toTICyclicHypothesis dataT hodd).W2.subgroupOf
        (typePData_toTICyclicHypothesis dataT hodd).W →* ℂˣ)) :
    (typePData_toTICyclicHypothesis dataT hodd).chiFam rfl appT P
      = (typePData_toTICyclicHypothesis dataS hodd).chiFam rfl appS
          (P.2.comp (subgroupOfTransport
              (section16_pair_tic_W_eq hG hodd hSW1 hSW2 dataT hTW1).symm.ge
              (section16_pair_tic_W1_eq_W2 hG hodd hSW1 dataT hTW1).symm.ge),
            P.1.comp (subgroupOfTransport
              (section16_pair_tic_W_eq hG hodd hSW1 hSW2 dataT hTW1).symm.ge
              (section16_pair_tic_W2_eq_W1 hG hodd hSW2 dataT hTW1).symm.ge)) :=
  ticyclic_chiFam_transpose _ _ rfl rfl
    (section16_pair_tic_V_eq hG hodd hSW1 hSW2 dataT hTW1).symm
    (section16_pair_tic_W_eq hG hodd hSW1 hSW2 dataT hTW1).symm
    (section16_pair_tic_W2_eq_W1 hG hodd hSW2 dataT hTW1).symm
    (section16_pair_tic_W1_eq_W2 hG hodd hSW1 dataT hTW1).symm appT appS P

/-- `IsHallSubgroup` is determined by the order: a subgroup of the same order as a Hall
`π`-subgroup is itself Hall (the index is pinned by Lagrange).  Upstream-hoist candidate
(`Isaacs/Ch03`). -/
theorem isHallSubgroup_of_card_eq {L : Type*} [Group L] [Finite L] {π : Set ℕ}
    {H K : Subgroup L} (hH : OddOrder.Isaacs.Ch03.IsHallSubgroup π H)
    (hcard : Nat.card K = Nat.card H) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup π K := by
  have h1 := Subgroup.card_mul_index H
  have h2 := Subgroup.card_mul_index K
  rw [hcard] at h2
  have hindex : K.index = H.index :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
  exact ⟨fun p hp => hH.1 p (by rwa [hcard] at hp),
    fun p hp => hH.2 p (by rwa [hindex] at hp)⟩

/-- **The cyclic factor `W₁` of a type-`P` datum is itself a κ-Hall subgroup**: `|W₁| = [M:M']`
equals the order of any Hall `κ(M)`-subgroup (`card_kappaHall_eq_derived_index`,
`TypePData.card_W1_eq_derived_index`), and Hall-ness is a card/index property
(`isHallSubgroup_of_card_eq`).  This is what lets the `M`-seeded pair construction
(`typeP_duality` at the §10 ambient `M`) take `K := hyp.typeP.W1` literally, so the pair's
dual factor is `W₁` by construction — no conjugation re-basing. -/
theorem typePData_W1_isHallSubgroup_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (data : TypePData M) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      (data.W1.subgroupOf M) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨K, hKM, hK, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (X := ⊥) bot_le (by simp)
  -- `K` is cyclic by BG Theorem A (mirror of `typePData_W1_hall_coprime`)
  obtain ⟨U', hU'hall, -⟩ :=
    OddOrder.Isaacs.Ch03.hall_D (G := ↥M)
      (π := (OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U := ⊥) (by simp)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'hall
  have : IsCyclic ↥K :=
    (OddOrder.BG.Ch4.S15.typeP_auxiliary_structure hG hM hKM (Subgroup.map_subtype_le U')
      hK rfl hU).2.1
  have hKW1 : Nat.card ↥K = Nat.card ↥data.W1 := by
    rw [OddOrder.BG.Ch4.S16.card_kappaHall_eq_derived_index hG hM hP hKM hK,
      data.card_W1_eq_derived_index]
  refine isHallSubgroup_of_card_eq hK ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hKW1]

/-- A maximal subgroup of type III, IV or V is **not** of type `P₂`: these types are `P₁`
(`kappa = sigmaComplementPrimes`, the BG §16 classification dictionary), and `P₁`/`P₂` are
exclusive by definition.  Discharges the `¬ IsTypeII mp.T` hypothesis of the strong
reduction `exists_conj_eq_S_of_isTypeII` when the pair is seeded at the §10 ambient `M`
(`Hypothesis.type_alt`); the same exclusivity forces the seeded pair's `P₂`-member (hence
the smaller κ-Hall, `K_lt_Kstar`) onto the partner side. -/
theorem not_isTypeP2_of_isTypeIII_or_IV_or_V [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (halt : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    ¬ OddOrder.BG.Ch4.S14.IsTypeP2 M := by
  intro hP2
  obtain ⟨-, -, hcIII_IV, hdV, -, -⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hM
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M := by
    rcases halt with hIII | hIV | hV
    · exact (hcIII_IV.mp (Or.inl hIII)).1
    · exact (hcIII_IV.mp (Or.inr hIV)).1
    · exact (hdV.mp hV).1
  exact hP2.2 hP1.2

/-- **The `M`-seeded canonical-pair data** (the pair-witness route of (10.7), issue 9079):
for a type-`P` non-`P₂` maximal `M` and a κ-Hall factor `W₁ ≤ M` (in practice
`hyp.typeP.W1`, `typePData_W1_isHallSubgroup_kappa`), BG `typeP_duality` **seeded at
`(M, W₁)`** produces the canonical partner `S` with the full Section16MaximalPair data in
which `T = M` and `Kstar = W₁` **literally** — no conjugation re-basing of the §10
machinery.  The labelling is forced (no relabel case split): `M` is not `P₂`, so the
duality disjunction pins `P₂` (hence type II, hence the *smaller* κ-Hall,
`isTypeP2_of_typeP_kappaHall_lt` contrapositive) onto the partner side. -/
theorem exists_section16MaximalPairCore_data_around [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M W1 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (hnotP2 : ¬ OddOrder.BG.Ch4.S14.IsTypeP2 M)
    (hW1M : W1 ≤ M)
    (hW1hall : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      (W1.subgroupOf M)) :
    ∃ S K : Subgroup G,
      S ∈ maximalSubgroups G ∧ S ≠ M ∧
      IsTypeNonI S ∧ IsTypeNonI M ∧ IsTypeII S ∧
      (∀ N : Subgroup G, N ∈ maximalSubgroups G →
        IsTypeI N ∨ (∃ g : G, MulAut.conj g • N = S) ∨ (∃ g : G, MulAut.conj g • N = M)) ∧
      K ≤ S ∧
      OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S) (K.subgroupOf S) ∧
      W1 = OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) ∧
      OddOrder.BG.Ch4.S14.IsTypeP S ∧
      ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S M ∧
      K = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (W1 : Set G) ∧
      IsCyclic ↥(K ⊔ W1) := by
  classical
  -- the type dictionaries (mirroring `exists_section16MaximalPair_data`)
  have notTypeI_imp_typeP : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
      ¬ IsTypeI N → OddOrder.BG.Ch4.S14.IsTypeP N := by
    intro N hN hnotI
    have hiff := (OddOrder.BG.Ch4.S16.proposition_type_classification hG hN).1
    have hnotF : ¬ OddOrder.BG.Ch4.S14.IsTypeF N := fun hF => hnotI (hiff.mpr hF)
    rw [OddOrder.BG.Ch4.S14.IsTypeP, Set.nonempty_iff_ne_empty]
    exact fun he => hnotF he
  have typeP_imp_nonI : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
      OddOrder.BG.Ch4.S14.IsTypeP N → IsTypeNonI N := by
    intro N hN hPN
    obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ :=
      OddOrder.BG.Ch4.S16.proposition_type_classification hG hN
    by_cases hk : OddOrder.BG.Ch4.S14.kappa N = OddOrder.BG.Ch4.S14.sigmaComplementPrimes N
    · have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 N := ⟨hPN, hk⟩
      by_cases hMF : OddOrder.BG.Ch4.S15.MF N = OddOrder.BG.Ch3.S10.Msigma N
      · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
      · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
        · exact Or.inr (Or.inl hIII)
        · exact Or.inr (Or.inr (Or.inl hIV))
    · exact Or.inl (hbII.mpr ⟨hPN, hk⟩)
  -- the partner via `typeP_duality`, seeded at `(M, W₁)`
  set K : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (W1 : Set G) with hKdef
  obtain ⟨-, -, Mstar, ⟨hMsMem, hMsP, hMnconjMs, ⟨hKleMs, hKhall, hW1eq⟩,
      hcyc, -, hP2disj, hcover⟩, -⟩ :=
    OddOrder.BG.Ch4.S14.typeP_duality hG hM hP hW1M hW1hall hKdef
  -- the labelling is forced: `M` is not `P₂`, so the partner is
  have hP2Ms : OddOrder.BG.Ch4.S14.IsTypeP2 Mstar := hP2disj.resolve_left hnotP2
  have hMsII : IsTypeII Mstar :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG hMsMem).2.1.mpr hP2Ms
  have hSne : Mstar ≠ M := by
    rintro rfl
    exact hMnconjMs (OddOrder.BG.Ch4.S14.IsConjugateSubgroup.refl Mstar)
  refine ⟨Mstar, K, hMsMem, hSne, typeP_imp_nonI Mstar hMsMem hMsP,
    typeP_imp_nonI M hM hP, hMsII, ?_, hKleMs, hKhall, hW1eq, hMsP,
    fun h => hMnconjMs h.symm, hKdef, ?_⟩
  · -- the covering, with the partner slot first
    intro N hN
    by_cases hNI : IsTypeI N
    · exact Or.inl hNI
    · rcases hcover N hN (notTypeI_imp_typeP N hN hNI) with hNM | hNMs
      · exact Or.inr (Or.inr hNM)
      · exact Or.inr (Or.inl hNMs)
  · rw [sup_comm]; exact hcyc

/-- **The `M`-seeded canonical pair, order-free `Core` form** (issue 1020 Phase 1a): a
`Section16MaximalPairCore` with `T = M` and `Kstar = W₁` literally, produced without any
(13.2.a)/`K_lt_Kstar` content — the pair the de-tainted (10.7)/(10.8) chain runs on. -/
theorem exists_section16MaximalPairCore_around [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M W1 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (hnotP2 : ¬ OddOrder.BG.Ch4.S14.IsTypeP2 M)
    (hW1M : W1 ≤ M)
    (hW1hall : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      (W1.subgroupOf M)) :
    ∃ mp : Section16MaximalPairCore G, mp.T = M ∧ mp.Kstar = W1 := by
  classical
  obtain ⟨S, K, hSmax, hSneM, hSnonI, hMnonI, hSII, hcov, hKleS, hKhall, hW1eq, hSP,
    hSnconj, hKdef, hcyc⟩ :=
    exists_section16MaximalPairCore_data_around hG hM hP hnotP2 hW1M hW1hall
  exact ⟨{ S := S
           T := M
           K := K
           Kstar := W1
           S_maximal := hSmax
           T_maximal := hM
           S_ne_T := hSneM
           S_nonI := hSnonI
           T_nonI := hMnonI
           one_typeII := Or.inl hSII
           theorem88_caseB := hcov
           K_le_S := hKleS
           K_hall := hKhall
           Kstar_eq := hW1eq
           S_typeP := hSP
           T_typeP := hP
           S_T_not_conj := hSnconj
           Kstar_le_T := hW1M
           Kstar_hall := hW1hall
           K_eq := hKdef
           Z_cyclic := hcyc
           S_typeP2 :=
             (OddOrder.BG.Ch4.S16.proposition_type_classification hG hSmax).2.1.mp hSII },
    rfl, rfl⟩

open scoped Classical FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **The §10 aligned σ-grid row is a full `χ`-family fiber sum** (the `M`-side half of the
(10.7) grid transpose): for every `W₁`-index character `r'char` of the §10 → §5 bridge
there is a row `r'` of `alignedOmegaSigmaGrid` whose sum over the full row equals the
`chiFam`-fiber sum `∑_q χ_{(r'char, q)}`.

The aligned grid at `(i, j)` is the `χ`-family member at the index
`omegaProdEquiv.symm (omegaProdCharTic (χ₂ j) i')` — as in
`exists_alignedOmegaSigmaGrid_chiFam_family`, with the internal transport `e` identified
pointwise with `ticWEquivSdiffW` (both fix the underlying element).  Its first index
component is constant along the row and enumerates `Ŵ₁` bijectively in `i`
(`omegaProdCharTic_symm_fst_eq` and Pontryagin counting `card_charGroup_subgroupOf`); its
second is constant in `i` and enumerates `Ŵ₂` bijectively in `j`
(`omegaProdCharTic_symm_snd_eq`/`_ne`).  So the row at the preimage of `r'char` sweeps
exactly the fiber.  This turns the transposed (5.8) column sum
(`section16_pair_chiFam_columnSum_transpose`) into the `nu_tau2_eq` row-sum shape of the
(10.7) cross-isometry package. -/
theorem Hypothesis.exists_alignedOmegaSigmaGrid_row_sum_eq_chiFam_fiber [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (r'char : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
      (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ) :
    ∃ r' : Fin hyp.w1,
      ∑ q : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ,
        (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
          (hyp.canonicalFullDadeApp hG hodd) (r'char, q)
        = ∑ j : Fin hyp.w2, hyp.alignedOmegaSigmaGrid hG hodd r' j := by
  have := hyp.finiteG
  classical
  -- context of `alignedOmegaSigmaGrid` (mirror of `exists_alignedOmegaSigmaGrid_chiFam_family`)
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : Fin hyp.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun j => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  let h46 := hyp.toHypothesis46 hG hodd
  have : NeZero (Nat.card h46.W1) := ⟨by have := h46.one_lt_card_W1; omega⟩
  -- the internal bridge `e` is `ticWEquivSdiffW h46` pointwise (both fix the `G`-element)
  have hew : ∀ x : ↥tic.W,
      e x = OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 x := fun x => by
    apply Subtype.ext
    apply Subtype.ext
    exact (OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW h46 x).symm
  -- the aligned grid value, in `chiFam`-at-`omegaProdCharTic`-index form
  have haligned : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      hyp.alignedOmegaSigmaGrid hG hodd i j
        = tic.chiFam rfl (hyp.canonicalFullDadeApp hG hodd)
            (tic.omegaProdEquiv.symm
              (OddOrder.Peterfalvi.S06.omegaProdCharTic h46 (χ₂ j)
                (finCongr hcardW1.symm i))) := by
    intro i j
    have hchar : OddOrder.Peterfalvi.S06.omegaProdCharTic h46 (χ₂ j) (finCongr hcardW1.symm i)
        = (h.sdiffTICyclicHypothesis.omegaProdChar
            (h.w1CharEquiv (finCongr hcardW1.symm i)) (χ₂ j)).comp e.toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      change (h.sdiffTICyclicHypothesis.omegaProdChar
            (h.w1CharEquiv (finCongr hcardW1.symm i)) (χ₂ j))
            (OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 x)
          = (h.sdiffTICyclicHypothesis.omegaProdChar
            (h.w1CharEquiv (finCongr hcardW1.symm i)) (χ₂ j)) (e x)
      rw [hew x]
    have step1 : hyp.alignedOmegaSigmaGrid hG hodd i j
        = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd)
            ((tic.omega ((h.sdiffTICyclicHypothesis.omegaProdChar
                (h.w1CharEquiv (finCongr hcardW1.symm i)) (χ₂ j)).comp e.toMonoidHom))
              : ClassFunction ↥tic.W ℂ) := by
      change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd) _ = _
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
      congr 1
    rw [step1, hchar, tic.sigma_omega rfl (hyp.canonicalFullDadeApp hG hodd)]
  -- the row-index map `r'' ↦ fst(index)`: constant in the column, bijective onto `Ŵ₁`
  let F : Fin hyp.w1 → ((tic.W1.subgroupOf tic.W) →* ℂˣ) := fun r'' =>
    (tic.omegaProdEquiv.symm (OddOrder.Peterfalvi.S06.omegaProdCharTic h46 1
      (finCongr hcardW1.symm r''))).1
  have hFinj : Function.Injective F := by
    intro a b hab
    have hsnd := omegaProdCharTic_symm_snd_eq h46 1
      (finCongr hcardW1.symm a) (finCongr hcardW1.symm b)
    have h1 : OddOrder.Peterfalvi.S06.omegaProdCharTic h46 1 (finCongr hcardW1.symm a)
        = OddOrder.Peterfalvi.S06.omegaProdCharTic h46 1 (finCongr hcardW1.symm b) :=
      tic.omegaProdEquiv.symm.injective (Prod.ext hab hsnd)
    have h2 := (MonoidHom.cancel_right
      (MulEquiv.surjective (OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46))).mp h1
    have h3 := (h.sdiffTICyclicHypothesis.omegaProdChar_inj h2).1
    exact (finCongr hcardW1.symm).injective (h.w1CharEquiv.injective h3)
  have hFbij : Function.Bijective F := by
    refine (Nat.bijective_iff_injective_and_card F).mpr ⟨hFinj, ?_⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_fin,
      tic.card_charGroup_subgroupOf tic.W1_le_W]
    rfl
  -- the column-index map `j ↦ snd(index)`: constant in the row, bijective onto `Ŵ₂`
  let Gcol : Fin hyp.w2 → ((tic.W2.subgroupOf tic.W) →* ℂˣ) := fun j =>
    (tic.omegaProdEquiv.symm (OddOrder.Peterfalvi.S06.omegaProdCharTic h46 (χ₂ j) 0)).2
  have hGinj : Function.Injective Gcol := by
    intro a b hab
    by_contra hne
    exact omegaProdCharTic_symm_snd_ne h46
      (fun hχ => hne ((finCongr hcardW2sub.symm).injective
        ((finCardEquivCharacterGroup _).injective hχ))) 0 hab
  have hGbij : Function.Bijective Gcol := by
    refine (Nat.bijective_iff_injective_and_card Gcol).mpr ⟨hGinj, ?_⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_fin,
      tic.card_charGroup_subgroupOf tic.W2_le_W]
    rfl
  -- pick the row hitting `r'char`, then sweep the fiber
  obtain ⟨r', hr'⟩ := hFbij.surjective r'char
  refine ⟨r', ?_⟩
  calc ∑ q : ((tic.W2.subgroupOf tic.W) →* ℂˣ),
        tic.chiFam rfl (hyp.canonicalFullDadeApp hG hodd) (r'char, q)
      = ∑ j : Fin hyp.w2,
          tic.chiFam rfl (hyp.canonicalFullDadeApp hG hodd) (r'char, Gcol j) :=
        (Fintype.sum_bijective Gcol hGbij _ _ (fun _ => rfl)).symm
    _ = ∑ j : Fin hyp.w2, hyp.alignedOmegaSigmaGrid hG hodd r' j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [haligned r' j]
        congr 1
        refine Prod.ext ?_ ?_
        · exact ((omegaProdCharTic_symm_fst_eq h46 (χ₂ j) 1
            (finCongr hcardW1.symm r')).trans hr').symm
        · exact (omegaProdCharTic_symm_snd_eq h46 (χ₂ j) (finCongr hcardW1.symm r') 0).symm

/-- The type-II-designated member of the canonical pair is indeed of type II:
`mp.S_typeP2` (Peterfalvi (13.2.a)) through the BG type dictionary
(`isTypeII_of_isTypeP2`, Proposition 16.1). -/
theorem section16_S_isTypeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (mp : Section16MaximalPairCore G) :
    IsTypeII mp.S :=
  OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG mp.S_maximal mp.S_typeP2

/-- **Peterfalvi (10.7) reduction, covering step** (Coq `Frob_der1_type2` head,
`PFsection10.v:552-556`): every type-II maximal subgroup `L` is conjugate to a member of
the canonical pair — to `mp.S`, or to `mp.T` with `mp.T` itself then of type II (types are
conjugation-invariant, `isTypeII_pointwise_smul`).  The type-I branch of the (8.8) covering
`theorem88_caseB` is killed by type exclusivity (`not_isTypeI_of_isTypeNonI`).

The `T`-branch is **not refutable from the pair data alone**: Peterfalvi (13.2.a) is
one-directional ("if `q < p` then `S` is of type II"), so the larger-κ member `mp.T` may
also be of type II; the Coq proof kills its corresponding branch only under the §10
contextual hypothesis `notMtype2` (the ambient pair member there is assumed not of type 2).
Consumers either use the returned `IsTypeII mp.T` certificate symmetrically (the pair
machinery of this file is `S`/`T`-symmetric through `exists_section16_partner_typePData`)
or discharge it with `exists_conj_eq_S_of_isTypeII` below. -/
theorem conj_eq_S_or_conj_eq_T_of_isTypeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (mp : Section16MaximalPairCore G)
    {L : Subgroup G} (hL : L ∈ maximalSubgroups G) (hLII : IsTypeII L) :
    (∃ g : G, MulAut.conj g • L = mp.S) ∨
      ((∃ g : G, MulAut.conj g • L = mp.T) ∧ IsTypeII mp.T) := by
  rcases mp.theorem88_caseB L hL with hI | hS | hT
  · exact absurd hI (OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG hL (Or.inl hLII))
  · exact Or.inl hS
  · refine Or.inr ⟨hT, ?_⟩
    obtain ⟨g, hg⟩ := hT
    exact hg ▸ isTypeII_pointwise_smul (MulAut.conj g) hLII

/-- **Peterfalvi (10.7) reduction, strong form**: if the partner `mp.T` is moreover not of
type II, every type-II maximal subgroup is conjugate to `mp.S` — the exact Lean form of the
Coq branch kill (`FTtypeJ` + `notMtype2`). -/
theorem exists_conj_eq_S_of_isTypeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (mp : Section16MaximalPairCore G)
    (hT : ¬ IsTypeII mp.T)
    {L : Subgroup G} (hL : L ∈ maximalSubgroups G) (hLII : IsTypeII L) :
    ∃ g : G, MulAut.conj g • L = mp.S := by
  rcases conj_eq_S_or_conj_eq_T_of_isTypeII hG mp hL hLII with hS | ⟨-, hTII⟩
  · exact hS
  · exact absurd hTII hT

/-- **The (10.7) WLOG entry** (Coq `Frob_der1_type2` head, the pair-witness reduction):
under Hypothesis (10.1) for `M`, every type-II maximal subgroup `S` is conjugate to the
`S`-member of an `M`-seeded canonical pair — a `Section16MaximalPair` with `T = M` and
`Kstar = hyp.typeP.W1` **literally**, so the §10 grid machinery of `M` plugs into the pair
lemmas with `dataT := hyp.typeP` unchanged.

Assembly: the seed Hall-ness is `typePData_W1_isHallSubgroup_kappa`, the non-`P₂`-ness of
`M` is `not_isTypeP2_of_isTypeIII_or_IV_or_V` at `hyp.type_alt`, the pair is
`exists_section16MaximalPair_around`, and the `T`-branch of the covering reduction
(`exists_conj_eq_S_of_isTypeII`) is killed by that same non-`P₂`-ness (Coq's contextual
`notMtype2`). -/
theorem Hypothesis.exists_seeded_pair_conj_typeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {S : Subgroup G} (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) :
    ∃ (mp : Section16MaximalPairCore G) (g : G),
      mp.T = M ∧ mp.Kstar = hyp.typeP.W1 ∧ MulAut.conj g • S = mp.S := by
  have hP : OddOrder.BG.Ch4.S14.IsTypeP M := hyp.bgTypeP hG
  have hnotP2 : ¬ OddOrder.BG.Ch4.S14.IsTypeP2 M :=
    not_isTypeP2_of_isTypeIII_or_IV_or_V hG hyp.maximal hyp.type_alt
  obtain ⟨mp, hT, hKstar⟩ := exists_section16MaximalPairCore_around hG hyp.maximal hP hnotP2
    hyp.typeP.W1_le (typePData_W1_isHallSubgroup_kappa hG hyp.maximal hP hyp.typeP)
  have hTnotII : ¬ IsTypeII mp.T := by
    rw [hT]
    exact fun hII => hnotP2
      ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.maximal).2.1.mp hII)
  obtain ⟨g, hg⟩ := exists_conj_eq_S_of_isTypeII hG mp hTnotII hSmax hSII
  exact ⟨mp, g, hT, hKstar, hg⟩

open scoped Classical FiniteInduce in
/-- **The (10.7) `ν^{τ₂}` row pin at the canonical pair** (issue 9079, the assembled grid
transpose): for the pair's type-II member `mp.S` with a `(K, K*)`-reconciled §9 setup and a
`T2`-coherence `c` (from `typeII_T2_coherent`), the coherent image of the reducible `ν` is
a **signed row sum of the `M`-side aligned σ-grid** — the exact
`TypeIICrossIsometryData.nu_tau2_eq` shape.

Chain: the (9.8) classification pins `ν` to a nontrivial column sum
(`typeII_reducible_inducedKernelFamily_eq_columnSum`); the (5.8) dichotomy pins `ν^{τ₂}` to
`±δ` times a full `S`-grid column (`typeII_nu_tau2_dichotomy`, running on
`ticVdiff_typeIIHypothesis46_eq`'s bridge); the pair transpose turns the column into a
`T = M`-side row (`section16_pair_chiFam_columnSum_transpose` at `dataT := hyp.typeP`,
`mp.Kstar = hyp.typeP.W1`); and the fiber sweep identifies that row with an aligned-grid
row (`exists_alignedOmegaSigmaGrid_row_sum_eq_chiFam_fiber`). -/
theorem Hypothesis.exists_nu_extension_eq_alignedRow_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPairCore G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_red : ¬ IsIrreducibleCharacter nu)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
            (derivedInG mp.S)
          ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S)) :
    ∃ (r' : Fin hyp.w1) (delta' : ℤ), (delta' = 1 ∨ delta' = -1) ∧
      c.extension nu
        = (delta' : ℂ) • ∑ j : Fin hyp.w2, hyp.alignedOmegaSigmaGrid hG hG.odd r' j := by
  classical
  subst hT
  -- `ν` is a nontrivial column sum ((9.8) classification through the world bridge)
  obtain ⟨χ₂, hne1, hkeq⟩ := typeII_reducible_inducedKernelFamily_eq_columnSum hG
    mp.S_maximal (section16_S_isTypeII hG mp) data.typeP
    (typeII_sOf_subset_inducedKernelFamily data Y hnu_mem) hnu_red
  -- the (5.8) dichotomy: `ν^{τ₂} = ±δ · (full S-grid column)`
  have hdich := typeII_nu_tau2_dichotomy hG mp.S_maximal (section16_S_isTypeII hG mp) data
    hlam_mem hlam_irr hnu_mem hdeg c hne1 hkeq 0
  -- any full `S`-grid column sum is an aligned-grid row sum (transpose + fiber sweep)
  have key : ∀ kcol : ((typePData_toTICyclicHypothesis data.typeP hG.odd).W2.subgroupOf
      (typePData_toTICyclicHypothesis data.typeP hG.odd).W) →* ℂˣ,
      ∃ r' : Fin hyp.w1,
        ∑ p : ((typePData_toTICyclicHypothesis data.typeP hG.odd).W1.subgroupOf
            (typePData_toTICyclicHypothesis data.typeP hG.odd).W) →* ℂˣ,
          (typePData_toTICyclicHypothesis data.typeP hG.odd).chiFam rfl
            (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
              (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP))
            (p, kcol)
          = ∑ j : Fin hyp.w2, hyp.alignedOmegaSigmaGrid hG hG.odd r' j := by
    intro kcol
    have htrans := section16_pair_chiFam_columnSum_transpose hG hG.odd hSW1 hSW2
      hyp.typeP hKstar.symm
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP))
      (hyp.canonicalFullDadeApp hG hG.odd) kcol
    obtain ⟨r', hr'⟩ := hyp.exists_alignedOmegaSigmaGrid_row_sum_eq_chiFam_fiber hG hG.odd
      (kcol.comp (subgroupOfTransport
        (section16_pair_tic_W_eq hG hG.odd hSW1 hSW2 hyp.typeP hKstar.symm).ge
        (section16_pair_tic_W2_eq_W1 hG hG.odd hSW2 hyp.typeP hKstar.symm).ge))
    exact ⟨r', htrans.trans hr'⟩
  rcases hdich with h | h
  · obtain ⟨r', hrow⟩ := key
      (((OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG mp.S_maximal
          (section16_S_isTypeII hG mp) data.typeP)).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic (typeIIHypothesis46 hG mp.S_maximal
          (section16_S_isTypeII hG mp) data.typeP) χ₂ 0)).2)
    refine ⟨r', ((typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp)
        data.typeP).columnFamily χ₂).sign,
      ((typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp)
        data.typeP).columnFamily χ₂).sign_eq, ?_⟩
    rw [h]
    exact congrArg (fun x => ((((typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).columnFamily χ₂).sign : ℂ)) • x) hrow
  · obtain ⟨r', hrow⟩ := key
      (((OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG mp.S_maximal
          (section16_S_isTypeII hG mp) data.typeP)).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic (typeIIHypothesis46 hG mp.S_maximal
          (section16_S_isTypeII hG mp) data.typeP) χ₂⁻¹ 0)).2)
    refine ⟨r', -((typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp)
        data.typeP).columnFamily χ₂).sign, ?_, ?_⟩
    · rcases ((typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp)
          data.typeP).columnFamily χ₂).sign_eq with hs | hs
      · exact Or.inr (by rw [hs])
      · exact Or.inl (by rw [hs]; norm_num)
    · rw [h, Int.cast_neg]
      exact congrArg (fun x => (-((((typeIIHypothesis46 hG mp.S_maximal
        (section16_S_isTypeII hG mp) data.typeP).columnFamily χ₂).sign : ℂ))) • x) hrow

/-- **Any type-II datum transports onto the canonical pair member with its factors
tracked** (the WLOG engine of the (10.7) conjugation transfer, issue 9079 (c)): for a
type-II maximal `S` with a `TypePData`, there are an `M`-seeded pair, a conjugator `u`
with `S^u = mp.S`, and a `(K, K*)`-reconciled datum on `mp.S` whose Fitting factor `H` and
complement `U` are the **conjugates of the given datum's** — so a Frobenius conclusion at
the pair member transports back to the given factors verbatim.

Composition of the seeded-pair reduction (`exists_seeded_pair_conj_typeII`) with the
Schur–Zassenhaus realignment of `exists_section16_partner_typePData` run on the `S`-side:
the transported `W₁` and the κ-Hall `mp.K` both complement `[mp.S, mp.S]`
(`M_complement` / `typeP_derivedInG_isComplement_kappaHall`), so an `mp.S`-conjugation
aligns them; `W₂ = K*` follows (`section16_S_typePData_W2_eq`), and conjugating the whole
datum (`TypePData.conj`) carries `H` and `U` along. -/
theorem exists_reconciled_conj_typePData_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {S : Subgroup G} (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (dataP : TypePData S) :
    ∃ (mp : Section16MaximalPairCore G) (u : G) (dataS : TypePData mp.S),
      mp.T = M ∧ mp.Kstar = hyp.typeP.W1 ∧
      MulAut.conj u • S = mp.S ∧
      dataS.W1 = mp.K ∧ dataS.W2 = mp.Kstar ∧
      dataS.H = MulAut.conj u • dataP.H ∧ dataS.U = MulAut.conj u • dataP.U := by
  classical
  obtain ⟨mp, g₀, hT, hKstar, hgS⟩ := hyp.exists_seeded_pair_conj_typeII hG hSmax hSII
  -- move the datum onto `mp.S`
  set data₁ : TypePData mp.S := hgS ▸ dataP.conj (MulAut.conj g₀) with hdata₁
  have hcastW1 : ∀ {X : Subgroup G} (h : X = mp.S) (d : TypePData X), (h ▸ d).W1 = d.W1 := by
    intro X h d; subst h; rfl
  have hcastH : ∀ {X : Subgroup G} (h : X = mp.S) (d : TypePData X), (h ▸ d).H = d.H := by
    intro X h d; subst h; rfl
  have hcastU : ∀ {X : Subgroup G} (h : X = mp.S) (d : TypePData X), (h ▸ d).U = d.U := by
    intro X h d; subst h; rfl
  have hd₁W1 : data₁.W1 = MulAut.conj g₀ • dataP.W1 := hcastW1 hgS _
  have hd₁H : data₁.H = MulAut.conj g₀ • dataP.H := hcastH hgS _
  have hd₁U : data₁.U = MulAut.conj g₀ • dataP.U := hcastU hgS _
  -- Schur–Zassenhaus: realign `data₁.W1` onto the κ-Hall `mp.K` inside `mp.S`
  have : IsCyclic ↥mp.K := mp.isCyclic_K
  have hKcompl := OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG
    mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
  have hS'sub : (derivedInG mp.S).subgroupOf mp.S = commutator ↥mp.S :=
    Subgroup.comap_map_eq_self_of_injective mp.S.subtype_injective _
  have : ((derivedInG mp.S).subgroupOf mp.S).Normal := by rw [hS'sub]; infer_instance
  have hN : Nat.Coprime (Nat.card ↥((derivedInG mp.S).subgroupOf mp.S))
      ((derivedInG mp.S).subgroupOf mp.S).index := by
    rw [hKcompl.symm.index_eq_card]
    exact OddOrder.BG.Ch4.S14.coprime_card_derived_kappaHall_of_isComplement'
      mp.K_hall hKcompl
  have hSsolv : Group.IsSolvable ↥mp.S := hG.isSolvable_of_mem_maximalSubgroups mp.S_maximal
  have hSolv : Group.IsSolvable ↥((derivedInG mp.S).subgroupOf mp.S) ∨
      Group.IsSolvable (↥mp.S ⧸ (derivedInG mp.S).subgroupOf mp.S) :=
    Or.inl (Group.isSolvable_of_isSolvable_injective
      (Subgroup.subtype_injective ((derivedInG mp.S).subgroupOf mp.S)))
  obtain ⟨n, -, hn⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hN hSolv
    data₁.M_complement hKcompl
  set g : G := (n : G) with hgdef
  have hcomp : mp.S.subtype.comp (MulAut.conj n).toMonoidHom
      = (MulAut.conj g).toMonoidHom.comp mp.S.subtype := by
    ext k
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hgdef, Subgroup.coe_mul, Subgroup.coe_inv]
  have hW1map : data₁.W1.map (MulAut.conj g).toMonoidHom = mp.K := by
    have key := congrArg (Subgroup.map mp.S.subtype) hn
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le data₁.W1_le,
      Subgroup.map_subgroupOf_eq_of_le mp.K_le_S] at key
    exact key
  have hW1smul : (MulAut.conj g) • data₁.W1 = mp.K := by
    rw [pointwise_mulAut_smul_eq_map]; exact hW1map
  have hgSfix : (MulAut.conj g) • mp.S = mp.S := Subgroup.conj_smul_eq_self_of_mem n.2
  set dataS : TypePData mp.S := hgSfix ▸ data₁.conj (MulAut.conj g) with hdataS
  have hSW1 : dataS.W1 = mp.K := by
    rw [hdataS, hcastW1 hgSfix,
      show (data₁.conj (MulAut.conj g)).W1 = (MulAut.conj g) • data₁.W1 from rfl, hW1smul]
  refine ⟨mp, g * g₀, dataS, hT, hKstar, ?_, hSW1,
    section16_S_typePData_W2_eq hG dataS hSW1, ?_, ?_⟩
  · rw [map_mul, mul_smul, hgS, hgSfix]
  · rw [hdataS, hcastH hgSfix,
      show (data₁.conj (MulAut.conj g)).H = (MulAut.conj g) • data₁.H from rfl, hd₁H,
      ← mul_smul, ← map_mul]
  · rw [hdataS, hcastU hgSfix,
      show (data₁.conj (MulAut.conj g)).U = (MulAut.conj g) • data₁.U from rfl, hd₁U,
      ← mul_smul, ← map_mul]

end PairPackaging

end OddOrder.Peterfalvi.S12


