-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems
-- name    : OddOrder_Peterfalvi_S08_CoherenceTheorems
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:27:41.180247+00:00
-- url     : https://prove2.me/theorems/096cfb87-9d4c-4c29-b6ef-4f8eb25c44a0
-- title:
--   Peterfalvi §8: Some Coherence Theorems, the (6.8) capstone
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §8, pp. 30-37: the (6.8) coherence capstone `sibleySetup_is_coherent`, with dispatch over the cases $X$ empty, Frobenius, (6.8)(c2) case A and case B.
--
--   Main definitions: `sibleySetup_is_coherent` (Peterfalvi (6.8) Theorem, under the faithful Sibley hypotheses `SibleyDadeHypothesis`) and `IndChainDecomposition` (the (6.8) to (7.10) consumer interface, a degree-scaled $Z$-chain decomposition).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CoherenceTheorems.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CoherenceTheorems.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCore
import Definitions.Def_OddOrder_Peterfalvi_S08_Theorem65c2
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseAWeightedEndgame
import Definitions.Def_OddOrder_Peterfalvi_S08_PGroupReduction

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

/-- **Peterfalvi (6.8) Theorem.**  Under the faithful Sibley hypotheses
`SibleyDadeHypothesis` (a)/(b)/(c), the set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` is
coherent: there is an integral isometric extension of the §4 Dade map `τ` from `Z[S, H^#]` to
`Z[S]` (`hyp.CoherenceTarget = IsCoherent hyp.tau S H^#`).

The proof dispatches on `hyp.cases`: the `X`-empty (abelian) branch is the `Y`-coherence
`coherenceTarget_of_Xset_empty`; the `X`-nonempty branch splits Frobenius
(`nonempty_coherent_S_of_frobenius`) vs (6.8)(c2) certain-type, where the (6.5) reduction makes
`H` a `p`-group and the (6.8.A/B) split on `Z(H) ∩ W₂` routes to the case-A producer
(`nonempty_coherent_S_caseA_of_c2`) or the case-B dispatch: `W₂ ⊊ H′` uses the (6.8.3) FPF
bootstrap (`nonempty_coherent_S_caseB_of_c2`), `W₂ = H′` uses the (6.8.2) seed directly
(`nonempty_coherent_S_caseB_edge`, since then `S = X(W₂) ∪ Y`).  Completed 2026-06-20; this was
one of the two sorries blocking §9 (7.10) `card_G0_lower_bound`
(`issues/0046-peterfalvi-s08-6-8-coherence.md`).

`noncomputable def` (not `theorem`) because `CoherenceTarget` (an `IsCoherent`) carries the
extension map `ν` as data, living in `Type`, not `Prop`. -/
noncomputable def sibleySetup_is_coherent {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (hyp : SibleyDadeHypothesis G L H) : hyp.CoherenceTarget := by
  haveI := hyp.H_normal
  by_cases hXe : hyp.Xset ⁅H, H⁆ = ∅
  · -- `X`-empty (abelian) branch: `S = Y`, discharged by the `Y`-coherence `coherentYset`.
    exact hyp.coherenceTarget_of_Xset_empty hXe
  · -- `X`-nonempty branch: dispatch on `hyp.cases` (Frobenius / (6.8)(c2) certain-type).
    have hXne : (hyp.Xset ⁅H, H⁆).Nonempty := Set.nonempty_iff_ne_empty.mpr hXe
    refine Nonempty.some ?_
    rcases hyp.cases with hF | ⟨h46, _hdade, hHK, hW1, hprime, hW2comm, hcop⟩
    · -- (c1) Frobenius
      exact nonempty_coherent_S_of_frobenius hyp hF hXne
    · -- (c2) certain-type: reduce to `H` a `p`-group ((6.5)), case-split (6.8.A/B) on `Z(H) ∩ W₂`.
      have : Finite ↥h46.W1 := inferInstance
      have : NeZero (Nat.card h46.W1) := ⟨Nat.card_pos.ne'⟩
      have : Invertible (Nat.card ↥h46.K : ℂ) := by
        have h : (Nat.card ↥h46.K : ℂ) = (Nat.card ↥H : ℂ) := by rw [hHK]
        rw [h]; infer_instance
      have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
      have : Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ) :=
        invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
      have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
      have : Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ) :=
        invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
      have hW2H : h46.W2 ≤ H := hW2comm.trans (by
        rw [Subgroup.commutator_le]; intro a ha b _hb; rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem ha _hb) (H.inv_mem ha)) (H.inv_mem _hb))
      by_contra hncoh
      have hbound := abelianization_card_le_of_not_coherent_c2 hyp h46 hHK hW1 hncoh
      have hsplit := caseAB_split_of_c2 h46 hW2H hprime
      refine hncoh (nonempty_coherent_S_of_c2_of_branches hyp h46 hHK hW1 hW2comm hcop hbound hsplit
        ?caseA ?caseB)
      case caseA =>
        intro p hp hHp hA
        refine nonempty_coherent_S_caseA_of_c2 hyp h46 hHK hW1
          (commutator_ne_bot_of_Xset_commutator_nonempty hyp hXne) ?_ hp
          (three_le_of_isPGroup_H hyp hp hHp) hHp
        rw [inf_comm]; exact disjoint_iff.mp hA
      case caseB =>
        intro p hp hHp hB
        have : Fintype ↥H := Fintype.ofFinite _
        have : Invertible (Nat.card ↥h46.W2 : ℂ) :=
          invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
        have : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
        have : Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ) :=
          invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
        have hW2cenL : h46.W2 ≤ Subgroup.center ↥L := caseB_W2_le_center_L hyp h46 hW1 hW2H hB
        have : h46.W2.Normal := ⟨fun w hw g => by
          have hc : g * w = w * g := Subgroup.mem_center_iff.mp (hW2cenL hw) g
          have hgw : g * w * g⁻¹ = w := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
          rw [hgw]; exact hw⟩
        have hderiv : h46.W2.subgroupOf H ≤ commutator ↥H := by
          rw [← commutator_subgroupOf_self]
          exact fun x hx => Subgroup.mem_subgroupOf.mpr (hW2comm (Subgroup.mem_subgroupOf.mp hx))
        have hW2Hne : h46.W2.subgroupOf H ≠ ⊥ := by
          rw [← (h46.W2.subgroupOf H).one_lt_card_iff_ne_bot,
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2H).toEquiv]
          exact hprime.one_lt
        have hXne' : (hyp.Xset h46.W2).Nonempty :=
          Xset_nonempty_of_subgroupOf_ne_bot_weighted hyp hW2Hne
        by_cases hWMgt : 1 < (h46.W2.subgroupOf H).relIndex (commutator ↥H)
        · exact nonempty_coherent_S_caseB_of_c2 hyp h46 hHK hW1 hW2H hcop hp hHp hprime hW2comm hB
            hWMgt hXne'
        · -- edge `W₂ = H′ = ⁅H,H⁆`: `relIndex = 1`, so `W₂.subgroupOf H = commutator H`.
          have hHHle : (⁅H, H⁆ : Subgroup ↥L) ≤ H := by
            rw [Subgroup.commutator_le]; intro a ha b _hb; rw [commutatorElement_def]
            exact H.mul_mem (H.mul_mem (H.mul_mem ha _hb) (H.inv_mem ha)) (H.inv_mem _hb)
          have hr1 : (h46.W2.subgroupOf H).relIndex (commutator ↥H) = 1 := by
            have hne0 : (h46.W2.subgroupOf H).relIndex (commutator ↥H) ≠ 0 := by
              have : Finite ↥(commutator ↥H) := inferInstance
              exact Subgroup.index_ne_zero_of_finite
            have hle1 : (h46.W2.subgroupOf H).relIndex (commutator ↥H) ≤ 1 := Nat.not_lt.mp hWMgt
            omega
          have hge : commutator ↥H ≤ h46.W2.subgroupOf H := Subgroup.relIndex_eq_one.mp hr1
          have hsubeq : h46.W2.subgroupOf H = commutator ↥H := le_antisymm hderiv hge
          have hcardeq : Nat.card ↥h46.W2 = Nat.card ↥(⁅H, H⁆ : Subgroup ↥L) := by
            rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2H).toEquiv,
              ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHHle).toEquiv,
              hsubeq, commutator_subgroupOf_self]
          have hWeq : h46.W2 = ⁅H, H⁆ := Subgroup.eq_of_le_of_card_ge hW2comm hcardeq.ge
          exact nonempty_coherent_S_caseB_edge hyp h46 hHK hW1 hW2H hB hderiv hcop hp hHp hprime
            hW2comm hW2cenL hWeq hXne'

/-- **Peterfalvi (6.8) → (7.10) consumer interface.**
A degree-scaled `Z`-chain decomposition: given a coherence input `τ` on `(S, A)`
and an orthonormal family `ζ : Fin n → ClassFunction L ℂ` in `S` with explicit
integer degree ratios `d : Fin n → ℤ` (`d 0 = 1`), the family of images
`χ t = ν (ζ t)` under the coherence extension `ν` is orthonormal, and
`τ (ζ t - d t • ζ 0) = χ t - d t • χ 0`.

This packages the orthonormal-subsets-with-Ind-equation language used in the
(7.10) proof (see `references/peterfalvi/04.9_*.mmd` L133-135). -/
structure IndChainDecomposition
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G)
    {n : ℕ} [NeZero n]
    (ζ : Fin n → ClassFunction L ℂ) (d : Fin n → ℤ)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The orthonormal output family `χ_t = ν(ζ_t)` in `ClassFunction G ℂ`. -/
  χ : Fin n → ClassFunction G ℂ
  /-- Each `χ_t` has norm `1`. -/
  norm_one : ∀ t, ClassFunction.inner (χ t) (χ t) = 1
  /-- Distinct indices give orthogonal `χ`. -/
  pairwise_inner_zero :
    ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (χ t) (χ u) = 0
  /-- The reference index has trivial scaling: `d 0 = 1`. -/
  d_zero : d 0 = 1
  /-- The Ind equation: `τ(ζ_t - d_t · ζ_0) = χ_t - d_t · χ_0`. -/
  image_eq :
    ∀ t, τ (ζ t - (d t) • ζ 0) = χ t - (d t) • χ 0

namespace IndChainDecomposition

variable {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

variable {n : ℕ} [NeZero n]

/-- The Ind-chain decomposition vanishes at the reference index: for `t = 0`,
`τ(ζ 0 - d 0 · ζ 0) = 0`. -/
@[simp] theorem image_eq_zero
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    τ (ζ 0 - (d 0) • ζ 0) = 0 := by
  rw [data.d_zero, one_smul, sub_self, map_zero]

end IndChainDecomposition

end OddOrder.Peterfalvi.S08


