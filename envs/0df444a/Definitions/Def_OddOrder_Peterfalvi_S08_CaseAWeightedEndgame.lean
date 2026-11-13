-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseAWeightedEndgame
-- name    : OddOrder_Peterfalvi_S08_CaseAWeightedEndgame
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:21:34.259338+00:00
-- url     : https://prove2.me/theorems/65a2fe7b-c9a6-4f2a-8ecb-8faa3c0d5634
-- title:
--   Peterfalvi (6.8.3): case-(A) norm-weighted endgame
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.8.3). The case-(A) ($Z=Z(H)\cap H'$) form of the (6.8.3) contradiction, the certain-type/c2 analogue of the Frobenius version.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseAWeightedEndgame.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseAWeightedEndgame.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBWeightedEndgame
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCore

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **Peterfalvi (6.8.3) case-(A): non-coherence of `S` is impossible.**

If `X(Z) ∪ Y` (`Z = Zc = Z(H) ∩ H′`) is coherent but `S` is not, a contradiction follows.  The
break pair `{ψ, ψ̄}` is dispatched irreducible / column (case (A) cannot absorb columns into
`X(Z)`);
either way the norm-weighted (5.6) `X`-sum bound forces
`|W₁|·|H:Z|·(|Z|−1) ≤ 2|W₁|²·d` with `d = θ(1) ≤ √|H:Z|` (`ψ = Ind θ`), refuted by the case-(A) FPF
bound `2|W₁| ≤ |Z|−1` via `false_of_centralCommutator_break_arith`.  The FPF data (`hfpf`) and
`2 ≤ |H:Z|` (`hZ2`) are supplied by the caller (the case-(A) producer). -/
theorem false_of_coherentXunionYset_caseA_of_not_coherentS
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    (hZ2 : 2 ≤ Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
    (hfpf : 2 * Nat.card hyp.W1 ≤ Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)
    (hXYcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) : False := by
  classical
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  have := hyp.centralCommutator_normal
  -- break pair on `Sa = X(Zc) ∪ Y`, `Sb = S`.
  have hSaSb : hyp.Xset hyp.centralCommutator ∪ hyp.Yset ⊆ hyp.S := by
    rintro φ (hX | hY)
    · exact hyp.Xset_subset_S hX
    · exact hyp.Yset_subset_S hY
  have hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset) := by
    intro φ hφ
    rcases hφ with hX | hY
    · exact Or.inl (hyp.Xset_closedUnderConjugate_unconditional hyp.centralCommutator hX)
    · exact Or.inr (hyp.Yset_closedUnderConjugate hY)
  obtain ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁Sb, hψSb, hψnS₁, hψcnS₁, hS₁cohN, hncN⟩ :=
    exists_coherentBreakPair_general hyp.tau hSaSb hyp.S_finite hyp.S_closedUnderConjugate
      (S_hasNoRealCharacters_caseB hyp h46 hHK) hSaconj hXYcoh hncoh
  have hS₁fin : S₁.Finite := hyp.S_finite.subset hS₁Sb
  have hXsub : hyp.Xset hyp.centralCommutator ⊆ S₁ := fun φ hφ => hSaS₁ (Or.inl hφ)
  -- anchor `η ∈ Y` of degree `|W₁|`.
  obtain ⟨η, hηY⟩ := hyp.Yset_nonempty
  have hηS₁ : η ∈ S₁ := hSaS₁ (Or.inr hηY)
  have hηdeg : η 1 = (Nat.card hyp.W1 : ℂ) := hyp.Yset_apply_one hηY
  -- `ψ = Ind θ` (every `S`-member is induced), `d = θ(1)`, `d² ≤ |H:Zc|` ([Is] Cor 2.30,
  -- `Zc ≤ Z(H)`).
  have hψS : ψ ∈ hyp.S := hψSb
  have hψSeq := hψS
  rw [hyp.S_eq, Set.mem_ofPred_eq] at hψSeq
  obtain ⟨θ, hθne, hψeq⟩ := hψSeq
  obtain ⟨d, hdpos, hθd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have hdsq : d ^ 2 ≤ Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := by
    obtain ⟨d', hθd', hd'sq⟩ := θ.isIrreducible.exists_degree_sq_le_index
      (hyp.centralCommutator.subgroupOf H) hyp.centralCommutator_subgroupOf_le_center
    have hdd' : d = d' := by
      have hcast : (d : ℂ) = (d' : ℂ) := by rw [← hθd, hθd']
      exact_mod_cast hcast
    rw [hdd', ← Subgroup.index_eq_card]; exact hd'sq
  -- the norm-weighted (5.6) `X`-sum bound, dispatching on whether `ψ` is a column or irreducible.
  have hxb : (H.index : ℝ) * ((Nat.card ↥H : ℝ)
        - (Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) : ℝ))
      ≤ 2 * (ψ 1).re * (η 1).re := by
    rcases caseB_S_member_column_or_irreducible hyp h46 hHK hψS with ⟨χ₂, hχ₂, hcol⟩ | hirr
    · have h := xSum_le_two_psi_caseB_columnBreak hyp h46 hHK hW1
        (W2 := hyp.centralCommutator) hS₁Sb hS₁conj hS₁fin hS₁cohN.some hXsub hηY hηS₁ hχ₂
        (by rw [hcol]; exact hψnS₁) (by rw [hcol]; exact hψcnS₁) (by rw [hcol]; exact hncN)
      rwa [hcol] at h
    · exact xSum_le_two_psi_caseB hyp h46 hHK hW1 (W2 := hyp.centralCommutator) hS₁Sb hS₁conj
        hS₁fin hS₁cohN.some hXsub hηY hηS₁ hψSb hirr hψnS₁ hψcnS₁ hncN
  have hψre : (ψ 1).re = (H.index : ℝ) * (d : ℝ) := by
    rw [hψeq, ClassFunction.induce_apply_one, hθd]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
  have hηre : (η 1).re = (Nat.card hyp.W1 : ℝ) := by rw [hηdeg, Complex.natCast_re]
  rw [hψre, hηre] at hxb
  -- cast the real inequality to ℕ.
  have hZle : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hxbN : H.index * (Nat.card ↥H - Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
      ≤ 2 * (H.index * d) * Nat.card hyp.W1 := by
    rw [← Nat.cast_le (α := ℝ)]
    push_cast [Nat.cast_sub hZle]
    nlinarith [hxb]
  rw [hyp.index_mul_card_sub_factor (Z := hyp.centralCommutator), hyp.index_H_eq_card_W1] at hxbN
  -- discharge the arithmetic core (case-(A) single-FPF form).
  refine SibleyDadeHypothesis.false_of_centralCommutator_break_arith (w1 := Nat.card hyp.W1) (d :=
      d)
    (hZ := Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H))
    (cZ := Nat.card ↥(hyp.centralCommutator.subgroupOf H))
    Nat.card_pos hdpos hdsq hZ2 hfpf ?_
  calc Nat.card hyp.W1 * Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
          * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)
      = Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H)
          * (Nat.card hyp.W1 * (Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1)) := by ring
    _ ≤ 2 * (Nat.card hyp.W1 * d) * Nat.card hyp.W1 := hxbN
    _ = 2 * Nat.card hyp.W1 ^ 2 * d := by ring

/-- **Peterfalvi (6.8) case-(A) coherence producer** (`hcaseA` of the c2 dispatch).

The certain-type / c2 analogue of the Frobenius `nonempty_coherent_S_caseA_of_frobenius`: given the
case-(A) condition `Z(H) ∩ W₂ = 1` (`hA`), the `p`-group structure, and `H` non-abelian, `S` is
coherent.  Constructs the `X(Zc) ∪ Y` coherence seed inline (splitting on `|X(Zc)| ≥ 3` / `= 2` via
the degree-ratio crux `crux_general_of_higher_anchor_c2_caseA` and the `n = 2` relabel
`exists_Xcoherence_crux_of_card_two_c2_caseA`, both feeding
`coherentXunionYset_centralCommutator_diagonal_general_c2_caseA`), then lifts to `S` by the (6.8.3)
contradiction `false_of_coherentXunionYset_caseA_of_not_coherentS`.  The FPF bound
`2|W₁| ≤ |Zc|−1` is `centralCommutator_card_subgroupOf_lower_c2_caseA`; `2 ≤ |H:Zc|` from
`Zc ≤ H′ ⊊ H`.  Feeds the dispatch skeleton `nonempty_coherent_S_of_c2_of_branches` (`hcaseA`). -/
theorem nonempty_coherent_S_caseA_of_c2
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    (hA : Subgroup.center ↥H ⊓ h46.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  classical
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  by_contra hncoh
  set cert := h46.toCertainTypeHypothesis with hcertdef
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA (cert := cert) hHK hW1 hA hφ
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty :=
    hyp.Xset_centralCommutator_nonempty_c2_caseA (cert := cert) hHK hW1 hA hHnonab
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.Xset_finite hyp.centralCommutator
  have h2X : 2 ≤ (hyp.xBaseBlock hyp.centralCommutator).ncard :=
    hyp.two_le_xBaseBlock_ncard_c2_caseA (cert := cert) hHK hW1 hA hXne
  -- two distinct base-block anchors.
  obtain ⟨χ₁, hχ₁base, χ₂, hχ₂base, hne⟩ : ∃ a ∈ hyp.xBaseBlock hyp.centralCommutator,
      ∃ b ∈ hyp.xBaseBlock hyp.centralCommutator, b ≠ a := by
    obtain ⟨a, ha⟩ : (hyp.xBaseBlock hyp.centralCommutator).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard
      (s := hyp.xBaseBlock hyp.centralCommutator) (by omega) a
    exact ⟨a, ha, b, hb, hba⟩
  have hχ₁X := hyp.xBaseBlock_subset _ hχ₁base
  have hχ₂X := hyp.xBaseBlock_subset _ hχ₂base
  -- `η₁ ∈ Y` (degree `|W₁|`) and the degree ratio `a`.
  obtain ⟨η₁, hη₁⟩ := hyp.Yset_nonempty
  obtain ⟨a, ha_pos, ha⟩ := hyp.sMember_charValue_one_eq_mul_anchor (hyp.Xset_subset_S hχ₁X)
    (hyp.Yset_apply_one hη₁)
  rw [hyp.Yset_apply_one hη₁] at ha
  -- base block equal-degree.
  have hdegeq : ∀ χ' ∈ hyp.xBaseBlock hyp.centralCommutator, χ' 1 = χ₁ 1 := by
    intro χ' hχ'
    have hre := hyp.xBaseBlock_degree_re_eq hχ' hχ₁base
    rw [OddOrder.Peterfalvi.S03.characterDegree_def,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hre
    obtain ⟨d', _, hd'⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ', hXirr χ' (hyp.xBaseBlock_subset _ hχ')⟩ : IrreducibleCharacter ↥L)
    obtain ⟨d₁, _, hd₁⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hXirr χ₁ hχ₁X⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd' hd₁
    rw [hd', hd₁] at hre ⊢
    exact_mod_cast hre
  have hdeg2 : χ₂ 1 = χ₁ 1 := hdegeq χ₂ hχ₂base
  -- E2: the `Y`-witness with the good case (m = 2 relabel folded in).
  obtain ⟨cY, hgood⟩ :=
    hyp.exists_Ycoherence_hgood_c2_caseA (cert := cert) hHK hW1 hA hHnonab hp hp3 hHp hη₁ hχ₁X
      ha_pos ha
  -- build `X(Zc) ∪ Y` coherent, splitting on `|X(Zc)|`.
  have hXYcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.Xset hyp.centralCommutator ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    by_cases h3X : 3 ≤ (hyp.Xset hyp.centralCommutator).ncard
    · have hex : ∃ c ∈ hyp.Xset hyp.centralCommutator, c ≠ χ₁ ∧ c ≠ χ₂ := by
        have hpair : ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Xset hyp.centralCommutator := by
          intro x hx; rcases hx with rfl | rfl
          · exact hχ₁X
          · exact hχ₂X
        have hdc : (hyp.Xset hyp.centralCommutator \ {χ₁, χ₂}).ncard
            = (hyp.Xset hyp.centralCommutator).ncard - 2 := by
          rw [Set.ncard_sdiff hpair, Set.ncard_pair (Ne.symm hne)]
        have hcne : (hyp.Xset hyp.centralCommutator \ {χ₁, χ₂}).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]; intro he; rw [he, Set.ncard_empty] at hdc; omega
        obtain ⟨c, hcs, hcnp⟩ := hcne
        rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcnp
        exact ⟨c, hcs, hcnp.1, hcnp.2⟩
      have cX0 := hyp.Xset_centralCommutator_isCoherent_of_c2_caseA (cert := cert) hHK hW1 hA
        hHnonab hp hp3 hHp
      exact hyp.coherentXunionYset_centralCommutator_diagonal_general_c2_caseA (cert := cert)
        hHK hW1 hA hp hHp cX0 cY hη₁ hχ₁base ha
        (hyp.crux_general_of_higher_anchor_c2_caseA (cert := cert) hHK hW1 hA hp hHp cX0 cY hη₁
          hχ₁base hχ₂X hne hdeg2 hex.choose_spec.1 hex.choose_spec.2.1 hex.choose_spec.2.2 ha hgood)
    · have h2Xle : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
        le_trans h2X (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
      have h2Xeq : (hyp.Xset hyp.centralCommutator).ncard = 2 := by omega
      have hpairsub : ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Xset hyp.centralCommutator := by
        intro x hx; rcases hx with rfl | rfl
        · exact hχ₁X
        · exact hχ₂X
      have hXeq : hyp.Xset hyp.centralCommutator = ({χ₁, χ₂} : Set (ClassFunction ↥L ℂ)) :=
        (Set.eq_of_subset_of_ncard_le hpairsub
          (h2Xeq.le.trans_eq (Set.ncard_pair (Ne.symm hne)).symm) hXfin).symm
      have hexX := hyp.exists_Xcoherence_crux_of_card_two_c2_caseA (cert := cert) hHK hW1 hA
        hHnonab hp hp3 hHp cY hη₁ hχ₁X hχ₂X hne hdeg2 hXeq ha hgood
      exact hyp.coherentXunionYset_centralCommutator_diagonal_general_c2_caseA (cert := cert)
        hHK hW1 hA hp hHp hexX.choose cY hη₁ hχ₁base ha hexX.choose_spec
  -- FPF bound `2|W₁| ≤ |Zc| − 1`.
  have hfpf : 2 * Nat.card hyp.W1 ≤ Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1 := by
    have h := hyp.centralCommutator_card_subgroupOf_lower_c2_caseA (cert := cert) hHK hW1 hA hHnonab
    omega
  -- `2 ≤ |H:Zc|` from `Zc ≤ H′ ⊊ H`.
  have hZ2 : 2 ≤ Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := by
    have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
    let : Group.IsNilpotent ↥H := hyp.H_nilpotent
    have hcommlt : (⁅H, H⁆ : Subgroup ↥L) < H := by
      have h1 : _root_.commutator ↥H < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥H
      rw [← commutator_subgroupOf_self] at h1
      refine lt_of_le_of_ne (Subgroup.commutator_le_left H H) (fun heq => ?_)
      rw [heq, Subgroup.subgroupOf_self] at h1
      exact lt_irrefl _ h1
    have hZcnotle : ¬ H ≤ hyp.centralCommutator := fun h =>
      (ne_of_lt hcommlt) (le_antisymm (Subgroup.commutator_le_left H H)
        (le_trans h hyp.centralCommutator_le_commutator))
    have hne' : hyp.centralCommutator.subgroupOf H ≠ ⊤ := fun heq =>
      hZcnotle (Subgroup.subgroupOf_eq_top.mp heq)
    have hcard1 : Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) ≠ 1 := by
      rw [← Subgroup.index_eq_card]; exact mt Subgroup.index_eq_one.mp hne'
    have hcardpos : 0 < Nat.card (↥H ⧸ hyp.centralCommutator.subgroupOf H) := Nat.card_pos
    omega
  exact false_of_coherentXunionYset_caseA_of_not_coherentS hyp h46 hHK hW1 hZ2 hfpf ⟨hXYcoh⟩ hncoh

end OddOrder.Peterfalvi.S08


