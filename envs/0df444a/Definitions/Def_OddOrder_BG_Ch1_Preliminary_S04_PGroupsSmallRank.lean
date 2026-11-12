-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_PGroupsSmallRank
-- name    : OddOrder_BG_Ch1_Preliminary_S04_PGroupsSmallRank
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:51:45.731701+00:00
-- url     : https://prove2.me/theorems/45bb2155-b25d-4182-982c-15f43b1ff342
-- title:
--   BG §4: $p$-groups of small rank (tail)
-- statement:
--   The final part of Bender–Glauberman §4 on $p$-groups of small rank.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_ExtraspecialCommutator

namespace OddOrder.BG.Ch1.S04

open OddOrder.BG.Ch1.S02

section Prop48ExponentPrime

open OddOrder.GroupTheory

/-- **BG Proposition 4.8(a)** (BG mmd L1511-1518): if `p` is a prime, `R` is a `p`-group of
rank `r(R) ≤ 2` (here `pRank R p ≤ 2`) with exponent `p` (here `∀ x, x ^ p = 1`), then
`|R| ≤ p³`.

Following BG's proof: take a self-centralizing normal abelian subgroup `A ∈ SCN(R)` (obtained
from `Ch06.exists_maximal_normal_isMulCommutative` + `centralizer_eq_…`). Since `exp R = p`,
`A` is elementary abelian, so `|A| = p^{m(A)}` with `m(A) ≤ pRank R p ≤ 2`, giving `|A| ≤ p²`.
Conjugation embeds `R/A = R/C_R(A) ↪ Aut(A)`, so `|R/A| ∣ |Aut A|`; as `R/A` is a `p`-group
and `|Aut A|_p ≤ |GL(2,p)|_p = p` (for `|A| ≤ p²`), we get `|R/A| ≤ p`. Hence
`|R| = |R/A|·|A| ≤ p·p² = p³`. -/
theorem card_le_prime_cube_of_pRank_le_two_of_exponent_prime
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hrank : pRank R p ≤ 2) (hexp : ∀ x : R, x ^ p = 1) :
    Nat.card R ≤ p ^ 3 := by
  classical
  have hp : p.Prime := Fact.out
  -- ── Step (i): take `A ∈ SCN(R)`, get self-centralizing `C_R(A) = A` (BG "Take A ∈ SCN(R)").
  obtain ⟨A, hA_normal, hA_comm, hA_max⟩ :=
    OddOrder.Isaacs.Ch06.exists_maximal_normal_isMulCommutative (P := R)
  have : A.Normal := hA_normal
  have hCent : Subgroup.centralizer (A : Set R) = A :=
    OddOrder.Isaacs.Ch06.centralizer_eq_of_maximal_normal_isMulCommutative hR hA_comm hA_max
  -- ── Step (ii): `exp p` ⇒ `A` elementary abelian; `|A| = p^kA`, `kA ≤ 2`, so `|A| ≤ p²`.
  have hA_ea : (A : Subgroup R).IsElementaryAbelian p := by
    refine ⟨isMulCommutative_iff.mp hA_comm, fun a => ?_⟩
    apply Subtype.ext
    push_cast
    exact hexp (a : R)
  let : IsMulCommutative (↥A) := IsMulCommutative.of_comm hA_ea.comm
  let := hA_ea.zmodModule
  have hlog_le : Nat.log p (Nat.card (↥A)) ≤ 2 := le_trans (le_pRank A hA_ea) hrank
  have hA_pow : Nat.card (↥A) = p ^ (Nat.log p (Nat.card (↥A))) := by
    rw [hA_ea.log_card_eq_finrank]
    exact hA_ea.card_eq_pow_finrank
  set kA := Nat.log p (Nat.card (↥A)) with hkA
  have hA_card : Nat.card (↥A) = p ^ kA := hA_pow
  have hA_le : Nat.card (↥A) ≤ p ^ 2 := by
    rw [hA_card]; exact Nat.pow_le_pow_right hp.pos hlog_le
  -- ── Step (iii): conjugation hom `R →* MulAut ↥A` with kernel `C_R(A) = A` ⇒ `R/A ↪ MulAut A`.
  let φ : R →* MulAut (↥A) := MulAut.conjNormal (H := A)
  -- `ker φ = C_R(A)` (the standard conjugation-kernel identity; cf. the local template
  -- `conjNormal_ker_eq_centralizer_local`), then `= A` by `hCent`.
  have hker_cent : φ.ker = Subgroup.centralizer (A : Set R) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg s hs
      have hfix0 : MulAut.conjNormal (H := A) g ⟨s, hs⟩ = (⟨s, hs⟩ : ↥A) := by
        rw [hg]; rfl
      have hfix : (g * s * g⁻¹ : R) = s := by
        have hh := congrArg (fun x : ↥A => (x : R)) hfix0
        simp only [MulAut.conjNormal_apply] at hh
        exact hh
      have : g * s * g⁻¹ * g = s * g := by rw [hfix]
      simpa [mul_assoc] using this.symm
    · intro hcent
      ext s
      have hcomm : (s : R) * g = g * (s : R) := hcent (s : R) s.2
      have hfix : MulAut.conjNormal (H := A) g s = s := by
        apply A.subtype_injective
        rw [Subgroup.coe_subtype, MulAut.conjNormal_apply, ← hcomm]; group
      rw [hfix]; rfl
  have hker : φ.ker = A := hker_cent.trans hCent
  let ψ : R ⧸ A →* MulAut (↥A) := QuotientGroup.lift A φ (by rw [hker])
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp only [ψ]
    rw [QuotientGroup.ker_lift, hker]
    simp
  have hdvd : Nat.card (R ⧸ A) ∣ Nat.card (MulAut (↥A)) :=
    Subgroup.card_dvd_of_injective ψ hψ_inj
  -- `R/A` is a `p`-group.
  obtain ⟨kQ, hkQ⟩ := IsPGroup.iff_card.mp (hR.to_quotient A)
  -- ── Step (iv): `|R/A| ≤ p` by case analysis on `kA ∈ {0, 1, 2}` (BG's `|Aut A|_p ≤ p`).
  have hquot_le : Nat.card (R ⧸ A) ≤ p := by
    -- It suffices to show `kQ ≤ 1`; then `|R/A| = p^kQ ≤ p`.
    suffices hkQ_le : kQ ≤ 1 by
      rw [hkQ]
      calc p ^ kQ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hkQ_le
        _ = p := pow_one p
    -- Reduce to `¬ (p² ∣ |MulAut A|)`: if `kQ ≥ 2` then `p² ∣ p^kQ = |R/A| ∣ |MulAut A|`.
    by_contra hkQ_gt
    rw [not_le] at hkQ_gt
    have hp2_dvd : p ^ 2 ∣ Nat.card (MulAut (↥A)) := by
      refine dvd_trans ?_ hdvd
      rw [hkQ]
      exact pow_dvd_pow p hkQ_gt
    -- `|MulAut A| = ∏_{i<kA}(p^kA - pⁱ)` (the `|GL(kA, p)|` formula), with `kA ≤ 2`.
    have hfr := hA_ea.log_card_eq_finrank
    rw [← hkA] at hfr
    have hcard_aut_gen :
        Nat.card (MulAut (↥A)) = ∏ i : Fin kA, (p ^ kA - p ^ (i : ℕ)) := by
      rw [hA_ea.card_mulAut, ← hfr]
    -- Now derive a contradiction by computing `|MulAut A|` in each rank case.
    have hp2_not_dvd : ¬ p ^ 2 ∣ Nat.card (MulAut (↥A)) := by
      rw [hcard_aut_gen]
      clear hp2_dvd hcard_aut_gen hdvd
      interval_cases kA
      · -- `kA = 0`: empty product `= 1`, `p² ∤ 1`.
        simp only [Finset.univ_eq_empty, Finset.prod_empty]
        intro hdvd1
        have := Nat.le_of_dvd one_pos hdvd1
        have hlt : 1 < p ^ 2 := by have := hp.two_le; nlinarith
        omega
      · -- `kA = 1`: product `= p^1 - p^0 = p - 1`, and `p ∤ p - 1` ⇒ `p² ∤ p - 1`.
        simp only [Fin.prod_univ_one, Fin.isValue, Fin.val_zero, pow_zero, pow_one]
        intro hdvd_pred
        have hp_dvd : p ∣ p - 1 :=
          (dvd_pow_self p (by norm_num : (2:ℕ) ≠ 0)).trans hdvd_pred
        have hpred_pos : 0 < p - 1 := by have := hp.two_le; omega
        have := Nat.le_of_dvd hpred_pos hp_dvd
        omega
      · -- `kA = 2`: product `= (p²-1)(p²-p) = p(p-1)(p-1)(p+1)`, whose `p`-part is `p¹`.
        have hcard_aut :
            (∏ i : Fin 2, (p ^ 2 - p ^ (i : ℕ))) = p * (p - 1) * (p - 1) * (p + 1) := by
          simp only [Fin.prod_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
          have h_sq_sub_one : p ^ 2 - 1 = (p + 1) * (p - 1) := by
            simpa using Nat.sq_sub_sq p 1
          have h_sq_sub_self : p ^ 2 - p = p * (p - 1) := by
            calc p ^ 2 - p = p * p - p * 1 := by rw [pow_two, mul_one]
              _ = p * (p - 1) := (Nat.mul_sub_left_distrib p p 1).symm
          rw [h_sq_sub_one, h_sq_sub_self]; ring
        rw [hcard_aut]
        -- `p² ∤ p(p-1)(p-1)(p+1)` because `p ∤ (p-1)(p-1)(p+1)`.
        intro hp2_dvd_aut
        have hp_not_dvd_pred : ¬ p ∣ p - 1 := by
          intro h
          have hpred_pos : 0 < p - 1 := by have := hp.two_le; omega
          have := Nat.le_of_dvd hpred_pos h
          omega
        have hp_not_dvd_succ : ¬ p ∣ p + 1 := by
          intro h
          have hsub : p ∣ (p + 1) - p := Nat.dvd_sub h (dvd_refl p)
          have hsub_eq : (p + 1) - p = 1 := by omega
          rw [hsub_eq] at hsub
          exact hp.not_dvd_one hsub
        have hp_not_dvd_rest : ¬ p ∣ (p - 1) * (p - 1) * (p + 1) := by
          intro h
          rcases hp.dvd_mul.mp h with hleft | hsucc
          · rcases hp.dvd_mul.mp hleft with h1 | h2
            · exact hp_not_dvd_pred h1
            · exact hp_not_dvd_pred h2
          · exact hp_not_dvd_succ hsucc
        have hp_dvd_rest : p ∣ (p - 1) * (p - 1) * (p + 1) := by
          have hmul : p * p ∣ p * ((p - 1) * (p - 1) * (p + 1)) := by
            simpa [pow_two, mul_assoc] using hp2_dvd_aut
          exact Nat.dvd_of_mul_dvd_mul_left hp.pos hmul
        exact hp_not_dvd_rest hp_dvd_rest
    exact hp2_not_dvd hp2_dvd
  -- ── Step (v): `|R| = |R/A|·|A| ≤ p·p² = p³`.
  have hmul : A.index * Nat.card (↥A) = Nat.card R := Subgroup.index_mul_card A
  have hindex : A.index = Nat.card (R ⧸ A) := (Subgroup.index_eq_card A).symm
  calc Nat.card R = A.index * Nat.card (↥A) := hmul.symm
    _ ≤ p * p ^ 2 := by rw [hindex]; exact Nat.mul_le_mul hquot_le hA_le
    _ = p ^ 3 := by ring

end Prop48ExponentPrime

section Prop48ExponentP

open OddOrder.GroupTheory

open scoped commutatorElement

/-- **`p`-group order bounds nilpotency class.** For a finite `p`-group `G` with
`|G| ≤ p^(j+1)` and `1 ≤ j`, the nilpotency class satisfies `cl(G) ≤ j`.

This is the standard fact "a group of order `pⁿ` has class `< n`" specialised to the
`j ≥ 1` regime where it holds without the abelian-endpoint exception (`Cₚ` has class
`1 = 0 + 1` but order `p = p^(0+1)`, so the naive `n = 1`, `j = 0` instance is false;
hence the `1 ≤ j` hypothesis).

Proof by strong induction on `|G|`, both `G` and `j` generalised:
* `Subsingleton G`: class `= 0 ≤ j`.
* `Nontrivial G`, `j = 1`: `|G| ≤ p²`, so `G` is abelian (order `1`, `p`, or `p²`;
  the `p²` case is `IsPGroup.isMulCommutative_of_card_eq_prime_sq`), giving `Z(G) = ⊤` and
  `cl(G) ≤ 1`.
* `Nontrivial G`, `j ≥ 2`: `|Z(G)| = pᵏ` with `k ≥ 1` (`card_center_eq_prime_pow`), so
  `|G/Z| ≤ p^((j-1)+1)`; the inductive hypothesis (on `j - 1 ≥ 1`) gives
  `cl(G/Z) ≤ j - 1`, and `cl(G) = cl(G/Z) + 1 ≤ j`. -/
theorem nilpotencyClass_le_of_card_le_pow {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G) {j : ℕ} (hj : 1 ≤ j)
    (hcard : Nat.card G ≤ p ^ (j + 1)) : Group.nilpotencyClass G ≤ j := by
  have hp : p.Prime := Fact.out
  -- Strong induction on `|G|`, with `j` and the group (as `R'`) quantified inside the motive.
  let motive : ℕ → Prop := fun N =>
    ∀ (j : ℕ), 1 ≤ j → ∀ {R' : Type _} [Group R'] [Finite R'], IsPGroup p R' →
      Nat.card R' = N → Nat.card R' ≤ p ^ (j + 1) → Group.nilpotencyClass R' ≤ j
  refine (Nat.strongRecOn (motive := motive) (Nat.card G) ?_) j hj hG rfl hcard
  intro N ih j hj R' _ _ hR' hcardN hcardR'
  have : Group.IsNilpotent R' := hR'.isNilpotent
  rcases subsingleton_or_nontrivial R' with hsub | hnt
  · -- `Subsingleton R'`: class `= 0 ≤ j`.
    exact le_trans (le_of_eq (Group.nilpotencyClass_zero_iff_subsingleton.mpr hsub)) (Nat.zero_le j)
  · -- `Nontrivial R'`.
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR'
    -- `m ≥ 1` since `R'` is nontrivial.
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hpos
      · exfalso; rw [hm0, pow_zero] at hm
        exact (not_subsingleton_iff_nontrivial.mpr hnt)
          (Finite.card_le_one_iff_subsingleton.mp (le_of_eq hm))
      · exact hpos
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · -- `j = 1`: `|R'| ≤ p²` ⇒ `R'` abelian ⇒ `cl(R') ≤ 1`.
      have hj_eq : j = 1 := by omega
      subst hj_eq
      -- `R'` is commutative: `m ∈ {1, 2}` and `isMulCommutative_of_card_eq_prime_sq` / cyclic.
      have hcomm : ∀ a b : R', a * b = b * a := by
        have hm_le : m ≤ 2 := by
          have hpm : p ^ m ≤ p ^ 2 := by rw [← hm]; exact hcardR'
          exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpm
        interval_cases m
        · -- `|R'| = p`: cyclic, hence commutative.
          have : IsCyclic R' := isCyclic_of_prime_card (p := p) (by rw [hm, pow_one])
          obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R')
          intro a b
          obtain ⟨i, rfl⟩ := hg a
          obtain ⟨l, rfl⟩ := hg b
          exact zpow_mul_comm g i l
        · -- `|R'| = p²`: commutative.
          exact isMulCommutative_iff.mp
            (IsPGroup.isMulCommutative_of_card_eq_prime_sq hm)
      -- `Z(R') = ⊤`, so `upperCentralSeries R' 1 = ⊤`, giving `cl(R') ≤ 1`.
      rw [← Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le,
          Subgroup.upperCentralSeries_one, eq_top_iff]
      intro z _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hcomm g z
    · -- `j ≥ 2`: recurse on `R'/Z`.
      -- `|Z(R')| = pᵏ`, `k ≥ 1`.
      obtain ⟨k, hk_pos, hk⟩ := IsPGroup.card_center_eq_prime_pow hm hm_pos
      -- `|Z| · |R'/Z| = |R'|`.
      have hZmul : Nat.card (Subgroup.center R') * Nat.card (R' ⧸ Subgroup.center R') =
          Nat.card R' := by
        rw [← Subgroup.index_eq_card]; exact (Subgroup.center R').card_mul_index
      -- `|R'/Z| ≤ p^((j-1)+1) = p^j`.
      have hquot_le : Nat.card (R' ⧸ Subgroup.center R') ≤ p ^ ((j - 1) + 1) := by
        have hj_sub : (j - 1) + 1 = j := by omega
        rw [hj_sub]
        -- `p * |R'/Z| ≤ pᵏ * |R'/Z| = |R'| ≤ p^(j+1) = p * pʲ`.
        have hpk : p ≤ Nat.card (Subgroup.center R') := by
          rw [hk]; calc p = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk_pos
        have hstep : p * Nat.card (R' ⧸ Subgroup.center R') ≤ p * p ^ j := by
          calc p * Nat.card (R' ⧸ Subgroup.center R')
              ≤ Nat.card (Subgroup.center R') * Nat.card (R' ⧸ Subgroup.center R') :=
                Nat.mul_le_mul_right _ hpk
            _ = Nat.card R' := hZmul
            _ ≤ p ^ (j + 1) := hcardR'
            _ = p * p ^ j := by rw [pow_succ]; ring
        exact Nat.le_of_mul_le_mul_left hstep hp.pos
      -- `|R'/Z| < |R'| = N` since `|Z| ≥ p > 1`.
      have hquot_lt : Nat.card (R' ⧸ Subgroup.center R') < N := by
        rw [← hcardN, ← hZmul]
        have hZ_gt : 1 < Nat.card (Subgroup.center R') := by
          rw [hk]; exact one_lt_pow₀ hp.one_lt hk_pos.ne'
        have hQ_pos : 0 < Nat.card (R' ⧸ Subgroup.center R') := Nat.card_pos
        exact (Nat.lt_mul_iff_one_lt_left hQ_pos).mpr hZ_gt
      -- Inductive hypothesis on `R'/Z` with parameter `j - 1`.
      have hQpg : IsPGroup p (R' ⧸ Subgroup.center R') := hR'.to_quotient _
      have hQclass : Group.nilpotencyClass (R' ⧸ Subgroup.center R') ≤ j - 1 :=
        ih (Nat.card (R' ⧸ Subgroup.center R')) hquot_lt (j - 1) (by omega) hQpg rfl hquot_le
      -- `cl(R') = cl(R'/Z) + 1 ≤ (j-1) + 1 = j`.
      rw [Group.nilpotencyClass_eq_quotient_center_plus_one]
      omega

/-- From `cl(G) ≤ 3` one gets that every weight-`3` commutator `⁅⁅a, b⁆, c⁆` is central.
Bridge from the `nilpotencyClass` form (output of `nilpotencyClass_le_of_card_le_pow`) to
the packaged-commutator hypothesis required by `omega1_pow_eq_one`.

`cl(G) ≤ 3 ⇒ γ₄ = lowerCentralSeries G 3 = ⊥`. The element `⁅⁅a, b⁆, c⁆` lies in
`γ₃ = lowerCentralSeries G 2`, so for every `d`, `⁅⁅⁅a, b⁆, c⁆, d⁆ ∈ γ₄ = ⊥`, i.e.
`⁅⁅a, b⁆, c⁆` commutes with every `d`, i.e. it is central. -/
theorem pointwise_central_of_nilpotencyClass_le_three {G : Type*} [Group G]
    [Group.IsNilpotent G] (h : Group.nilpotencyClass G ≤ 3) :
    ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G := by
  -- `γ₄ = (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥`.
  have hbot : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h
  intro a b c
  -- `⁅a, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 = commutator G = ⁅⊤, ⊤⁆`.
  have h1 : ⁅a, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  -- `⁅⁅a, b⁆, c⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 = ⁅lcs 1, ⊤⁆`.
  have h2 : ⁅⁅a, b⁆, c⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator h1 (Subgroup.mem_top c)
  -- For every `d`, `⁅⁅⁅a, b⁆, c⁆, d⁆ ∈ lcs 3 = ⊥`, so the commutator is `1`.
  rw [Subgroup.mem_center_iff]
  intro d
  have h3 : ⁅⁅⁅a, b⁆, c⁆, d⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator h2 (Subgroup.mem_top d)
  rw [hbot, Subgroup.mem_bot] at h3
  exact (commutatorElement_eq_one_iff_commute.mp h3).symm

/-- **BG Proposition 4.8(b)** (BG mmd L1511-1520): for a prime `p > 3` and a finite
`p`-group `R` of rank `r(R) ≤ 2` (here `pRank R p ≤ 2`), `Ω₁(R) = Omega R p 1` has
exponent one or `p`; i.e. every `g ∈ Ω₁(R)` satisfies `g ^ p = 1`.

Following BG's minimal-counterexample argument, recast (as in `omega1_pow_eq_one`) as a
strong induction on `|R|` proving the product-closure `x ^ p = y ^ p = 1 ⇒ (x*y)^p = 1`.
For each `R'`:
* If `⟨x, y⟩ ≠ R'`: apply the inductive hypothesis to the proper subgroup `⟨x, y⟩`.
* If `⟨x⟩ = R'`: `R'` is abelian, so `(x*y)^p = x^p y^p = 1`.
* Otherwise take a maximal (normal) `S ⊇ ⟨x⟩`. By induction `Ω₁(S)` has exponent `p`, so
  by part (a) `|Ω₁(S)| ≤ p³`; with `R' = ⟨Ω₁(S), y⟩` and `|⟨y⟩| ≤ p`, `|R'| ≤ p⁴`. Then
  `cl(R') ≤ 3` (`nilpotencyClass_le_of_card_le_pow`), so the weight-`3` commutators are
  central (`pointwise_central_of_nilpotencyClass_le_three`), and `omega1_pow_eq_one` (the
  `cl ≤ 3` branch of Prop 4.3) gives `(x*y)^p = 1`. -/
theorem omega1_pow_eq_one_of_pRank_le_two_of_three_lt
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hp3 : 3 < p)
    (hrank : OddOrder.GroupTheory.pRank R p ≤ 2)
    {g : R} (hg : g ∈ Omega R p 1) : g ^ p = 1 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  -- Reduce to product-closure of `{g | g^p = 1}`.
  suffices hclosed : ∀ x y : R, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 by
    let omega1 : Subgroup R :=
      { carrier := {g : R | g ^ p = 1}
        mul_mem' := fun {x y} hx hy => hclosed x y hx hy
        one_mem' := one_pow p
        inv_mem' := fun {x} hx => by rw [Set.mem_ofPred_eq, inv_pow, hx, inv_one] }
    have hle : Omega R p 1 ≤ omega1 := by
      rw [Omega, Subgroup.closure_le]
      intro x hx
      change x ^ p = 1
      exact pow_one p ▸ hx
    simpa [omega1] using hle hg
  clear hg g
  -- Strong induction on `Nat.card R`, with `R` and `pRank ≤ 2` in the motive.
  let motive : ℕ → Prop := fun n =>
    ∀ {R' : Type _} [Group R'] [Finite R'], IsPGroup p R' →
      OddOrder.GroupTheory.pRank R' p ≤ 2 → Nat.card R' = n →
        ∀ x y : R', x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1
  refine (Nat.strongRecOn (motive := motive) (Nat.card R) ?_) hR hrank rfl
  clear hR hrank
  intro n ih R' _ _ hR' hrank' hcard x y hxp hyp
  -- WLOG `⟨x, y⟩ = ⊤`: otherwise the inductive hypothesis on `K := ⟨x, y⟩` closes the goal.
  by_cases hxytop : Subgroup.closure ({x, y} : Set R') = ⊤
  · -- Main argument under `⟨x, y⟩ = ⊤`.
    by_cases hxtop : Subgroup.zpowers x = ⊤
    · -- `⟨x⟩ = ⊤`: `R'` is cyclic, hence abelian; `x, y` commute.
      have hxy : Commute x y := by
        have hy_mem : y ∈ Subgroup.zpowers x := hxtop ▸ Subgroup.mem_top y
        obtain ⟨ky, hk⟩ := hy_mem
        rw [← hk]; exact (Commute.refl x).zpow_right ky
      rw [hxy.mul_pow, hxp, hyp, mul_one]
    · -- `⟨x⟩ ≠ ⊤`: take a maximal (normal) subgroup `S ⊇ ⟨x⟩`.
      obtain ⟨S, hS_coatom, hxS_le⟩ :=
        (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.zpowers x)).resolve_left hxtop
      have hS_normal : S.Normal := hS_coatom.normal_of_isPGroup hR'
      have hxS : x ∈ S := hxS_le (Subgroup.mem_zpowers x)
      -- `|↥S| < |R'| = n`.
      have hScard : Nat.card ↥S < n := by
        rw [← hcard]
        have h_dvd : Nat.card ↥S ∣ Nat.card R' := ⟨S.index, by rw [mul_comm, S.index_mul_card]⟩
        have h_le : Nat.card ↥S ≤ Nat.card R' := Nat.le_of_dvd Nat.card_pos h_dvd
        have h_ne : Nat.card ↥S ≠ Nat.card R' := fun heq =>
          hS_coatom.1 (Subgroup.eq_top_of_card_eq _ heq)
        exact Nat.lt_of_le_of_ne h_le h_ne
      have hSpg : IsPGroup p ↥S := hR'.to_subgroup S
      have hrankS : OddOrder.GroupTheory.pRank ↥S p ≤ 2 :=
        (OddOrder.GroupTheory.pRank_mono_of_le S).trans hrank'
      -- Inductive hypothesis: product-closure on `↥S`.
      have IHS : ∀ a b : ↥S, a ^ p = 1 → b ^ p = 1 → (a * b) ^ p = 1 :=
        ih (Nat.card ↥S) hScard hSpg hrankS rfl
      -- `{a : ↥S | a^p = 1}` is a subgroup of `↥S`; every element of `Ω₁(↥S)` has `p`-th power `1`.
      have hΩSpow : ∀ a ∈ Omega ↥S p 1, a ^ p = 1 := by
        let omega1S : Subgroup ↥S :=
          { carrier := {a : ↥S | a ^ p = 1}
            mul_mem' := fun {a b} ha hb => IHS a b ha hb
            one_mem' := one_pow p
            inv_mem' := fun {a} ha => by rw [Set.mem_ofPred_eq, inv_pow, ha, inv_one] }
        have hΩle : Omega ↥S p 1 ≤ omega1S := by
          rw [Omega, Subgroup.closure_le]
          intro a ha
          change a ^ p = 1
          exact pow_one p ▸ ha
        intro a ha
        simpa [omega1S] using hΩle ha
      -- `Ω₁(↥S)` (as an `R'`-subgroup) is normal in `R'` and has exponent `p`.
      have : (Omega ↥S p 1).Characteristic := Omega.characteristic
      set H : Subgroup R' := (Omega ↥S p 1).map S.subtype with hH_def
      have hH_normal : H.Normal := by rw [hH_def]; infer_instance
      have hHpow : ∀ z ∈ H, z ^ p = 1 := by
        intro z hz
        rw [hH_def, Subgroup.mem_map] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        have hap : a ^ p = 1 := hΩSpow a ha
        rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hap, Subgroup.coe_one]
      -- `x ∈ H`.
      have hxH : x ∈ H := by
        rw [hH_def, Subgroup.mem_map]
        refine ⟨⟨x, hxS⟩, ?_, by rw [Subgroup.coe_subtype]⟩
        exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact Subtype.ext (by simpa using hxp))
      -- **Step 5**: `|Ω₁(↥S)| ≤ p³` by part (a).
      have hSomega_pg : IsPGroup p ↥(Omega ↥S p 1) := hSpg.to_subgroup _
      have hSomega_rank : OddOrder.GroupTheory.pRank ↥(Omega ↥S p 1) p ≤ 2 :=
        (OddOrder.GroupTheory.pRank_mono_of_le (Omega ↥S p 1)).trans hrankS
      have hSomega_exp : ∀ w : ↥(Omega ↥S p 1), w ^ p = 1 := by
        intro w
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hΩSpow (w : ↥S) w.2
      have hcube : Nat.card ↥(Omega ↥S p 1) ≤ p ^ 3 :=
        card_le_prime_cube_of_pRank_le_two_of_exponent_prime hSomega_pg hSomega_rank hSomega_exp
      -- **Step 6**: `|R'| ≤ p⁴`. `R' = H ⊔ ⟨y⟩`, `|H| = |Ω₁(↥S)| ≤ p³`, `|⟨y⟩| ≤ p`.
      have hHcard : Nat.card ↥H ≤ p ^ 3 := by
        rw [hH_def, Subgroup.card_map_of_injective S.subtype_injective]
        exact hcube
      have hYcard : Nat.card ↥(Subgroup.zpowers y) ≤ p := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hyp)
      have hHY_top : H ⊔ Subgroup.zpowers y = ⊤ := by
        rw [eq_top_iff, ← hxytop, Subgroup.closure_le]
        intro w hw
        rcases hw with hw | hw
        · rw [hw]; exact Subgroup.mem_sup_left hxH
        · rw [Set.mem_singleton_iff] at hw; rw [hw]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      have hR'card : Nat.card R' ≤ p ^ 4 := by
        -- `↥(H ⊔ ⟨y⟩) = ↑H * ↑⟨y⟩`, so the multiplication map is surjective.
        have hsurj : Function.Surjective
            (fun q : ↥H × ↥(Subgroup.zpowers y) => ((q.1 : R') * (q.2 : R') : R')) := by
          intro z
          have hzmem : z ∈ H ⊔ Subgroup.zpowers y := hHY_top ▸ Subgroup.mem_top z
          rw [← SetLike.mem_coe, Subgroup.normal_mul] at hzmem
          obtain ⟨a, ha, b, hb, rfl⟩ := hzmem
          exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
        have hcard_le : Nat.card R' ≤ Nat.card (↥H × ↥(Subgroup.zpowers y)) := by
          have hRtop : Nat.card R' = Nat.card ↥(H ⊔ Subgroup.zpowers y) := by
            rw [hHY_top]; exact (Nat.card_congr (Subgroup.topEquiv).symm.toEquiv)
          rw [hRtop, hHY_top]
          have : Nat.card (↥(⊤ : Subgroup R')) = Nat.card R' :=
            Nat.card_congr (Subgroup.topEquiv).toEquiv
          rw [this]
          exact Nat.card_le_card_of_surjective _ hsurj
        calc Nat.card R' ≤ Nat.card (↥H × ↥(Subgroup.zpowers y)) := hcard_le
          _ = Nat.card ↥H * Nat.card ↥(Subgroup.zpowers y) := Nat.card_prod _ _
          _ ≤ p ^ 3 * p := Nat.mul_le_mul hHcard hYcard
          _ = p ^ 4 := by ring
      -- **Step 7**: `cl(R') ≤ 3`.
      have : Group.IsNilpotent R' := hR'.isNilpotent
      have hclass : Group.nilpotencyClass R' ≤ 3 :=
        nilpotencyClass_le_of_card_le_pow hR' (j := 3) (by norm_num) (by simpa using hR'card)
      -- **Step 8**: weight-`3` commutators central; apply `omega1_pow_eq_one`.
      have hc3' : ∀ a b c : R', ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R' :=
        pointwise_central_of_nilpotencyClass_le_three hclass
      have hxy_mem : x * y ∈ Omega R' p 1 :=
        mul_mem
          (Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hxp))
          (Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hyp))
      exact omega1_pow_eq_one hR' hodd (Or.inr ⟨hp3, hc3'⟩) hxy_mem
  · -- `⟨x, y⟩ ≠ ⊤`: apply the inductive hypothesis to `K := ⟨x, y⟩`.
    set K : Subgroup R' := Subgroup.closure ({x, y} : Set R') with hK_def
    have hxK : x ∈ K := Subgroup.subset_closure (by left; rfl)
    have hyK : y ∈ K := Subgroup.subset_closure (by right; rfl)
    have hKcard : Nat.card ↥K < n := by
      rw [← hcard]
      have h_dvd : Nat.card ↥K ∣ Nat.card R' := ⟨K.index, by rw [mul_comm, K.index_mul_card]⟩
      have h_le : Nat.card ↥K ≤ Nat.card R' := Nat.le_of_dvd Nat.card_pos h_dvd
      have h_ne : Nat.card ↥K ≠ Nat.card R' := fun heq =>
        hxytop (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne h_le h_ne
    have hKpg : IsPGroup p ↥K := hR'.to_subgroup K
    have hrankK : OddOrder.GroupTheory.pRank ↥K p ≤ 2 :=
      (OddOrder.GroupTheory.pRank_mono_of_le K).trans hrank'
    have IHK : ∀ a b : ↥K, a ^ p = 1 → b ^ p = 1 → (a * b) ^ p = 1 :=
      ih (Nat.card ↥K) hKcard hKpg hrankK rfl
    have hxKp : (⟨x, hxK⟩ : ↥K) ^ p = 1 := by
      apply Subtype.ext; rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hxp
    have hyKp : (⟨y, hyK⟩ : ↥K) ^ p = 1 := by
      apply Subtype.ext; rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hyp
    have hxyKp := IHK ⟨x, hxK⟩ ⟨y, hyK⟩ hxKp hyKp
    have hcoe : ((⟨x, hxK⟩ * ⟨y, hyK⟩ : ↥K) : R') ^ p = 1 := by
      rw [← Subgroup.coe_pow, hxyKp, Subgroup.coe_one]
    simpa using hcoe

/-- A maximal (coatom) normal subgroup `M` of a finite `p`-group `Q` has index `p`:
`Q/M` is a nontrivial `p`-group whose only subgroups are `⊥` and `⊤` (correspondence with
the coatom `M`), so a Cauchy order-`p` subgroup must be all of `Q/M`. -/
private theorem index_eq_prime_of_coatom {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQpg : IsPGroup p Q) (M : Subgroup Q) [M.Normal] (hM_coatom : IsCoatom M) :
    M.index = p := by
  have hp : p.Prime := Fact.out
  have hQMpg : IsPGroup p (Q ⧸ M) := hQpg.to_quotient M
  have hQMnt : Nontrivial (Q ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM_coatom.1
  have hpdvd : p ∣ Nat.card (Q ⧸ M) := by
    rcases hQMpg.card_eq_or_dvd with h1 | hd
    · exact absurd (Finite.card_le_one_iff_subsingleton.mp h1.le)
        (not_subsingleton_iff_nontrivial.mpr hQMnt)
    · exact hd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q ⧸ M) p hpdvd
  set H : Subgroup (Q ⧸ M) := Subgroup.zpowers g with hH_def
  have hHcard : Nat.card H = p := by rw [hH_def, Nat.card_zpowers, hg]
  have hHne : H ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hHcard; exact hp.one_lt.ne' hHcard.symm
  set Hc : Subgroup Q := H.comap (QuotientGroup.mk' M) with hHc_def
  have hM_le : M ≤ Hc := by
    rw [hHc_def]; intro m hm
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff m).mpr hm]
    exact one_mem H
  have hHc_eq : H = Hc.map (QuotientGroup.mk' M) := by
    rw [hHc_def, Subgroup.map_comap_eq, QuotientGroup.range_mk', top_inf_eq]
  have hHc_ne_M : Hc ≠ M := by
    intro heq; apply hHne; rw [hHc_eq, heq, QuotientGroup.map_mk'_self]
  have hHc_top : Hc = ⊤ := by
    rcases (hM_coatom.le_iff.mp hM_le) with h | h
    · exact h
    · exact absurd h.symm hHc_ne_M.symm
  have hH_top : H = ⊤ := by
    rw [hHc_eq, hHc_top, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)]
  rw [Subgroup.index_eq_card]
  have hcard : Nat.card (Q ⧸ M) = Nat.card H := by
    rw [hH_top]; exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
  rw [hcard, hHcard]

/-- **BG Lemma 4.9** (mmd L1522-1544). For `p > 3`, a `p`-group `R` with `|Ω₁(R)| ≤ p²`
satisfies `|Ω₁(R/T)| ≤ p²` for *every* normal subgroup `T ⊴ R`.

The proof is the double minimal-counterexample argument of BG: take `R` minimal among
counterexamples (strong induction on `|R|`) and, within `R`, take `T₀ ⊴ R` minimal subject
to `|Ω₁(R/T₀)| > p²`.

* `|T₀| = p`: otherwise pick a central `Z ≤ T₀ ∩ Z(R)` of order `p`; minimality of `T₀`
  gives `|Ω₁(R/Z)| ≤ p²`, induction (`|R/Z| < |R|`) applied to `R/Z` with `T₀/Z` plus the
  third isomorphism `(R/Z)/(T₀/Z) ≅ R/T₀` give `|Ω₁(R/T₀)| ≤ p²`, contradiction.
* `(4.6)`: `|R| = p⁴` and `R/T₀` has exponent `p`. The key sub-fact is that *every proper
  subgroup* `K < R/T₀` has `|Ω₁(K)| ≤ p²` (lift `K` to `K̃ < R`, apply induction to `K̃`).
  Hence `Ω₁(R/T₀)` is not contained in any maximal subgroup, so `Ω₁(R/T₀) = ⊤`; with
  Prop 4.8(b) (rank `≤ 2`) resp. the elementary-abelian extraction (rank `> 2`) this forces
  `R/T₀` of exponent `p` and order `p³`, whence `|R| = p⁴` (`|T₀| = p`).
* Final contradiction: `|Ω₁(R)| = p²` (Lemma 4.5 lower bound + hypothesis), so
  `|R/Ω₁(R)| = p²`. Since `cl(R) ≤ 3` (from `|R| ≤ p⁴`), `φ(x) = xᵖ` is a homomorphism
  (Prop 4.3(b)) with `ker φ = Ω₁(R)` and image in `T₀`, giving
  `p² = |R/Ω₁(R)| = |R/ker φ| = |im φ| ≤ |T₀| = p`, a contradiction. -/
theorem card_omega1_quotient_le_prime_sq {R : Type*} [Group R] [Finite R] {p : ℕ}
    [Fact p.Prime] (hR : IsPGroup p R) (hp3 : 3 < p)
    (hΩ : Nat.card (Omega R p 1) ≤ p ^ 2) (T : Subgroup R) [T.Normal] :
    Nat.card (Omega (R ⧸ T) p 1) ≤ p ^ 2 := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  -- Strong induction on `|R|`, with `R` and the hypotheses packaged in the motive.
  let motive : ℕ → Prop := fun n =>
    ∀ {R' : Type _} [Group R'] [Finite R'], IsPGroup p R' → Nat.card (Omega R' p 1) ≤ p ^ 2 →
      Nat.card R' = n → ∀ (T' : Subgroup R') [T'.Normal],
        Nat.card (Omega (R' ⧸ T') p 1) ≤ p ^ 2
  refine (Nat.strongRecOn (motive := motive) (Nat.card R) ?_) hR hΩ rfl T
  clear hR hΩ
  intro n ih R' _ _ hR' hΩ' hcard T' hT'N
  -- `ih : ∀ m < n, motive m`.
  -- Goal: `∀ T' [Normal], |Ω₁(R'/T')| ≤ p²`. By contradiction, pick a minimal bad `T₀`.
  by_contra hcon
  -- minimal `T₀` among normal subgroups with `|Ω₁(R'/T₀)| > p²`.
  have hex : ∃ (S : Subgroup R') (_ : S.Normal), p ^ 2 < Nat.card (Omega (R' ⧸ S) p 1) := by
    refine ⟨T', hT'N, ?_⟩; exact lt_of_not_ge hcon
  let Qpred : {S : Subgroup R' // S.Normal} → Prop := fun S =>
    haveI := S.2; p ^ 2 < Nat.card (Omega (R' ⧸ S.1) p 1)
  have hQne : {S : {S : Subgroup R' // S.Normal} | Qpred S}.Nonempty := by
    obtain ⟨S, hN, h⟩ := hex; exact ⟨⟨S, hN⟩, h⟩
  obtain ⟨T₀sub, hT₀mem, hT₀minraw⟩ :=
    Set.exists_min_image {S | Qpred S} (fun S => Nat.card S.1) (Set.toFinite _) hQne
  set T₀ : Subgroup R' := T₀sub.1 with hT₀def
  have hT₀N : T₀.Normal := T₀sub.2
  have hT₀bad : p ^ 2 < Nat.card (Omega (R' ⧸ T₀) p 1) := hT₀mem
  have hT₀min : ∀ (S : Subgroup R') [S.Normal],
      p ^ 2 < Nat.card (Omega (R' ⧸ S) p 1) → Nat.card T₀ ≤ Nat.card S := by
    intro S hSN hSbad; exact hT₀minraw ⟨S, hSN⟩ hSbad
  have hQpg : IsPGroup p (R' ⧸ T₀) := hR'.to_quotient T₀
  -- `R'/T₀` is nontrivial since `|Ω₁(R'/T₀)| > p² > 1`.
  have hQnt : Nontrivial (R' ⧸ T₀) := by
    rcases subsingleton_or_nontrivial (R' ⧸ T₀) with hs | hn
    · exfalso
      have := hs
      have h1 : Nat.card (Omega (R' ⧸ T₀) p 1) ≤ Nat.card (R' ⧸ T₀) :=
        Subgroup.card_le_card_group _
      have h2 : Nat.card (R' ⧸ T₀) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
      rw [h2] at h1
      have : 1 < p ^ 2 := by nlinarith [hp.two_le]
      omega
    · exact hn
  -- ============================================================
  -- Fact F: every proper subgroup `K < R'/T₀` has `|Ω₁(K)| ≤ p²`.
  -- ============================================================
  have factF : ∀ (K : Subgroup (R' ⧸ T₀)), K ≠ ⊤ →
      Nat.card (Omega ↥K p 1) ≤ p ^ 2 := by
    intro K hKtop
    -- Lift `K` to `M ≤ R'` via `comap (mk' T₀)`; then `K = M.map (mk' T₀)`, `M ≠ ⊤`.
    set M : Subgroup R' := K.comap (QuotientGroup.mk' T₀) with hM_def
    have hMmap : M.map (QuotientGroup.mk' T₀) = K := by
      rw [hM_def, Subgroup.map_comap_eq, QuotientGroup.range_mk', top_inf_eq]
    have hMtop : M ≠ ⊤ := by
      intro hMtop'
      exact hKtop (by rw [← hMmap, hMtop',
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective T₀)])
    have hMpg : IsPGroup p ↥M := hR'.to_subgroup M
    have hMcard_lt : Nat.card ↥M < n := by
      rw [← hcard]
      have hdvd : Nat.card ↥M ∣ Nat.card R' := ⟨M.index, by rw [mul_comm, M.index_mul_card]⟩
      have hle : Nat.card ↥M ≤ Nat.card R' := Nat.le_of_dvd Nat.card_pos hdvd
      have hne : Nat.card ↥M ≠ Nat.card R' := fun heq => hMtop (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne hle hne
    -- `|Ω₁(↥M)| ≤ |Ω₁(R')| ≤ p²` (`Ω₁(↥M)` maps into `Ω₁(R')`).
    have hΩM : Nat.card (Omega ↥M p 1) ≤ p ^ 2 := by
      have hmap_le : (Omega ↥M p 1).map M.subtype ≤ Omega R' p 1 := by
        rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
        rintro ⟨g, hgM⟩ (hg : (⟨g, hgM⟩ : ↥M) ^ (p ^ 1) = 1)
        change (⟨g, hgM⟩ : ↥M) ∈ Subgroup.comap M.subtype (Omega R' p 1)
        rw [Subgroup.mem_comap]
        have hgp : g ^ (p ^ 1) = 1 := by
          have := congrArg (Subgroup.subtype M) hg; rwa [map_pow, map_one] at this
        exact Omega.mem_of_pow_eq_one hgp
      calc Nat.card (Omega ↥M p 1)
          = Nat.card ((Omega ↥M p 1).map M.subtype) :=
            (Subgroup.card_map_of_injective M.subtype_injective).symm
        _ ≤ Nat.card (Omega R' p 1) := Subgroup.card_le_of_le hmap_le
        _ ≤ p ^ 2 := hΩ'
    -- Induction on `↥M`: `4.9` holds for `↥M`.
    have h49M : ∀ (U : Subgroup ↥M) [U.Normal], Nat.card (Omega (↥M ⧸ U) p 1) ≤ p ^ 2 :=
      fun U _ => ih (Nat.card ↥M) hMcard_lt hMpg hΩM rfl U
    -- Transport: `↥K ≃ ↥M ⧸ (T₀.subgroupOf M)` via the first isomorphism theorem.
    let φ : M →* (R' ⧸ T₀) := (QuotientGroup.mk' T₀).comp M.subtype
    have hrange : φ.range = K := by
      rw [← hMmap]; ext x; simp [φ, MonoidHom.mem_range, Subgroup.mem_map]
    let e : (↥M ⧸ φ.ker) ≃* ↥φ.range := QuotientGroup.quotientKerEquivRange φ
    have hmap : (Omega (↥M ⧸ φ.ker) p 1).map e.toMonoidHom = Omega (↥φ.range) p 1 := by
      rw [Omega, Omega, MonoidHom.map_closure]
      congr 1
      ext b
      simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨a, ha, rfl⟩; rw [← map_pow, ha, map_one]
      · intro hb
        refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
        have hbb : e (e.symm b ^ p ^ 1) = b ^ p ^ 1 := by rw [map_pow, e.apply_symm_apply]
        rw [hb] at hbb
        have h1 : e.symm b ^ p ^ 1 = e.symm 1 := by rw [← hbb, e.symm_apply_apply]
        rw [h1, map_one]
    have hcardeq : Nat.card (Omega (↥φ.range) p 1) = Nat.card (Omega (↥M ⧸ φ.ker) p 1) := by
      rw [← hmap]; exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    rw [show Nat.card (Omega ↥K p 1) = Nat.card (Omega (↥φ.range) p 1) by rw [hrange], hcardeq]
    exact h49M φ.ker
  -- ============================================================
  -- Step 1: `|T₀| = p`.
  -- ============================================================
  have hT₀card : Nat.card T₀ = p := by
    have hT₀pg : IsPGroup p T₀ := hR'.to_subgroup T₀
    -- `T₀` is nontrivial: if `T₀ = ⊥`, then `R'/⊥ ≃* R'` and `|Ω₁(R'/T₀)| = |Ω₁(R')| ≤ p²`,
    -- contradicting `|Ω₁(R'/T₀)| > p²`.
    have hT₀nt : Nontrivial T₀ := by
      rcases subsingleton_or_nontrivial T₀ with hs | hn
      · exfalso
        have hbot : T₀ = ⊥ := by
          rw [Subgroup.eq_bot_iff_card]
          exact Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩
        -- `R'/T₀ ≃* R'/⊥ ≃* R'` (avoids rewriting `T₀` inside a quotient type).
        let e : (R' ⧸ T₀) ≃* R' :=
          (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot (G := R'))
        have hmap : (Omega (R' ⧸ T₀) p 1).map e.toMonoidHom = Omega R' p 1 := by
          rw [Omega, Omega, MonoidHom.map_closure]; congr 1; ext b
          simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
          constructor
          · rintro ⟨a, ha, rfl⟩; rw [← map_pow, ha, map_one]
          · intro hb; refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
            have hbb : e (e.symm b ^ p ^ 1) = b ^ p ^ 1 := by rw [map_pow, e.apply_symm_apply]
            rw [hb] at hbb
            have h1 : e.symm b ^ p ^ 1 = e.symm 1 := by rw [← hbb, e.symm_apply_apply]
            rw [h1, map_one]
        have hceq : Nat.card (Omega (R' ⧸ T₀) p 1) = Nat.card (Omega R' p 1) := by
          rw [← hmap]
          exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
        rw [hceq] at hT₀bad; omega
      · exact hn
    by_contra hne
    -- Take a central `Z ≤ T₀` of order `p`.
    have hinf_nt : Nontrivial ((T₀ ⊓ Subgroup.center R' : Subgroup R')) :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hR' hT₀nt
    have hpg_inf : IsPGroup p (T₀ ⊓ Subgroup.center R' : Subgroup R') := hR'.to_subgroup _
    have hpdvd : p ∣ Nat.card (T₀ ⊓ Subgroup.center R' : Subgroup R') := by
      rcases hpg_inf.card_eq_or_dvd with h1 | hd
      · exact absurd (Finite.card_le_one_iff_subsingleton.mp h1.le)
          (not_subsingleton_iff_nontrivial.mpr hinf_nt)
      · exact hd
    obtain ⟨g, hg⟩ :=
      exists_prime_orderOf_dvd_card' (G := (T₀ ⊓ Subgroup.center R' : Subgroup R')) p hpdvd
    set z : R' := (g : R') with hz_def
    set Z : Subgroup R' := Subgroup.zpowers z with hZ_def
    have hZ_le_center : Z ≤ Subgroup.center R' := by
      rw [hZ_def, Subgroup.zpowers_le]; exact g.2.2
    have hZ_normal : Z.Normal := by
      constructor; intro nn hnn g'
      have := Subgroup.mem_center_iff.mp (hZ_le_center hnn) g'
      rw [this, mul_assoc, mul_inv_cancel, mul_one]; exact hnn
    have hZT : Z ≤ T₀ := by rw [hZ_def, Subgroup.zpowers_le]; exact g.2.1
    have hZcard : Nat.card Z = p := by
      rw [hZ_def, Nat.card_zpowers, hz_def, Subgroup.orderOf_coe, hg]
    -- `|T₀| > p` (since `|T₀| ≥ |Z| = p` and `|T₀| ≠ p`).
    have hT₀_gt : p < Nat.card T₀ := by
      have hge : p ≤ Nat.card T₀ := hZcard ▸ Subgroup.card_le_of_le hZT
      omega
    -- Minimality of `T₀`: `|Z| = p < |T₀|` ⇒ `|Ω₁(R'/Z)| ≤ p²`.
    have hΩRZ : Nat.card (Omega (R' ⧸ Z) p 1) ≤ p ^ 2 := by
      by_contra hbad
      have hbad' : p ^ 2 < Nat.card (Omega (R' ⧸ Z) p 1) := lt_of_not_ge hbad
      have := hT₀min Z hbad'; rw [hZcard] at this; omega
    -- `|R'/Z| < |R'| = n`.
    have hRZ_lt : Nat.card (R' ⧸ Z) < n := by
      rw [← hcard, ← Z.index_eq_card]
      have hmul := Z.card_mul_index
      have hZpos : 1 < Nat.card Z := by rw [hZcard]; exact hp.one_lt
      calc Z.index = Nat.card R' / Nat.card Z := by
              rw [← hmul, Nat.mul_div_cancel_left _ Nat.card_pos]
        _ < Nat.card R' := Nat.div_lt_self Nat.card_pos hZpos
    have hRZpg : IsPGroup p (R' ⧸ Z) := hR'.to_quotient Z
    have hT₀map_normal : (T₀.map (QuotientGroup.mk' Z)).Normal :=
      Subgroup.Normal.map (inferInstance : T₀.Normal) (QuotientGroup.mk' Z)
        (QuotientGroup.mk'_surjective Z)
    -- Induction on `R'/Z` with `T₀/Z = T₀.map (mk' Z)`.
    have h49RZ := ih (Nat.card (R' ⧸ Z)) hRZ_lt hRZpg hΩRZ rfl (T₀.map (QuotientGroup.mk' Z))
    -- Third isomorphism `(R'/Z)/(T₀/Z) ≃* R'/T₀`, transport `Ω₁`.
    let e := QuotientGroup.quotientQuotientEquivQuotient Z T₀ hZT
    have hmap : (Omega ((R' ⧸ Z) ⧸ (T₀.map (QuotientGroup.mk' Z))) p 1).map e.toMonoidHom
        = Omega (R' ⧸ T₀) p 1 := by
      rw [Omega, Omega, MonoidHom.map_closure]; congr 1; ext b
      simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨a, ha, rfl⟩; rw [← map_pow, ha, map_one]
      · intro hb; refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
        have hbb : e (e.symm b ^ p ^ 1) = b ^ p ^ 1 := by rw [map_pow, e.apply_symm_apply]
        rw [hb] at hbb
        have h1 : e.symm b ^ p ^ 1 = e.symm 1 := by rw [← hbb, e.symm_apply_apply]
        rw [h1, map_one]
    have hcard_eq : Nat.card (Omega (R' ⧸ T₀) p 1)
        = Nat.card (Omega ((R' ⧸ Z) ⧸ (T₀.map (QuotientGroup.mk' Z))) p 1) := by
      rw [← hmap]; exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    rw [hcard_eq] at hT₀bad
    exact absurd h49RZ (not_le.mpr hT₀bad)
  -- ============================================================
  -- Step 2 (4.6): `R'/T₀` has exponent `p`, `|R'/T₀| = p³`, `|R'| = p⁴`.
  -- ============================================================
  -- Helper: a subgroup `K ≤ M ≤ R'/T₀` of exponent `p` injects into `Ω₁(M)`.
  have hexp_card_le : ∀ (K M : Subgroup (R' ⧸ T₀)), K ≤ M → (∀ k ∈ K, k ^ p = 1) →
      Nat.card K ≤ Nat.card (Omega ↥M p 1) := by
    intro K M hKM hKexp
    have hsub_le : K.subgroupOf M ≤ Omega ↥M p 1 := by
      intro k hk
      rw [Subgroup.mem_subgroupOf] at hk
      refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]; apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hKexp _ hk
    calc Nat.card K = Nat.card (K.subgroupOf M) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv).symm
      _ ≤ Nat.card (Omega ↥M p 1) := Subgroup.card_le_of_le hsub_le
  -- `R'/T₀` has exponent `p` and order `p³`. Case split on `pRank (R'/T₀) p`.
  have hQ : (∀ x : R' ⧸ T₀, x ^ p = 1) ∧ Nat.card (R' ⧸ T₀) = p ^ 3 := by
    rcases Nat.lt_or_ge (OddOrder.GroupTheory.pRank (R' ⧸ T₀) p) 3 with hr | hr
    · -- Case `r(R'/T₀) ≤ 2`.
      have hr2 : OddOrder.GroupTheory.pRank (R' ⧸ T₀) p ≤ 2 := by omega
      -- Prop 4.8(b): every element of `Ω₁(R'/T₀)` has `p`-th power `1`.
      have hΩexp : ∀ g ∈ Omega (R' ⧸ T₀) p 1, g ^ p = 1 := fun g hg =>
        omega1_pow_eq_one_of_pRank_le_two_of_three_lt hQpg hp3 hr2 hg
      -- `Ω₁(R'/T₀) = ⊤`: else it sits in a maximal subgroup `M̄`, but then
      -- `|Ω₁(R'/T₀)| ≤ |Ω₁(M̄)| ≤ p²` (Fact F), contradicting `|Ω₁(R'/T₀)| > p²`.
      have hΩtop : Omega (R' ⧸ T₀) p 1 = ⊤ := by
        by_contra hne
        obtain ⟨M, hM_coatom, hΩM_le⟩ :=
          (IsCoatomic.eq_top_or_exists_le_coatom (Omega (R' ⧸ T₀) p 1)).resolve_left hne
        have hMtop : M ≠ ⊤ := hM_coatom.1
        have hcard_le := hexp_card_le (Omega (R' ⧸ T₀) p 1) M hΩM_le hΩexp
        have := hcard_le.trans (factF M hMtop)
        omega
      have hexp : ∀ x : R' ⧸ T₀, x ^ p = 1 := fun x =>
        hΩexp x (hΩtop ▸ Subgroup.mem_top x)
      refine ⟨hexp, ?_⟩
      -- `|R'/T₀| ≤ p³` (Prop 4.8(a)) and `> p²` (since `Ω₁ = ⊤`), so `= p³`.
      have hub : Nat.card (R' ⧸ T₀) ≤ p ^ 3 :=
        card_le_prime_cube_of_pRank_le_two_of_exponent_prime hQpg hr2 hexp
      have hgt : p ^ 2 < Nat.card (R' ⧸ T₀) := by
        have : Nat.card (Omega (R' ⧸ T₀) p 1) = Nat.card (R' ⧸ T₀) := by
          rw [hΩtop]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
        rw [← this]; exact hT₀bad
      -- `p² < |Q| ≤ p³`, `|Q|` a power of `p` ⇒ `|Q| = p³`.
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQpg
      rw [hm] at hub hgt ⊢
      have h2 : 2 < m := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hgt
      have h3 : m ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hub
      have : m = 3 := by omega
      rw [this]
    · -- Case `r(R'/T₀) ≥ 3`: there is an elementary abelian `A` with `p³ ≤ |A|`.
      have hnotle : ¬ OddOrder.GroupTheory.pRank (R' ⧸ T₀) p ≤ 2 := by omega
      rw [OddOrder.GroupTheory.pRank_le_iff] at hnotle
      simp only [not_forall, not_le, exists_prop] at hnotle
      obtain ⟨A, hA_elem, hA_log⟩ := hnotle
      have hA_card_ge : p ^ 3 ≤ Nat.card A := by
        calc p ^ 3 ≤ p ^ (Nat.log p (Nat.card A)) :=
              Nat.pow_le_pow_right hp.pos (by omega)
          _ ≤ Nat.card A := Nat.pow_log_le_self p Nat.card_pos.ne'
      have hA_exp : ∀ a ∈ A, a ^ p = 1 := by
        intro a ha
        have := hA_elem.pow_eq_one ⟨a, ha⟩
        simpa using congrArg (Subtype.val) this
      -- `A = ⊤`: else `A ≤ coatom M̄`, but then `p³ ≤ |A| ≤ |Ω₁(M̄)| ≤ p²`, contradiction.
      have hAtop : A = ⊤ := by
        by_contra hne
        obtain ⟨M, hM_coatom, hAM_le⟩ :=
          (IsCoatomic.eq_top_or_exists_le_coatom A).resolve_left hne
        have hcard_le := hexp_card_le A M hAM_le hA_exp
        have hcontra := hA_card_ge.trans (hcard_le.trans (factF M hM_coatom.1))
        have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
        omega
      -- `R'/T₀` is elementary abelian (`= A`), hence exponent `p`.
      have hQ_elem : (⊤ : Subgroup (R' ⧸ T₀)).IsElementaryAbelian p := hAtop ▸ hA_elem
      have hexp : ∀ x : R' ⧸ T₀, x ^ p = 1 := by
        intro x
        have := hQ_elem.pow_eq_one ⟨x, Subgroup.mem_top x⟩
        simpa using congrArg (Subtype.val) this
      refine ⟨hexp, ?_⟩
      -- `|R'/T₀| ≥ p³` (from `A`) and `≤ p³` (each maximal subgroup has order `≤ p²`).
      have hge : p ^ 3 ≤ Nat.card (R' ⧸ T₀) := by
        calc p ^ 3 ≤ Nat.card A := hA_card_ge
          _ ≤ Nat.card (R' ⧸ T₀) := Subgroup.card_le_card_group A
      have hle : Nat.card (R' ⧸ T₀) ≤ p ^ 3 := by
        -- maximal `M̄`: `|M̄| ≤ p²` (Fact F, `M̄` exp `p`), index `p`, so `|Q| ≤ p³`.
        obtain ⟨M, hM_coatom, _⟩ :=
          (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup (R' ⧸ T₀))).resolve_left
            (fun hbot => (bot_lt_top (α := Subgroup (R' ⧸ T₀))).ne hbot)
        have hMtop : M ≠ ⊤ := hM_coatom.1
        have : M.Normal := hM_coatom.normal_of_isPGroup hQpg
        have hMexp_card : Nat.card M ≤ p ^ 2 :=
          (hexp_card_le M M (le_refl M) (fun k _ => hexp k)).trans (factF M hMtop)
        have hindex : M.index = p := index_eq_prime_of_coatom hQpg M hM_coatom
        calc Nat.card (R' ⧸ T₀) = M.index * Nat.card M := (M.index_mul_card).symm
          _ = p * Nat.card M := by rw [hindex]
          _ ≤ p * p ^ 2 := Nat.mul_le_mul_left p hMexp_card
          _ = p ^ 3 := by ring
      exact le_antisymm hle hge
  have hQexp : ∀ x : R' ⧸ T₀, x ^ p = 1 := hQ.1
  have hQcard : Nat.card (R' ⧸ T₀) = p ^ 3 := hQ.2
  have hR'card : Nat.card R' = p ^ 4 := by
    have hmul := T₀.card_mul_index
    rw [hT₀card, Subgroup.index_eq_card, hQcard] at hmul
    rw [← hmul]; ring
  -- ============================================================
  -- Step 3: `|Ω₁(R')| = p²`, `|R'/Ω₁(R')| = p²`.
  -- ============================================================
  have hΩeq : Nat.card (Omega R' p 1) = p ^ 2 := by
    -- `R'/T₀` is noncyclic (`|Ω₁(R'/T₀)| > p² > p`), hence `R'` is noncyclic.
    have hQnc : ¬ IsCyclic (R' ⧸ T₀) := by
      intro hcyc
      have := hcyc
      have := card_omega1_eq_prime_of_isCyclic hQpg
      rw [this] at hT₀bad
      nlinarith [hp.two_le]
    have hRnc : ¬ IsCyclic R' := by
      intro hcyc
      have := hcyc
      have : IsCyclic (R' ⧸ T₀) :=
        isCyclic_of_surjective (QuotientGroup.mk' T₀) (QuotientGroup.mk'_surjective T₀)
      exact hQnc inferInstance
    -- Lemma 4.5(a): `R'` has an elementary abelian subgroup `E` of order `p²`; `E ≤ Ω₁(R')`.
    obtain ⟨E, hE_elem, hE_card⟩ :=
      exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic hR' hodd hRnc
    have hE_le : E ≤ Omega R' p 1 := by
      intro a ha
      refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]
      have := hE_elem.pow_eq_one ⟨a, ha⟩
      simpa using congrArg (Subtype.val) this
    have hlb : p ^ 2 ≤ Nat.card (Omega R' p 1) := by
      rw [← hE_card]; exact Subgroup.card_le_of_le hE_le
    exact le_antisymm hΩ' hlb
  have hRΩcard : Nat.card (R' ⧸ Omega R' p 1) = p ^ 2 := by
    have hmul := (Omega R' p 1).card_mul_index
    rw [Subgroup.index_eq_card, hΩeq, hR'card] at hmul
    have : p ^ 2 * Nat.card (R' ⧸ Omega R' p 1) = p ^ 2 * p ^ 2 := by rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  -- ============================================================
  -- Step 4: `φ(x) = xᵖ` is a homomorphism `R' →* R'`, image `≤ T₀`.
  -- ============================================================
  -- cl(R') ≤ 3
  have : Group.IsNilpotent R' := hR'.isNilpotent
  have hclass : Group.nilpotencyClass R' ≤ 3 :=
    nilpotencyClass_le_of_card_le_pow hR' (j := 3) (by norm_num) (by simpa using hR'card.le)
  have hc3 : ∀ a b c : R', ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R' :=
    pointwise_central_of_nilpotencyClass_le_three hclass
  -- `commutator R' ≤ Ω₁(R')` from `R'/Ω₁(R')` abelian (order p²).
  have hcomm_le : _root_.commutator R' ≤ Omega R' p 1 := by
    have : IsMulCommutative (R' ⧸ Omega R' p 1) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq hRΩcard
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp ‹_›
  have hpow_hom : ∀ x y : R', (x * y) ^ p = x ^ p * y ^ p := fun x y =>
    pow_mul_eq_mul_pow_of_commutator_le_omega1 hR' hodd (Or.inr ⟨hp3, hc3⟩) hcomm_le x y
  let φ : R' →* R' := MonoidHom.mk' (fun x => x ^ p) (fun x y => hpow_hom x y)
  -- image ≤ T₀
  have hφ_range : φ.range ≤ T₀ := by
    rintro _ ⟨x, rfl⟩
    change (x ^ p) ∈ T₀
    have hq : (QuotientGroup.mk' T₀ x) ^ p = 1 := hQexp _
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    exact hq
  -- ============================================================
  -- Step 5: `ker φ = Ω₁(R')` and the final contradiction.
  -- ============================================================
  have hker : φ.ker = Omega R' p 1 := by
    let om : Subgroup R' :=
      { carrier := {g : R' | g ^ p = 1}
        mul_mem' := fun {x y} hx hy => by
          rw [Set.mem_ofPred_eq] at hx hy ⊢; rw [hpow_hom, hx, hy, mul_one]
        one_mem' := one_pow p
        inv_mem' := fun {x} hx => by
          rw [Set.mem_ofPred_eq, inv_pow, (by exact hx : x ^ p = 1), inv_one] }
    have hker_eq : φ.ker = om := by
      ext x; simp only [MonoidHom.mem_ker, MonoidHom.mk'_apply, φ]; rfl
    rw [hker_eq]
    apply le_antisymm
    · intro x hx
      exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hx)
    · rw [Omega, Subgroup.closure_le]
      intro x hx
      simpa [om] using (pow_one p ▸ hx : x ^ p = 1)
  -- `|R'/ker φ| = |im φ| ≤ |T₀| = p`, but `= |R'/Ω₁(R')| = p²`.
  have hquot_card : Nat.card (R' ⧸ φ.ker) = p ^ 2 := by
    rw [hker]; exact hRΩcard
  have hrange_card : Nat.card φ.range = p ^ 2 := by
    have e := QuotientGroup.quotientKerEquivRange φ
    rw [← hquot_card]; exact (Nat.card_congr e.toEquiv).symm
  have hle_T₀ : Nat.card φ.range ≤ Nat.card T₀ := Subgroup.card_le_of_le hφ_range
  rw [hrange_card, hT₀card] at hle_T₀
  -- `p² ≤ p` with `p > 3`: contradiction.
  have : p ^ 2 ≤ p := hle_T₀
  nlinarith [hp.two_le, sq_nonneg p]

end Prop48ExponentP

section Lemma417

open OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

open scoped commutatorElement IsMulCommutative

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- **GL(2,p) branch engine for Lemma 4.17**: a finite odd-order group `B` mapping
injectively into `GL (Fin 2) (ZMod p)` either has `p`-group commutator (`p ∣ |B|`,
Thm 2.6(b) via `isPGroup_commutator_of_faithful_two_dim_charP`) or is abelian
(`p ∤ |B|`, Thm 2.6(a) via `odd_two_dim_abelian`). The representation lives on the
concrete module `Fin 2 → ZMod p` (via `Matrix.GeneralLinearGroup.toLin`), keeping all
instances global — a `letI`-bound module on `Additive Q` would wedge instance synthesis
(cf. the warning at `IsElementaryAbelian.addAutEquivGL`). -/
private theorem isPGroup_commutator_or_comm_of_homGLTwo
    {p : ℕ} [Fact p.Prime] {B : Type*} [Group B] [Finite B] (hB_odd : Odd (Nat.card B))
    (ι : B →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (hι : Function.Injective ι) :
    IsPGroup p (_root_.commutator B) ∨ ∀ x y : B, x * y = y * x := by
  classical
  have hdim : Module.finrank (ZMod p) (Fin 2 → ZMod p) = 2 := by
    rw [Module.finrank_pi]
    simp
  let ρ : Representation (ZMod p) B (Fin 2 → ZMod p) :=
    (Units.coeHom (Module.End (ZMod p) (Fin 2 → ZMod p))).comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ι)
  have hρ_inj : Function.Injective ρ := by
    simp only [ρ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact Function.Injective.comp (fun _ _ h => Units.ext h)
      (Function.Injective.comp Matrix.GeneralLinearGroup.toLin.injective hι)
  by_cases hp_dvd : p ∣ Nat.card B
  · exact Or.inl (isPGroup_commutator_of_faithful_two_dim_charP hB_odd hdim ρ hρ_inj
      hp_dvd (ZMod.charP p))
  · refine Or.inr ?_
    have hchar' : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → ¬ CharP (ZMod p) q := by
      intro q hq hq_dvd hcharq
      exact hp_dvd ((CharP.eq (ZMod p) hcharq (ZMod.charP p)) ▸ hq_dvd)
    have hcomm := OddOrder.BG.Ch1.S02.odd_two_dim_abelian hB_odd hdim ρ hρ_inj hchar'
    exact fun x y => hcomm.comm x y

/-- **BG Lemma 4.17** (mmd L1706): `p` 奇素数, `R` 有限 `p`-群 with `r(R) ≤ 2`, `A` を
`R` の自己同型群の odd 位数部分群 (`φ : A →* MulAut R` faithful) とすると, `A'`
(`commutator A`) は `p`-群。

BG は `A` solvable も仮定するが, 本証明の §2 エンジンは odd のみで成立するため不要
(docstring 冒頭の section コメント参照)。下流: Thm 4.18 / BG §5 Thm 5.5(a) (rank ≤ 2 分岐) /
Cor 4.19。 -/
theorem isPGroup_commutator_of_mulAut_odd_of_pRank_le_two
    (hp_odd : Odd p) (hR : IsPGroup p R) (hrank : pRank R p ≤ 2)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hφ : Function.Injective φ) (hA_odd : Odd (Nat.card A)) :
    IsPGroup p (_root_.commutator A) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hp_odd
    norm_num at hp_odd
  -- R trivial: A embeds in the trivial `MulAut R`, so `A` and `A'` are trivial.
  rcases subsingleton_or_nontrivial R with hsub | hnontriv
  · have : Subsingleton (MulAut R) := ⟨fun f g => by ext r; exact Subsingleton.elim _ _⟩
    have : Subsingleton A := ⟨fun a b => hφ (Subsingleton.elim _ _)⟩
    intro g
    exact ⟨0, by
      rw [pow_zero, pow_one]
      exact Subtype.ext (Subsingleton.elim _ _)⟩
  -- Theorem 1.13: critical characteristic `H` with `exp H = p`, `C_{Aut R}(H)` a `p`-group.
  obtain ⟨H, hHchar, hHcommtop, hHcommcenter, hHexp, hHaut⟩ :=
    OddOrder.BG.Ch1.S01.thompson_critical_omega (p := p) hp2 hR
  have : H.Characteristic := hHchar
  have hH_inv : IsAInvariant φ H := IsAInvariant.of_characteristic φ
  set ψH : A →* MulAut ↥H := OddOrder.BG.Ch1.S01.restrictAction hH_inv with hψH_def
  have hH_pg : IsPGroup p ↥H := hR.to_subgroup H
  -- `C_A(H) = ker ψH` is a `p`-group (pulled back from `C_{Aut R}(H)` along the faithful `φ`).
  have hkerH_le : ψH.ker ≤ (autCentralizer H).comap φ := by
    intro a ha
    rw [Subgroup.mem_comap, mem_autCentralizer]
    intro h hh
    have := congrArg (fun e : MulAut ↥H => ((e ⟨h, hh⟩ : ↥H) : R)) ha
    simpa [hψH_def, OddOrder.BG.Ch1.S01.restrictAction_apply] using this
  have hkerH_pg : IsPGroup p ψH.ker :=
    (hHaut.comap_of_injective φ hφ).to_le hkerH_le
  -- `V = H/Φ(H)` with the induced `A`-action; `C = C_A(V)`.
  have : (_root_.frattini ↥H).Normal := inferInstance
  have hΦ_inv : IsAInvariant ψH (_root_.frattini ↥H) := IsAInvariant.of_characteristic ψH
  set ψV : A →* MulAut (↥H ⧸ _root_.frattini ↥H) :=
    quotientMulAutHom hΦ_inv with hψV_def
  set C : Subgroup A := ψV.ker with hC_def
  -- (i) `C` is a `p`-group.
  have hC_pg : IsPGroup p ↥C := by
    intro c
    set a : A := (c : A) with ha_def
    have ha_mem : a ∈ C := c.2
    have hn_pos : 0 < orderOf a := orderOf_pos a
    obtain ⟨k, m, hpm, hmn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hn_pos.ne' p hp.ne_one
    have hm_cop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
    -- the `p'`-part `a' = a ^ p ^ k` has order dividing `m`
    have ha'_pow_m : (a ^ p ^ k) ^ m = 1 := by
      rw [← pow_mul, ← hmn, pow_orderOf_eq_one]
    have ha'_order_dvd : orderOf (a ^ p ^ k) ∣ m := orderOf_dvd_of_pow_eq_one ha'_pow_m
    -- all powers of `a'` lie in `C`, hence act trivially mod `Φ(H)`
    have ha'_mem_C : a ^ p ^ k ∈ C := C.pow_mem ha_mem _
    have htriv : ∀ z : ℤ, ∀ r : ↥H,
        ∃ x ∈ _root_.frattini ↥H, ((ψH (a ^ p ^ k)) ^ z) r = r * x := by
      intro z r
      have hz_mem : (a ^ p ^ k) ^ z ∈ C := C.zpow_mem ha'_mem_C z
      have hz_ker : ψV ((a ^ p ^ k) ^ z) = 1 := hz_mem
      have hcoset : (((ψH ((a ^ p ^ k) ^ z)) r : ↥H) : ↥H ⧸ _root_.frattini ↥H) =
          (r : ↥H ⧸ _root_.frattini ↥H) := by
        rw [hψV_def] at hz_ker
        have h2 := congrArg (fun e : MulAut (↥H ⧸ _root_.frattini ↥H) =>
          e (r : ↥H ⧸ _root_.frattini ↥H)) hz_ker
        simp only [MulAut.one_apply] at h2
        exact h2
      refine ⟨r⁻¹ * (ψH ((a ^ p ^ k) ^ z)) r, QuotientGroup.eq.mp hcoset.symm, ?_⟩
      rw [← map_zpow]
      group
    -- Burnside: the `p'`-part acts trivially on `H`, so it lies in the `p`-group `ker ψH`.
    have hψ_cop : Nat.Coprime (orderOf (ψH (a ^ p ^ k))) p :=
      Nat.Coprime.coprime_dvd_left ((orderOf_map_dvd ψH _).trans ha'_order_dvd) hm_cop.symm
    have hf_one : ψH (a ^ p ^ k) = 1 :=
      OddOrder.BG.Ch1.S01.mulAut_eq_one_of_coprime_orderOf_of_frattini hH_pg _ hψ_cop htriv
    have ha'_kerH : a ^ p ^ k ∈ ψH.ker := hf_one
    -- inside the `p`-group `ker ψH`, a `p'`-order element is trivial
    obtain ⟨j, hj⟩ := hkerH_pg ⟨a ^ p ^ k, ha'_kerH⟩
    have hj' : (a ^ p ^ k) ^ p ^ j = 1 := by
      have := congrArg (Subtype.val) hj
      simpa using this
    have hdvd_pj : orderOf (a ^ p ^ k) ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj'
    have ha'_one : a ^ p ^ k = 1 := by
      rw [← orderOf_eq_one_iff]
      have hcop' : Nat.Coprime (orderOf (a ^ p ^ k)) (p ^ j) :=
        Nat.Coprime.pow_right j (Nat.Coprime.coprime_dvd_left ha'_order_dvd hm_cop.symm)
      exact Nat.eq_one_of_dvd_coprimes hcop' dvd_rfl hdvd_pj
    exact ⟨k, Subtype.ext (by simpa using ha'_one)⟩
  -- `|H| ≤ p³` (Prop 4.8) and `H ≠ 1`.
  have hHexp' : ∀ x : ↥H, x ^ p = 1 := fun x => by
    rw [← hHexp]; exact Monoid.pow_exponent_eq_one x
  have hHrank : pRank ↥H p ≤ 2 :=
    le_trans (pRank_le_of_injective (f := H.subtype) H.subtype_injective) hrank
  have hHcard : Nat.card ↥H ≤ p ^ 3 :=
    card_le_prime_cube_of_pRank_le_two_of_exponent_prime hH_pg hHrank hHexp'
  have hH_nontriv : Nontrivial ↥H := by
    rcases subsingleton_or_nontrivial ↥H with h | h
    · exfalso
      have h1 : Monoid.exponent ↥H = 1 := Monoid.exp_eq_one_of_subsingleton
      rw [hHexp] at h1
      exact hp.one_lt.ne' h1
    · exact h
  -- `V` is elementary abelian of order `p ^ d`, `1 ≤ d ≤ 3`.
  have hV_pg : IsPGroup p (↥H ⧸ _root_.frattini ↥H) := hH_pg.to_quotient _
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hV_pg
  have hV_elem : OddOrder.GroupTheory.IsElementaryAbelian p (↥H ⧸ _root_.frattini ↥H) :=
    hH_pg.quotient_frattini_isElementaryAbelian
  have hV_dvd : Nat.card (↥H ⧸ _root_.frattini ↥H) ∣ Nat.card ↥H := by
    have := Subgroup.index_dvd_card (_root_.frattini ↥H)
    simpa [Subgroup.index] using this
  have hΦ_ne_top : _root_.frattini ↥H ≠ ⊤ := by
    obtain ⟨M, hM, _⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup ↥H)).resolve_left bot_lt_top.ne
    exact fun htop => hM.1 (le_antisymm le_top (htop ▸ frattini_le_coatom hM))
  have hV_ne_one : Nat.card (↥H ⧸ _root_.frattini ↥H) ≠ 1 := by
    intro h1
    exact hΦ_ne_top (Subgroup.index_eq_one.mp (by simpa [Subgroup.index] using h1))
  have hd_pos : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · exact absurd (by simpa [h0] using hd) hV_ne_one
    · exact h
  have hd_le : d ≤ 3 := by
    have hle : p ^ d ≤ p ^ 3 :=
      le_trans (Nat.le_of_dvd Nat.card_pos (hd ▸ hV_dvd)) hHcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  -- Case split on `d = m(V)`.
  interval_cases d
  -- (iii) `|V| = p`: `Aut V` is abelian, so `A' ≤ C`.
  · have hVcyc : IsCyclic (↥H ⧸ _root_.frattini ↥H) :=
      isCyclic_of_prime_card (by simpa using hd)
    let e := IsCyclic.mulAutMulEquiv (↥H ⧸ _root_.frattini ↥H)
    let : CommGroup (MulAut (↥H ⧸ _root_.frattini ↥H)) :=
      e.toMonoidHom.commGroupOfInjective e.injective
    have hA'_le : _root_.commutator A ≤ C := by
      rw [_root_.commutator, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      have : ψV ⁅g₁, g₂⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
      exact this
    exact hC_pg.to_le hA'_le
  -- (iv) `|V| = p²`: `A/C` acts faithfully on the 2-dimensional `F_p`-space `V`.
  · have hquot_dvd : Nat.card (A ⧸ C) ∣ Nat.card A := by
      have := Subgroup.index_dvd_card C
      simpa [Subgroup.index] using this
    have hquot_odd : Odd (Nat.card (A ⧸ C)) := by
      rcases Nat.even_or_odd (Nat.card (A ⧸ C)) with he | ho
      · exfalso
        have h2 : (2 : ℕ) ∣ Nat.card A := dvd_trans he.two_dvd hquot_dvd
        rw [Nat.odd_iff] at hA_odd
        omega
      · exact ho
    -- `MulAut V ≃* GL (Fin 2) (ZMod p)` via the elementary abelian bridge
    have hfinrank := hV_elem.log_card_eq_finrank
    rw [hd, Nat.log_pow hp.one_lt] at hfinrank
    have ν := hV_elem.mulAutEquivGeneralLinearGroup
    rw [← hfinrank] at ν
    rcases isPGroup_commutator_or_comm_of_homGLTwo hquot_odd
        (ν.toMonoidHom.comp (QuotientGroup.kerLift ψV))
        (fun x y hxy => QuotientGroup.kerLift_injective ψV (ν.injective hxy))
        with hQ | hcomm
    · -- Thm 2.6(b): `(A/C)'` is a `p`-group; extend by the `p`-group `C`.
      have hker_pg : IsPGroup p ((QuotientGroup.mk' C).ker) := by
        rw [QuotientGroup.ker_mk']
        exact hC_pg
      have hcomap : IsPGroup p
          ((_root_.commutator (A ⧸ C)).comap (QuotientGroup.mk' C)) :=
        hQ.comap_of_ker_isPGroup (QuotientGroup.mk' C) hker_pg
      refine hcomap.to_le ?_
      have hmap : (_root_.commutator A).map (QuotientGroup.mk' C) =
          _root_.commutator (A ⧸ C) := by
        rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
      rw [← hmap]
      exact Subgroup.le_comap_map _ _
    · -- Thm 2.6(a): `A/C` is abelian, so `A' ≤ C`.
      have hA'_le : _root_.commutator A ≤ C := by
        rw [_root_.commutator, Subgroup.commutator_le]
        intro g₁ _ g₂ _
        have hmk : (QuotientGroup.mk' C) ⁅g₁, g₂⁆ = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_commute.mpr (hcomm _ _)
        exact (QuotientGroup.eq_one_iff _).mp hmk
      exact hC_pg.to_le hA'_le
  -- (ii) `|V| = p³` is impossible: `Φ(H) = 1` makes `H` elementary abelian of rank 3.
  · exfalso
    have hmul : Nat.card (_root_.frattini ↥H) * Nat.card (↥H ⧸ _root_.frattini ↥H) =
        Nat.card ↥H := by
      have := Subgroup.card_mul_index (_root_.frattini ↥H)
      simpa [Subgroup.index] using this
    have hΦ1 : Nat.card (_root_.frattini ↥H) = 1 := by
      have hle : Nat.card (_root_.frattini ↥H) * p ^ 3 ≤ 1 * p ^ 3 := by
        rw [one_mul]
        calc Nat.card (_root_.frattini ↥H) * p ^ 3
            = Nat.card (_root_.frattini ↥H) * Nat.card (↥H ⧸ _root_.frattini ↥H) := by
              rw [hd]
          _ = Nat.card ↥H := hmul
          _ ≤ p ^ 3 := hHcard
      have hle' := Nat.le_of_mul_le_mul_right hle (pow_pos hp.pos 3)
      have hpos := Nat.card_pos (α := ↥(_root_.frattini ↥H))
      omega
    have hΦbot : _root_.frattini ↥H = ⊥ := Subgroup.eq_bot_of_card_eq _ hΦ1
    have hH_elem : OddOrder.GroupTheory.IsElementaryAbelian p ↥H :=
      hH_pg.isElementaryAbelian_of_frattini_eq_bot hΦbot
    have hHcard3 : Nat.card ↥H = p ^ 3 := by
      rw [← hmul, hΦ1, one_mul, hd]
    have h3rank : 3 ≤ pRank R p := pow_le_card_of_le_pRank H hH_elem hHcard3
    omega

end Lemma417

end OddOrder.BG.Ch1.S04


