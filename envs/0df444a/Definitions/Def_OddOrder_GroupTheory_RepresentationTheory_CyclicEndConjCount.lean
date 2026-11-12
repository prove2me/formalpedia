-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclicEndConjCount
-- name    : OddOrder_GroupTheory_RepresentationTheory_CyclicEndConjCount
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:36.575389+00:00
-- url     : https://prove2.me/theorems/f49553b2-076e-48cf-b9a2-47f702aecd81
-- title:
--   Counting lemmas for BG Proposition 2.4(j)(k)
-- statement:
--   Elementary finite-combinatorics building blocks for Proposition 2.4(j)(k) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, the eigenspace-dimension number theory behind $h\mid q^n\pm 1$ in Theorem 2.5. The first block is field- and group-free: an integer family summing to $0$ whose squares sum to $2$ has exactly one $+1$, one $-1$ and zeros elsewhere.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CyclicEndConjCount.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CyclicEndConjCount.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_EigenspaceUnderCyclicAction

namespace OddOrder.RepresentationTheory

open Finset

/-- **Integers summing to `0` with squares summing to `2`**: the support has
exactly two points, carrying `+1` and `-1`. -/
theorem exists_pos_neg_of_sum_sq_eq_two {α : Type*} [Fintype α]
    (d : α → ℤ) (hsum : ∑ i, d i = 0) (hsq : ∑ i, d i ^ 2 = 2) :
    ∃ i j : α, i ≠ j ∧ d i = 1 ∧ d j = -1 ∧ ∀ k, d k ≠ 0 → k = i ∨ k = j := by
  classical
  set S : Finset α := univ.filter (fun i => d i ≠ 0) with hS
  have hmemS : ∀ k, k ∈ S ↔ d k ≠ 0 := by
    intro k; simp [hS]
  -- the squares supported on `S` still sum to `2`
  have hsupp : ∑ i ∈ S, d i ^ 2 = 2 := by
    rw [hS, sum_filter, ← hsq]
    exact sum_congr rfl fun i _ => by by_cases h : d i = 0 <;> simp [h]
  -- the values supported on `S` still sum to `0`
  have hsum' : ∑ i ∈ S, d i = 0 := by
    have heq : ∑ i ∈ S, d i = ∑ i, d i := by
      rw [hS, sum_filter]
      exact sum_congr rfl fun i _ => by by_cases h : d i = 0 <;> simp [h]
    rw [heq, hsum]
  -- on the support each square is `≥ 1`
  have hge : ∀ i ∈ S, (1 : ℤ) ≤ d i ^ 2 := by
    intro i hi
    have hne : d i ≠ 0 := (hmemS i).mp hi
    have h0 : d i ^ 2 ≠ 0 := pow_ne_zero 2 hne
    have h1 : (0 : ℤ) ≤ d i ^ 2 := sq_nonneg _
    omega
  -- the support has exactly two elements
  have hcard : S.card = 2 := by
    have hle : (S.card : ℤ) ≤ 2 := by
      calc (S.card : ℤ) = ∑ _i ∈ S, (1 : ℤ) := by simp
        _ ≤ ∑ i ∈ S, d i ^ 2 := sum_le_sum hge
        _ = 2 := hsupp
    have hcard2 : S.card ≤ 2 := by exact_mod_cast hle
    have hne0 : S.card ≠ 0 := by
      intro h; rw [card_eq_zero] at h; rw [h, sum_empty] at hsupp; norm_num at hsupp
    have hne1 : S.card ≠ 1 := by
      intro h
      obtain ⟨a, ha⟩ := card_eq_one.mp h
      rw [ha, sum_singleton] at hsupp
      have hb1 : d a ≤ 2 := by nlinarith [sq_nonneg (d a - 2)]
      have hb2 : -2 ≤ d a := by nlinarith [sq_nonneg (d a + 2)]
      interval_cases (d a) <;> simp_all
    omega
  -- extract the two support points and pin their values
  obtain ⟨i, j, hij, hSeq⟩ := card_eq_two.mp hcard
  have hinotj : i ∉ ({j} : Finset α) := by simp [hij]
  have hsupp' : d i ^ 2 + d j ^ 2 = 2 := by
    rw [hSeq, sum_insert hinotj, sum_singleton] at hsupp; exact hsupp
  have hsum'' : d i + d j = 0 := by
    rw [hSeq, sum_insert hinotj, sum_singleton] at hsum'; exact hsum'
  have hii : i ∈ S := hSeq ▸ mem_insert_self i {j}
  have hjj : j ∈ S := hSeq ▸ mem_insert_of_mem (mem_singleton_self j)
  have hi2 : d i ^ 2 = 1 := by have := hge i hii; have := hge j hjj; omega
  have hj2 : d j ^ 2 = 1 := by have := hge i hii; have := hge j hjj; omega
  have hisupp : ∀ k, d k ≠ 0 → k = i ∨ k = j := by
    intro k hk
    have : k ∈ S := (hmemS k).mpr hk
    rw [hSeq, mem_insert, mem_singleton] at this; exact this
  have hival : d i = 1 ∨ d i = -1 := by rw [← mul_self_eq_one_iff, ← sq]; exact hi2
  rcases hival with h | h
  · exact ⟨i, j, hij, h, by omega, hisupp⟩
  · exact ⟨j, i, hij.symm, by omega, h, fun k hk => (hisupp k hk).symm⟩

/-- **For each nonzero shift, exactly two indices move** (BG Prop 2.4(j), `m`-step shape). If the
"squared shift difference" sum is `2`, then `n i ≠ n (i + m)` for exactly two `i`. -/
theorem card_filter_ne_shift_eq_two {h : ℕ} [NeZero h] (n : ZMod h → ℤ) {m : ZMod h}
    (hsq : ∑ i, (n i - n (i + m)) ^ 2 = 2) :
    (univ.filter (fun i => n i ≠ n (i + m))).card = 2 := by
  classical
  have hshift : ∑ x, n (x + m) = ∑ x, n x :=
    Fintype.sum_equiv (Equiv.addRight m) (fun x => n (x + m)) n (fun _ => rfl)
  have hsum : ∑ i, (n i - n (i + m)) = 0 := by
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  obtain ⟨a, b, hab, ha, hb, hsupp⟩ :=
    exists_pos_neg_of_sum_sq_eq_two (fun i => n i - n (i + m)) hsum hsq
  have hfilter : (univ.filter (fun i => n i ≠ n (i + m))) = {a, b} := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    rw [← sub_ne_zero]
    constructor
    · exact hsupp i
    · rintro (rfl | rfl)
      · rw [ha]; norm_num
      · rw [hb]; norm_num
  rw [hfilter, Finset.card_pair hab]

/-- **Total number of "moved" ordered pairs is `2(h−1)`** (BG Prop 2.4(j), step P2): summing the
per-shift count over the `h−1` nonzero shifts. -/
theorem sum_ne_pairs_eq {h : ℕ} [NeZero h] (n : ZMod h → ℤ)
    (H : ∀ m : ZMod h, m ≠ 0 → ∑ i, (n i - n (i + m)) ^ 2 = 2) :
    ∑ i, ∑ j, (if n i ≠ n j then (1 : ℕ) else 0) = 2 * (h - 1) := by
  classical
  have step1 : (∑ i, ∑ j, (if n i ≠ n j then (1 : ℕ) else 0))
      = ∑ i, ∑ m, (if n i ≠ n (i + m) then (1 : ℕ) else 0) :=
    Finset.sum_congr rfl fun i _ =>
      (Fintype.sum_equiv (Equiv.addLeft i) _ _ fun _ => rfl).symm
  rw [step1, Finset.sum_comm]
  have step2 : ∀ m : ZMod h, (∑ i, (if n i ≠ n (i + m) then (1 : ℕ) else 0))
      = if m = 0 then 0 else 2 := by
    intro m
    by_cases hm : m = 0
    · subst hm; simp
    · rw [if_neg hm, Finset.sum_boole]
      exact_mod_cast card_filter_ne_shift_eq_two n (H m hm)
  rw [Finset.sum_congr rfl fun m _ => step2 m, Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, smul_eq_mul, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ, ZMod.card]
  ring

/-- **Sum of value-multiplicities** (BG Prop 2.4(j), step P3): `∑ᵢ #{j | nⱼ = nᵢ} = h² − 2(h−1)`,
the complement of the moved-pair count. -/
theorem sum_mult_add_eq {h : ℕ} [NeZero h] (n : ZMod h → ℤ)
    (H : ∀ m : ZMod h, m ≠ 0 → ∑ i, (n i - n (i + m)) ^ 2 = 2) :
    (∑ i, (univ.filter (fun j => n j = n i)).card) + 2 * (h - 1) = h ^ 2 := by
  classical
  have hP2 : ∑ i, (univ.filter (fun j => n i ≠ n j)).card = 2 * (h - 1) := by
    rw [← sum_ne_pairs_eq n H]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_boole _ _).symm
  have hcompl : ∀ i, (univ.filter (fun j => n j = n i)).card
      + (univ.filter (fun j => n i ≠ n j)).card = h := by
    intro i
    have h1 : (univ.filter (fun j => n i ≠ n j)) = (univ.filter (fun j => ¬ n j = n i)) :=
      Finset.filter_congr fun j _ => ne_comm
    rw [h1, Finset.card_filter_add_card_filter_not, Finset.card_univ, ZMod.card]
  calc (∑ i, (univ.filter (fun j => n j = n i)).card) + 2 * (h - 1)
      = (∑ i, (univ.filter (fun j => n j = n i)).card)
        + ∑ i, (univ.filter (fun j => n i ≠ n j)).card := by rw [hP2]
    _ = ∑ i, ((univ.filter (fun j => n j = n i)).card
        + (univ.filter (fun j => n i ≠ n j)).card) := by rw [← Finset.sum_add_distrib]
    _ = ∑ _i : ZMod h, h := Finset.sum_congr rfl fun i _ => hcompl i
    _ = h ^ 2 := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]; ring

/-- **Exactly one outlier index** (BG Prop 2.4(j), steps P4–P5): under the shift hypothesis, `n` is
constant (`= v₀`) off a single index `i₁`. The most frequent value has multiplicity exactly `h − 1`
(from `∑ mult = h² − 2h + 2`, `max mult ≥ h−1`, and `≠ h` since `n` is non-constant). -/
theorem exists_outlier {h : ℕ} [NeZero h] (hh : 2 ≤ h) (n : ZMod h → ℤ)
    (H : ∀ m : ZMod h, m ≠ 0 → ∑ i, (n i - n (i + m)) ^ 2 = 2) :
    ∃ (i₁ : ZMod h) (v₀ : ℤ), (∀ i, i ≠ i₁ → n i = v₀) ∧ n i₁ ≠ v₀ := by
  classical
  have : Fact (1 < h) := ⟨by omega⟩
  have hcu : (univ : Finset (ZMod h)).card = h := by rw [Finset.card_univ, ZMod.card]
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image (univ : Finset (ZMod h))
      (fun i => (univ.filter (fun j => n j = n i)).card) ⟨0, mem_univ 0⟩
  set C := (univ.filter (fun j => n j = n i₀)).card with hC
  -- ∑ mult ≤ h * C
  have hbound : (∑ i, (univ.filter (fun j => n j = n i)).card) ≤ h * C :=
    calc (∑ i, (univ.filter (fun j => n j = n i)).card)
        ≤ ∑ _i : ZMod h, C := Finset.sum_le_sum fun i _ => hi₀ i (mem_univ i)
      _ = h * C := by rw [Finset.sum_const, hcu, smul_eq_mul]
  have hP3 := sum_mult_add_eq n H
  have hle : C ≤ h := hC ▸ le_trans (Finset.card_filter_le _ _) (le_of_eq hcu)
  -- `C ≠ h`: otherwise `n` is constant, contradicting the shift hypothesis.
  have hcne : C ≠ h := by
    intro hc
    have huniv : univ.filter (fun j => n j = n i₀) = univ :=
      Finset.eq_univ_of_card _ (by rw [← hC, hc, ZMod.card])
    have hconst : ∀ j, n j = n i₀ := fun j => by
      have hj : j ∈ univ.filter (fun j => n j = n i₀) := by rw [huniv]; exact mem_univ j
      simpa using hj
    have := H 1 one_ne_zero
    rw [Finset.sum_eq_zero fun i _ => by rw [hconst i, hconst (i + 1)]; ring] at this
    exact two_ne_zero this.symm
  -- `C ≥ h − 1` from the multiplicity bound (worked in ℤ).
  have hge : h - 1 ≤ C := by
    by_contra hlt
    rw [not_le] at hlt
    have hC2 : (C : ℤ) + 2 ≤ (h : ℤ) := by
      have : C + 2 ≤ h := by omega
      exact_mod_cast this
    have h1 : (1 : ℕ) ≤ h := by omega
    have hbz : (∑ i, ((univ.filter (fun j => n j = n i)).card : ℤ)) ≤ (h : ℤ) * C := by
      exact_mod_cast hbound
    have hpz : (∑ i, ((univ.filter (fun j => n j = n i)).card : ℤ)) + 2 * ((h : ℤ) - 1)
        = (h : ℤ) ^ 2 := by
      have hh3 := hP3; zify [h1] at hh3; linarith [hh3]
    have hmul : (h : ℤ) * C ≤ (h : ℤ) * ((h : ℤ) - 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [hbz, hpz, hmul]
  have hCeq : C = h - 1 := by omega
  -- complement has exactly one element
  have hcompl : (univ.filter (fun j => n j ≠ n i₀)).card = 1 := by
    have hadd := Finset.card_filter_add_card_filter_not (s := (univ : Finset (ZMod h)))
      (fun j => n j = n i₀)
    simp only [ne_eq] at hadd ⊢
    rw [hcu, ← hC] at hadd
    omega
  obtain ⟨i₁, hi₁⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨i₁, n i₀, fun i hi => ?_, ?_⟩
  · by_contra hni
    have : i ∈ univ.filter (fun j => n j ≠ n i₀) := by simp [hni]
    rw [hi₁, mem_singleton] at this
    exact hi this
  · have : i₁ ∈ univ.filter (fun j => n j ≠ n i₀) := by rw [hi₁]; exact mem_singleton_self i₁
    simpa using this

/-- **BG Proposition 2.4(j) (number-theoretic core).** Under the shift hypothesis with `h ≥ 2`,
there is an index `i₁`, a base value `v₀`, and `δ = ±1` such that `n` equals `v₀` off `i₁`,
`n i₁ = v₀ + δ`, and `∑ᵢ nᵢ = h·v₀ + δ`. In particular `∑ nᵢ ≡ ±1 (mod h)`.

This packages the eigenvalue-multiplicity structure that BG Thm 2.5 feeds into the `h ∣ qⁿ ± 1`
conclusion (with `q := ∑ nᵢ = dim V`). -/
theorem prop24j {h : ℕ} [NeZero h] (hh : 2 ≤ h) (n : ZMod h → ℤ)
    (H : ∀ m : ZMod h, m ≠ 0 → ∑ i, (n i - n (i + m)) ^ 2 = 2) :
    ∃ (i₁ : ZMod h) (v₀ δ : ℤ), (δ = 1 ∨ δ = -1) ∧ (∀ i, i ≠ i₁ → n i = v₀) ∧
      n i₁ = v₀ + δ ∧ (∑ i, n i) = (h : ℤ) * v₀ + δ := by
  classical
  have : Fact (1 < h) := ⟨by omega⟩
  have hcu : (univ : Finset (ZMod h)).card = h := by rw [Finset.card_univ, ZMod.card]
  obtain ⟨i₁, v₀, hconst, _hne⟩ := exists_outlier hh n H
  have hm : (1 : ZMod h) ≠ 0 := one_ne_zero
  have hi₁m : i₁ - 1 ≠ i₁ := fun hc => hm (sub_eq_self.mp hc)
  -- the `m = 1` shift sum is supported on `{i₁, i₁ - 1}` and equals `2 (n i₁ - v₀)²`
  have hf0 : ∀ x ∈ (univ : Finset (ZMod h)), x ∉ ({i₁, i₁ - 1} : Finset (ZMod h)) →
      (n x - n (x + 1)) ^ 2 = 0 := by
    intro x _ hx
    simp only [mem_insert, mem_singleton, not_or] at hx
    rw [hconst x hx.1, hconst (x + 1) (fun hc => hx.2 (eq_sub_of_add_eq hc)), sub_self]; ring
  have hsq1 : (n i₁ - v₀) ^ 2 = 1 := by
    have h2 := H 1 hm
    rw [← Finset.sum_subset (Finset.subset_univ ({i₁, i₁ - 1} : Finset (ZMod h))) hf0,
      Finset.sum_pair hi₁m.symm,
      hconst (i₁ + 1) (fun hc => hm (by simpa using sub_eq_zero.mpr hc)),
      hconst (i₁ - 1) hi₁m, sub_add_cancel] at h2
    nlinarith [h2]
  -- the value sum
  have hsumn : (∑ i, n i) = (h : ℤ) * v₀ + (n i₁ - v₀) := by
    rw [← Finset.add_sum_erase univ n (mem_univ i₁),
      Finset.sum_congr rfl (fun i hi => hconst i (Finset.ne_of_mem_erase hi)),
      Finset.sum_const, Finset.card_erase_of_mem (mem_univ i₁), hcu, nsmul_eq_mul]
    push_cast [Nat.cast_sub (show 1 ≤ h by omega)]
    ring
  refine ⟨i₁, v₀, n i₁ - v₀, ?_, hconst, by ring, hsumn⟩
  have hmul : (n i₁ - v₀) * (n i₁ - v₀) = 1 := by rw [← pow_two]; exact hsq1
  exact mul_self_eq_one_iff.mp hmul

/-- **BG Proposition 2.4(k).** If additionally all `nᵢ ≥ 0` (eigenspace dimensions),
`q := ∑ nᵢ ≥ 2`, and the fixed value `n 0 = 0`, then `q = h − 1`, i.e. `h = q + 1`.
(The `C_V(H) = 0 ⟹ h = qⁿ + 1` half of BG Thm 2.5.) -/
theorem prop24k {h : ℕ} [NeZero h] (hh : 2 ≤ h) (n : ZMod h → ℤ) (hpos : ∀ i, 0 ≤ n i)
    (hq : 2 ≤ ∑ i, n i) (H : ∀ m : ZMod h, m ≠ 0 → ∑ i, (n i - n (i + m)) ^ 2 = 2)
    (h0 : n 0 = 0) : (∑ i, n i) = (h : ℤ) - 1 := by
  have : Fact (1 < h) := ⟨by omega⟩
  obtain ⟨i₁, v₀, δ, hδ, hconst, hi₁, hsum⟩ := prop24j hh n H
  by_cases hi0 : i₁ = 0
  · subst hi0
    have hv : v₀ + δ = 0 := hi₁.symm.trans h0
    have hv0 : (0 : ℤ) ≤ v₀ := by rw [← hconst 1 one_ne_zero]; exact hpos 1
    rcases hδ with hd | hd
    · exfalso; rw [hd] at hv; omega
    · have : v₀ = 1 := by rw [hd] at hv; omega
      rw [hsum, hd, this]; ring
  · exfalso
    have hv0 : v₀ = 0 := by rw [← hconst 0 (fun hc => hi0 hc.symm), h0]
    rw [hsum, hv0, mul_zero, zero_add] at hq
    rcases hδ with hd | hd <;> rw [hd] at hq <;> omega

/-- **`Fin h`-indexed form of `prop24k`** — transported through `ZMod.finEquiv`. The
`C_V(H) = 0 ⟹ q = h − 1` half of Thm 2.5, for `Fin h`-indexed eigenspace dimensions. -/
theorem prop24k_fin {h : ℕ} [NeZero h] (hh : 2 ≤ h) (n : Fin h → ℤ) (hpos : ∀ i, 0 ≤ n i)
    (hq : 2 ≤ ∑ i, n i) (H : ∀ m : Fin h, m ≠ 0 → ∑ i, (n i - n (i + m)) ^ 2 = 2)
    (h0 : n 0 = 0) : (∑ i, n i) = (h : ℤ) - 1 := by
  classical
  let e : Fin h ≃+* ZMod h := ZMod.finEquiv h
  set n' : ZMod h → ℤ := fun z => n (e.symm z) with hn'
  have hsumeq : ∑ i, n i = ∑ i', n' i' :=
    Fintype.sum_equiv e.toEquiv _ _ fun i => by simp [hn']
  have H' : ∀ m' : ZMod h, m' ≠ 0 → ∑ i', (n' i' - n' (i' + m')) ^ 2 = 2 := by
    intro m' hm'
    have hm : e.symm m' ≠ 0 := fun hc => hm' (by rw [← e.apply_symm_apply m', hc, map_zero])
    rw [← H (e.symm m') hm]
    refine (Fintype.sum_equiv e.toEquiv _ _ fun i => ?_).symm
    simp [hn', map_add]
  have hpos' : ∀ i', 0 ≤ n' i' := fun i' => by rw [hn']; exact hpos _
  have h0' : n' 0 = 0 := by change n (e.symm (0 : ZMod h)) = 0; rw [map_zero]; exact h0
  rw [hsumeq]
  exact prop24k hh n' hpos' (hsumeq ▸ hq) H' h0'

end OddOrder.RepresentationTheory


