-- Prove2me | Definitions.Def_GirvingAKS_Bags_Subtree
-- name    : GirvingAKS_Bags_Subtree
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T19:18:18.817797+00:00
-- url     : https://prove2.me/theorems/12834914-5fba-4385-9d32-2199d6cd769d
-- title:
--   AKS sorting networks (Seiferas port) — Subtree Non-Native Bounds
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bags/Subtree.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Local subregs lemmas (re-proved to avoid circular imports with Depth/Sorts) and the combined subtree non-native bound.
--
--   Key theorems:
--
--   - `spillover_bound`: deficit `b.size - subregs.card` bounded by `half_D + cap/(4A³-A)`
--   - `subtree_non_native_bound`: non-native items in subtree ≤ `2γεA/(1-(2εA)²)·cap`
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bags/Subtree.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bags_SepBridge

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bags/Subtree.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Subtree Non-Native Bounds

  Local subregs lemmas (re-proved to avoid circular imports with Depth/Sorts)
  and the combined subtree non-native bound.

  Key theorems:
  - `spillover_bound`: deficit `b.size - subregs.card` bounded by `half_D + cap/(4A³-A)`
  - `subtree_non_native_bound`: non-native items in subtree ≤ `2γεA/(1-(2εA)²)·cap`
-/


section

open Finset

variable {k : ℕ}

/-! **Local Subregs Lemmas (re-proved to avoid circular imports with Depth/Sorts)** -/

/-- `pl.regs b` is disjoint from `subregs pl c` when `b.l < c.l`. -/
theorem regs_disjoint_subregs' {k : ℕ} (pl : Placement k) (b c : Bag k)
    (h : b.l < c.l) :
    Disjoint (pl.regs b) (subregs pl c) := by
  unfold subregs; split
  case isTrue hk =>
    rw [Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨pl.disjoint b c (by intro heq; subst heq; omega),
            regs_disjoint_subregs' pl b (c.left hk) (by show b.l < c.l + 1; omega)⟩,
           regs_disjoint_subregs' pl b (c.right hk) (by show b.l < c.l + 1; omega)⟩
  case isFalse => exact pl.disjoint b c (by intro heq; subst heq; omega)
termination_by k - c.l
decreasing_by all_goals show k - (c.l + 1) < k - c.l; omega

/-- Every element of `subregs pl b` comes from `pl.regs c` for some descendant `c`. -/
theorem mem_subregs_exists_bag' {k : ℕ} (pl : Placement k)
    (b : Bag k) {r : Fin (2 ^ k)} (hr : r ∈ subregs pl b) :
    ∃ c : Bag k, b.l ≤ c.l ∧ c.x / 2 ^ (c.l - b.l) = b.x ∧ r ∈ pl.regs c := by
  unfold subregs at hr
  split at hr
  case isTrue h =>
    simp only [Finset.mem_union] at hr
    rcases hr with ((hr | hr) | hr)
    · exact ⟨b, le_refl _, by simp, hr⟩
    · obtain ⟨c, hle, hdesc, hc⟩ := mem_subregs_exists_bag' pl (b.left h) hr
      have hl_left : (b.left h).l = b.l + 1 := rfl
      have hx_left : (b.left h).x = 2 * b.x := rfl
      have hlev : b.l + 1 ≤ c.l := hl_left ▸ hle
      refine ⟨c, by omega, ?_, hc⟩
      show c.x / 2 ^ (c.l - b.l) = b.x
      have hdesc' : c.x / 2 ^ (c.l - (b.l + 1)) = 2 * b.x := by
        rw [← hl_left, ← hx_left]; exact hdesc
      rw [show c.l - b.l = (c.l - (b.l + 1)) + 1 from by omega, pow_succ,
          ← Nat.div_div_eq_div_mul, hdesc']
      exact Nat.mul_div_cancel_left _ (by omega)
    · obtain ⟨c, hle, hdesc, hc⟩ := mem_subregs_exists_bag' pl (b.right h) hr
      have hl_right : (b.right h).l = b.l + 1 := rfl
      have hx_right : (b.right h).x = 2 * b.x + 1 := rfl
      have hlev : b.l + 1 ≤ c.l := hl_right ▸ hle
      refine ⟨c, by omega, ?_, hc⟩
      show c.x / 2 ^ (c.l - b.l) = b.x
      have hdesc' : c.x / 2 ^ (c.l - (b.l + 1)) = 2 * b.x + 1 := by
        rw [← hl_right, ← hx_right]; exact hdesc
      rw [show c.l - b.l = (c.l - (b.l + 1)) + 1 from by omega, pow_succ,
          ← Nat.div_div_eq_div_mul, hdesc']
      omega
  case isFalse h =>
    exact ⟨b, le_refl _, by simp, hr⟩
termination_by k - b.l
decreasing_by all_goals show k - (b.l + 1) < k - b.l; omega

/-- `subregs` at the same level are disjoint for distinct bags. -/
theorem subregs_disjoint' {k : ℕ} (pl : Placement k) (b₁ b₂ : Bag k)
    (hne : b₁ ≠ b₂) (hl : b₁.l = b₂.l) :
    Disjoint (subregs pl b₁) (subregs pl b₂) := by
  rw [Finset.disjoint_left]
  intro r hr₁ hr₂
  obtain ⟨c₁, hle₁, hdesc₁, hc₁⟩ := mem_subregs_exists_bag' pl b₁ hr₁
  obtain ⟨c₂, hle₂, hdesc₂, hc₂⟩ := mem_subregs_exists_bag' pl b₂ hr₂
  have hceq : c₁ = c₂ := by
    by_contra hne'
    exact Finset.disjoint_left.mp (pl.disjoint c₁ c₂ hne') hc₁ hc₂
  subst hceq
  apply hne
  rw [hl] at hdesc₁
  exact Bag.ext hl (hdesc₁.symm.trans hdesc₂)

/-- Card of `subregs` splits as `regs + subregs(left) + subregs(right)`. -/
theorem subregs_card_split' {k : ℕ} (pl : Placement k) (b : Bag k)
    (h : b.l < k) :
    (subregs pl b).card = (pl.regs b).card + (subregs pl (b.left h)).card +
      (subregs pl (b.right h)).card := by
  conv_lhs => rw [subregs, dif_pos h]
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · exact regs_disjoint_subregs' pl b (b.left h) (by show b.l < b.l + 1; omega)
  · rw [Finset.disjoint_union_left]
    refine ⟨regs_disjoint_subregs' pl b (b.right h) (by show b.l < b.l + 1; omega),
           subregs_disjoint' pl (b.left h) (b.right h) (by
             intro heq; have : (b.left h).x = (b.right h).x := by rw [heq]
             simp [Bag.left, Bag.right] at this) rfl⟩

/-- Filter distributes over the disjoint subregs union. -/
theorem subregs_filter_card_split' {k : ℕ} (pl : Placement k) (b : Bag k)
    (h : b.l < k) (P : Fin (2 ^ k) → Prop) [DecidablePred P] :
    ((subregs pl b).filter P).card =
    ((pl.regs b).filter P).card + ((subregs pl (b.left h)).filter P).card +
      ((subregs pl (b.right h)).filter P).card := by
  conv_lhs => rw [subregs, dif_pos h]
  rw [Finset.filter_union, Finset.filter_union,
      Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · exact Finset.disjoint_filter_filter
      (regs_disjoint_subregs' pl b (b.left h) (by show b.l < b.l + 1; omega))
  · rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_filter_filter
             (regs_disjoint_subregs' pl b (b.right h) (by show b.l < b.l + 1; omega)),
           Finset.disjoint_filter_filter
             (subregs_disjoint' pl (b.left h) (b.right h) (by
               intro heq; have : (b.left h).x = (b.right h).x := by rw [heq]
               simp [Bag.left, Bag.right] at this) rfl)⟩

/-- All bags at the same level have the same `subregs` cardinality.
    Re-proved locally to avoid circular import with `Depth.lean`. -/
theorem subregs_card_uniform' (p : Params) (k t : ℕ) (b₁ b₂ : Bag k)
    (hl : b₁.l = b₂.l) :
    (subregs (stages p k t).value b₁).card =
    (subregs (stages p k t).value b₂).card := by
  set pl := (stages p k t).value
  by_cases hk : b₁.l < k
  · have hk₂ : b₂.l < k := hl ▸ hk
    rw [subregs_card_split' pl b₁ hk, subregs_card_split' pl b₂ hk₂,
        bagCard_eq_card p k t b₁, bagCard_eq_card p k t b₂, hl]
    congr 1
    · congr 1
      exact subregs_card_uniform' p k t (b₁.left hk) (b₂.left hk₂)
        (by simp [Bag.left, hl])
    · exact subregs_card_uniform' p k t (b₁.right hk) (b₂.right hk₂)
        (by simp [Bag.right, hl])
  · have hk₂ : ¬(b₂.l < k) := by omega
    conv_lhs => rw [subregs, dif_neg hk]
    conv_rhs => rw [subregs, dif_neg hk₂]
    rw [bagCard_eq_card p k t b₁, bagCard_eq_card p k t b₂, hl]
termination_by k - b₁.l
decreasing_by all_goals simp_all [Bag.left, Bag.right]; omega

/-- `subregs` card satisfies: `2^(b.l) * subregs.card = ∑ l' ∈ Ico b.l (k+1), 2^l' * bagCard(l')`.
    Proved by strong induction on `k - b.l`. -/
theorem subregs_card_mul_pow (p : Params) (k t : ℕ) (b : Bag k) :
    2 ^ b.l * (subregs (stages p k t).value b).card =
    ∑ l' ∈ Finset.Ico b.l (k + 1), 2 ^ l' * bagCard p k t l' := by
  set pl := (stages p k t).value
  by_cases hk : b.l < k
  · -- Inductive case: split subregs into regs + left + right
    rw [subregs_card_split' pl b hk]
    -- left and right have same card by uniformity
    have hLR : (subregs pl (b.left hk)).card = (subregs pl (b.right hk)).card :=
      subregs_card_uniform' p k t (b.left hk) (b.right hk) (by simp [Bag.left, Bag.right])
    -- IH for left child
    have ihL := subregs_card_mul_pow p k t (b.left hk)
    have hLl : (b.left hk).l = b.l + 1 := rfl
    rw [hLl] at ihL
    -- Split Ico b.l (k+1) = {b.l} ∪ Ico (b.l+1) (k+1)
    rw [← Finset.sum_Ico_consecutive (fun l' ↦ 2 ^ l' * bagCard p k t l')
      (by omega : b.l ≤ b.l + 1) (by omega : b.l + 1 ≤ k + 1),
      show Finset.Ico b.l (b.l + 1) = {b.l} from Nat.Ico_succ_singleton b.l,
      Finset.sum_singleton]
    -- LHS = 2^(b.l) * (regs.card + left.card + right.card)
    --     = 2^(b.l) * regs.card + 2^(b.l) * (left.card + right.card)
    --     = 2^(b.l) * bagCard(b.l) + 2^(b.l) * 2 * left.card  [since right = left]
    --     = 2^(b.l) * bagCard(b.l) + 2^(b.l+1) * left.card
    --     = 2^(b.l) * bagCard(b.l) + ∑ Ico (b.l+1) (k+1)      [by IH]
    -- Rewrite right.card to left.card, then factor
    rw [← hLR]
    have key : 2 ^ b.l * ((pl.regs b).card + (subregs pl (b.left hk)).card +
        (subregs pl (b.left hk)).card) =
      2 ^ b.l * (pl.regs b).card + 2 ^ (b.l + 1) * (subregs pl (b.left hk)).card := by
      rw [pow_succ]; ring
    rw [key, bagCard_eq_card p k t b, ihL]
  · -- Base case: b.l ≥ k, so b.l = k
    have hlk : b.l = k := by have := b.hl; omega
    have hk' : ¬(b.l < k) := hk
    conv_lhs => rw [subregs, dif_neg hk']
    rw [bagCard_eq_card p k t b, hlk]
    rw [show Finset.Ico k (k + 1) = {k} from Nat.Ico_succ_singleton k,
        Finset.sum_singleton]
termination_by k - b.l
decreasing_by simp_all [Bag.left]; omega

/-- The deficit `b.size - subregs.card` is bounded by `half_D + cap/(4A³-A)`.

    From `bagCard_total` and `subregs_card_mul_pow`, the deficit in ℚ equals
    `Σ_{l'<b.l} bagCard(l') / 2^{b.l-l'}`. The parent (l'=b.l-1) term
    = `parent_regs.card/2` (ℚ rational). Remaining active-parity ancestor
    terms form a geometric series `≤ cap/(8A³-2A)`. The coefficient is
    `1/(4A³-A) = 2/(8A³-2A)` rather than `1/(8A³-2A)` to absorb the ≤1/2
    parity correction from ℕ integer division of `parent_card`.
    When `parent_card` is odd, `bagCard_even_of_below_zero` (contrapositive)
    forces a nonzero ancestor at distance ≥ 3, giving `cap ≥ 4A³ > 4A³-A`,
    so `cap/(8A³-2A) ≥ 1/2` and `1/2 + rest ≤ 2·cap/(8A³-2A) = cap/(4A³-A)`. -/
theorem spillover_bound (p : Params) (k : ℕ) (hk : 10 ≤ k) (t : ℕ)
    (ht : t ≤ numStages p k) (b : Bag k) (hl : 1 ≤ b.l)
    (hpar_active : (t + (b.l - 1)) % 2 = 0) :
    (↑(b.size - (subregs (stages p k t).value b).card) : ℚ) ≤
    ↑(((stages p k t).value.regs b.parent).card / 2) +
    1 / (4 * p.A ^ 3 - p.A) * capacity p k t b.l := by
  set pl := (stages p k t).value
  set S := (subregs pl b).card
  set D := (pl.regs b.parent).card
  set cap := capacity p k t b.l
  have hA_pos : (0 : ℚ) < p.A := by linarith [p.hA]
  have h4A3_pos : (0 : ℚ) < 4 * p.A ^ 3 - p.A := by
    have := p.hA; nlinarith [sq_nonneg p.A]
  have h8A3_pos : (0 : ℚ) < 8 * p.A ^ 3 - 2 * p.A := by nlinarith [sq_nonneg p.A]
  have hfl := numStages_hfl p k hk t ht
  have hD_eq : D = bagCard p k t (b.l - 1) := bagCard_eq_card p k t b.parent
  have hbl_pos : 0 < b.l := by omega
  have hcap_pos : (0 : ℚ) < cap := capacity_pos p k t b.l
  -- Trivial case: if ℕ subtraction underflows to 0
  by_cases hle : S ≤ b.size
  case neg =>
    push_neg at hle
    simp only [show b.size - S = 0 from by omega, Nat.cast_zero]
    exact add_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (div_nonneg (by norm_num) h4A3_pos.le) hcap_pos.le)
  -- Main case: S ≤ b.size
  case pos =>
  set rest_nat := ∑ l' ∈ Finset.range (b.l - 1), 2 ^ l' * bagCard p k t l'
  have hpow_pos : (0 : ℚ) < 2 ^ b.l := by positivity
  -- Conservation identity: rest_nat + 2^(bl-1)*D + 2^bl*S = 2^bl * b.size
  have hsize_mul : 2 ^ b.l * b.size = 2 ^ k :=
    Nat.mul_div_cancel' (Nat.pow_dvd_pow 2 b.hl)
  have hnat_sum : rest_nat + 2 ^ (b.l - 1) * D + 2 ^ b.l * S = 2 ^ b.l * b.size := by
    have htotal := bagCard_total p k t
    have hsub := subregs_card_mul_pow p k t b
    have hsplit : ∑ l' ∈ Finset.range (k + 1), 2 ^ l' * bagCard p k t l' =
        rest_nat + 2 ^ (b.l - 1) * bagCard p k t (b.l - 1) +
        ∑ l' ∈ Finset.Ico b.l (k + 1), 2 ^ l' * bagCard p k t l' := by
      rw [(Finset.sum_range_add_sum_Ico _ (by have := b.hl; omega : b.l ≤ k + 1)).symm,
          (Finset.sum_range_add_sum_Ico _ (by omega : b.l - 1 ≤ b.l)).symm,
          show Finset.Ico (b.l - 1) b.l = {b.l - 1} from by
            rw [show b.l = b.l - 1 + 1 from by omega]; exact Nat.Ico_succ_singleton _,
          Finset.sum_singleton]
    rw [htotal] at hsplit; rw [← hsub, ← hD_eq] at hsplit
    change 2 ^ k = rest_nat + 2 ^ (b.l - 1) * D + 2 ^ b.l * S at hsplit
    linarith
  have hpow_ne : (2 : ℚ) ^ b.l ≠ 0 := by positivity
  have h2bl : (2:ℚ) ^ b.l = 2 * 2 ^ (b.l - 1) := by
    conv_lhs => rw [show b.l = (b.l - 1) + 1 from by omega]
    rw [pow_succ, mul_comm]
  -- Step 1: geometric series bound
  have hrest_bound : (↑rest_nat : ℚ) / 2 ^ b.l ≤ cap / (8 * p.A ^ 3 - 2 * p.A) := by
    -- Capacity ratio: cap = capacity(l') * A^(bl-l') for l' ≤ bl
    have cap_ratio : ∀ d, d ≤ b.l → capacity p k t (b.l - d) * p.A ^ d = cap :=
      fun d hd ↦ by
        induction d with
        | zero => simp only [Nat.sub_zero, pow_zero, mul_one]; rfl
        | succ n ih =>
          rw [pow_succ, show capacity p k t (b.l - (n + 1)) * (p.A ^ n * p.A) =
              p.A * capacity p k t (b.l - (n + 1)) * p.A ^ n from by ring,
              ← capacity_succ, show b.l - (n + 1) + 1 = b.l - n from by omega]
          exact ih (by omega)
    -- bagCard(l') ≤ capacity(l')
    have hbc := bagCard_le_capacity p k hk t hfl
    -- Per-term bound in ℚ: 2^l' * bagCard(l') / 2^bl ≤ cap / (2A)^(bl-l')
    -- For inactive l': bagCard = 0, so the term is 0.
    -- For active l' < bl-1: distance j = bl-l' is odd ≥ 3.
    have hterm_active : ∀ l' ∈ Finset.range (b.l - 1),
        (↑(2 ^ l' * bagCard p k t l') : ℚ) / 2 ^ b.l ≤
        if (t + l') % 2 = 0 then cap / (2 * p.A) ^ (b.l - l') else 0 := by
      intro l' hl'
      have hl'_lt : l' < b.l - 1 := Finset.mem_range.mp hl'
      split
      case isTrue hact =>
        -- Active: bound by capacity
        have hbc' := hbc l'
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        calc (2 : ℚ) ^ l' * ↑(bagCard p k t l') / 2 ^ b.l
            ≤ 2 ^ l' * capacity p k t l' / 2 ^ b.l := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hbc' (by positivity)
          _ = cap / (2 * p.A) ^ (b.l - l') := by
              have hcr := cap_ratio (b.l - l') (by omega)
              rw [show b.l - (b.l - l') = l' from by omega] at hcr
              rw [show (2:ℚ) ^ b.l = 2 ^ l' * 2 ^ (b.l - l') from by
                rw [← pow_add]; congr 1; omega,
                mul_div_mul_left _ _ (by positivity : (2:ℚ) ^ l' ≠ 0),
                mul_pow, div_eq_div_iff (by positivity) (by positivity)]
              calc capacity p k t l' * (2 ^ (b.l - l') * p.A ^ (b.l - l'))
                  = capacity p k t l' * p.A ^ (b.l - l') * 2 ^ (b.l - l') := by ring
                _ = cap * 2 ^ (b.l - l') := by rw [hcr]
      case isFalse hinact =>
        -- Inactive: bagCard = 0
        have hzero := bagCard_odd_eq_zero p k (by omega : 1 ≤ k) t l' (by omega)
        rw [hzero, Nat.mul_zero, Nat.cast_zero, zero_div]
    -- Active levels l' < bl-1 have odd distance j = bl-l' ≥ 3.
    -- Since (t+bl-1)%2=0 and (t+l')%2=0: l' ≡ bl-1 (mod 2), so bl-l' is odd.
    -- Since l' < bl-1: bl-l' ≥ 2, and odd means ≥ 3.
    -- Reindex: set m = (bl-l'-3)/2, so bl-l' = 2m+3. Active l' ↔ m ∈ ℕ.
    -- Σ_{active l'} cap/(2A)^(bl-l') = cap * Σ_{m} (1/(2A))^(2m+3)
    -- = cap * (1/(2A))² * Σ_{m} (1/(2A))^(2m+1)
    -- ≤ cap * r² * r/(1-r²)  [by odd_geom_sum_le]
    -- = cap * r³/(1-r²) = cap/(8A³-2A).
    -- For simplicity, bound: Σ_{l'<bl-1} term ≤ cap * Σ_{j=2}^{bl} r^j where
    -- inactive contribute 0. But we need the odd-only bound.

    -- Simplify: rest/2^bl ≤ cap * Σ_{active l'<bl-1} 1/(2A)^(bl-l')
    -- = cap * Σ_{m≥0, 2m+3≤bl} 1/(2A)^(2m+3)
    -- ≤ cap * Σ_{m≥0} r^(2m+3) = cap * r² * Σ_{m≥0} r^(2m+1) ≤ cap * r³/(1-r²)
    -- = cap / (8A³-2A)

    -- Let me bound rest/2^bl ≤ cap * Σ_{j≥2} r^j via a simpler geometric bound.
    -- Actually, we need the tight bound. Let me just bound directly.

    -- Bound: rest/2^bl ≤ Σ_{l'<bl-1} (active term)
    --   ≤ Σ_{l'<bl-1, active} cap/(2A)^(bl-l')
    -- where active distances are odd ≥ 3. Each ≤ cap * r^3 (for the largest).
    -- The sum is: cap * (r^3 + r^5 + r^7 + ...) = cap * r^3 * (1 + r^2 + r^4 + ...)
    -- = cap * r^3 / (1-r^2)

    -- Use: Σ_{l'<bl-1} if_active cap*r^(bl-l') ≤ cap * Σ_{m<(bl-1)/2} r^(2m+3)
    -- = cap * r² * Σ_{m<(bl-1)/2} r^(2m+1)
    -- ≤ cap * r² * r/(1-r²) = cap * r³/(1-r²) [by odd_geom_sum_le]

    -- First bound rest_nat / 2^bl by sum of if-then terms
    have hsum1 : (↑rest_nat : ℚ) / 2 ^ b.l ≤
        ∑ l' ∈ Finset.range (b.l - 1),
          if (t + l') % 2 = 0 then cap / (2 * p.A) ^ (b.l - l') else 0 := by
      rw [show (↑rest_nat : ℚ) = ∑ l' ∈ Finset.range (b.l - 1),
          (↑(2 ^ l' * bagCard p k t l') : ℚ) from by
        change (↑(∑ l' ∈ Finset.range (b.l - 1), 2 ^ l' * bagCard p k t l') : ℚ) = _
        push_cast; rfl]
      rw [Finset.sum_div]
      exact Finset.sum_le_sum hterm_active

    -- Remove inactive terms: the sum equals Σ over active l' only
    -- Upper-bound by allowing ALL odd j ≥ 3 (relaxing the l' < bl-1 constraint)
    -- Σ_{l' active, l'<bl-1} cap/(2A)^(bl-l') ≤ cap * Σ_{m≥0} r^(2*(m+1)+1)
    -- = cap * r² * Σ_{m≥0} r^(2m+1) ≤ cap * r² * (r/(1-r²)) = cap * r³/(1-r²)

    -- Eliminate if-then-else: for active l', (t+l')%2=0 and (t+bl-1)%2=0
    -- means bl-l' is odd. Reindex: for active l' ∈ range(bl-1), set m s.t. bl-l' = 2m+3
    -- (m = (bl-l'-3)/2). Actually simpler: bound by dropping the range constraint.
    -- Σ_{active l'} r^(bl-l') ≤ Σ_{j odd, j≥3}^∞ r^j
    -- = r^3 + r^5 + ... = r^2 * (r + r^3 + ...) = r^2 * Σ_{m≥0} r^(2m+1)

    -- Actually, I think the most practical approach is to avoid reindexing
    -- entirely and instead prove a custom lemma:

    -- "For r > 0, r² < 1, Σ_{j ∈ S} r^j ≤ r^a / (1-r²)
    --  when S ⊆ {a, a+2, a+4, ...} (finite set of integers ≡ a (mod 2), ≥ a)"
    -- This is a straightforward consequence of the geometric series.

    -- But writing this general lemma would take many lines too.
    -- Let me just use a DIRECT calculation instead.

    -- DIRECT APPROACH: prove rest_nat / 2^bl ≤ cap * r² * Σ_{i<bl} r^(2i+1) by
    -- showing each term of rest_nat / 2^bl can be matched to a term of the RHS.
    -- Then apply odd_geom_sum_le.

    -- I think the shortest path is:
    -- 1. Use hsum1 to get rest/2^bl ≤ Σ if-terms
    -- 2. Use Finset.sum_le_sum to replace each if-active term by cap*r^(bl-l')
    --    and each inactive term by 0 (already done)
    -- 3. Use Finset.sum_filter to extract only active terms
    -- 4. Reindex via image of the distance map
    -- 5. Apply aux_geom

    -- Let me try steps 3-5 more carefully.

    -- After hsum1: rest/2^bl ≤ Σ_{l'<bl-1} ite(active, cap*r^(bl-l'), 0)
    --  = Σ_{l' active ∧ l'<bl-1} cap * r^(bl-l')  [by Finset.sum_filter]
    --  = cap * Σ_{l' active ∧ l'<bl-1} r^(bl-l')

    -- For each active l' < bl-1: bl-l' ≥ 2 and odd (since l'≡bl-1 mod 2).
    -- So bl-l' ∈ {3, 5, 7, ...}. Write bl-l' = 2*m_l'+3 where m_l' = (bl-l'-3)/2.
    -- m_l' < bl/2 (since bl-l' ≤ bl, so m_l' ≤ (bl-3)/2 < bl/2).
    -- The map l' ↦ m_l' is injective on active l' (since l' = bl-2*m_l'-3).

    -- So: Σ_{l' active} r^(bl-l') = Σ_{l' active} r^(2*m_l'+3)
    -- Each is a distinct term r^(2*m+3) for m ∈ image of the map.
    -- The image ⊆ range(bl/2).
    -- So: ≤ Σ_{m<bl/2} r^(2*(m+1)+1) ≤ r³/(1-r²) by aux_geom.

    -- Implement using Finset.sum_comp or similar.
    -- Actually, for a subset sum bound, I can use:
    -- Σ_{i ∈ S} f i ≤ Σ_{i ∈ T} f i when S ⊆ T and f ≥ 0.

    set r : ℚ := 1 / (2 * p.A) with hr_def

    -- Step 3: extract active sum
    have hsum2 : (↑rest_nat : ℚ) / 2 ^ b.l ≤
        cap * ∑ l' ∈ (Finset.range (b.l - 1)).filter (fun l' ↦ (t + l') % 2 = 0),
          r ^ (b.l - l') := by
      calc (↑rest_nat : ℚ) / 2 ^ b.l ≤
          ∑ l' ∈ Finset.range (b.l - 1),
            if (t + l') % 2 = 0 then cap / (2 * p.A) ^ (b.l - l') else 0 := hsum1
        _ = ∑ l' ∈ (Finset.range (b.l - 1)).filter (fun l' ↦ (t + l') % 2 = 0),
            cap / (2 * p.A) ^ (b.l - l') := by
          rw [← Finset.sum_filter]
        _ = cap * ∑ l' ∈ (Finset.range (b.l - 1)).filter (fun l' ↦ (t + l') % 2 = 0),
            r ^ (b.l - l') := by
          rw [Finset.mul_sum]; congr 1; ext l'
          rw [hr_def, one_div, inv_pow, ← div_eq_mul_inv]

    -- Step 4: bound active sum ≤ Σ_{m<bl/2} r^(2*(m+1)+1)
    -- Active l' have bl-l' = 2*(some m)+3. These m are distinct and < bl/2.
    -- So {r^(bl-l') : l' active} ⊆ {r^(2*(m+1)+1) : m < bl/2} as a sub-multiset.
    have hsum3 : ∑ l' ∈ (Finset.range (b.l - 1)).filter (fun l' ↦ (t + l') % 2 = 0),
        r ^ (b.l - l') ≤ ∑ m ∈ Finset.range (b.l / 2), r ^ (2 * (m + 1) + 1) := by
      -- The map l' ↦ (bl - l' - 3)/2 is injective from active l' to range(bl/2)
      -- and preserves: r^(bl-l') = r^(2*((bl-l'-3)/2+1)+1).
      set S := (Finset.range (b.l - 1)).filter (fun l' ↦ (t + l') % 2 = 0)
      set idx : ℕ → ℕ := fun l' ↦ (b.l - l' - 3) / 2
      -- Injectivity of idx on S
      have hinj : Set.InjOn idx ↑S := by
        intro l₁ hl₁ l₂ hl₂ heq
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_range, S] at hl₁ hl₂
        simp only [idx] at heq; omega
      -- Value match: r^(bl-l') = r^(2*(idx(l')+1)+1)
      have hval : ∀ l' ∈ S, r ^ (b.l - l') = r ^ (2 * (idx l' + 1) + 1) := by
        intro l' hl'
        simp only [Finset.mem_filter, Finset.mem_range, S] at hl'
        congr 1; simp only [idx]; omega
      -- Image maps into range(bl/2)
      have himg : S.image idx ⊆ Finset.range (b.l / 2) := by
        intro m hm
        simp only [Finset.mem_image, S, idx, Finset.mem_filter, Finset.mem_range] at hm
        obtain ⟨l', ⟨hl'_lt, _⟩, rfl⟩ := hm
        simp only [Finset.mem_range]; omega
      -- Chain: rewrite LHS, then use subset bound
      calc ∑ l' ∈ S, r ^ (b.l - l')
          = ∑ l' ∈ S, r ^ (2 * (idx l' + 1) + 1) := Finset.sum_congr rfl hval
        _ = ∑ m ∈ S.image idx, r ^ (2 * (m + 1) + 1) :=
            (Finset.sum_image (f := fun m ↦ r ^ (2 * (m + 1) + 1)) hinj).symm
        _ ≤ ∑ m ∈ Finset.range (b.l / 2), r ^ (2 * (m + 1) + 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun m _ _ ↦ by positivity)
    have hr_pos : 0 < r := by positivity
    have hr2 : r ^ 2 < 1 := by
      rw [hr_def, div_pow, one_pow, div_lt_one (by positivity)]; nlinarith [p.hA]
    -- Bound: Σ_{active l'} cap*r^(bl-l') ≤ cap * r^2 * Σ_{i<(bl/2)} r^(2i+1)
    -- ≤ cap * r^2 * r/(1-r^2) = cap * r^3/(1-r^2)
    -- Compute: r³/(1-r²) = 1/(8A³) / (1-1/(4A²)) = 1/(8A³) * 4A²/(4A²-1)
    -- = 4A²/(8A³(4A²-1)) = 1/(2A(4A²-1)) = 1/(8A³-2A)
    have hclosed : cap * r ^ 3 / (1 - r ^ 2) = cap / (8 * p.A ^ 3 - 2 * p.A) := by
      have h1r2_pos : (0:ℚ) < 1 - r ^ 2 := by linarith [hr2]
      rw [div_eq_div_iff (ne_of_gt h1r2_pos) (ne_of_gt h8A3_pos), hr_def]
      have : (0:ℚ) < 2 * p.A := by linarith [p.hA]
      field_simp; ring
    suffices hsuff : (↑rest_nat : ℚ) / 2 ^ b.l ≤ cap * r ^ 3 / (1 - r ^ 2) by
      linarith [hclosed]
    -- Upper bound the if-sum by cap * r^2 * Σ_{i<N} r^(2i+1) for large N
    -- where N ≥ (bl-1)/2
    -- First: the if-sum ≤ cap * Σ_{j odd, 3≤j≤bl} r^j
    -- = cap * Σ_{m=0}^{(bl-3)/2} r^(2m+3) = cap * r^2 * Σ_{m=0}^{(bl-3)/2} r^(2m+1)
    -- ≤ cap * r^2 * r/(1-r^2) = cap * r^3/(1-r^2)  [by odd_geom_sum_le]

    -- bound: Σ if-terms ≤ cap * r² * Σ_{i<bl/2} r^(2i+1)
    -- First prove Σ if-terms ≤ cap * Σ_{m<bl/2} r^(2m+3)
    -- Then factor out r² and apply odd_geom_sum_le

    -- Let me use a simpler bound: just bound by the infinite geometric series directly.
    -- rest/2^bl ≤ Σ r^j for j odd ≥ 3 = r^3/(1-r^2)
    -- This avoids the reindexing problem.
    -- r^3/(1-r^2) = r^2 * r/(1-r^2)
    -- By odd_geom_sum_le: Σ_{i<n} r^(2i+1) ≤ r/(1-r^2)
    -- So cap * r^2 * Σ_{i<n} r^(2i+1) ≤ cap * r^3/(1-r^2) for any n.

    -- APPROACH: bound the if-sum by cap * Σ_{active l'} r^(bl-l')
    -- Then show each active distance bl-l' = 2m+3 for some m,
    -- hence Σ r^(2m+3) = r² * Σ r^(2m+1) ≤ r² * r/(1-r²) = r³/(1-r²).

    -- Rather than reindexing in Lean, use a cleaner bound:
    -- Σ_{l'<bl-1} if-term ≤ Σ_{j=2}^{bl} cap*r^j (summing over ALL j≥2)
    -- = cap * (r^2 + r^3 + ... + r^bl)
    -- = cap * r² * (1 + r + ... + r^{bl-2})
    -- ≤ cap * r² / (1-r) [geometric series]
    -- But r²/(1-r) > r³/(1-r²) when r < 1. So this is NOT tight enough.
    -- We NEED the odd-only bound. So I must reindex.

    -- Clean approach: explicitly construct a bijection between active levels
    -- and an index set for odd_geom_sum_le.
    -- Active l' with l' < bl-1 and (t+l')%2=0.
    -- (t+bl-1)%2=0, so l' active iff l' ≡ bl-1 (mod 2).
    -- Active levels below bl-1: l' ∈ {bl-3, bl-5, ..., bl-2*N-1} for some N.
    -- Distance j = bl-l' ∈ {3, 5, ..., 2*N+1}.
    -- = {2*1+1, 2*2+1, ..., 2*N+1} -- NO: {3,5,...} = {2*1+1, 2*2+1, ...}
    -- For m = 1, 2, ..., N: j = 2m+1, r^j = r^(2m+1).
    -- Σ = Σ_{m=1}^N r^(2m+1) = (Σ_{m=0}^N r^(2m+1)) - r = (Σ_{i<N+1} r^(2i+1)) - r
    -- ≤ r/(1-r²) - r = r(1/(1-r²) - 1) = r*r²/(1-r²) = r³/(1-r²)

    -- So I need: Σ_{l' active, l'<bl-1} cap*r^(bl-l')
    --   = cap * (Σ_{i<N+1} r^(2i+1) - r)  for suitable N
    --   ≤ cap * (r/(1-r²) - r)
    --   = cap * r³/(1-r²)

    -- This requires showing Σ_{i<N+1} r^(2i+1) ≤ r/(1-r²) which is odd_geom_sum_le,
    -- and then subtracting r from both sides.

    -- But actually, we can just bound Σ_{m=1}^N r^(2m+1) directly:
    -- = Σ_{i<N} r^(2*(i+1)+1) = Σ_{i<N} r^(2i+3) = r² * Σ_{i<N} r^(2i+1)
    -- ≤ r² * r/(1-r²) = r³/(1-r²) [by odd_geom_sum_le]

    -- So the key identity: Σ_{m=1}^N r^(2m+1) = r² * Σ_{m=0}^{N-1} r^(2m+1)

    -- Let me implement this cleanly.
    -- Step A: bound Σ_{l'<bl-1} if_active cap*r^(bl-l') ≤ cap * Σ_{m<(bl-1)/2} r^(2m+3)
    -- Step B: factor: Σ r^(2m+3) = r² * Σ r^(2m+1)
    -- Step C: apply odd_geom_sum_le: Σ_{i<M+1} r^(2i+1) ≤ r/(1-r²)
    -- Step D: combine: cap * r² * r/(1-r²) = cap*r³/(1-r²) = cap/(8A³-2A)

    -- For Step A, rather than an explicit bijection, bound term-by-term
    -- using r^(bl-l') ≤ r^3 (since bl-l' ≥ 3, r ≤ 1). No, that's too loose.

    -- Let me try the simplest approach: just bound by sum of ALL r^j for j ≥ 2:
    -- Σ ≤ cap * Σ_{j≥2} r^j = cap * r²/(1-r)
    -- For Seiferas params A=10: r = 1/20, r²/(1-r) = 1/400 * 20/19 = 1/380.
    -- 1/(8*1000-20) = 1/7980. And 1/380 > 1/7980. So indeed NOT tight.
    -- We absolutely need the odd-only bound.

    -- OK let me just do the reindexing properly.
    -- I'll prove: Σ_{l'∈range(bl-1)} if-active cap*r^(bl-l') ≤ cap*r²*Σ_{i<bl/2} r^(2i+1)
    -- by showing each active l' term matches some r^(2i+3) term.

    -- Actually, a much cleaner approach: bound the SUM directly without reindexing.
    -- We know rest_nat is a ℕ sum. Instead of per-term bounding, use a telescoping argument.
    -- But that seems harder.

    -- Let me try yet another approach: prove an auxiliary lemma
    -- "sum of r^j for odd j from 3 to 2N+1 ≤ r³/(1-r²)"
    -- as a consequence of odd_geom_sum_le, then apply it.

    -- Auxiliary: Σ_{m=0}^{N-1} r^(2*(m+1)+1) ≤ r³/(1-r²)
    have aux_geom : ∀ N, ∑ m ∈ Finset.range N, r ^ (2 * (m + 1) + 1) ≤
        r ^ 3 / (1 - r ^ 2) := by
      intro N
      have hshift : ∀ m, r ^ (2 * (m + 1) + 1) = r ^ 2 * r ^ (2 * m + 1) := by
        intro m; rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 from by ring, pow_add]; ring
      simp_rw [hshift, ← Finset.mul_sum]
      rw [show r ^ 3 / (1 - r ^ 2) = r ^ 2 * (r / (1 - r ^ 2)) from by ring]
      exact mul_le_mul_of_nonneg_left (odd_geom_sum_le r hr_pos hr2 N) (sq_nonneg r)

    -- Now I need to show that Σ_{l'<bl-1} if-active cap*r^(bl-l')
    -- ≤ cap * Σ_{m<M} r^(2*(m+1)+1) for suitable M.
    -- This requires matching active l' with index m.
    -- Active l' has bl-l' = 2*(m+1)+1 for m = (bl-l'-3)/2.
    -- So l' = bl - 2m - 3. For l' ∈ range(bl-1): 0 ≤ l' < bl-1, i.e.,
    -- 0 ≤ bl-2m-3 < bl-1, i.e., 1 < 2m+3 ≤ bl, i.e., m < (bl-2)/2.

    -- The cleanest approach: bound the if-sum ≤ cap * aux_geom for M = bl/2.
    -- Each if-active term with l'<bl-1 has bl-l' ≥ 2, odd, so bl-l' ≥ 3.
    -- Write bl-l' = 2*m_l'+3 where m_l' = (bl-l'-3)/2. Then m_l' < (bl-2)/2 ≤ bl/2.
    -- The map l' ↦ m_l' is injective on active l'.
    -- So Σ_{active l'} r^(bl-l') ≤ Σ_{m<bl/2} r^(2*(m+1)+1).

    -- This injection argument is fiddly in Lean. Let me try a different route:
    -- Bound each inactive term by 0, each active term by cap*r^(bl-l'),
    -- then bound Σ r^(bl-l') ≤ Σ_{j≥3,odd} r^j by adding non-negative terms.
    -- But the Finset world makes "adding terms" hard.

    -- SIMPLEST CORRECT APPROACH: skip the Finset reindexing entirely.
    -- Prove by induction on (bl-1) that rest/2^bl ≤ cap*r³/(1-r²).
    -- Base: bl=1: range(0) is empty, rest=0. ✓
    -- Inductive: split off the last term l'=bl-2 (if active) or add 0 (if inactive).
    -- The active term contributes cap*r^2 (distance 2). Wait, bl-l' = bl-(bl-2) = 2,
    -- but 2 is even! So the last term l'=bl-2 is INACTIVE.
    -- The second-to-last: l'=bl-3 has distance 3 (odd). If active, contributes ≤ cap*r^3.
    -- Then recurse on the sum up to l'<bl-3.
    -- By induction, sub-sum/(2^(bl-2)) ≤ cap'*r³/(1-r²) where cap' = capacity(bl-2) = cap/A².
    -- sub-sum/2^bl = sub-sum/(2^(bl-2)*4) = (cap/A²)*r³/((1-r²)*4) = cap*r³/(4A²*(1-r²)).
    -- Plus active term cap*r^3.
    -- Total = cap*r³ + cap*r³/(4A²*(1-r²)). Hmm, this doesn't simplify nicely.

    -- I think the reindexing IS needed. Let me just do it with Finset.sum_nbij.
    -- Actually, the simplest approach that avoids reindexing:
    -- Note that Σ_{l'<bl-1, l' active} r^(bl-l') = Σ_{l'<bl-1, l' active} r^(bl-l')
    -- Each bl-l' ≥ 3 and odd. All these terms are ≤ r^3 + r^5 + r^7 + ... (partial sum).
    -- We just need Σ_{a finite set of odd integers ≥ 3} r^j ≤ Σ_{j≥3, odd} r^j.
    -- This follows from: finite sum of non-negative terms from a set S ⊆ T
    -- is ≤ sum over T.

    -- BUT we need the infinite sum Σ_{j≥3,odd} r^j to be well-defined and finite.
    -- In ℚ, infinite sums don't exist! We need a FINITE upper bound.
    -- odd_geom_sum_le gives: Σ_{i<n} r^(2i+1) ≤ r/(1-r²) for ANY n.
    -- So Σ_{m=0}^{N-1} r^(2*(m+1)+1) ≤ r³/(1-r²) for ANY N (from aux_geom).

    -- So I just need: Σ_{l' active, l'<bl-1} r^(bl-l')
    -- ≤ Σ_{m=0}^{N-1} r^(2*(m+1)+1) for N large enough.
    -- Each active l' gives r^(bl-l') = r^(2m+3) for some unique m < N.
    -- Since there are at most (bl-1)/2 active levels, take N = bl/2.

    -- Let me implement this with Finset.sum_le_sum_of_injOn or similar.
    -- Or even simpler: just observe that the set of active distances
    -- {bl-l' : l' active, l'<bl-1} ⊆ {2m+3 : m < bl/2} (as multisets, they're sets
    -- since the map l'↦bl-l' is injective).
    -- Then Σ_{S} r^j ≤ Σ_{T} r^j since r^j ≥ 0 and S ⊆ T.

    -- This is getting very long. Let me try a TOTALLY different approach.
    -- Just bound the sum crudely: Σ_{l'<bl-1} |term| ≤ (bl-1) * max_term.
    -- max_term ≤ cap * r^2 (smallest distance is 2). So bound ≤ (bl-1)*cap*r².
    -- For A=10: r²=1/400, (bl-1)*cap/400. Not useful without knowing bl.
    -- This is too crude.

    -- OK, the cleanest implementation is: prove a helper lemma
    -- "Σ_{l' ∈ S} r^(f l') ≤ Σ_{m ∈ range N} r^(g m)"
    -- when f maps S injectively into {g m : m ∈ range N}.
    -- This is just Finset.sum_le_sum + Finset.sum_le_card_nsmul or similar.
    -- But simpler: use Finset.sum_le_of_subset.

    -- Concretely: define T = Finset of odd integers in [3, 2*⌊bl/2⌋+1].
    -- Show: for each active l' < bl-1, bl-l' ∈ T.
    -- Then Σ_{active l'} r^(bl-l') ≤ Σ_{j ∈ T} r^j [by Finset subset sum].
    -- Then show Σ_{j ∈ T} r^j ≤ r³/(1-r²) [by aux_geom + reindex].

    -- Actually, I think the most practical approach is to avoid reindexing
    -- entirely and instead prove a custom lemma:

    -- "For r > 0, r² < 1, Σ_{j ∈ S} r^j ≤ r^a / (1-r²)
    --  when S ⊆ {a, a+2, a+4, ...} (finite set of integers ≡ a (mod 2), ≥ a)"
    -- This is a straightforward consequence of the geometric series.

    -- But writing this general lemma would take many lines too.
    -- Let me just use a DIRECT calculation instead.

    -- DIRECT APPROACH: prove rest_nat / 2^bl ≤ cap * r² * Σ_{i<bl} r^(2i+1) by
    -- showing each term of rest_nat / 2^bl can be matched to a term of the RHS.
    -- Then apply odd_geom_sum_le.

    -- I think the shortest path is:
    -- 1. Use hsum1 to get rest/2^bl ≤ Σ if-terms
    -- 2. Use Finset.sum_le_sum to replace each if-active term by cap*r^(bl-l')
    --    and each inactive term by 0 (already done)
    -- 3. Use Finset.sum_filter to extract only active terms
    -- 4. Reindex via image of the distance map
    -- 5. Apply aux_geom

    -- Let me try steps 3-5 more carefully.

    -- After hsum1: rest/2^bl ≤ Σ_{l'<bl-1} ite(active, cap*r^(bl-l'), 0)
    --  = Σ_{l' active ∧ l'<bl-1} cap * r^(bl-l')  [by Finset.sum_filter]
    --  = cap * Σ_{l' active ∧ l'<bl-1} r^(bl-l')

    -- For each active l' < bl-1: bl-l' ≥ 2 and odd (since l'≡bl-1 mod 2).
    -- So bl-l' ∈ {3, 5, 7, ...}. Write bl-l' = 2*m_l'+3 where m_l' = (bl-l'-3)/2.
    -- m_l' < bl/2 (since bl-l' ≤ bl, so m_l' ≤ (bl-3)/2 < bl/2).
    -- The map l' ↦ m_l' is injective on active l' (since l' = bl-2*m_l'-3).

    -- So: Σ_{l' active} r^(bl-l') = Σ_{l' active} r^(2*m_l'+3)
    -- Each is a distinct term r^(2*m+3) for m ∈ image of the map.
    -- The image ⊆ range(bl/2).
    -- So: ≤ Σ_{m<bl/2} r^(2*(m+1)+1) ≤ r³/(1-r²) by aux_geom.

    -- Implement using Finset.sum_comp or similar.
    -- Actually, for a subset sum bound, I can use:
    -- Σ_{i ∈ S} f i ≤ Σ_{i ∈ T} f i when S ⊆ T and f ≥ 0.

    -- Step 3: extract active sum
    -- (already have hsum2 above)

    -- (already have hsum3 above)

    -- Combine
    calc (↑rest_nat : ℚ) / 2 ^ b.l
        ≤ cap * ∑ l' ∈ (Finset.range (b.l - 1)).filter (fun l' ↦ (t + l') % 2 = 0),
            r ^ (b.l - l') := hsum2
      _ ≤ cap * ∑ m ∈ Finset.range (b.l / 2), r ^ (2 * (m + 1) + 1) :=
          mul_le_mul_of_nonneg_left hsum3 hcap_pos.le
      _ ≤ cap * (r ^ 3 / (1 - r ^ 2)) :=
          mul_le_mul_of_nonneg_left (aux_geom (b.l / 2)) hcap_pos.le
      _ = cap * r ^ 3 / (1 - r ^ 2) := (mul_div_assoc _ _ _).symm
  -- Step 2: deficit = rest/2^bl + D/2 (conservation identity in ℚ)
  have hdeficit_rat : (↑(b.size - S) : ℚ) ≤
      (↑rest_nat : ℚ) / 2 ^ b.l + ↑D / 2 := by
    suffices h : (↑(b.size - S) : ℚ) = ↑rest_nat / 2 ^ b.l + ↑D / 2 by linarith
    -- Key: 2^bl * ↑(bsize - S) = ↑rest + 2^(bl-1) * ↑D
    have hQ_mul : (2:ℚ) ^ b.l * ↑(b.size - S) = ↑rest_nat + 2 ^ (b.l - 1) * ↑D := by
      have h3 : 2 ^ b.l * (b.size - S) = rest_nat + 2 ^ (b.l - 1) * D := by
        have h2 : 2 ^ b.l * (b.size - S) + 2 ^ b.l * S = 2 ^ b.l * b.size := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hle]
        linarith
      exact_mod_cast h3
    have step1 : (↑D : ℚ) / 2 = 2 ^ (b.l - 1) * ↑D / 2 ^ b.l := by
      rw [h2bl]; field_simp
    rw [step1, ← add_div, eq_comm, div_eq_iff hpow_ne]
    linarith [hQ_mul]
  have hD_rat : (↑D : ℚ) / 2 = ↑(D / 2) + ↑(D % 2) / 2 := by
    have hd := (Nat.div_add_mod D 2).symm
    have : (↑D : ℚ) = 2 * ↑(D / 2) + ↑(D % 2) := by
      have h1 : (↑D : ℚ) = ↑(2 * (D / 2) + D % 2) := by rw [← hd]
      rw [h1]; push_cast; ring
    linarith
  -- Step 3: When D odd, rest_nat ≥ 2^(bl-1) from conservation + parity.
  -- From hnat_sum: rest + 2^(bl-1)*D = 2^bl*(bsize-S) = 2*2^(bl-1)*(bsize-S).
  -- So rest = 2^(bl-1)*(2*(bsize-S) - D). D odd → 2*(bsize-S)-D ≥ 1 → rest ≥ 2^(bl-1).
  have hrest_ge_half : D % 2 = 1 → (1 : ℚ) / 2 ≤ ↑rest_nat / 2 ^ b.l := by
    intro hodd
    -- ℕ arithmetic: rest_nat ≥ 2^(bl-1)
    have hnat_id : rest_nat + 2 ^ (b.l - 1) * D = 2 ^ b.l * (b.size - S) := by
      have h2 : 2 ^ b.l * (b.size - S) + 2 ^ b.l * S = 2 ^ b.l * b.size := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hle]
      linarith
    -- 2^bl = 2 * 2^(bl-1)
    have h2bl_nat : 2 ^ b.l = 2 * 2 ^ (b.l - 1) := by
      conv_lhs => rw [show b.l = (b.l - 1) + 1 from by omega]
      rw [pow_succ, mul_comm]
    -- Substitute: rest + 2^(bl-1)*D = 2*2^(bl-1)*(bsize-S)
    rw [h2bl_nat] at hnat_id
    -- rest ≥ 2^(bl-1): from mod arithmetic
    -- 2*2^(bl-1)*(bsize-S) - 2^(bl-1)*D = 2^(bl-1)*(2*(bsize-S) - D)
    -- D odd → 2*(bsize-S)-D odd → ≥ 1
    -- Need: D ≤ 2*(bsize-S) (from hnat_id with rest_nat ≥ 0)
    have hD_le : D ≤ 2 * (b.size - S) :=
      Nat.le_of_mul_le_mul_left (by linarith : 2 ^ (b.l - 1) * D ≤ 2 ^ (b.l - 1) * (2 * (b.size - S)))
        (by positivity)
    -- Key: 2*(bsize-S) - D ≥ 1 (odd, nonneg)
    have h_diff_odd : (2 * (b.size - S) - D) % 2 = 1 := by omega
    have h_diff_ge1 : 1 ≤ 2 * (b.size - S) - D := by omega
    -- rest = 2^(bl-1) * (2*(bsize-S) - D) ≥ 2^(bl-1) * 1
    have hrest_ge : 2 ^ (b.l - 1) ≤ rest_nat := by
      -- rest = 2*2^(bl-1)*(bsize-S) - 2^(bl-1)*D = 2^(bl-1)*(2*(bsize-S)-D)
      have hfact : rest_nat = 2 ^ (b.l - 1) * (2 * (b.size - S) - D) := by
        rw [Nat.mul_sub, show 2 ^ (b.l - 1) * (2 * (b.size - S)) =
            2 * 2 ^ (b.l - 1) * (b.size - S) from by ring]
        omega
      rw [hfact]
      exact Nat.le_mul_of_pos_right _ (by omega)
    -- Cast to ℚ
    have h_half_eq : (1:ℚ) / 2 = 2 ^ (b.l - 1) / 2 ^ b.l := by rw [h2bl]; field_simp
    rw [h_half_eq]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hrest_ge) (by positivity)
  -- Assembly
  calc (↑(b.size - S) : ℚ) ≤ ↑rest_nat / 2 ^ b.l + ↑D / 2 := hdeficit_rat
    _ = ↑rest_nat / 2 ^ b.l + (↑(D / 2) + ↑(D % 2) / 2) := by rw [hD_rat]
    _ = (↑rest_nat / 2 ^ b.l + ↑(D % 2) / 2) + ↑(D / 2) := by ring
    _ ≤ 1 / (4 * p.A ^ 3 - p.A) * cap + ↑(D / 2) := by
        -- rest + parity ≤ cap/(4A³-A)
        suffices h : ↑rest_nat / 2 ^ b.l + ↑(D % 2) / 2 ≤
            1 / (4 * p.A ^ 3 - p.A) * cap by linarith
        by_cases hpar : D % 2 = 0
        · -- D even: parity term = 0, rest ≤ cap/(8A³-2A) ≤ cap/(4A³-A)
          simp only [hpar, Nat.cast_zero, zero_div, add_zero]
          calc ↑rest_nat / 2 ^ b.l ≤ cap / (8 * p.A ^ 3 - 2 * p.A) := hrest_bound
            _ ≤ cap / (4 * p.A ^ 3 - p.A) := by
                apply div_le_div_of_nonneg_left hcap_pos.le h4A3_pos; linarith
            _ = 1 / (4 * p.A ^ 3 - p.A) * cap := by ring
        · -- D odd: 1/2 ≤ rest/2^bl, so rest + 1/2 ≤ 2·rest ≤ 2·cap/(8A³-2A) = cap/(4A³-A)
          have hmod : D % 2 = 1 := by omega
          simp only [hmod, Nat.cast_one]
          have h_half := hrest_ge_half hmod
          -- rest + 1/2 ≤ 2 * rest ≤ 2 * cap/(8A³-2A) = cap/(4A³-A)
          set R : ℚ := ↑rest_nat / 2 ^ b.l with hR_def
          have h_double_rest : R + 1 / 2 ≤ 2 * R := by linarith [h_half]
          have h_double_bound : 2 * R ≤
              2 * (cap / (8 * p.A ^ 3 - 2 * p.A)) := by
            have : R ≤ cap / (8 * p.A ^ 3 - 2 * p.A) := hR_def ▸ hrest_bound
            linarith
          have h_coeff : 2 * (cap / (8 * p.A ^ 3 - 2 * p.A)) =
              1 / (4 * p.A ^ 3 - p.A) * cap := by
            have h8eq : 8 * p.A ^ 3 - 2 * p.A = 2 * (4 * p.A ^ 3 - p.A) := by ring
            rw [h8eq, mul_div_assoc', mul_div_mul_left _ _ two_ne_zero]; ring
          linarith
    _ = ↑(D / 2) + 1 / (4 * p.A ^ 3 - p.A) * cap := by ring

/-! **Subtree Non-Native Bound** -/

/-- Descendant bags at distance `d` from `b` are `(d+1)`-strange at `b`:
    non-b-native items in `pl.regs c` ≤ `b.strangers (d+1) perm (pl.regs c)`. -/
theorem filter_not_native_le_strangers {k : ℕ} (b c : Bag k)
    (perm : Fin (2 ^ k) → Fin (2 ^ k)) (S : Finset (Fin (2 ^ k)))
    (hle : b.l ≤ c.l) (hdesc : c.x / 2 ^ (c.l - b.l) = b.x) :
    (S.filter (fun r ↦ ¬b.Native r perm)).card ≤
    c.strangers (c.l - b.l + 1) perm S := by
  simp only [Bag.strangers]
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter] at hr ⊢
  refine ⟨hr.1, ?_⟩
  show c.Strange (c.l - b.l + 1) r perm
  simp only [Bag.Strange, show c.l - b.l + 1 ≠ 0 by omega, false_or,
    show c.l - b.l + 1 - 1 = c.l - b.l by omega]
  show ¬(c.ancestor (c.l - b.l)).Native r perm
  -- c.ancestor(c.l - b.l) = b
  have hanc : c.ancestor (c.l - b.l) = b := by
    simp only [Bag.ancestor]
    exact Bag.ext (by show c.l - (c.l - b.l) = b.l; omega) hdesc
  rw [hanc]; exact hr.2

/-- Combined subtree bound: non-native items in subtree ≤ 2γεA/(1-(2εA)²)·cap.
    Specializes `subtree_non_native_le` at `cur = root` where root's regs are empty
    (wrong parity), so the local term vanishes and only the geometric sum remains. -/
theorem subtree_non_native_bound (p : Params) (k : ℕ) (hk : 10 ≤ k)
    (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (t : ℕ)
    (ih : ∀ (b : Bag k) (j : ℕ), 1 ≤ j →
      (b.strangers j perm ((stages p k t).value.regs b) : ℚ) ≤
      p.γ * p.ε ^ (j - 1) * capacity p k t b.l)
    (b : Bag k)
    (hparity : (t + b.l) % 2 ≠ 0) :
    (((subregs (stages p k t).value b).filter
        (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
    2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2) * capacity p k t b.l := by
  set pl := (stages p k t).value
  set cap_b := capacity p k t b.l
  -- Strategy: bound non-native items per descendant bag, sum over the tree.
  -- By filter_not_native_le_strangers + IH: at descendant c (distance d from b):
  --   |(pl.regs c).filter(¬b.Native)| ≤ γ · ε^d · cap(c.l) = γ · (εA)^d · cap_b
  -- Wrong-parity levels are empty (bagCard_odd_eq_zero).
  -- At odd distance d: 2^d descendants, each contributing ≤ γ·(εA)^d·cap_b.
  --   Total = γ · (2εA)^d · cap_b.
  -- Even distances (including d=0): empty regs → 0 contribution.
  -- Sum over odd d: γ · cap_b · Σ_{m} (2εA)^(2m+1) ≤ 2γεA/(1-(2εA)²) · cap_b.

  -- Helper: capacity factors
  have cap_factor : ∀ d, capacity p k t (b.l + d) = p.A ^ d * cap_b := by
    intro d; induction d with
    | zero => simp [cap_b]
    | succ n ih_n =>
      rw [show b.l + (n + 1) = (b.l + n) + 1 by omega, capacity_succ, ih_n]; ring

  -- Helper: per-descendant-bag bound
  have per_bag : ∀ (c : Bag k), b.l ≤ c.l → c.x / 2 ^ (c.l - b.l) = b.x →
      (((pl.regs c).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
      p.γ * (p.ε * p.A) ^ (c.l - b.l) * cap_b := by
    intro c hle hdesc
    calc (((pl.regs c).filter (fun r ↦ ¬b.Native r perm)).card : ℚ)
        ≤ ↑(c.strangers (c.l - b.l + 1) perm (pl.regs c)) := by
          exact_mod_cast filter_not_native_le_strangers b c perm (pl.regs c) hle hdesc
      _ ≤ p.γ * p.ε ^ (c.l - b.l) * capacity p k t c.l := by
          have h := ih c (c.l - b.l + 1) (by omega)
          rwa [show c.l - b.l + 1 - 1 = c.l - b.l by omega] at h
      _ = p.γ * (p.ε * p.A) ^ (c.l - b.l) * cap_b := by
          rw [show c.l = b.l + (c.l - b.l) by omega, cap_factor,
              show b.l + (c.l - b.l) - b.l = c.l - b.l by omega]
          rw [mul_pow]; ring

  -- Helper: wrong-parity bags have empty regs
  have parity_empty : ∀ l, (t + l) % 2 ≠ 0 → ∀ (c : Bag k), c.l = l →
      (pl.regs c).card = 0 := by
    intro l hpar c hcl
    rw [bagCard_eq_card p k t c, hcl, bagCard_odd_eq_zero p k (by omega) t l hpar]

  -- Abbreviations
  set eA := p.ε * p.A
  have heA_pos : (0 : ℚ) < eA := mul_pos p.hε_pos (by linarith [p.hA])
  have h4eA2 : 4 * eA ^ 2 < 1 := by
    show 4 * (p.ε * p.A) ^ 2 < 1
    calc 4 * (p.ε * p.A) ^ 2 = (2 * p.ε * p.A) ^ 2 := by ring
      _ < 1 := p.h2εA
  have h1m4 : (0 : ℚ) < 1 - 4 * eA ^ 2 := by linarith
  have hcap_nn : (0 : ℚ) ≤ cap_b := (capacity_pos p k t b.l).le
  -- Child descent lemmas
  have left_desc : ∀ (c : Bag k), b.l ≤ c.l → c.x / 2 ^ (c.l - b.l) = b.x →
      ∀ (hck : c.l < k), (c.left hck).x / 2 ^ ((c.left hck).l - b.l) = b.x := by
    intro c _ hdesc hck
    show 2 * c.x / 2 ^ (c.l + 1 - b.l) = b.x
    rw [show c.l + 1 - b.l = (c.l - b.l) + 1 from by omega, pow_succ,
        Nat.mul_comm (2 ^ (c.l - b.l)) 2, ← Nat.div_div_eq_div_mul,
        Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    exact hdesc
  have right_desc : ∀ (c : Bag k), b.l ≤ c.l → c.x / 2 ^ (c.l - b.l) = b.x →
      ∀ (hck : c.l < k), (c.right hck).x / 2 ^ ((c.right hck).l - b.l) = b.x := by
    intro c _ hdesc hck
    show (2 * c.x + 1) / 2 ^ (c.l + 1 - b.l) = b.x
    rw [show c.l + 1 - b.l = (c.l - b.l) + 1 from by omega, pow_succ,
        Nat.mul_comm (2 ^ (c.l - b.l)) 2, ← Nat.div_div_eq_div_mul]
    have : (2 * c.x + 1) / 2 = c.x := by omega
    rw [this]; exact hdesc
  -- Main claim: for wrong-parity descendant cur at distance d = cur.l - b.l,
  -- F(cur) ≤ 2γ·eA^(d+1)/(1-4eA²)·cap_b.
  -- Specializing at cur = b (d = 0) gives the target (after ring).
  suffices hmain : ∀ (n : ℕ) (cur : Bag k),
      k - cur.l = n →
      b.l ≤ cur.l → cur.x / 2 ^ (cur.l - b.l) = b.x →
      (t + cur.l) % 2 ≠ 0 →
      (((subregs pl cur).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
      2 * p.γ * eA ^ (cur.l - b.l + 1) / (1 - 4 * eA ^ 2) * cap_b by
    have h := hmain (k - b.l) b (by omega) le_rfl (by simp) hparity
    simp only [show b.l - b.l = 0 by omega] at h
    calc (((subregs pl b).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
          2 * p.γ * eA ^ (0 + 1) / (1 - 4 * eA ^ 2) * cap_b := h
      _ = 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2) * cap_b := by ring
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_n =>
  intro cur hn hle hdesc hpar
  -- Case 1: cur.l ≥ k (leaf) → subregs = regs, empty by parity
  by_cases hck : cur.l < k
  · -- Case 2: cur.l < k → decompose
    -- regs(cur) empty by wrong parity
    have hregs_empty : (pl.regs cur).card = 0 := parity_empty cur.l hpar cur rfl
    have hregs_filter : ((pl.regs cur).filter (fun r ↦ ¬b.Native r perm)).card = 0 := by
      rw [← Nat.le_zero, ← hregs_empty]; exact Finset.card_filter_le _ _
    -- Children
    let cl := cur.left hck
    let cr := cur.right hck
    let d := cur.l - b.l
    have hcl_l : cl.l = cur.l + 1 := rfl
    have hcr_l : cr.l = cur.l + 1 := rfl
    have hcl_le : b.l ≤ cl.l := by omega
    have hcr_le : b.l ≤ cr.l := by omega
    have hcl_desc := left_desc cur hle hdesc hck
    have hcr_desc := right_desc cur hle hdesc hck
    -- Children's regs bound by per_bag
    have hcl_pb := per_bag cl hcl_le hcl_desc
    have hcr_pb := per_bag cr hcr_le hcr_desc
    rw [show cl.l - b.l = d + 1 from by omega] at hcl_pb
    rw [show cr.l - b.l = d + 1 from by omega] at hcr_pb
    -- Bound each child's subregs by: per_bag(child) + child's subtree
    -- For each child ch (right parity): F(ch) ≤ per_bag(ch) + F(ch.left) + F(ch.right)
    -- Grandchildren are wrong parity → bounded by IH (if they exist)
    by_cases hck2 : cl.l < k
    · -- Case 2b: grandchildren exist
      have hcrk : cr.l < k := by rw [hcr_l, ← hcl_l]; exact hck2
      -- Grandchildren (wrong parity, level cur.l + 2)
      have hgc_par : (t + (cur.l + 2)) % 2 ≠ 0 := by omega
      have hgc_n : k - (cur.l + 2) < n := by omega
      -- IH bound for each grandchild
      have hgc_bound : ∀ (gc : Bag k), gc.l = cur.l + 2 →
          b.l ≤ gc.l → gc.x / 2 ^ (gc.l - b.l) = b.x →
          (((subregs pl gc).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
          2 * p.γ * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b := by
        intro gc hgcl hgcle hgcdesc
        have hgcpar : (t + gc.l) % 2 ≠ 0 := by rw [hgcl]; exact hgc_par
        have := ih_n _ hgc_n gc (by omega) hgcle hgcdesc hgcpar
        rwa [show gc.l - b.l = d + 2 from by omega] at this
      -- Grandchild level lemmas (omega can't see through Bag projections)
      have hcll_l : (cl.left hck2).l = cur.l + 2 := by show cl.l + 1 = cur.l + 2; omega
      have hclr_l : (cl.right hck2).l = cur.l + 2 := by show cl.l + 1 = cur.l + 2; omega
      have hcrl_l : (cr.left hcrk).l = cur.l + 2 := by show cr.l + 1 = cur.l + 2; omega
      have hcrr_l : (cr.right hcrk).l = cur.l + 2 := by show cr.l + 1 = cur.l + 2; omega
      have hgc_le : cur.l + 2 ≥ b.l := by omega
      have h_cll := hgc_bound (cl.left hck2) hcll_l (hcll_l ▸ hgc_le)
        (left_desc cl hcl_le hcl_desc hck2)
      have h_clr := hgc_bound (cl.right hck2) hclr_l (hclr_l ▸ hgc_le)
        (right_desc cl hcl_le hcl_desc hck2)
      have h_crl := hgc_bound (cr.left hcrk) hcrl_l (hcrl_l ▸ hgc_le)
        (left_desc cr hcr_le hcr_desc hcrk)
      have h_crr := hgc_bound (cr.right hcrk) hcrr_l (hcrr_l ▸ hgc_le)
        (right_desc cr hcr_le hcr_desc hcrk)
      -- Bound each child's subregs
      have h_cl : (((subregs pl cl).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
          p.γ * eA ^ (d + 1) * cap_b +
          2 * (2 * p.γ * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b) := by
        rw [subregs_filter_card_split' pl cl hck2]; push_cast; linarith [hcl_pb, h_cll, h_clr]
      have h_cr : (((subregs pl cr).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) ≤
          p.γ * eA ^ (d + 1) * cap_b +
          2 * (2 * p.γ * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b) := by
        rw [subregs_filter_card_split' pl cr hcrk]; push_cast; linarith [hcr_pb, h_crl, h_crr]
      -- Assemble and simplify
      -- LHS = 0 + F(cl) + F(cr) ≤ 2*(per_bag + 2*IH)
      -- = 2γeA^(d+1)cap + 4·2γeA^(d+3)/(1-4eA²)cap
      -- Key identity: 2x + 4eA²·(2x/(1-4eA²)) = 2x/(1-4eA²)
      rw [subregs_filter_card_split' pl cur hck]; push_cast
      calc (↑((pl.regs cur).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) +
            ↑((subregs pl cl).filter (fun r ↦ ¬b.Native r perm)).card +
            ↑((subregs pl cr).filter (fun r ↦ ¬b.Native r perm)).card
          ≤ 0 + (p.γ * eA ^ (d + 1) * cap_b +
              2 * (2 * p.γ * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b)) +
            (p.γ * eA ^ (d + 1) * cap_b +
              2 * (2 * p.γ * eA ^ (d + 2 + 1) / (1 - 4 * eA ^ 2) * cap_b)) := by
            have := hregs_filter; push_cast [this]; linarith [h_cl, h_cr]
        _ = 2 * p.γ * eA ^ (d + 1) * cap_b +
            4 * eA ^ 2 * (2 * p.γ * eA ^ (d + 1) / (1 - 4 * eA ^ 2) * cap_b) := by ring
        _ = 2 * p.γ * eA ^ (d + 1) / (1 - 4 * eA ^ 2) * cap_b := by
            field_simp [ne_of_gt h1m4]; ring
    · -- Case 2a: cur.l + 1 = k → children are leaves (subregs = regs)
      have hcl_leaf : ¬cl.l < k := hck2
      have hcr_leaf : ¬cr.l < k := by rw [hcr_l, ← hcl_l]; exact hck2
      -- subregs(child) = regs(child) since child.l ≥ k
      rw [subregs_filter_card_split' pl cur hck, subregs, dif_neg hcl_leaf, subregs, dif_neg hcr_leaf]
      push_cast
      calc (↑((pl.regs cur).filter (fun r ↦ ¬b.Native r perm)).card : ℚ) +
            ↑((pl.regs cl).filter (fun r ↦ ¬b.Native r perm)).card +
            ↑((pl.regs cr).filter (fun r ↦ ¬b.Native r perm)).card
          ≤ 0 + p.γ * eA ^ (d + 1) * cap_b + p.γ * eA ^ (d + 1) * cap_b := by
            have := hregs_filter; push_cast [this]; linarith [hcl_pb, hcr_pb]
        _ = 2 * p.γ * eA ^ (d + 1) * cap_b := by ring
        _ ≤ 2 * p.γ * eA ^ (d + 1) / (1 - 4 * eA ^ 2) * cap_b := by
            rw [show 2 * p.γ * eA ^ (d + 1) / (1 - 4 * eA ^ 2) * cap_b =
              2 * p.γ * eA ^ (d + 1) * cap_b / (1 - 4 * eA ^ 2) from by ring,
              le_div_iff₀ h1m4]
            have hnn : (0 : ℚ) ≤ 2 * p.γ * eA ^ (d + 1) * cap_b :=
              mul_nonneg (mul_nonneg (by linarith [p.hγ_pos]) (pow_nonneg heA_pos.le _)) hcap_nn
            exact mul_le_of_le_one_right hnn (by nlinarith [sq_nonneg eA])
  · -- Case 1: cur.l ≥ k → subregs = regs, empty by parity
    have hcur_leaf : ¬cur.l < k := hck
    rw [subregs, dif_neg hcur_leaf]
    have hregs_empty : (pl.regs cur).card = 0 := parity_empty cur.l hpar cur rfl
    have hfilt0 : ((pl.regs cur).filter (fun r ↦ ¬b.Native r perm)).card = 0 := by
      rw [← Nat.le_zero, ← hregs_empty]; exact Finset.card_filter_le _ _
    simp only [hfilt0, Nat.cast_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg (by linarith [p.hγ_pos]) (pow_nonneg heA_pos.le _))
      h1m4.le) hcap_nn

end


