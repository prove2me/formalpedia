-- Prove2me | Definitions.Def_GirvingAKS_Bags_Source3
-- name    : GirvingAKS_Bags_Source3
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T19:20:59.390035+00:00
-- url     : https://prove2.me/theorems/931021fc-c3a8-48f3-a171-e743ddfa6f53
-- title:
--   AKS sorting networks (Seiferas port) — Parent Stranger Bound for j=1
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bags/Source3.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Proves `parent_stranger_eq1_le`: the j=1 parent stranger bound with paper-exact coefficient from Seiferas (2009), Section 5.  This is the most complex stranger bound lemma because 1-strangers are "almost native" — their value lies in the parent's interval but not the child's own interval.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bags/Source3.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bags_Subtree

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bags/Source3.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Parent Stranger Bound for j=1

  Proves `parent_stranger_eq1_le`: the j=1 parent stranger bound with paper-exact
  coefficient from Seiferas (2009), Section 5.  This is the most complex stranger
  bound lemma because 1-strangers are "almost native" — their value lies in the
  parent's interval but not the child's own interval.
-/


section

open Finset

variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- Items received from parent: 1-stranger bound with paper-exact coefficient.

    **Status:** proved below (the statement was first checked empirically).

    Simulation (rust/test-stranger-bound.rs) shows 0 violations with max ratio ~0.96.
    The bound is tight but valid.

    The proof requires:
    1. Separator ε-filtering: bounds on strangers passing through separator
    2. Sibling-native equidistribution: the `1/(8A³-2A)` term from Seiferas (2009)

    This is the most complex of the stranger bound lemmas because j=1 strangers
    are "almost native" — their value is in the parent's interval but not the
    child's own interval. The equidistribution term accounts for how such items
    are distributed between sibling bags.

    See Seiferas (2009), Section 5 for the derivation of the coefficient. -/
theorem parent_stranger_eq1_le (p : Params) (k : ℕ) (hk : 10 ≤ k)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k))
    (hperm : Function.Bijective perm₀)
    (t : ℕ)
    (ht : t ≤ numStages p k)
    (ih : ∀ (b : Bag k) (j : ℕ), 1 ≤ j →
      (b.strangers j ((stages p k t).net.exec perm₀)
        ((stages p k t).value.regs b) : ℚ) ≤
      p.γ * p.ε ^ (j - 1) * capacity p k t b.l)
    (b : Bag k) (hl : 1 ≤ b.l)
    (S : Finset (Fin (2 ^ k)))
    (hS_child : let regs := (stages p k t).value.regs b.parent
                let f := fringe p k t b.parent.l regs.card
                S ⊆ if b.x % 2 = 0 then (split regs f).toLeft
                    else (split regs f).toRight) :
    (b.strangers 1 ((stages p k (t + 1)).net.exec perm₀) S : ℚ) ≤
    (p.ε * p.γ / p.A + p.ε / (2 * p.A)
     + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
     + 1 / (8 * p.A ^ 3 - 2 * p.A)
     + p.γ / p.A
     + 1 / (8 * p.A ^ 3 - 2 * p.A)) * capacity p k t b.l := by
  /-
  Proof structure following Seiferas (2009) Section 5:

  1-strangers in B after stage t+1, among items S received from parent D, come from:
    - Source 2: Items that were 1-strangers in D (filtered by ε)
    - Source 3: Items native to D but sent to wrong child (sibling C's items sent to B)
      - 3a: Halving errors (separator misroutes items between halves)
      - 3b: Excess sibling-native items (C-native items in D > d/2)

  The coefficient breakdown:
    εγ/A        — Source 2: ε × (parent's 1-strangers) = ε × γ(b/A)
    ε/(2A)      — Source 3a: halving errors ≤ ε × d/2 = ε × b/(2A)
    2γεA/(1-(2εA)²) — Source 3b-ii: strangers in C's subtree push out C-native items
    1/(8A³-2A)  — Source 3b-i: C-native items from above D
  -/

  -- Abbreviations
  set perm_t := (stages p k t).net.exec perm₀ with hperm_t_def
  set perm_t1 := (stages p k (t + 1)).net.exec perm₀ with hperm_t1_def
  set parent := b.parent with hparent_def
  set sibling := b.sibling hl with hsibling_def
  set parent_regs := (stages p k t).value.regs parent with hparent_regs_def
  set cap := capacity p k t b.l with hcap_def

  -- Parent's level
  have hparent_l : parent.l = b.l - 1 := rfl

  -- Derive S ⊆ toLeft ∪ toRight from the child-side hypothesis
  have hS_mid : S ⊆ (split parent_regs (fringe p k t parent.l parent_regs.card)).toLeft ∪
      (split parent_regs (fringe p k t parent.l parent_regs.card)).toRight := by
    by_cases he : b.x % 2 = 0
    · exact (show S ⊆ _ from by simp only [if_pos he] at hS_child; exact hS_child).trans
        Finset.subset_union_left
    · exact (show S ⊆ _ from by simp only [if_neg he] at hS_child; exact hS_child).trans
        Finset.subset_union_right

  -- Positivity facts
  have hA_pos : (0 : ℚ) < p.A := by linarith [p.hA]
  have hA_ne : p.A ≠ 0 := ne_of_gt hA_pos
  have hcap_nn : (0 : ℚ) ≤ cap := capacity_nonneg p k t b.l
  have hε_pos : (0 : ℚ) < p.ε := p.hε_pos
  have hγ_pos : (0 : ℚ) < p.γ := p.hγ_pos

  -- Capacity at parent level = cap / A
  have hcap_parent : capacity p k t parent.l = cap / p.A := by
    simp only [capacity, hcap_def, hparent_l]
    rw [pow_sub₀ _ hA_ne hl, pow_one, inv_eq_one_div]; ring

  -- Decomposition of 1-strangers using Bag.one_strange_decomp:
  -- 1-stranger in b ↔ parent is 1-stranger ∨ (parent-native ∧ sibling-native)
  --
  -- Count 1-strangers in S:
  -- strangers(b, 1, S) = |{r ∈ S : b.Strange 1 r perm_t1}|
  --                    ≤ |{r ∈ S : parent.Strange 1 r perm_t1}|
  --                    + |{r ∈ S : parent.Native r perm_t1 ∧ sibling.Native r perm_t1}|
  --
  -- Source 2: parent.strangers 1 perm_t1 S  (items that were 1-strangers in parent)
  -- Source 3: sibling-native among parent-native items in S

  -- Define the decomposition sets
  set source2 := S.filter (fun r ↦ parent.Strange 1 r perm_t1) with hsource2_def
  set source3 := S.filter (fun r ↦ parent.Native r perm_t1 ∧ sibling.Native r perm_t1)
    with hsource3_def

  -- 1-strangers ≤ source2 + source3 (by Bag.one_strange_decomp)
  have hdecomp : b.strangers 1 perm_t1 S ≤ source2.card + source3.card := by
    simp only [Bag.strangers]
    have hunion : (S.filter (fun r ↦ b.Strange 1 r perm_t1)) ⊆ source2 ∪ source3 := by
      intro r hr
      simp only [mem_filter] at hr ⊢
      simp only [mem_union]
      obtain ⟨hrS, hstrange⟩ := hr
      rw [Bag.one_strange_decomp b hl r perm_t1] at hstrange
      rcases hstrange with hparent_strange | ⟨hparent_native, hsibling_native⟩
      · left; exact mem_filter.mpr ⟨hrS, hparent_strange⟩
      · right; exact mem_filter.mpr ⟨hrS, hparent_native, hsibling_native⟩
    calc (S.filter (fun r ↦ b.Strange 1 r perm_t1)).card
        ≤ (source2 ∪ source3).card := Finset.card_le_card hunion
      _ ≤ source2.card + source3.card := Finset.card_union_le _ _

  -- Now bound each source

  -- Source 2: Parent 1-strangers filtered through separator
  -- This is similar to j≥2 case: at most ε × parent.strangers 1 perm_t parent_regs
  have hsource2_bound : (source2.card : ℚ) ≤ p.ε * p.γ / p.A * cap := by
    -- source2 = items in S that are 1-strange in parent
    -- By separator_filter_strangers: strangers in S ≤ ε × strangers in parent_regs
    -- By IH: parent.strangers 1 perm_t parent_regs ≤ γ × capacity(parent) = γ × cap/A

    -- First, note that source2.card = parent.strangers 1 perm_t1 S
    have heq_source2 : source2.card = parent.strangers 1 perm_t1 S := by
      simp only [source2, Bag.strangers]

    -- IH on parent for j=1
    have hih : (parent.strangers 1 perm_t parent_regs : ℚ) ≤ p.γ * p.ε ^ 0 * capacity p k t parent.l := by
      exact ih parent 1 (by omega)
    simp only [pow_zero, mul_one] at hih
    have hih' : (parent.strangers 1 perm_t parent_regs : ℚ) ≤ p.γ * (cap / p.A) := by
      have hih := ih parent 1 (by omega)
      simp only [Nat.sub_self, pow_zero, mul_one, hcap_parent] at hih; exact hih

    -- Apply separator_filter_strangers for parent, j=1
    -- **Now resolved with capacity-based boundary:**
    -- IH gives: strangers 1 ≤ γ * ε^0 * capacity = γ * capacity
    -- Need: strangers 1 ≤ ⌊γ * capacity⌋₊
    -- This follows directly from Nat.le_floor!
    have hT_le : parent.strangers 1 perm_t parent_regs ≤ ⌊p.γ * capacity p k t parent.l⌋₊ := by
      have hih_1 : (parent.strangers 1 perm_t parent_regs : ℚ) ≤
          p.γ * p.ε ^ (1 - 1) * capacity p k t parent.l := ih parent 1 (by omega)
      simp only [Nat.sub_self, pow_zero, mul_one] at hih_1
      exact Nat.le_floor hih_1

    have hsep_filter : (parent.strangers 1 perm_t1 S : ℚ) ≤
        p.ε * ↑(parent.strangers 1 perm_t parent_regs) :=
      separator_filter_strangers p k perm₀ hperm t parent 1 (by omega) S hS_mid hT_le

    -- Chain the bounds
    calc (source2.card : ℚ)
        = (parent.strangers 1 perm_t1 S : ℚ) := by exact_mod_cast heq_source2
      _ ≤ p.ε * ↑(parent.strangers 1 perm_t parent_regs) := hsep_filter
      _ ≤ p.ε * (p.γ * (cap / p.A)) := mul_le_mul_of_nonneg_left hih' hε_pos.le
      _ = p.ε * p.γ / p.A * cap := by field_simp

  -- Source 3: Parent-native but sibling-native items
  -- This decomposes into:
  -- - 3a: Halving errors (separator routing errors)
  -- - 3b: Excess C-native items that got pushed to D
  have hsource3_bound : (source3.card : ℚ) ≤
      (p.ε / (2 * p.A) + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
       + 1 / (8 * p.A ^ 3 - 2 * p.A)
       + p.γ / p.A
       + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap := by
    -- Factored proof (Seiferas 2009, Section 5):
    -- source3 ≤ ε·(d/2) + max(0, d/2 - b_native)  [halver + rank counting]
    -- where d/2 ≤ cap/(2A)  [capacity bound, proved]
    -- and max(0, d/2 - b_native) ≤ (benchmark) × cap  [benchmark comparison]
    -- KEY: d/2 - b = (c - d/2) + s captures C-excess + stranger displacement.
    -- The naive `source3 ≤ ε·m + max(0, c - d/2)` is FALSE (strangers shift ranks).
    set half_D := parent_regs.card / 2 with hhalf_D_def
    -- n_local = 2 * half_D: the number of items in the separator's domain
    -- (equals parent_regs.card when even, parent_regs.card - 1 when odd)
    set n_local := 2 * half_D with hn_local_def
    -- Sorted embedding of D's registers
    set embed : Fin parent_regs.card ↪o Fin (2 ^ k) :=
      parent_regs.orderEmbOfFin rfl with hembed_def
    -- B-native count among the n_local items in the separator's domain
    -- (NOT over all parent_regs, to avoid off-by-one when parent_regs.card is odd)
    set b_native := (Finset.univ.filter (fun i : Fin n_local ↦
        b.Native (embed ⟨i.val, by omega⟩) perm_t)).card
      with hb_native_def
    -- Step 1 (proved): d/2 ≤ cap/(2A)
    have h_half_le : (half_D : ℚ) ≤ cap / (2 * p.A) := by
      have hd_le : (parent_regs.card : ℚ) ≤ cap / p.A := by
        calc (↑parent_regs.card : ℚ)
            = ↑(bagCard p k t parent.l) := by exact_mod_cast bagCard_eq_card p k t parent
          _ ≤ capacity p k t parent.l :=
              bagCard_le_capacity p k hk t (numStages_hfl p k hk t ht) parent.l
          _ = cap / p.A := hcap_parent
      rw [le_div_iff₀ (by positivity : (0 : ℚ) < 2 * p.A)]
      rw [le_div_iff₀ hA_pos] at hd_le
      have : (↑half_D : ℚ) * 2 ≤ ↑parent_regs.card := by
        exact_mod_cast Nat.div_mul_le_self parent_regs.card 2
      nlinarith
    -- Step 2: Halver + rank decomposition
    -- Items crossing midpoint ≤ ε·m (halver); C-native with rank < m ≤ max(0, d/2 - b).
    --
    -- PROOF STRATEGY (Seiferas 2009, Section 5):
    -- The separator is an ε-halver (SeparatorFamily.isHalver), so by
    -- halver_isSeparator_half it's a (1/2, ε)-separator.
    --
    -- For S ⊆ toLeft (B is left child, lower interval):
    --   S has positions in [f, half_D) — the bottom half.
    --   C-native values are in the UPPER part of D's interval.
    --   Among D's n_local items sorted by value:
    --     ranks [0, s_below): strangers below D
    --     ranks [s_below, s_below + b_native): B-native
    --     ranks [s_below + b_native, s_below + b_native + c_native): C-native
    --     ranks [n_local - s_above, n_local): strangers above D
    --   C-native items with value rank < half_D ≤ max(0, half_D - b_native) [counting]
    --   C-native items with value rank ≥ half_D at position < half_D ≤ ε * half_D [halver]
    --   Total: source3 ≤ ε * half_D + max(0, half_D - b_native)
    --
    -- Symmetric argument for S ⊆ toRight (B is right child, upper interval),
    -- using the final direction of the halver.
    --
    -- Infrastructure needed:
    -- 1. Local coordinate system (embed', u', sep_local) as in separator_filter_strangers
    -- 2. halver_isSeparator_half: IsEpsilonHalver → IsSeparator (1/2) ε
    -- 3. separator_injective_initial/final with γ = 1/2 for crossing bound
    -- 4. Value rank ordering: strangers_below < B-native < C-native < strangers_above
    --    (when B is left child; reversed when B is right child)
    have h_decomp : (source3.card : ℚ) ≤
        p.ε * ↑half_D + max (0 : ℚ) (↑half_D - ↑b_native) := by
      -- Trivial if source3 empty
      by_cases hsrc0 : source3.card = 0
      · simp [hsrc0]; positivity
      -- Local coordinate setup (mirrors separator_filter_strangers)
      -- Use parent_regs.card directly to avoid set abbreviation opacity
      set f_val := fringe p k t parent.l parent_regs.card
      set embed' : Fin n_local ↪o Fin (2 ^ k) :=
        (Fin.castLEOrderEmb (show n_local ≤ parent_regs.card by omega)).trans embed
        with hembed'_def
      set u' : Fin n_local → Fin (2 ^ k) := perm_t ∘ embed' with hu'_def
      have hu'_inj : Function.Injective u' := fun i₁ i₂ heq ↦
        embed'.injective (ComparatorNetwork.exec_injective _ hperm.1 heq)
      have hembed'_mem : ∀ i : Fin n_local, embed' i ∈ parent_regs :=
        fun i ↦ orderEmbOfFin_mem _ rfl _
      let γₑ := effectiveGamma p.γ (capacity p k t parent.l) n_local
      have hγₑ_pos := effectiveGamma_pos p.hγ_pos (capacity_pos p k t parent.l) n_local
      set sep_local := separatorNet γₑ p.ε hγₑ_pos p.hε_pos (parent_regs.card / 2)
        with hsep_local_def
      -- (1/2, ε)-separator via halver → separator bridge
      have hsep_half : IsSeparator sep_local (1/2 : ℝ) ↑p.ε :=
        halver_isSeparator_half _ _ (by exact_mod_cast p.hε_pos.le)
          (separatorNet_isHalver γₑ p.ε hγₑ_pos p.hε_pos (parent_regs.card / 2))
      -- perm_t1 = sep_local.exec u' on local coordinates
      have hexec_stage : perm_t1 = (stage p (stages p k t).value t).net.exec perm_t := by
        show (do let pl' ← stages p k t; stage p pl' t).net.exec perm₀ = _
        rw [Build.exec_bind]
      have hperm_eq : ∀ (pos : Fin n_local),
          perm_t1 (embed' pos) = sep_local.exec u' pos := by
        intro pos
        have := stage_exec_on_regs p k (stages p k t).value t parent perm_t
          (embed' pos) (hembed'_mem pos)
        rw [hexec_stage, this]
        exact ComparatorNetwork.scatterEmbed_exec_inside sep_local (2 ^ k) embed' perm_t pos
      -- Boundary: ⌊(1/2) * n_local⌋₊ = half_D
      have hbdry : ⌊(1/2 : ℝ) * ↑n_local⌋₊ = half_D := by
        have : (1/2 : ℝ) * ↑n_local = ↑half_D := by
          simp only [hn_local_def]; push_cast; ring
        rw [this, Nat.floor_natCast]
      -- S ⊆ parent_regs
      have hS_regs : S ⊆ parent_regs :=
        hS_mid.trans (union_subset (split_toLeft_subset _ _) (split_toRight_subset _ _))
      -- S nonempty
      have hS_ne : S.Nonempty := by
        by_contra h; rw [not_nonempty_iff_eq_empty] at h; simp [source3, h] at hsrc0
      -- f < C/2 (toLeft ∪ toRight nonempty)
      have hf_lt : f_val < parent_regs.card / 2 := by
        by_contra hge; push_neg at hge
        have ⟨hl', hr'⟩ := split_leaf parent_regs f_val hge
        exact hS_ne.ne_empty (eq_empty_iff_forall_notMem.mpr fun r hr_S ↦ by
          have := hS_mid hr_S; rw [hl', hr', union_empty] at this; exact notMem_empty _ this)
      -- embed' pos and b_native connection
      have hn_le_C : n_local ≤ parent_regs.card := by omega
      have hembed'_val : ∀ (pos : Fin n_local),
          embed' pos = embed ⟨pos.val, Nat.lt_of_lt_of_le pos.isLt hn_le_C⟩ :=
        fun pos ↦ congrArg embed (Fin.ext rfl)
      -- Count preservation: exec doesn't change filter cardinalities
      have hcount : ∀ (P : Fin (2 ^ k) → Prop) [DecidablePred P],
          (univ.filter (fun pos : Fin n_local ↦ P (sep_local.exec u' pos))).card =
          (univ.filter (fun i : Fin n_local ↦ P (u' i))).card := by
        intro P _
        have hexec_inj := ComparatorNetwork.exec_injective sep_local hu'_inj
        have himages : univ.image (sep_local.exec u') = univ.image u' := by
          ext v; simp only [mem_image, mem_univ, true_and]
          constructor
          · rintro ⟨p, rfl⟩
            have : sep_local.exec u' p ∈ Set.range u' :=
              sep_local.exec_range_eq u' ▸ Set.mem_range_self p
            exact this
          · rintro ⟨i, rfl⟩
            have : u' i ∈ Set.range (sep_local.exec u') :=
              (sep_local.exec_range_eq u').symm ▸ Set.mem_range_self i
            exact this
        have aux : ∀ (g : Fin n_local → Fin (2 ^ k)), Function.Injective g →
          (univ.filter (fun i ↦ P (g i))).card = ((univ.image g).filter P).card := by
          intro g hg; rw [← card_image_of_injective _ hg]; congr 1; ext v
          simp only [mem_image, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨i, hP, rfl⟩; exact ⟨⟨i, rfl⟩, hP⟩
          · rintro ⟨⟨i, rfl⟩, hP⟩; exact ⟨i, hP, rfl⟩
        rw [aux _ hexec_inj, aux _ hu'_inj, himages]
      -- Resolved separator bounds (boundary = half_D)
      have hsep_final_bound : ∀ (thr : ℕ),
          (univ.filter (fun i : Fin n_local ↦ thr ≤ (u' i).val)).card ≤ half_D →
          ((univ.filter (fun pos : Fin n_local ↦
            pos.val < half_D ∧ thr ≤ (sep_local.exec u' pos).val)).card : ℝ) ≤
          (↑p.ε : ℝ) * ↑(univ.filter (fun i : Fin n_local ↦ thr ≤ (u' i).val)).card := by
        intro thr ha
        have h := separator_injective_final hsep_half
          (by norm_num) u' hu'_inj thr (by rwa [hbdry])
        have hb : n_local - ⌊(1/2 : ℝ) * ↑n_local⌋₊ = half_D := by rw [hbdry]; omega
        rwa [hb] at h
      have hsep_init_bound : ∀ (thr : ℕ),
          (univ.filter (fun i : Fin n_local ↦ (u' i).val < thr)).card ≤ half_D →
          ((univ.filter (fun pos : Fin n_local ↦
            half_D ≤ pos.val ∧ (sep_local.exec u' pos).val < thr)).card : ℝ) ≤
          (↑p.ε : ℝ) * ↑(univ.filter (fun i : Fin n_local ↦ (u' i).val < thr)).card := by
        intro thr ha
        have h := separator_injective_initial hsep_half
          (by norm_num) u' hu'_inj thr (by rwa [hbdry])
        rwa [hbdry] at h
      -- Case split on child direction
      by_cases he : b.x % 2 = 0
      · -- LEFT CHILD: S ⊆ toLeft, sibling values are HIGH
        have hS_left : S ⊆ (split parent_regs f_val).toLeft := by
          simp only [if_pos he] at hS_child; exact hS_child
        -- b.hi = sibling.lo (left child's sibling starts where b ends)
        have hsib_lo : sibling.lo = b.hi := by
          show (b.sibling hl).lo = b.hi
          simp only [Bag.lo, Bag.hi, Bag.size, Bag.sibling, if_pos he, Bag.right, Bag.parent]
          have h1 : b.l - 1 + 1 = b.l := by omega
          have h2 : 2 * (b.x / 2) = b.x := by omega
          rw [h1]; congr 1; omega
        -- Inject source3 into {pos < half_D : exec val ≥ sibling.lo}
        have hsrc3_le : source3.card ≤
            (univ.filter (fun pos : Fin n_local ↦
              pos.val < half_D ∧ sibling.lo ≤ (sep_local.exec u' pos).val)).card := by
          suffices h : source3 ⊆ image embed' (univ.filter (fun pos : Fin n_local ↦
              pos.val < half_D ∧ sibling.lo ≤ (sep_local.exec u' pos).val)) by
            calc source3.card ≤ _ := card_le_card h
              _ = _ := card_image_of_injective _ embed'.injective
          intro r hr
          have ⟨hr_S, _, hr_sib⟩ := mem_filter.mp hr
          obtain ⟨j, hj_mem, hj_eq⟩ := mem_image.mp (hS_left hr_S)
          have ⟨hj_lo, hj_hi⟩ := mem_filter.mp hj_mem
          have hj_lt : j.val < n_local := by
            have := hj_hi.2; omega
          set pos : Fin n_local := ⟨j.val, hj_lt⟩
          have hpos_eq : embed' pos = r := by
            rw [hembed'_val]; exact hj_eq
          have hpos_lt : pos.val < half_D := by
            show j.val < half_D; have := hj_hi.2; omega
          exact mem_image.mpr ⟨pos, mem_filter.mpr ⟨mem_univ _, hpos_lt, by
            rw [← hperm_eq pos, hpos_eq]; exact ((Bag.native_iff _ _ _).mp hr_sib).1⟩, hpos_eq⟩
        -- a_above = items with value ≥ sibling.lo
        set a_above := (univ.filter (fun i : Fin n_local ↦ sibling.lo ≤ (u' i).val)).card
        -- b_native + a_above ≤ n_local (disjoint: B-native values < b.hi = sibling.lo)
        have hbn_disj : b_native + a_above ≤ n_local := by
          have hd : Disjoint
            (univ.filter (fun i : Fin n_local ↦ b.Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le_C⟩) perm_t))
            (univ.filter (fun i : Fin n_local ↦ sibling.lo ≤ (u' i).val)) := by
            rw [disjoint_filter]; intro i _ hnat hhi
            have h1 := ((Bag.native_iff _ _ _).mp hnat).2  -- val < b.hi
            have h2 : (perm_t (embed' i)).val = (perm_t (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le_C⟩)).val := by
              rw [hembed'_val]
            have h3 : (u' i).val = (perm_t (embed' i)).val := rfl
            rw [hsib_lo] at hhi; omega
          calc b_native + a_above
              = (univ.filter _ ∪ univ.filter _).card := (card_union_of_disjoint hd).symm
            _ ≤ univ.card := card_le_card (subset_univ _)
            _ = n_local := by rw [Finset.card_univ, Fintype.card_fin]
        -- a_below = n_local - a_above (complement count)
        set a_below := n_local - a_above with ha_below_def
        -- a_below + a_above = n_local
        have ha_sum : a_below + a_above = n_local := by
          have : a_above ≤ n_local := by linarith
          omega
        -- a_below = count of items with value < sibling.lo
        have ha_below_eq : a_below =
            (univ.filter (fun i : Fin n_local ↦ (u' i).val < sibling.lo)).card := by
          have hsum : a_above + (univ.filter (fun i : Fin n_local ↦ (u' i).val < sibling.lo)).card
              = n_local := by
            have := card_filter_add_card_filter_not (s := univ) (fun i : Fin n_local ↦
              sibling.lo ≤ (u' i).val)
            simp only [not_le] at this
            rwa [Finset.card_univ, Fintype.card_fin] at this
          omega
        -- b_native ≤ a_below
        have hbn_le : b_native ≤ a_below := by omega
        -- Work in ℚ directly (avoid ℝ intermediate)
        by_cases ha_le : a_above ≤ half_D
        · -- Easy case: separator_injective_final directly
          have hsep := hsep_final_bound sibling.lo ha_le
          -- Work in ℝ, then cast back to ℚ
          suffices hR : (source3.card : ℝ) ≤
              (↑p.ε : ℝ) * ↑half_D + max 0 (↑half_D - (↑b_native : ℝ)) by exact_mod_cast hR
          calc (source3.card : ℝ)
              ≤ ↑(univ.filter (fun pos : Fin n_local ↦
                  pos.val < half_D ∧ sibling.lo ≤ (sep_local.exec u' pos).val)).card := by
                exact_mod_cast hsrc3_le
            _ ≤ (↑p.ε : ℝ) * ↑a_above := hsep
            _ ≤ (↑p.ε : ℝ) * ↑half_D := by
                exact mul_le_mul_of_nonneg_left (by exact_mod_cast ha_le)
                  (by exact_mod_cast p.hε_pos.le)
            _ ≤ _ := le_add_of_nonneg_right (le_max_left 0 _)
        · -- Hard case: complement argument
          push_neg at ha_le
          have ha_below_lt : a_below < half_D := by omega
          have ha_below_le : (univ.filter (fun i : Fin n_local ↦ (u' i).val < sibling.lo)).card ≤ half_D := by
            omega
          -- Separator bound on complement direction
          have hsep_compl := hsep_init_bound sibling.lo ha_below_le
          -- Work in ℝ
          suffices hR : (source3.card : ℝ) ≤
              (↑p.ε : ℝ) * ↑half_D + max 0 (↑half_D - (↑b_native : ℝ)) by exact_mod_cast hR
          -- Count preservation for positions < half_D
          -- |{pos < hD : exec val < thr}| + |{pos < hD : exec val ≥ thr}| = half_D
          have hcard_lo : (univ.filter (fun pos : Fin n_local ↦
              pos.val < half_D)).card = half_D :=
            fin_double_card_lt half_D
          have hpart_lo : (univ.filter (fun pos : Fin n_local ↦
                pos.val < half_D ∧ (sep_local.exec u' pos).val < sibling.lo)).card +
              (univ.filter (fun pos : Fin n_local ↦
                pos.val < half_D ∧ sibling.lo ≤ (sep_local.exec u' pos).val)).card =
              half_D := by
            have hsplit := card_filter_add_card_filter_not
              (s := univ.filter (fun pos : Fin n_local ↦ pos.val < half_D))
              (fun pos ↦ sibling.lo ≤ (sep_local.exec u' pos).val)
            simp only [Finset.filter_filter, not_le] at hsplit
            rw [hcard_lo] at hsplit; linarith
          -- Count preservation: filter by value predicate preserved by exec
          have hcount_lo : (univ.filter (fun pos : Fin n_local ↦
                pos.val < half_D ∧ (sep_local.exec u' pos).val < sibling.lo)).card +
              (univ.filter (fun pos : Fin n_local ↦
                half_D ≤ pos.val ∧ (sep_local.exec u' pos).val < sibling.lo)).card =
              a_below := by
            rw [ha_below_eq, ← hcount (fun v ↦ v.val < sibling.lo)]
            have hsplit' := card_filter_add_card_filter_not
              (s := univ.filter (fun pos : Fin n_local ↦ (sep_local.exec u' pos).val < sibling.lo))
              (fun pos ↦ pos.val < half_D)
            simp only [Finset.filter_filter, not_lt] at hsplit'
            -- hsplit' has (exec < sib ∧ pos < hD) + (exec < sib ∧ hD ≤ pos) = filter(exec < sib)
            -- Need to swap conjuncts to match goal
            have h_eq1 : (univ.filter (fun pos : Fin n_local ↦
                (sep_local.exec u' pos).val < sibling.lo ∧ pos.val < half_D)) =
              (univ.filter (fun pos : Fin n_local ↦
                pos.val < half_D ∧ (sep_local.exec u' pos).val < sibling.lo)) := by
              ext pos; simp only [mem_filter, mem_univ, true_and]; tauto
            have h_eq2 : (univ.filter (fun pos : Fin n_local ↦
                (sep_local.exec u' pos).val < sibling.lo ∧ half_D ≤ pos.val)) =
              (univ.filter (fun pos : Fin n_local ↦
                half_D ≤ pos.val ∧ (sep_local.exec u' pos).val < sibling.lo)) := by
              ext pos; simp only [mem_filter, mem_univ, true_and]; tauto
            rw [h_eq1, h_eq2] at hsplit'; linarith
          -- Combine: source3 ≤ half_D - (1-ε) * a_below ≤ ε * half_D + (half_D - b_native)
          have key : (source3.card : ℝ) ≤ ↑half_D - (1 - ↑p.ε) * ↑a_below :=
            complement_counting_bound (ε := ↑p.ε) (hsrc := hsrc3_le)
              (hpart := by linarith [hpart_lo]) (hcount := hcount_lo) (hsep := by
              have h1 := hsep_compl; rw [← ha_below_eq] at h1; exact_mod_cast h1)
          exact source3_hard_case_tail ↑p.ε (by exact_mod_cast p.hε_pos.le)
            (by exact_mod_cast p.hε_lt) _ _ _ _ key hbn_le (hbn_le.trans ha_below_lt.le)
      · -- RIGHT CHILD: S ⊆ toRight, sibling values are LOW
        have hS_right : S ⊆ (split parent_regs f_val).toRight := by
          simp only [if_neg he] at hS_child; exact hS_child
        have hsib_hi : sibling.hi = b.lo := by
          show (b.sibling hl).hi = b.lo
          simp only [Bag.sibling, if_neg he, Bag.parent, Bag.left, Bag.lo, Bag.hi, Bag.size]
          have h1 : b.l - 1 + 1 = b.l := by omega
          rw [h1]; congr 1; omega
        have hsrc3_le : source3.card ≤
            (univ.filter (fun pos : Fin n_local ↦
              half_D ≤ pos.val ∧ (sep_local.exec u' pos).val < sibling.hi)).card := by
          suffices h : source3 ⊆ image embed' (univ.filter (fun pos : Fin n_local ↦
              half_D ≤ pos.val ∧ (sep_local.exec u' pos).val < sibling.hi)) by
            calc source3.card ≤ _ := card_le_card h
              _ = _ := card_image_of_injective _ embed'.injective
          intro r hr
          have ⟨hr_S, _, hr_sib⟩ := mem_filter.mp hr
          obtain ⟨j, hj_mem, hj_eq⟩ := mem_image.mp (hS_right hr_S)
          have ⟨_, hj⟩ := mem_filter.mp hj_mem
          have hj_lt : j.val < n_local := by have := hj.2; omega
          set pos : Fin n_local := ⟨j.val, hj_lt⟩
          have hpos_eq : embed' pos = r := by rw [hembed'_val]; exact hj_eq
          have hpos_ge : half_D ≤ pos.val := by show half_D ≤ j.val; have := hj.1; omega
          exact mem_image.mpr ⟨pos, mem_filter.mpr ⟨mem_univ _, hpos_ge, by
            rw [← hperm_eq pos, hpos_eq]; exact ((Bag.native_iff _ _ _).mp hr_sib).2⟩, hpos_eq⟩
        set a_below := (univ.filter (fun i : Fin n_local ↦ (u' i).val < sibling.hi)).card
        have hbn_disj : b_native + a_below ≤ n_local := by
          have hd : Disjoint
            (univ.filter (fun i : Fin n_local ↦ b.Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le_C⟩) perm_t))
            (univ.filter (fun i : Fin n_local ↦ (u' i).val < sibling.hi)) := by
            rw [disjoint_filter]; intro i _ hnat hhi
            have h1 := ((Bag.native_iff _ _ _).mp hnat).1
            have h3 : (u' i).val = (perm_t (embed' i)).val := rfl
            have h2 : (perm_t (embed' i)).val = (perm_t (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le_C⟩)).val := by
              rw [hembed'_val]
            rw [hsib_hi] at hhi; omega
          calc b_native + a_below
              = (univ.filter _ ∪ univ.filter _).card := (card_union_of_disjoint hd).symm
            _ ≤ univ.card := card_le_card (subset_univ _)
            _ = n_local := by rw [Finset.card_univ, Fintype.card_fin]
        set a_above := n_local - a_below with ha_above_def
        have ha_above_eq : a_above =
            (univ.filter (fun i : Fin n_local ↦ sibling.hi ≤ (u' i).val)).card := by
          have hsum : a_below + (univ.filter (fun i : Fin n_local ↦ sibling.hi ≤ (u' i).val)).card
              = n_local := by
            have := card_filter_add_card_filter_not (s := univ) (fun i : Fin n_local ↦
              (u' i).val < sibling.hi)
            simp only [not_lt] at this
            rwa [Finset.card_univ, Fintype.card_fin] at this
          omega
        have hbn_le : b_native ≤ a_above := by omega
        suffices hR : (source3.card : ℝ) ≤
            (↑p.ε : ℝ) * ↑half_D + max 0 (↑half_D - (↑b_native : ℝ)) by exact_mod_cast hR
        by_cases ha_le : a_below ≤ half_D
        · -- Easy case
          calc (source3.card : ℝ)
              ≤ ↑(univ.filter (fun pos : Fin n_local ↦
                  half_D ≤ pos.val ∧ (sep_local.exec u' pos).val < sibling.hi)).card := by
                exact_mod_cast hsrc3_le
            _ ≤ (↑p.ε : ℝ) * ↑a_below := hsep_init_bound sibling.hi ha_le
            _ ≤ (↑p.ε : ℝ) * ↑half_D := mul_le_mul_of_nonneg_left
                (by exact_mod_cast ha_le) (by exact_mod_cast p.hε_pos.le)
            _ ≤ _ := le_add_of_nonneg_right (le_max_left 0 _)
        · -- Hard case: complement argument (factored to right_child_hard_case)
          push_neg at ha_le
          have ha_above_lt : a_above < half_D := by omega
          exact right_child_hard_case rfl p.ε p.hε_pos p.hε_lt sep_local u' sibling.hi
            source3.card b_native a_below a_above hsrc3_le hbn_le ha_above_lt
            ha_above_eq hcount hsep_final_bound
    -- Step 3: Benchmark comparison (Seiferas Section 5, pages 5-6)
    -- B-native deficit bounded by subtree IH + equidistribution from above.
    --
    -- Decompose: half_D - b_native = (c_native - half_D) + strangers_at_D
    -- where c_native = sibling-native items in D, strangers_at_D = D-strangers.
    --
    -- Among n_local items in D: b_native + c_native + strangers_at_D ≥ n_local
    -- (actually = n_local since B-native ∨ C-native ∨ D-strange is exhaustive for D-native items,
    --  and non-D-native items are D-strange)
    --
    -- Source (i): C-native items from levels above D → 1/(8A³-2A) · cap
    -- Source (ii): strangers in C's subtree displace C-native → 2γεA/(1-(2εA)²) · cap
    have h_deficit : max (0 : ℚ) (↑half_D - ↑b_native) ≤
        (2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
         + 1 / (8 * p.A ^ 3 - 2 * p.A)
         + p.γ / p.A
         + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap := by
      -- Positivity of the coefficient × cap
      have h_denom1 : (0 : ℚ) < 1 - (2 * p.ε * p.A) ^ 2 := by linarith [p.h2εA]
      have hA2 : (1 : ℚ) ≤ p.A ^ 2 := by nlinarith [p.hA]
      have h_denom2 : (0 : ℚ) < 8 * p.A ^ 3 - 2 * p.A := by nlinarith
      -- Count strangers at parent D for j = 1
      set s_D := parent.strangers 1 perm_t parent_regs
      -- IH: s_D ≤ γ · cap(parent.l) = γ · cap/A
      have hs_D_bound : (parent.strangers 1 perm_t parent_regs : ℚ) ≤ p.γ * (cap / p.A) := by
        have h1 := ih parent 1 (by omega)
        simp only [Nat.sub_self, pow_zero, mul_one, hcap_parent] at h1; exact h1
      -- Individual term non-negativity (used in multiple branches below)
      have ht1 : (0 : ℚ) ≤ 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2) :=
        div_nonneg (by positivity) h_denom1.le
      have ht2 : (0 : ℚ) ≤ 1 / (8 * p.A ^ 3 - 2 * p.A) := div_nonneg (by positivity) h_denom2.le
      have ht3 : (0 : ℚ) ≤ p.γ / p.A := div_nonneg p.hγ_pos.le hA_pos.le
      -- Eliminate max: suffices to show each branch ≤ RHS
      apply max_le
      · -- 0 ≤ RHS: positivity
        exact mul_nonneg (by linarith) hcap_nn
      · -- Core bound: half_D - b_native ≤ budget · cap
        -- Trivial when half_D = 0
        by_cases hhD0 : half_D = 0
        · simp only [hhD0, Nat.cast_zero, zero_sub]
          exact le_trans (neg_nonpos.mpr (Nat.cast_nonneg _)) (mul_nonneg (by linarith) hcap_nn)
        -- half_D ≥ 1
        have hhD_pos : 0 < half_D := by omega
        -- D-stranger count ≤ γ/A · cap
        have hd_strange : ↑(parent.strangers 1 perm_t parent_regs) ≤ p.γ / p.A * cap := by
          calc (↑(parent.strangers 1 perm_t parent_regs) : ℚ)
              ≤ p.γ * (cap / p.A) := hs_D_bound
            _ = p.γ / p.A * cap := by ring
        -- Conservation: partition + IH bound.
        -- Increase heartbeats for this block (partition proof involves large filter terms).
        have hn_le : n_local ≤ parent_regs.card := by
          show 2 * (parent_regs.card / 2) ≤ parent_regs.card
          omega
        -- Sibling-native and parent-strange counts
        let c_card := (Finset.univ.filter (fun i : Fin n_local ↦
            (b.sibling hl).Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t)).card
        let s_card := (Finset.univ.filter (fun i : Fin n_local ↦
            ¬ b.parent.Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t)).card
        -- Partition: b_native + c_card + s_card = n_local
        -- (parent.Native ↔ b.Native ∨ sibling.Native, disjoint)
        have hpart : b_native + c_card + s_card = n_local := by
          have h_pn := Finset.card_filter_add_card_filter_not
            (s := Finset.univ) (fun i : Fin n_local ↦
              b.parent.Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t)
          simp only [Finset.card_univ, Fintype.card_fin] at h_pn
          -- parent_nat + s_card = n_local, and parent_nat = b_native + c_card
          suffices heq : b_native + c_card =
            (Finset.univ.filter (fun i : Fin n_local ↦
              b.parent.Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t)).card by
            omega
          -- parent.Native ↔ b.Native ∨ sibling.Native
          have hunion : (Finset.univ.filter (fun i : Fin n_local ↦
              b.parent.Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t)) =
            (Finset.univ.filter (fun i : Fin n_local ↦
              b.Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t)) ∪
            (Finset.univ.filter (fun i : Fin n_local ↦
              (b.sibling hl).Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t)) := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
            exact Bag.parent_native_iff b hl _ _
          have hdisj : Disjoint
            (Finset.univ.filter (fun i : Fin n_local ↦
              b.Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t))
            (Finset.univ.filter (fun i : Fin n_local ↦
              (b.sibling hl).Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t)) := by
            rw [Finset.disjoint_filter]
            intro i _ hb hsib
            exact Set.disjoint_left.mp (Bag.sibling_interval_disjoint b hl)
              (Set.mem_Ico.mpr ((Bag.native_iff b _ _).mp hb))
              (Set.mem_Ico.mpr ((Bag.native_iff (b.sibling hl) _ _).mp hsib))
          rw [hunion, Finset.card_union_of_disjoint hdisj]
        -- s_card ≤ parent.strangers 1 perm_t parent_regs ≤ γ/A · cap
        have hs_le : (s_card : ℚ) ≤ p.γ / p.A * cap := by
          suffices h : s_card ≤ parent.strangers 1 perm_t parent_regs by
            exact le_trans (by exact_mod_cast h) hd_strange
          -- s_card = card of {i : Fin n_local | ¬parent.Native (embed ⟨i, _⟩) perm_t}
          -- strangers = card of {r ∈ parent_regs | parent.Strange 1 r perm_t}
          -- Map i ↦ embed ⟨i, _⟩ is an injection from s_D_set into strangers set
          let s_D_set := Finset.univ.filter (fun i : Fin n_local ↦
              ¬ b.parent.Native (embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩) perm_t)
          show s_D_set.card ≤ (parent_regs.filter (fun r ↦ parent.Strange 1 r perm_t)).card
          apply Finset.card_le_card_of_injOn
            (fun i : Fin n_local ↦ embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩)
          · intro i hi
            have hi' := (Finset.mem_filter.mp hi).2
            refine Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem parent_regs rfl _, ?_⟩
            -- Strange 1 = ¬(ancestor 0).Native = ¬parent.Native
            show parent.Strange 1 _ perm_t
            unfold Bag.Strange; right
            show ¬(parent.ancestor 0).Native _ _
            unfold Bag.ancestor; simp only [Nat.sub_zero, pow_zero, Nat.div_one]
            exact hi'
          · intro x _ y _ hxy
            have hinj := embed.injective hxy
            exact Fin.ext (by simp only [Fin.mk.injEq] at hinj; exact hinj)
        -- Case split on c_card vs half_D
        by_cases hc_le : c_card ≤ half_D
        · -- Easy: half_D - b_native ≤ s_card ≤ γ/A · cap ≤ budget · cap
          have hle_nat : half_D ≤ b_native + s_card := by omega
          have hkey : (↑half_D : ℚ) - ↑b_native ≤ ↑s_card := by
            have h := Nat.cast_le (α := ℚ).mpr hle_nat
            rw [Nat.cast_add] at h; linarith
          calc (↑half_D : ℚ) - ↑b_native ≤ ↑s_card := hkey
            _ ≤ p.γ / p.A * cap := hs_le
            _ ≤ _ := by
              apply mul_le_mul_of_nonneg_right _ hcap_nn; linarith
        · -- Hard: c_card > half_D, uses tree induction
          push_neg at hc_le
          -- half_D - b_native = (c_card - half_D) + s_card
          have hbn_nat : b_native = 2 * half_D - c_card - s_card := by omega
          have hdef : (↑half_D : ℚ) - ↑b_native = (↑c_card - ↑half_D) + ↑s_card := by
            have h1 : (↑b_native : ℚ) = ↑(2 * half_D) - ↑c_card - ↑s_card := by
              rw [hbn_nat, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
            rw [h1, Nat.cast_mul]; ring
          rw [hdef]
          -- Benchmark comparison (Seiferas 2009, Section 5, pp. 5-6).
          -- Excess C-native items in D come from two sources:
          --
          -- Source (ii): Non-C-native items in C's subtree displace C-native
          -- items upward. By IH, descendant bags at odd distances d from C have
          -- ≤ γ·ε^d·cap·A^d strangers, giving geometric sum < 2γεA/(1-(2εA)²)·cap.
          --
          -- Source (i): C-native items from levels above D contribute
          -- at most cap/(8A³-2A) via `bagCard_le_capacity` and geometric series.
          --
          -- Combined via conservation (bijectivity + bagCard_total):
          -- c_card - half_D ≤ source(ii) + source(i).
          have hc_excess : (↑c_card : ℚ) - ↑half_D ≤
              (2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
               + 1 / (4 * p.A ^ 3 - p.A)) * cap := by
            -- Seiferas (2009, Section 5): benchmark comparison.
            -- Conservation: total C-native items = sibling.size = 2^(k-ℓ).
            -- C-native items in D ≤ (C.size - subtree_items + non_C_sub).
            -- Splitting: C.size - subtree_items = Σ_{l<ℓ} bagCard(l)/2^(ℓ-l),
            -- where l=ℓ-1 gives ≥ half_D and remaining terms ≤ cap/(8A³-2A).
            --
            -- Source (ii): non-C-native items in C's subtree
            -- By IH, total non-C-native at odd distance d: γ(2εA)^d·cap.
            -- Geometric sum < 2γεA/(1-(2εA)²)·cap.
            -- Define non_C_sub: count of non-sibling-native items in sibling's subtree.
            -- These are items r ∈ subregs(sibling) with ¬sibling.Native r perm_t.
            set pl := (stages p k t).value
            set sib_sub := subregs pl sibling
            set non_C_sub_nat := (sib_sub.filter (fun r ↦ ¬ sibling.Native r perm_t)).card
            -- Source (ii): non_C_sub ≤ 2γεA/(1-(2εA)²) · cap
            -- Proof: each descendant bag b' at distance d from sibling has
            -- b'.strangers(d+1) ≤ γε^d·cap·A^d items that are not sibling-native.
            -- Sum over odd d (alternating levels): geometric series.
            have h_subtree_bound : (non_C_sub_nat : ℚ) ≤
                2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2) * cap := by
              -- Parity: parent level active → sibling level inactive
              have hpar_active : (t + (b.l - 1)) % 2 = 0 := by
                -- half_D > 0 → parent_regs nonempty → bagCard > 0 → parity must be right
                by_contra hpar
                push_neg at hpar
                have h0 : bagCard p k t parent.l = 0 :=
                  bagCard_odd_eq_zero p k (by omega) t parent.l (by rwa [hparent_l])
                have h1 : parent_regs.card = 0 :=
                  (bagCard_eq_card p k t parent).trans h0
                omega
              have hsib_parity : (t + b.l) % 2 ≠ 0 := by omega
              have hsib_l_eq : sibling.l = b.l := Bag.sibling_level_eq b hl
              -- Apply the subtree bound helper
              have hsib_bound := subtree_non_native_bound p k hk perm_t t ih
                sibling (by rw [hsib_l_eq]; exact hsib_parity)
              rwa [hsib_l_eq] at hsib_bound
            -- Conservation: c_card ≤ half_D + non_C_sub + cap/(8A³-2A)
            -- Proof outline:
            -- (a) Bijectivity: exactly sibling.size = 2^(k-b.l) items are C-native
            -- (b) C-native in subtree ≥ sub_card - non_C_sub
            -- (c) By bagCard_total: sub_card = sibling.size - Σ_{l<b.l} bagCard(l)/2^(b.l-l)
            -- (d) The l = parent.l term gives bagCard(parent.l)/2 ≥ half_D
            -- (e) Remaining ancestor terms ≤ cap/(8A³-2A) via bagCard_le_capacity
            -- (f) c_card ≤ sibling.size - (sub_card - non_C_sub)
            --     = Σ_{l<b.l} bagCard(l)/2^(b.l-l) + non_C_sub
            --     ≤ half_D + cap/(8A³-2A) + non_C_sub
            have h_conservation : (↑c_card : ℚ) ≤ ↑half_D + ↑non_C_sub_nat +
                1 / (4 * p.A ^ 3 - p.A) * cap := by
              -- Step A: perm_t is bijective (Fin is finite, so injective → bijective)
              have hperm_t_bij : Function.Bijective perm_t := by
                have hinj := ComparatorNetwork.exec_injective (stages p k t).net hperm.1
                exact hinj.bijective_of_finite
              -- Step B: Total sibling-native items in Fin(2^k) = sibling.size
              -- Under bijection perm_t, exactly sibling.size items map into [lo, hi)
              have hglob_native : (Finset.univ.filter
                  (fun r : Fin (2 ^ k) ↦ sibling.Native r perm_t)).card = sibling.size := by
                -- Step B1: bijection counting: card filter(P ∘ perm) = card filter(P)
                have hbij_count : ∀ (P : Fin (2 ^ k) → Prop) [DecidablePred P],
                    (Finset.univ.filter (P ∘ perm_t)).card =
                    (Finset.univ.filter P).card := by
                  intro P _
                  apply Finset.card_nbij' perm_t (Function.surjInv hperm_t_bij.2)
                  · intro v hv
                    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                      (Finset.mem_filter.mp hv).2⟩
                  · intro v hv
                    apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
                    show P (perm_t (Function.surjInv hperm_t_bij.2 v))
                    rw [Function.surjInv_eq hperm_t_bij.2 v]
                    exact (Finset.mem_filter.mp hv).2
                  · intro v _
                    exact hperm_t_bij.1 (Function.surjInv_eq hperm_t_bij.2 (perm_t v))
                  · intro v _; exact Function.surjInv_eq hperm_t_bij.2 v
                -- Step B2: Native r perm_t = (P ∘ perm_t) r where P v = (lo ≤ v.val < hi)
                have hnat_eq : (Finset.univ.filter (fun r ↦ sibling.Native r perm_t)) =
                  (Finset.univ.filter ((fun v : Fin (2 ^ k) ↦
                    sibling.lo ≤ v.val ∧ v.val < sibling.hi) ∘ perm_t)) := by
                  ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    Function.comp_apply, Bag.native_iff]
                rw [hnat_eq, hbij_count]
                -- Step B3: count items in [lo, hi) = hi - lo = size
                have hhi_le : sibling.hi ≤ 2 ^ k := by
                  simp only [Bag.hi, Bag.size, bagSize]
                  calc (sibling.x + 1) * (2 ^ k / 2 ^ sibling.l)
                      ≤ 2 ^ sibling.l * (2 ^ k / 2 ^ sibling.l) :=
                        Nat.mul_le_mul_right _ sibling.hx
                    _ ≤ 2 ^ k := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
                -- Bijection between filter and Ico
                let f_ico : { x // x ∈ Finset.Ico sibling.lo sibling.hi } → Fin (2 ^ k) :=
                  fun ⟨i, hi_mem⟩ ↦ ⟨i, by
                    have := (Finset.mem_Ico.mp hi_mem).2; omega⟩
                have hf_inj : Function.Injective f_ico := by
                  intro ⟨a, _⟩ ⟨b', _⟩ h
                  simp only [f_ico, Fin.mk.injEq] at h; exact Subtype.ext h
                have hset_eq : Finset.univ.filter (fun v : Fin (2 ^ k) ↦
                    sibling.lo ≤ v.val ∧ v.val < sibling.hi) =
                  Finset.univ.map ⟨f_ico, hf_inj⟩ := by
                  ext v; constructor
                  · intro hv
                    have hmem := Finset.mem_filter.mp hv
                    rw [Finset.mem_map]
                    exact ⟨⟨v.val, Finset.mem_Ico.mpr hmem.2⟩, Finset.mem_univ _,
                      Fin.ext rfl⟩
                  · intro hv
                    rw [Finset.mem_map] at hv
                    obtain ⟨⟨i, hi_mem⟩, _, hveq⟩ := hv
                    rw [Finset.mem_filter]
                    refine ⟨Finset.mem_univ _, ?_⟩
                    have hvi : v = f_ico ⟨i, hi_mem⟩ := hveq.symm
                    have : v.val = i := by simp [hvi, f_ico]
                    have := Finset.mem_Ico.mp hi_mem; omega
                rw [hset_eq, Finset.card_map, Finset.card_univ, Fintype.card_coe,
                    Nat.card_Ico]
                -- hi - lo = size
                show sibling.hi - sibling.lo = sibling.size
                show (sibling.x + 1) * bagSize k sibling.l -
                  sibling.x * bagSize k sibling.l = bagSize k sibling.l
                have : (sibling.x + 1) * bagSize k sibling.l =
                  sibling.x * bagSize k sibling.l + bagSize k sibling.l := by ring
                omega
              -- Step C: Disjoint parent_regs and sib_sub
              have hparent_sib_disj : Disjoint parent_regs sib_sub := by
                have hlt : parent.l < sibling.l := by
                  have : sibling.l = b.l := Bag.sibling_level_eq b hl
                  rw [hparent_l, this]; omega
                exact regs_disjoint_subregs' pl parent sibling hlt
              -- Step D: c_card ≤ sibling-native in parent_regs
              -- (embed is injective from Fin n_local to parent_regs)
              set c_in_parent := (parent_regs.filter
                  (fun r ↦ sibling.Native r perm_t)).card
              have hc_le_parent : c_card ≤ c_in_parent := by
                apply Finset.card_le_card_of_injOn
                  (fun i : Fin n_local ↦ embed ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn_le⟩)
                · intro i hi
                  have hi' := (Finset.mem_filter.mp hi).2
                  exact Finset.mem_filter.mpr
                    ⟨Finset.orderEmbOfFin_mem parent_regs rfl _, hi'⟩
                · intro x _ y _ hxy
                  have hinj := embed.injective hxy
                  exact Fin.ext (by simp only [Fin.mk.injEq] at hinj; exact hinj)
              -- Step E: sibling-native in parent_regs + sibling-native in sib_sub ≤ total
              set c_in_sib := (sib_sub.filter (fun r ↦ sibling.Native r perm_t)).card
              have hc_in_sib_eq : c_in_sib = sib_sub.card - non_C_sub_nat := by
                have hsplit := Finset.card_filter_add_card_filter_not
                  (s := sib_sub) (p := fun r ↦ sibling.Native r perm_t)
                omega
              have hsum_le : c_in_parent + c_in_sib ≤ sibling.size := by
                calc c_in_parent + c_in_sib
                    = (parent_regs.filter (fun r ↦ sibling.Native r perm_t) ∪
                       sib_sub.filter (fun r ↦ sibling.Native r perm_t)).card := by
                      rw [Finset.card_union_of_disjoint
                        (Finset.disjoint_filter_filter hparent_sib_disj)]
                  _ ≤ (Finset.univ.filter (fun r ↦ sibling.Native r perm_t)).card := by
                      apply Finset.card_le_card; intro r hr
                      simp only [Finset.mem_union, Finset.mem_filter] at hr
                      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.elim And.right And.right⟩
                  _ = sibling.size := hglob_native
              -- Step F: c_card ≤ sibling.size - sib_sub.card + non_C_sub_nat
              -- From: c_card ≤ c_in_parent ≤ sibling.size - c_in_sib
              --      = sibling.size - (sib_sub.card - non_C_sub_nat)
              have hc_bound_nat : c_card ≤ sibling.size - sib_sub.card + non_C_sub_nat := by
                have h1 : c_in_parent ≤ sibling.size - c_in_sib := by omega
                rw [hc_in_sib_eq] at h1; omega
              -- Step G: sibling.size - sib_sub.card ≤ half_D + 1/(8A³-2A) * cap (in ℚ)
              -- From bagCard_total: Σ_l 2^l · bagCard(l) = 2^k
              -- subregs_card_le_bagSize: sib_sub.card ≤ sibling.size
              -- The deficit sibling.size - sib_sub.card comes from registers at levels above sibling
              -- that are in sibling's native interval. By bagCard_total decomposition:
              -- sibling.size - sib_sub.card ≤ Σ_{l'<b.l} bagCard(l') / 2^(b.l-l')
              -- The l'=b.l-1 term = bagCard(parent.l) / 2 = parent_regs.card / 2 = half_D + {0 or 1/2}
              -- Remaining terms ≤ cap/(8A³-2A) by geometric series + bagCard_le_capacity
              have h_spillover : (↑(sibling.size - sib_sub.card) : ℚ) ≤
                  ↑half_D + 1 / (4 * p.A ^ 3 - p.A) * cap := by
                -- Use spillover_bound for sibling
                have hsib_l_eq : sibling.l = b.l := Bag.sibling_level_eq b hl
                have hsib_parent : sibling.parent = b.parent :=
                  Bag.sibling_parent_eq b hl
                -- Parent is active at level b.l - 1
                have hpar_active' : (t + (b.l - 1)) % 2 = 0 := by
                  by_contra hpar
                  push_neg at hpar
                  have h0 : bagCard p k t parent.l = 0 :=
                    bagCard_odd_eq_zero p k (by omega) t parent.l (by rwa [hparent_l])
                  have h1 : parent_regs.card = 0 := by
                    show ((stages p k t).value.regs parent).card = 0
                    exact (bagCard_eq_card p k t parent).trans h0
                  omega
                have hpar_active_sib : (t + (sibling.l - 1)) % 2 = 0 := by
                  rw [hsib_l_eq]; exact hpar_active'
                have hspill := spillover_bound p k hk t ht sibling
                  (by rw [hsib_l_eq]; exact hl) hpar_active_sib
                rw [hsib_l_eq, hsib_parent] at hspill
                have hsib_sub_eq : sib_sub = subregs (stages p k t).value sibling := rfl
                rw [← hsib_sub_eq] at hspill
                exact hspill
              -- Assembly: combine steps E, F, G
              calc (↑c_card : ℚ)
                  ≤ ↑(sibling.size - sib_sub.card + non_C_sub_nat) := by
                    exact_mod_cast hc_bound_nat
                _ = ↑(sibling.size - sib_sub.card) + ↑non_C_sub_nat := by
                    rw [Nat.cast_add]
                _ ≤ (↑half_D + 1 / (4 * p.A ^ 3 - p.A) * cap) + ↑non_C_sub_nat := by
                    linarith [h_spillover]
                _ = ↑half_D + ↑non_C_sub_nat + 1 / (4 * p.A ^ 3 - p.A) * cap := by
                    ring
            linarith [Nat.cast_nonneg (α := ℚ) non_C_sub_nat]
          -- Combine: (c-h) + s ≤ (excess_budget + 1/(4A³-A)) * cap + γ/A * cap
          --   = (excess_budget + 1/(8A³-2A) + γ/A + 1/(8A³-2A)) * cap
          calc (↑c_card : ℚ) - ↑half_D + ↑s_card
              ≤ (2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
                 + 1 / (4 * p.A ^ 3 - p.A)) * cap + p.γ / p.A * cap := by
                linarith [hs_le]
            _ ≤ (2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
                 + 1 / (8 * p.A ^ 3 - 2 * p.A)
                 + p.γ / p.A
                 + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap := by
              have hA4 : (0 : ℚ) < 4 * p.A ^ 3 - p.A := by nlinarith [p.hA]
              -- 1/(4A³-A) = 2/(8A³-2A) = 1/(8A³-2A) + 1/(8A³-2A)
              have h4to8 : (1 : ℚ) / (4 * p.A ^ 3 - p.A) =
                  1 / (8 * p.A ^ 3 - 2 * p.A) + 1 / (8 * p.A ^ 3 - 2 * p.A) := by
                have h1 : (8 : ℚ) * p.A ^ 3 - 2 * p.A = 2 * (4 * p.A ^ 3 - p.A) := by ring
                rw [h1]; field_simp; norm_num
              rw [h4to8] at hc_excess
              have hgA : (0 : ℚ) ≤ p.γ / p.A := div_nonneg p.hγ_pos.le hA_pos.le
              nlinarith
            _ ≤ _ := by linarith
    -- Assembly
    calc (source3.card : ℚ)
        ≤ p.ε * ↑half_D + max (0 : ℚ) (↑half_D - ↑b_native) := h_decomp
      _ ≤ p.ε * (cap / (2 * p.A)) +
          (2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
           + 1 / (8 * p.A ^ 3 - 2 * p.A)
           + p.γ / p.A
           + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap :=
          add_le_add (mul_le_mul_of_nonneg_left h_half_le hε_pos.le) h_deficit
      _ = (p.ε / (2 * p.A) + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
           + 1 / (8 * p.A ^ 3 - 2 * p.A)
           + p.γ / p.A
           + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap :=
          source3_assembly_algebra p.ε p.A p.γ cap p.hA p.h2εA

  -- Combine the bounds
  calc (b.strangers 1 perm_t1 S : ℚ)
      ≤ ↑source2.card + ↑source3.card := by exact_mod_cast hdecomp
    _ ≤ (p.ε * p.γ / p.A * cap) +
        ((p.ε / (2 * p.A) + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
          + 1 / (8 * p.A ^ 3 - 2 * p.A)
          + p.γ / p.A
          + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap) := by
        exact add_le_add hsource2_bound hsource3_bound
    _ = (p.ε * p.γ / p.A + p.ε / (2 * p.A)
         + 2 * p.γ * p.ε * p.A / (1 - (2 * p.ε * p.A) ^ 2)
         + 1 / (8 * p.A ^ 3 - 2 * p.A)
         + p.γ / p.A
         + 1 / (8 * p.A ^ 3 - 2 * p.A)) * cap := by ring


end


