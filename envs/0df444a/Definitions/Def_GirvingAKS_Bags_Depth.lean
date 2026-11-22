-- Prove2me | Definitions.Def_GirvingAKS_Bags_Depth
-- name    : GirvingAKS_Bags_Depth
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T19:35:11.339801+00:00
-- url     : https://prove2.me/theorems/59f83d5d-5829-428d-8aa3-eabfefe98b77
-- title:
--   AKS sorting networks (Seiferas port) — Seiferas Network Depth Bound
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bags/Depth.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Proves that `seiferasNetwork p k` has O(log n) depth, where n = 2^k.
--
--   Key definitions:
--
--   - `stageDepth p`: depth of a single separator stage (constant, independent of k)
--   - `Params.depth p`: the O(1) constant such that depth ≤ p.depth * k
--
--   Key results:
--
--   - `numStages_le`: `numStages p k ≤ 2 * k` (proved)
--   - `stage_depth_le`: each stage has depth ≤ `stageDepth p` (proved)
--   - `stages_depth_le`: `t` stages have depth ≤ `t * stageDepth p` (proved)
--   - `finishAt_depth_le`: finish step has depth ≤ 4 (proved)
--   - `seiferasNetwork_depth_le`: main theorem (proved from above)
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bags/Depth.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bags_Network
import Definitions.Def_GirvingAKS_Bags_Sizes
import Definitions.Def_GirvingAKS_Bags_Sorts
import Definitions.Def_GirvingAKS_Sort_Depth
import Definitions.Def_GirvingAKS_Bitonic_Shrink
import Definitions.Def_GirvingAKS_Separator_General

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bags/Depth.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Seiferas Network Depth Bound

  Proves that `seiferasNetwork p k` has O(log n) depth, where n = 2^k.

  Key definitions:
  - `stageDepth p`: depth of a single separator stage (constant, independent of k)
  - `Params.depth p`: the O(1) constant such that depth ≤ p.depth * k

  Key results:
  - `numStages_le`: `numStages p k ≤ 2 * k` (proved)
  - `stage_depth_le`: each stage has depth ≤ `stageDepth p` (proved)
  - `stages_depth_le`: `t` stages have depth ≤ `t * stageDepth p` (proved)
  - `finishAt_depth_le`: finish step has depth ≤ 4 (proved)
  - `seiferasNetwork_depth_le`: main theorem (proved from above)
-/


section


/-! **Per-Stage Depth** -/

/-- Depth of a single separator stage: all bag separators run in parallel
    since bags have disjoint wire sets (`Placement.disjoint`).
    Equals the depth of the underlying separator construction,
    independent of `k` and the number of wires. -/
def stageDepth (p : Params) : ℕ :=
  separatorDepth p.γ p.ε p.hγ_pos p.hε_pos

/-! **numStages Bound** -/

/-- `numStages p k ≤ p.stagesFactor * k`.

    At stage `c * k` (where `c = stagesFactor`), capacity at level `k - 2` is
    `2^k · ν^(ck) · A^(k-2) = (2 · ν^c)^k · A^(k-2) / A^k · A^k`...
    Since `ν^c · 2A < 1` (by `stagesFactor_spec`), we get `(2 · ν^c · A)^k < 1`,
    so `capacity(ck, k-2) < 1/A^2`, and `γ · capacity < γ/A^2 ≤ 1/2 < 1`. -/
theorem numStages_le (p : Params) (k : ℕ) : numStages p k ≤ p.stagesFactor * k := by
  by_contra h; push_neg at h
  have h1 := numStages_pre p k (p.stagesFactor * k) h
  -- But γ * capacity(c*k, k-2) < 1, contradiction
  have h2 : p.γ * capacity p k (p.stagesFactor * k) (k - 2) < 1 := by
    unfold capacity
    set c := p.stagesFactor
    have hνc := p.stagesFactor_spec  -- ν^c · 2A ≤ 1
    have h2νcA : 2 * p.ν ^ c * p.A ≤ 1 := by linarith
    rw [show p.ν ^ (c * k) = (p.ν ^ c) ^ k from by rw [pow_mul]]
    have hν_pos := pow_pos p.hν_pos c
    have hAk2 : p.A ^ (k - 2) ≤ p.A ^ k :=
      pow_le_pow_right₀ (by linarith [p.hA]) (by omega)
    have h2νcA_nn : 0 ≤ 2 * p.ν ^ c * p.A :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg p.hν_pos.le _)) (by linarith [p.hA])
    calc p.γ * ((2:ℚ) ^ k * (p.ν ^ c) ^ k * p.A ^ (k - 2))
        ≤ p.γ * ((2:ℚ) ^ k * (p.ν ^ c) ^ k * p.A ^ k) := by
          apply mul_le_mul_of_nonneg_left _ p.hγ_pos.le
          exact mul_le_mul_of_nonneg_left hAk2 (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg hν_pos.le _))
      _ = p.γ * (2 * p.ν ^ c * p.A) ^ k := by ring
      _ ≤ (1/2) * 1 := by
          apply mul_le_mul p.hγ_half (pow_le_one₀ h2νcA_nn h2νcA)
            (pow_nonneg h2νcA_nn _) (by norm_num)
      _ < 1 := by norm_num
  linarith

/-! **Depth Bound Constant** -/

/-- O(log n) depth constant: `(seiferasNetwork p k).depth ≤ p.depth * k`.

    Components:
    - `p.stagesFactor * stageDepth p`: accounts for `numStages p k ≤ stagesFactor * k`
      stages, each with depth ≤ `stageDepth p`
    - `9`: finish depth — each subtree at level `k - 3` has
      ≤ 8 registers (by `bagSize_finishLevel_le`), so `bitonicNetwork` has
      depth ≤ `(⌈log₂ 8⌉)² = 9`. Subtrees are wire-disjoint. -/
def Params.depth (p : Params) : ℕ :=
  p.stagesFactor * stageDepth p + 9

/-! **Helper: depth of networks on 1 wire** -/

/-- Any comparator network on 1 wire has depth 0 (no valid comparators exist). -/
theorem depth_one (net : ComparatorNetwork 1) : net.depth = 0 := by
  suffices h : net.comparators = [] by simp [ComparatorNetwork.depth, h]
  rcases net with ⟨cs⟩
  induction cs with
  | nil => rfl
  | cons c _ _ => exact absurd c.h (by omega)

/-! **effectiveGamma bound** -/

/-- The effective separator fraction is at least `p.γ` when the bag's wire
    count doesn't exceed the capacity.
    When `C = 0`, `γₑ = p.γ` trivially. When `C > 0`, `γₑ = p.γ · cap / C ≥ p.γ`
    iff `cap ≥ C`. -/
theorem effectiveGamma_ge_gamma (γ cap : ℚ) (hγ : 0 < γ)
    (C : ℕ) (hle : ↑C ≤ cap) :
    γ ≤ effectiveGamma γ cap C := by
  unfold effectiveGamma
  by_cases hC : C = 0
  · rw [if_pos hC]
  · rw [if_neg hC, le_div_iff₀ (Nat.cast_pos.mpr (by omega : 0 < C))]
    exact mul_le_mul_of_nonneg_left hle hγ.le

/-- Wire count ≤ capacity: `2 * (card / 2) ≤ bagCard ≤ capacity`. -/
theorem bag_wire_count_le_capacity (p : Params) (k : ℕ) (hk : 10 ≤ k)
    (t : ℕ) (ht : t ≤ numStages p k) (b : Bag k) :
    ↑(2 * (((stages p k t).value.regs b).card / 2)) ≤ capacity p k t b.l := by
  set card := ((stages p k t).value.regs b).card
  have h1 : 2 * (card / 2) ≤ card := by
    have := Nat.div_mul_le_self card 2; omega
  have h2 : card = bagCard p k t b.l := bagCard_eq_card p k t b
  calc ↑(2 * (card / 2))
      ≤ (card : ℚ) := Nat.cast_le.mpr h1
    _ = (bagCard p k t b.l : ℚ) := by rw [h2]
    _ ≤ capacity p k t b.l := bagCard_le_capacity p k hk t (numStages_hfl p k hk t ht) b.l

/-! **Per-bag depth bound** -/

/-- Each bag's scatter-embedded separator has depth ≤ `separatorDepth γₑ ε`. -/
theorem built_depth_le (p : Params) (k : ℕ) (hk : 10 ≤ k) (t : ℕ) (ht : t ≤ numStages p k)
    (b : Bag k) :
    let pl := (stages p k t).value
    let regs := pl.regs b
    let γₑ := effectiveGamma p.γ (capacity p k t b.l) (2 * (regs.card / 2))
    let hγₑ := effectiveGamma_pos p.hγ_pos (capacity_pos p k t b.l) _
    (separateAndSplit γₑ p.ε hγₑ p.hε_pos regs (fringe p k t b.l regs.card)).net.depth ≤
    stageDepth p := by
  intro pl regs γₑ hγₑ
  show (⟨((separatorNet γₑ p.ε hγₑ p.hε_pos (regs.card / 2)).scatterEmbed
    (2 ^ k) _).comparators ++ []⟩ : ComparatorNetwork (2 ^ k)).depth ≤ _
  rw [List.append_nil]
  calc (((separatorNet γₑ p.ε hγₑ p.hε_pos (regs.card / 2)).scatterEmbed (2 ^ k) _)).depth
      ≤ (separatorNet γₑ p.ε hγₑ p.hε_pos (regs.card / 2)).depth :=
        depth_scatterEmbed_le _ _ _
    _ ≤ separatorDepth γₑ p.ε hγₑ p.hε_pos := separatorNet_depth_le _ _ _ _ _
    _ ≤ separatorDepth p.γ p.ε p.hγ_pos p.hε_pos :=
        separatorDepth_antitone p.hγ_pos hγₑ
          (effectiveGamma_ge_gamma p.γ _ p.hγ_pos _
            (bag_wire_count_le_capacity p k hk t ht b)) p.hε_pos

/-! **Wire disjointness between bags** -/

/-- Scatter-embedded comparator wires lie in the embedding's range. -/
theorem scatterEmbed_wire_mem {m n : ℕ} (net : ComparatorNetwork m)
    (f : Fin m ↪o Fin n) (c : Comparator n)
    (hc : c ∈ (net.scatterEmbed n f).comparators) :
    c.i ∈ Set.range f ∧ c.j ∈ Set.range f := by
  simp only [ComparatorNetwork.scatterEmbed, List.mem_map] at hc
  obtain ⟨c', _, rfl⟩ := hc
  exact ⟨⟨c'.i, rfl⟩, ⟨c'.j, rfl⟩⟩

/-- The embedding used in `separate` maps into the bag's register set. -/
theorem separate_emb_range_subset {k : ℕ} (regs : Finset (Fin (2 ^ k))) :
    Set.range ((Fin.castLEOrderEmb (by omega : 2 * (regs.card / 2) ≤ regs.card)).trans
      (regs.orderEmbOfFin rfl)) ⊆ ↑regs := by
  intro x ⟨i, hi⟩
  rw [← hi, RelEmbedding.coe_trans]
  exact Finset.orderEmbOfFin_mem regs rfl _

/-- Comparators from bag `a`'s separator only touch wires in `pl.regs a`. -/
theorem stage_comparators_subset (p : Params) {k : ℕ} (pl : Placement k)
    (t : ℕ) (a : Bag k) (c : Comparator (2 ^ k))
    (hc : c ∈ ((fun b ↦
      let regs := pl.regs b
      let γₑ := effectiveGamma p.γ (capacity p k t b.l) (2 * (regs.card / 2))
      (separateAndSplit γₑ p.ε (effectiveGamma_pos p.hγ_pos (capacity_pos p k t b.l) _) p.hε_pos
        regs (fringe p k t b.l regs.card)).net) a).comparators) :
    c.i ∈ (pl.regs a : Set (Fin (2 ^ k))) ∧
    c.j ∈ (pl.regs a : Set (Fin (2 ^ k))) := by
  -- (built a).net.comparators = scatter-embedded comparators ++ []
  simp only at hc
  rw [show (separateAndSplit _ _ _ _ _ _).net.comparators =
    ((separatorNet _ _ _ _ _).scatterEmbed _ _).comparators ++ [] from rfl] at hc
  rw [List.append_nil] at hc
  have ⟨hi, hj⟩ := scatterEmbed_wire_mem _ _ c hc
  exact ⟨separate_emb_range_subset _ hi, separate_emb_range_subset _ hj⟩

/-! **Stage depth bound** -/

/-- Each separator stage has depth ≤ `stageDepth p`.

    Within a stage, each bag's separator is scatter-embedded into disjoint
    wire subsets (by `Placement.disjoint`), so all bag separators execute
    in parallel via `depth_flatMap_disjoint`. Each individual separator has
    depth ≤ `separatorDepth` by `separatorNet_depth_le` + `depth_scatterEmbed_le`. -/
theorem stage_depth_le (p : Params) (k : ℕ) (hk : 10 ≤ k) (t : ℕ)
    (ht : t ≤ numStages p k) :
    (stage p (stages p k t).value t).net.depth ≤ stageDepth p := by
  set pl := (stages p k t).value
  let built : Bag k → Build (2 ^ k) (BagSplit k) := fun b ↦
    let regs := pl.regs b
    let γₑ := effectiveGamma p.γ (capacity p k t b.l) (2 * (regs.card / 2))
    separateAndSplit γₑ p.ε (effectiveGamma_pos p.hγ_pos (capacity_pos p k t b.l) _) p.hε_pos
      regs (fringe p k t b.l regs.card)
  -- Step 1: strip trailing [] from Build.emit >>= return
  have h1 : (stage p pl t).net.depth ≤
      (⟨(allBags k).flatMap fun b ↦ (built b).net.comparators⟩ :
        ComparatorNetwork (2 ^ k)).depth :=
    le_of_le_of_eq
      (depth_append ⟨(allBags k).flatMap fun b ↦ (built b).net.comparators⟩ ⟨[]⟩)
      (by simp [depth_nil])
  -- Step 2: flatMap depth ≤ stageDepth via depth_flatMap_disjoint
  have h2 : (⟨(allBags k).flatMap fun b ↦ (built b).net.comparators⟩ :
      ComparatorNetwork (2 ^ k)).depth ≤ stageDepth p := by
    apply depth_flatMap_disjoint (allBags k) (fun b ↦ (built b).net.comparators) (stageDepth p)
    · -- Per-bag depth bound
      intro b _
      exact built_depth_le p k hk t ht b
    · -- Wire disjointness between bags
      apply allBags_nodup.pairwise_of_forall_ne
      intro a _ b _ hab c₁ hc₁ c₂ hc₂
      have ⟨hi₁, hj₁⟩ := stage_comparators_subset p pl t a c₁ hc₁
      have ⟨hi₂, hj₂⟩ := stage_comparators_subset p pl t b c₂ hc₂
      have hdisj := pl.disjoint a b hab
      rw [Finset.disjoint_left] at hdisj
      exact ⟨⟨fun h ↦ hdisj (Finset.mem_coe.mp hi₁) (h ▸ Finset.mem_coe.mp hi₂),
              fun h ↦ hdisj (Finset.mem_coe.mp hi₁) (h ▸ Finset.mem_coe.mp hj₂)⟩,
             ⟨fun h ↦ hdisj (Finset.mem_coe.mp hj₁) (h ▸ Finset.mem_coe.mp hi₂),
              fun h ↦ hdisj (Finset.mem_coe.mp hj₁) (h ▸ Finset.mem_coe.mp hj₂)⟩⟩
  exact h1.trans h2

/-! **Iterated stages depth** -/

/-- Depth of `t` iterated stages ≤ `t * stageDepth p`. -/
theorem stages_depth_le (p : Params) (k : ℕ) (hk : 10 ≤ k) (t : ℕ)
    (ht : t ≤ numStages p k) :
    (stages p k t).net.depth ≤ t * stageDepth p := by
  induction t with
  | zero =>
    simp only [stages, Nat.zero_mul]
    exact le_of_eq depth_nil
  | succ t ih =>
    calc (stages p k (t + 1)).net.depth
        ≤ (stages p k t).net.depth +
          (stage p (stages p k t).value t).net.depth :=
          depth_append (stages p k t).net (stage p (stages p k t).value t).net
      _ ≤ t * stageDepth p + stageDepth p :=
          Nat.add_le_add (ih (by omega)) (stage_depth_le p k hk t (by omega))
      _ = (t + 1) * stageDepth p := by ring

/-! **Subregs card bound** -/

/-- `pl.regs b` is disjoint from `subregs pl c` when `b` is at a strictly
    higher level than `c` (lower `l` value). -/
theorem regs_disjoint_subregs {k : ℕ} (pl : Placement k) (b c : Bag k) (h : b.l < c.l) :
    Disjoint (pl.regs b) (subregs pl c) := by
  unfold subregs; split
  case isTrue hk =>
    rw [Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨pl.disjoint b c (by intro heq; subst heq; omega),
            regs_disjoint_subregs pl b (c.left hk) (by show b.l < c.l + 1; omega)⟩,
           regs_disjoint_subregs pl b (c.right hk) (by show b.l < c.l + 1; omega)⟩
  case isFalse => exact pl.disjoint b c (by intro heq; subst heq; omega)
termination_by k - c.l
decreasing_by all_goals show k - (c.l + 1) < k - c.l; omega

/-- Card of `subregs` splits as a disjoint sum: `regs + subregs(left) + subregs(right)`. -/
theorem subregs_card_split {k : ℕ} (pl : Placement k) (b : Bag k) (h : b.l < k) :
    (subregs pl b).card = (pl.regs b).card + (subregs pl (b.left h)).card +
      (subregs pl (b.right h)).card := by
  conv_lhs => rw [subregs, dif_pos h]
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · exact regs_disjoint_subregs pl b (b.left h) (by show b.l < b.l + 1; omega)
  · rw [Finset.disjoint_union_left]
    refine ⟨regs_disjoint_subregs pl b (b.right h) (by show b.l < b.l + 1; omega),
           subregs_disjoint pl (b.left h) (b.right h) (by
             intro heq; have : (b.left h).x = (b.right h).x := by rw [heq]
             simp [Bag.left, Bag.right] at this) rfl⟩

/-- All bags at the same level have the same `subregs` card (for placements from `stages`). -/
theorem subregs_card_uniform (p : Params) (k t : ℕ) (b₁ b₂ : Bag k) (hl : b₁.l = b₂.l) :
    (subregs (stages p k t).value b₁).card = (subregs (stages p k t).value b₂).card := by
  set pl := (stages p k t).value
  by_cases hk : b₁.l < k
  · have hk₂ : b₂.l < k := hl ▸ hk
    rw [subregs_card_split pl b₁ hk, subregs_card_split pl b₂ hk₂,
        bagCard_eq_card p k t b₁, bagCard_eq_card p k t b₂, hl]
    congr 1
    · congr 1
      exact subregs_card_uniform p k t (b₁.left hk) (b₂.left hk₂) (by simp [Bag.left, hl])
    · exact subregs_card_uniform p k t (b₁.right hk) (b₂.right hk₂) (by simp [Bag.right, hl])
  · have hk₂ : ¬(b₂.l < k) := by omega
    conv_lhs => rw [subregs, dif_neg hk]
    conv_rhs => rw [subregs, dif_neg hk₂]
    rw [bagCard_eq_card p k t b₁, bagCard_eq_card p k t b₂, hl]
termination_by k - b₁.l
decreasing_by all_goals simp_all [Bag.left, Bag.right]; omega

/-- Subregs card at any level is bounded by `bagSize`: `(subregs pl b).card ≤ 2^(k - b.l)`.

    Proof: all `2^l` subtrees at level `l` have pairwise disjoint subregs
    (by `subregs_disjoint`), equal card (by `subregs_card_uniform`), and
    each is a subset of `Fin (2^k)`. So `2^l * card ≤ 2^k`. -/
theorem subregs_card_le_bagSize (p : Params) (k t : ℕ) (b : Bag k) :
    (subregs (stages p k t).value b).card ≤ b.size := by
  set pl := (stages p k t).value
  set l := b.l
  set s := (subregs pl b).card
  -- Build an injective map from 2^l copies of s elements into Fin(2^k)
  -- via the disjoint subregs at level l.
  -- All bags at level l have the same subregs card = s.
  -- There are 2^l bags at level l, with pairwise disjoint subregs ⊆ Fin(2^k).
  -- So 2^l * s ≤ 2^k, hence s ≤ 2^(k-l) = bagSize k l = b.size.
  unfold Bag.size bagSize
  rw [Nat.le_div_iff_mul_le (by positivity)]
  -- Goal: s * 2^l ≤ 2^k
  set bags := bagsAt k l b.hl
  have hlen : bags.length = 2 ^ l := by
    show (bagsAt k l b.hl).length = 2 ^ l
    simp [bagsAt, List.length_map, List.length_attach, List.length_range]
  have hnodup : bags.Nodup := bagsAt_nodup b.hl
  have huniform : ∀ b' ∈ bags, (subregs pl b').card = s := by
    intro b' hb'
    exact subregs_card_uniform p k t b' b (bagsAt_level hb')
  have hdisj : ∀ b₁ ∈ bags, ∀ b₂ ∈ bags, b₁ ≠ b₂ →
      Disjoint (subregs pl b₁) (subregs pl b₂) := by
    intro b₁ hb₁ b₂ hb₂ hne
    exact subregs_disjoint pl b₁ b₂ hne (by rw [bagsAt_level hb₁, bagsAt_level hb₂])
  -- Card of biUnion = sum of cards (disjoint) = 2^l * s
  have hsum : (bags.toFinset.biUnion (subregs pl)).card =
      ∑ _ ∈ bags.toFinset, s := by
    rw [Finset.card_biUnion (fun b₁ hb₁ b₂ hb₂ hne ↦
      hdisj b₁ (List.mem_toFinset.mp hb₁) b₂ (List.mem_toFinset.mp hb₂) hne)]
    apply Finset.sum_congr rfl
    intro b' hb'; exact huniform b' (List.mem_toFinset.mp hb')
  rw [Finset.sum_const, show bags.toFinset.card = bags.length from
    by rw [List.card_toFinset, hnodup.dedup], hlen] at hsum
  -- biUnion ⊆ Finset.univ, so card ≤ 2^k
  have hle : (bags.toFinset.biUnion (subregs pl)).card ≤ 2 ^ k :=
    (Finset.card_le_card (Finset.subset_univ _)).trans
      (by simp [Finset.card_univ, Fintype.card_fin])
  rw [hsum] at hle
  -- hle : 2^l • s ≤ 2^k, goal : s * 2^l ≤ 2^k
  change 2 ^ l * s ≤ 2 ^ k at hle; rw [Nat.mul_comm] at hle; exact hle

/-! **Finish depth bound** -/

/-- `bitonicNetwork` on ≤ 8 elements has depth ≤ 9: `(⌈log₂ m⌉)² ≤ 9`. -/
theorem bitonicNetwork_depth_le_nine (m : ℕ) (hm : m ≤ 8) :
    (bitonicNetwork m).depth ≤ 9 := by
  calc (bitonicNetwork m).depth
      ≤ (Nat.clog 2 m) ^ 2 := bitonicNetwork_depth_le m
    _ ≤ 9 := by
        have : Nat.clog 2 m ≤ 3 := by
          calc Nat.clog 2 m ≤ Nat.clog 2 8 := Nat.clog_mono_right 2 hm
            _ = 3 := by decide
        calc (Nat.clog 2 m) ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left this 2
          _ = 9 := by norm_num

/-- `bagSize k (k - 3) ≤ 8`: each subtree at the finish level `k - 3` has ≤ 8 wires. -/
theorem bagSize_finishLevel_le (k : ℕ) : bagSize k (k - 3) ≤ 8 := by
  unfold bagSize
  by_cases hk : 3 ≤ k
  · rw [Nat.pow_div (by omega) (by omega), show k - (k - 3) = 3 from by omega]
  · rw [show k - 3 = 0 from by omega, pow_zero, Nat.div_one]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 8 := by omega

/-- Depth of the finish step is bounded by 9.

    Each subtree at level `k - 3` has at most `bagSize k (k-3) = 8`
    registers (by `subregs_card_le_bagSize`).
    `bitonicNetwork` on ≤ 8 items has depth ≤ 9.
    Subtrees at the same level are wire-disjoint (by `subregs_disjoint`),
    so all bitonic sorts execute in parallel via `depth_flatMap_disjoint`. -/
theorem finishAt_depth_le (p : Params) (k : ℕ) :
    (finishAt p (stages p k (numStages p k)).value).net.depth ≤ 9 := by
  set T := numStages p k
  set pl := (stages p k T).value
  set fl := k - 3
  set bags := bagsAt k fl (by omega)
  -- finishAt builds: for each bag, scatter-embed bitonicNetwork into subregs
  let mkNet := fun b ↦
    let regs := subregs pl b
    (bitonicNetwork regs.card).scatterEmbed (2 ^ k) (regs.orderEmbOfFin rfl)
  -- The net is the flatMap of all mkNet comparators
  have hnet : (finishAt p pl).net =
      ⟨(bags.map fun b ↦ mkNet b).flatMap ComparatorNetwork.comparators⟩ := by
    simp only [finishAt, Build.emit]; rfl
  rw [hnet, show (List.map (fun b ↦ mkNet b) bags).flatMap ComparatorNetwork.comparators =
    bags.flatMap (fun b ↦ (mkNet b).comparators) from by simp [List.flatMap_map]]
  -- Apply depth_flatMap_disjoint
  apply depth_flatMap_disjoint bags (fun b ↦ (mkNet b).comparators) 9
  · -- Per-bag depth: bitonicNetwork on ≤ 8 items has depth ≤ 9
    intro b hb
    show (mkNet b).depth ≤ 9
    have hbl : b.l = fl := bagsAt_level hb
    have hsize : b.size ≤ 8 := by
      unfold Bag.size; rw [hbl]; exact bagSize_finishLevel_le k
    calc (mkNet b).depth
        ≤ (bitonicNetwork (subregs pl b).card).depth := depth_scatterEmbed_le _ _ _
      _ ≤ 9 := bitonicNetwork_depth_le_nine _
          ((subregs_card_le_bagSize p k T b).trans hsize)
  · -- Wire disjointness: comparators from different bags touch disjoint subregs
    apply (bagsAt_nodup (by omega : fl ≤ k)).pairwise_of_forall_ne
    intro a ha b' hb' hab c₁ hc₁ c₂ hc₂
    have ⟨hi₁, hj₁⟩ := scatterEmbed_wire_mem _ _ c₁ hc₁
    have ⟨hi₂, hj₂⟩ := scatterEmbed_wire_mem _ _ c₂ hc₂
    rw [Finset.range_orderEmbOfFin] at hi₁ hj₁ hi₂ hj₂
    have hdisj := subregs_disjoint pl a b' hab
      (by rw [bagsAt_level ha, bagsAt_level hb'])
    rw [Finset.disjoint_left] at hdisj
    exact ⟨⟨fun h ↦ hdisj (Finset.mem_coe.mp hi₁) (h ▸ Finset.mem_coe.mp hi₂),
            fun h ↦ hdisj (Finset.mem_coe.mp hi₁) (h ▸ Finset.mem_coe.mp hj₂)⟩,
           ⟨fun h ↦ hdisj (Finset.mem_coe.mp hj₁) (h ▸ Finset.mem_coe.mp hi₂),
            fun h ↦ hdisj (Finset.mem_coe.mp hj₁) (h ▸ Finset.mem_coe.mp hj₂)⟩⟩

/-! **Main Depth Theorem** -/

/-- **O(log n) depth of the Seiferas sorting network.**

    `(seiferasNetwork p k).depth ≤ p.depth * k`

    where `n = 2^k`, so `k = log₂ n` and the depth is O(log n).

    Proof: decompose into stages + finish via `depth_append`, bound
    each part, then use `numStages_le` and algebra. -/
theorem seiferasNetwork_depth_le (p : Params) (k : ℕ) (hk : 10 ≤ k) :
    (seiferasNetwork p k).depth ≤ p.depth * k := by
  -- k ≥ 10 ≥ 1, so write k = k' + 1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set T := numStages p (k' + 1)
  -- depth ≤ stages depth + finish depth
  have h_decomp :=
    depth_append (stages p (k' + 1) T).net
      (finishAt p (stages p (k' + 1) T).value).net
  -- stages depth ≤ T * stageDepth
  have h_stages := stages_depth_le p (k' + 1) hk T le_rfl
  -- finish depth ≤ 9
  have h_finish := finishAt_depth_le p (k' + 1)
  -- T ≤ stagesFactor * (k' + 1)
  have h_T := numStages_le p (k' + 1)
  -- Assembly
  calc (seiferasNetwork p (k' + 1)).depth
      ≤ (stages p (k' + 1) T).net.depth +
        (finishAt p (stages p (k' + 1) T).value).net.depth := h_decomp
    _ ≤ T * stageDepth p + 9 := Nat.add_le_add h_stages h_finish
    _ ≤ p.stagesFactor * (k' + 1) * stageDepth p + 9 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ h_T) 9
    _ ≤ p.stagesFactor * (k' + 1) * stageDepth p + 9 * (k' + 1) := by omega
    _ = (p.stagesFactor * stageDepth p + 9) * (k' + 1) := by ring
    _ = p.depth * (k' + 1) := by unfold Params.depth; ring

/-! **Concrete Depth Bound** -/

/-- Concrete bound on `seiferasParams.depth` -/
theorem seiferasParams_depth_le : seiferasParams.depth ≤ 141 * 10 ^ 62 := by decide +kernel

/-- Our concrete bound is sharp -/
theorem le_seiferasParams_depth : 140 * 10 ^ 62 ≤ seiferasParams.depth := by decide +kernel

end


