-- Prove2me | Definitions.Def_GirvingAKS_Bags_Sorts
-- name    : GirvingAKS_Bags_Sorts
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T19:32:04.895962+00:00
-- url     : https://prove2.me/theorems/1bb08889-d9d6-4794-a3ee-63e4a5f14fa7
-- title:
--   AKS sorting networks (Seiferas port) — Seiferas Network Sorts
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bags/Sorts.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Proves that `seiferasNetwork p k` is a sorting network, assuming the stranger bound (Seiferas 2009, Section 5) and sufficient stages.
--
--   The argument:
--
--   1. `stranger_bound` gives: after `t` stages, j-strangers in each bag ≤
--
--   `γ · ε^(j-1) · capacity p k t l`.
--
--   2. At the finish level `k-2`, if `γ · capacity < 1`, then 0 strangers
--
--   at j=1 for every bag at that level (since stranger count is ℕ).
--
--   3. For descendant bags `c` at level `l > k-2`, we use j = l - (k-2) + 1.
--
--   The (l-k+3)-stranger bound at `c` is `γ · (εA)^(l-k+2) · cap(k-2)`, which is `< γ · cap(k-2) < 1` since `εA < 1`.
--
--   4. So all wires in `subregs pl b` (the subtree rooted at each level-(k-2)
--
--   bag) are native to `b`: their sorted ranks lie in `[b.lo, b.hi)`.
--
--   5. `stages_subregs_ordered` shows wire indices are ordered across
--
--   finish-level bags: smaller `x` coordinate implies smaller wire indices. Uses alternating emptiness (`bagCard_odd_eq_zero`) as the structural invariant.
--
--   6. `finishAt` applies `bitonicNetwork` (proved sorting network) to each
--
--   subtree.  Since the subtrees partition wires by rank intervals and wire indices are ordered across bags, local sorting yields global monotonicity.
--
--   Key theorem: `seiferasNetwork_sorts`
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bags/Sorts.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bags_Strange
import Definitions.Def_GirvingAKS_Bags_Defs
import Definitions.Def_GirvingAKS_Bitonic_Shrink
import Definitions.Def_GirvingAKS_Sort_Perm

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bags/Sorts.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Seiferas Network Sorts

  Proves that `seiferasNetwork p k` is a sorting network, assuming the
  stranger bound (Seiferas 2009, Section 5) and sufficient stages.

  The argument:
  1. `stranger_bound` gives: after `t` stages, j-strangers in each bag ≤
     `γ · ε^(j-1) · capacity p k t l`.
  2. At the finish level `k-2`, if `γ · capacity < 1`, then 0 strangers
     at j=1 for every bag at that level (since stranger count is ℕ).
  3. For descendant bags `c` at level `l > k-2`, we use j = l - (k-2) + 1.
     The (l-k+3)-stranger bound at `c` is `γ · (εA)^(l-k+2) · cap(k-2)`,
     which is `< γ · cap(k-2) < 1` since `εA < 1`.
  4. So all wires in `subregs pl b` (the subtree rooted at each level-(k-2)
     bag) are native to `b`: their sorted ranks lie in `[b.lo, b.hi)`.
  5. `stages_subregs_ordered` shows wire indices are ordered across
     finish-level bags: smaller `x` coordinate implies smaller wire indices.
     Uses alternating emptiness (`bagCard_odd_eq_zero`) as the structural
     invariant.
  6. `finishAt` applies `bitonicNetwork` (proved sorting network) to each
     subtree.  Since the subtrees partition wires by rank intervals and
     wire indices are ordered across bags, local sorting yields global
     monotonicity.

  Key theorem: `seiferasNetwork_sorts`
-/


section

open Finset

/-! **Convergence: stranger bound forces nativeness** -/

/-- When the stranger bound's RHS is `< 1`, there are no j-strangers.
    Since `strangers` is a natural number and the bound gives
    `↑(strangers ...) ≤ γ · ε^(j-1) · capacity < 1`, the count must be 0. -/
theorem strangers_eq_zero_of_bound_lt_one (p : Params) (k : ℕ) (hk : 10 ≤ k)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k))
    (hperm : Function.Bijective perm₀)
    (t : ℕ)
    (ht : t ≤ numStages p k)
    (b : Bag k) (j : ℕ) (hj : 1 ≤ j)
    (hlt : p.γ * p.ε ^ (j - 1) * capacity p k t b.l < 1) :
    b.strangers j ((stages p k t).net.exec perm₀)
      ((stages p k t).value.regs b) = 0 := by
  have hbound := stranger_bound p k hk perm₀ hperm t ht b j hj
  have hlt1 : (b.strangers j ((stages p k t).net.exec perm₀)
      ((stages p k t).value.regs b) : ℚ) < 1 := hbound.trans_lt hlt
  have hlt2 : (b.strangers j ((stages p k t).net.exec perm₀)
      ((stages p k t).value.regs b) : ℕ) < 1 := by exact_mod_cast hlt1
  omega

/-- Zero j-strangers at bag `c` with `j = d + 1` means every wire in
    `pl.regs c` is native to `c.ancestor d`. -/
theorem all_native_ancestor_of_strangers_zero {k : ℕ} (c : Bag k) (d : ℕ)
    (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (S : Finset (Fin (2 ^ k)))
    (h : c.strangers (d + 1) perm S = 0) :
    ∀ r ∈ S, (c.ancestor d).Native r perm := by
  intro r hr
  by_contra h_not
  have hmem : r ∈ S.filter (fun r ↦ c.Strange (d + 1) r perm) := by
    simp only [Finset.mem_filter]
    exact ⟨hr, Or.inr (by simpa [Nat.add_sub_cancel] using h_not)⟩
  simp only [Bag.strangers, Finset.card_eq_zero] at h
  rw [h] at hmem
  simp at hmem

/-! **Converged placement** -/

/-- A placement is *converged* at level `l` if every wire in every subtree
    rooted at a level-`l` bag is native to that bag (with respect to `perm`).
    This uses `subregs` (the full subtree), not just `pl.regs b`. -/
def Placement.Converged {k : ℕ} (pl : Placement k) (l : ℕ)
    (perm : Fin (2 ^ k) → Fin (2 ^ k)) : Prop :=
  ∀ (b : Bag k), b.l = l → ∀ r ∈ subregs pl b, b.Native r perm

/-! **Helper lemmas for convergence proof** -/


/-- `ε * A < 1` follows from `(2εA)² < 1`. -/
private theorem εA_lt_one (p : Params) (h : (2 * p.ε * p.A) ^ 2 < 1) :
    p.ε * p.A < 1 := by
  have h1 : 0 < p.ε * p.A := mul_pos p.hε_pos (by linarith [p.hA])
  nlinarith [sq_nonneg (2 * p.ε * p.A)]

/-- Capacity at level `l` equals capacity at level `l₀` times `A^(l - l₀)`. -/
private theorem capacity_level_shift (p : Params) (k t l₀ l : ℕ)
    (h : l₀ ≤ l) :
    capacity p k t l = capacity p k t l₀ * p.A ^ (l - l₀) := by
  simp only [capacity]
  rw [show p.A ^ l = p.A ^ l₀ * p.A ^ (l - l₀) from by
    rw [← pow_add, Nat.add_sub_cancel' h]]
  ring

/-- The ancestor of a descendant is the root bag.
    When `c.l ≥ b.l` and `c.x / 2^(c.l - b.l) = b.x`,
    `c.ancestor(c.l - b.l) = b`. -/
private theorem ancestor_eq_of_desc {k : ℕ} (b c : Bag k)
    (hle : b.l ≤ c.l) (hdesc : c.x / 2 ^ (c.l - b.l) = b.x) :
    c.ancestor (c.l - b.l) = b := by
  ext
  · show c.l - (c.l - b.l) = b.l; omega
  · show c.x / 2 ^ (c.l - b.l) = b.x; exact hdesc

/-- Left child's x-coordinate divided by `2^(depth+1)` equals parent's quotient. -/
private theorem left_desc {k : ℕ} (c : Bag k) (b : Bag k)
    (hle : b.l ≤ c.l) (hdesc : c.x / 2 ^ (c.l - b.l) = b.x)
    (h : c.l < k) :
    (c.left h).x / 2 ^ ((c.left h).l - b.l) = b.x := by
  show 2 * c.x / 2 ^ (c.l + 1 - b.l) = b.x
  rw [show c.l + 1 - b.l = (c.l - b.l) + 1 from by omega,
      pow_succ, Nat.mul_comm (2 ^ _) 2, Nat.mul_div_mul_left _ _ (by omega : 0 < 2)]
  exact hdesc

/-- Right child's x-coordinate divided by `2^(depth+1)` equals parent's quotient. -/
private theorem right_desc {k : ℕ} (c : Bag k) (b : Bag k)
    (hle : b.l ≤ c.l) (hdesc : c.x / 2 ^ (c.l - b.l) = b.x)
    (h : c.l < k) :
    (c.right h).x / 2 ^ ((c.right h).l - b.l) = b.x := by
  show (2 * c.x + 1) / 2 ^ (c.l + 1 - b.l) = b.x
  rw [show c.l + 1 - b.l = (c.l - b.l) + 1 from by omega, pow_succ,
      Nat.mul_comm (2 ^ _) 2]
  -- (2*c.x + 1) / (2 * 2^d) where d = c.l - b.l
  -- = (2*c.x + 1) / (2 * 2^d)
  -- Since c.x / 2^d = b.x, write c.x = 2^d * b.x + r with r < 2^d
  -- Then 2*c.x + 1 = 2*(2^d*b.x + r) + 1 = 2*2^d*b.x + 2*r + 1
  -- and (2*2^d*b.x + 2*r + 1) / (2*2^d) = b.x since 2*r + 1 < 2*2^d
  set d := c.l - b.l
  have hD : 0 < 2 * 2 ^ d := by positivity
  have hr : c.x % 2 ^ d < 2 ^ d := Nat.mod_lt _ (by positivity)
  rw [← Nat.div_add_mod c.x (2 ^ d), hdesc,
      show 2 * (2 ^ d * b.x + c.x % 2 ^ d) + 1
        = (2 * (c.x % 2 ^ d) + 1) + b.x * (2 * 2 ^ d) from by ring,
      Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt (by omega), Nat.zero_add]

/-- The stranger bound is `< 1` for any descendant of a finish-level bag,
    using `j = c.l - b.l + 1`. -/
private theorem stranger_bound_desc_lt_one (p : Params) (k t : ℕ)
    (b c : Bag k) (hle : b.l ≤ c.l)
    (hconv : p.γ * capacity p k t b.l < 1) :
    p.γ * p.ε ^ (c.l - b.l) * capacity p k t c.l < 1 := by
  rw [capacity_level_shift p k t b.l c.l hle]
  have hεA := εA_lt_one p p.h2εA
  calc p.γ * p.ε ^ (c.l - b.l) * (capacity p k t b.l * p.A ^ (c.l - b.l))
      = p.γ * capacity p k t b.l * (p.ε * p.A) ^ (c.l - b.l) := by ring
    _ ≤ p.γ * capacity p k t b.l * 1 := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_one₀ (mul_nonneg p.hε_pos.le (by linarith [p.hA])) hεA.le
        · exact mul_nonneg p.hγ_pos.le (capacity_pos p k t b.l).le
    _ = p.γ * capacity p k t b.l := mul_one _
    _ < 1 := hconv

/-- All wires in `subregs pl c` are native to bag `b`, when `c` is a descendant
    of `b` and the stranger bound forces zero strangers at each level.
    By induction on `k - c.l`. -/
private theorem subregs_all_native {k : ℕ}
    (pl : Placement k) (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (b c : Bag k) (hle : b.l ≤ c.l) (hdesc : c.x / 2 ^ (c.l - b.l) = b.x)
    (hstrange : ∀ (d : Bag k), b.l ≤ d.l → d.x / 2 ^ (d.l - b.l) = b.x →
      c.l ≤ d.l → d.l ≤ k →
      d.strangers (d.l - b.l + 1) perm (pl.regs d) = 0) :
    ∀ r ∈ subregs pl c, b.Native r perm := by
  unfold subregs
  split
  case isTrue h =>
    -- c.l < k: subregs = pl.regs c ∪ subregs(left) ∪ subregs(right)
    intro r hr
    simp only [Finset.mem_union] at hr
    -- Get nativeness for pl.regs c
    have hregs : ∀ r ∈ pl.regs c, b.Native r perm := by
      have hzero := hstrange c hle hdesc (le_refl _) c.hl
      intro r' hr'
      have := all_native_ancestor_of_strangers_zero c (c.l - b.l) perm _ hzero r' hr'
      rwa [ancestor_eq_of_desc b c hle hdesc] at this
    rcases hr with ((hr | hr) | hr)
    · exact hregs r hr
    · -- r ∈ subregs pl (c.left h)
      exact subregs_all_native pl perm b (c.left h)
        (by show b.l ≤ c.l + 1; omega) (left_desc c b hle hdesc h)
        (fun d hle' hdesc' hge hdk ↦
          hstrange d hle' hdesc' (by change c.l + 1 ≤ d.l at hge; omega) hdk) r hr
    · -- r ∈ subregs pl (c.right h)
      exact subregs_all_native pl perm b (c.right h)
        (by show b.l ≤ c.l + 1; omega) (right_desc c b hle hdesc h)
        (fun d hle' hdesc' hge hdk ↦
          hstrange d hle' hdesc' (by change c.l + 1 ≤ d.l at hge; omega) hdk) r hr
  case isFalse h =>
    -- c.l ≥ k (leaf): subregs = pl.regs c
    intro r hr
    have hzero := hstrange c hle hdesc (le_refl _) c.hl
    have := all_native_ancestor_of_strangers_zero c (c.l - b.l) perm _ hzero r hr
    rwa [ancestor_eq_of_desc b c hle hdesc] at this
termination_by k - c.l
decreasing_by all_goals show k - (c.l + 1) < k - c.l; omega

/-- When `γ · capacity < 1` at the finish level and `εA < 1`, every wire
    in every subtree at level k-2 is native to the subtree root.

    For a descendant `c` at level `l ≥ k-2`, we use the stranger bound with
    `j = l - (k-2) + 1`.  A `j`-stranger at `c` is not native to
    `c.ancestor(j-1) = b` (the level-(k-2) root).  The bound is
    `γ · ε^(l-k+2) · capacity(l) = γ · (εA)^(l-k+2) · capacity(k-2)`.
    Since `εA < 1` (from `(2εA)² < 1`), this is `< γ · capacity(k-2) < 1`,
    so all wires in `pl.regs c` are native to `b`. -/
theorem converged_of_stranger_bound (p : Params) (k : ℕ) (hk : 10 ≤ k)
    (perm₀ : Fin (2 ^ k) → Fin (2 ^ k))
    (hperm : Function.Bijective perm₀)
    (t : ℕ)
    (ht : t ≤ numStages p k)
    (hconv : p.γ * capacity p k t ((k - 3)) < 1) :
    (stages p k t).value.Converged ((k - 3))
      ((stages p k t).net.exec perm₀) := by
  set pl := (stages p k t).value
  set perm := (stages p k t).net.exec perm₀
  -- Get the full stranger bound
  have hstrange := stranger_bound p k hk perm₀ hperm t ht
  -- Prove convergence
  intro b hbl r hr
  refine subregs_all_native pl perm b b (le_refl _) (by simp [Nat.div_one])
    (fun d hle hdesc_d _ hdk ↦ ?_) r hr
  -- Need: for all descendants d, strangers(d, d.l - b.l + 1) = 0
  have hconv' : p.γ * capacity p k t b.l < 1 := hbl ▸ hconv
  have hlt : p.γ * p.ε ^ (d.l - b.l) * capacity p k t d.l < 1 :=
    stranger_bound_desc_lt_one p k t b d hle hconv'
  have hbound := hstrange d (d.l - b.l + 1) (by omega)
  have hlt1 : (d.strangers (d.l - b.l + 1) perm (pl.regs d) : ℚ) < 1 :=
    hbound.trans_lt (by rwa [Nat.add_sub_cancel])
  have hlt2 : (d.strangers (d.l - b.l + 1) perm (pl.regs d) : ℕ) < 1 := by
    exact_mod_cast hlt1
  omega

/-! **Sublemmas for finishAt sorting proof** -/

/-- Every element of `subregs pl b` comes from `pl.regs c` for some descendant `c` of `b`. -/
private theorem mem_subregs_exists_bag {k : ℕ} (pl : Placement k)
    (b : Bag k) {r : Fin (2 ^ k)} (hr : r ∈ subregs pl b) :
    ∃ c : Bag k, b.l ≤ c.l ∧ c.x / 2 ^ (c.l - b.l) = b.x ∧ r ∈ pl.regs c := by
  unfold subregs at hr
  split at hr
  case isTrue h =>
    simp only [Finset.mem_union] at hr
    rcases hr with ((hr | hr) | hr)
    · exact ⟨b, le_refl _, by simp, hr⟩
    · obtain ⟨c, hle, hdesc, hc⟩ := mem_subregs_exists_bag pl (b.left h) hr
      -- (b.left h).l = b.l + 1, (b.left h).x = 2 * b.x
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
    · obtain ⟨c, hle, hdesc, hc⟩ := mem_subregs_exists_bag pl (b.right h) hr
      -- (b.right h).l = b.l + 1, (b.right h).x = 2 * b.x + 1
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
theorem subregs_disjoint {k : ℕ} (pl : Placement k) (b₁ b₂ : Bag k)
    (hne : b₁ ≠ b₂) (hl : b₁.l = b₂.l) :
    Disjoint (subregs pl b₁) (subregs pl b₂) := by
  rw [Finset.disjoint_left]
  intro r hr₁ hr₂
  obtain ⟨c₁, hle₁, hdesc₁, hc₁⟩ := mem_subregs_exists_bag pl b₁ hr₁
  obtain ⟨c₂, hle₂, hdesc₂, hc₂⟩ := mem_subregs_exists_bag pl b₂ hr₂
  -- c₁ = c₂ by placement disjointness
  have hceq : c₁ = c₂ := by
    by_contra hne'
    exact Finset.disjoint_left.mp (pl.disjoint c₁ c₂ hne') hc₁ hc₂
  subst hceq
  -- c is a descendant of both b₁ and b₂ at the same level, so b₁ = b₂
  apply hne
  rw [hl] at hdesc₁
  exact Bag.ext hl (hdesc₁.symm.trans hdesc₂)

/-- If `c` is a descendant of `b` in the bag tree, then any register in
    `pl.regs c` belongs to `subregs pl b`. -/
private theorem mem_subregs_of_desc {k : ℕ} (pl : Placement k)
    (b c : Bag k) (hle : b.l ≤ c.l) (hdesc : c.x / 2 ^ (c.l - b.l) = b.x)
    {r : Fin (2 ^ k)} (hr : r ∈ pl.regs c) :
    r ∈ subregs pl b := by
  unfold subregs
  split
  case isTrue h =>
    -- b.l < k: subregs = pl.regs b ∪ subregs(left) ∪ subregs(right)
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- c.l = b.l, so c = b
      have hcb : c = b := by
        have : c.l - b.l = 0 := by omega
        rw [this, pow_zero, Nat.div_one] at hdesc
        exact Bag.ext heq.symm hdesc
      subst hcb
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hr)
    · -- c.l > b.l: c is in left or right subtree
      set d := c.l - b.l
      have hd1 : d ≥ 1 := by omega
      -- c.x / 2^(d-1) is either 2*b.x or 2*b.x + 1
      have hdiv : c.x / 2 ^ (d - 1) = 2 * b.x + c.x / 2 ^ (d - 1) % 2 := by
        have key : c.x / 2 ^ (d - 1) / 2 = b.x := by
          rw [Nat.div_div_eq_div_mul,
              show 2 ^ (d - 1) * 2 = 2 ^ d from by
                rw [← pow_succ, show d - 1 + 1 = d from by omega]]
          exact hdesc
        have := Nat.div_add_mod (c.x / 2 ^ (d - 1)) 2
        omega
      by_cases hbit : c.x / 2 ^ (d - 1) % 2 = 0
      · -- Left subtree
        have hdesc_left : c.x / 2 ^ (c.l - (b.left h).l) = (b.left h).x := by
          show c.x / 2 ^ (c.l - (b.l + 1)) = 2 * b.x
          rw [show c.l - (b.l + 1) = d - 1 from by omega]
          omega
        exact Finset.mem_union_left _
          (Finset.mem_union_right _
            (mem_subregs_of_desc pl (b.left h) c (by show b.l + 1 ≤ c.l; omega)
              hdesc_left hr))
      · -- Right subtree
        have hdesc_right : c.x / 2 ^ (c.l - (b.right h).l) = (b.right h).x := by
          show c.x / 2 ^ (c.l - (b.l + 1)) = 2 * b.x + 1
          rw [show c.l - (b.l + 1) = d - 1 from by omega]
          omega
        exact Finset.mem_union_right _
          (mem_subregs_of_desc pl (b.right h) c (by show b.l + 1 ≤ c.l; omega)
            hdesc_right hr)
  case isFalse h =>
    -- b.l ≥ k (leaf): c = b
    have heql : c.l = b.l := by have := c.hl; omega
    have hcb : c = b := by
      have : c.l - b.l = 0 := by omega
      rw [this, pow_zero, Nat.div_one] at hdesc
      exact Bag.ext heql hdesc
    subst hcb; exact hr
termination_by c.l - b.l
decreasing_by all_goals show c.l - (b.l + 1) < c.l - b.l; omega

/-- Every wire belongs to some `subregs` at level `l`, provided all bags at
    levels below `l` are empty. (Ancestor bags being empty ensures all wires
    are in bags at level ≥ `l`, hence captured by some subtree at level `l`.) -/
theorem subregs_cover {k : ℕ} (pl : Placement k) (l : ℕ)
    (hempty : ∀ b : Bag k, b.l < l → pl.regs b = ∅)
    (r : Fin (2 ^ k)) :
    ∃ b : Bag k, b.l = l ∧ r ∈ subregs pl b := by
  -- Every wire is in some bag
  obtain ⟨c, hc⟩ := pl.complete r
  -- The bag must be at level ≥ l (ancestor bags are empty)
  have hcl : l ≤ c.l := by
    by_contra h
    push_neg at h
    rw [hempty c h] at hc; simp at hc
  -- The ancestor of c at level l
  refine ⟨c.ancestor (c.l - l), ?_, ?_⟩
  · -- Level is l
    show c.l - (c.l - l) = l; omega
  · -- r ∈ subregs pl (ancestor)
    exact mem_subregs_of_desc pl (c.ancestor (c.l - l)) c
      (by show c.l - (c.l - l) ≤ c.l; omega)
      (by show c.x / 2 ^ (c.l - (c.l - (c.l - l))) = c.x / 2 ^ (c.l - l)
          rw [show c.l - (c.l - (c.l - l)) = c.l - l from by omega])
      hc

/-- Convergence implies rank partition: every wire in `subregs pl b` has
    rank in `[b.lo, b.hi)`. -/
theorem converged_rank_in_range {k : ℕ} (pl : Placement k)
    (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (b : Bag k) (l : ℕ) (hbl : b.l = l)
    (hconv : pl.Converged l perm)
    (r : Fin (2 ^ k)) (hr : r ∈ subregs pl b) :
    b.lo ≤ (perm r).val ∧ (perm r).val < b.hi := by
  exact (b.native_iff r perm).mp (hconv b hbl r hr)

/-! **Ancestor bags are empty after convergence**

When `γ · capacity(k-3) < 1` and `γ · A² ≥ 1` (from `p.hA2_le`), all bags
at levels below `k - 3` are empty:
- Wrong-parity levels are empty by `bagCard_odd_eq_zero`
- Same-parity levels have capacity < 1 (since `capacity(l) ≤ capacity(k-2)/A²`
  for levels `l < k - 3`, and `γ·A² ≥ 1`), so `bagCard = 0`

This ensures `subregs_cover` at the finish level: every wire is in some subtree. -/

/-- Capacity at an ancestor level is < 1 when `γ·A² ≥ 1` and convergence holds
    at level `k - 2`.  Uses `p.hA2_le` (non-strict `≥ 1`) from `Params`;
    the strict inequality comes from `hconv : γ · cap(k-2) < 1` propagating
    through the capacity chain. -/
private theorem capacity_ancestor_lt_one (p : Params) (k t : ℕ)
    (hconv : p.γ * capacity p k t ((k - 2)) < 1)
    (l : ℕ) (hlt : l < (k - 2)) (hdist : 2 ≤ (k - 2) - l) :
    capacity p k t l < 1 := by
  have hA_pos : (0 : ℚ) < p.A := by linarith [p.hA]
  -- capacity(cl) = capacity(l) * A^(cl-l)
  have hcl_eq := capacity_level_shift p k t l ((k - 2)) (by omega)
  -- So capacity(l) = capacity(cl) / A^(cl-l)
  have hApow_pos : (0 : ℚ) < p.A ^ ((k - 2) - l) := by positivity
  rw [hcl_eq] at hconv
  -- capacity(l) * A^(cl-l) < 1/γ
  -- capacity(l) < 1/(γ * A^(cl-l)) ≤ 1/(γ * A^2) ≤ 1
  have hcap_l := capacity_pos p k t l
  -- A^(cl-l) ≥ A^2
  have hApow_ge : p.A ^ ((k - 2) - l) ≥ p.A ^ 2 :=
    pow_le_pow_right₀ p.hA.le hdist
  -- γ * A^(cl-l) ≥ γ * A^2 ≥ 1
  have hgA : p.γ * p.A ^ ((k - 2) - l) ≥ p.γ * p.A ^ 2 :=
    mul_le_mul_of_nonneg_left hApow_ge p.hγ_pos.le
  have hgA_le : 1 ≤ p.γ * p.A ^ ((k - 2) - l) := le_trans p.hA2_le hgA
  -- capacity(l) * (γ * A^(cl-l)) < 1  [from hconv: γ * (cap(l) * A^(cl-l)) < 1]
  have : capacity p k t l * (p.γ * p.A ^ ((k - 2) - l)) < 1 := by linarith
  -- capacity(l) ≤ capacity(l) * (γ * A^(cl-l)) < 1
  calc capacity p k t l
      = capacity p k t l * 1 := (mul_one _).symm
    _ ≤ capacity p k t l * (p.γ * p.A ^ ((k - 2) - l)) :=
        mul_le_mul_of_nonneg_left hgA_le hcap_l.le
    _ < 1 := this

/-- After enough stages with convergence, all bags at levels below the finish
    level are empty (have 0 registers).

    Uses convergence at level `k - 2` (not `k - 3`).
    For any `l < k - 3`, we have `(k-2) - l ≥ 2` unconditionally,
    so no parity argument is needed.

    - `bagCard_odd_eq_zero`: wrong-parity levels have bagCard = 0
    - `bagCard_le_capacity` + `capacity_ancestor_lt_one`: same-parity levels
      have capacity < 1, so bagCard = 0
    - `bagCard_eq_card`: bagCard = actual register count -/
theorem ancestor_bags_empty (p : Params) (k : ℕ) (hk : 10 ≤ k) (t : ℕ)
    (ht : t ≤ numStages p k)
    (hconv_cl : p.γ * capacity p k t ((k - 2)) < 1) :
    ∀ (b : Bag k), b.l < (k - 3) →
      ((stages p k t).value.regs b) = ∅ := by
  intro b hbl
  -- bagCard = actual register count
  have hcard := bagCard_eq_card p k t b
  -- Show bagCard = 0, hence register set empty
  suffices h : bagCard p k t b.l = 0 by
    rw [← Finset.card_eq_zero]; rw [hcard]; exact h
  -- Case 1: wrong parity → 0 by bagCard_odd_eq_zero
  by_cases hpar : (t + b.l) % 2 ≠ 0
  · exact bagCard_odd_eq_zero p k (by omega) t b.l hpar
  · -- Case 2: same parity → capacity < 1 → bagCard ≤ capacity < 1 → bagCard = 0
    push_neg at hpar
    -- Distance from k-2 to l is ≥ 2 unconditionally (l < k-3)
    have hlt_cl : b.l < (k - 2) :=
      lt_of_lt_of_le hbl (by omega)
    have hdist : 2 ≤ (k - 2) - b.l := by
      omega
    have hcap_bound := bagCard_le_capacity p k hk t
      (numStages_hfl p k hk t ht) b.l
    have hcap_lt : capacity p k t b.l < 1 :=
      capacity_ancestor_lt_one p k t hconv_cl b.l hlt_cl hdist
    -- bagCard ≤ capacity < 1, so bagCard = 0 (natural number)
    have : (bagCard p k t b.l : ℚ) < 1 := hcap_bound.trans_lt hcap_lt
    have : bagCard p k t b.l < 1 := by exact_mod_cast this
    omega

/-! **Helper lemmas for finishAt proofs** -/

/-- `min`/`max` of values in an interval stay in the interval. -/
private theorem Comparator.apply_preserves_interval_inside {n : ℕ}
    (c : Comparator n) (v : Fin n → Fin n)
    (S : Finset (Fin n)) (lo hi : ℕ)
    (hv : ∀ s ∈ S, lo ≤ (v s).val ∧ (v s).val < hi)
    (hi_in : c.i ∈ S) (hj_in : c.j ∈ S) :
    ∀ s ∈ S, lo ≤ (c.apply v s).val ∧ (c.apply v s).val < hi := by
  intro s hs
  simp only [Comparator.apply]
  split_ifs with h1 h2
  · simp only [min_def]; split <;> [exact hv c.i hi_in; exact hv c.j hj_in]
  · simp only [max_def]; split <;> [exact hv c.j hj_in; exact hv c.i hi_in]
  · exact hv s hs

/-- Interval invariant is preserved across a comparator list when each
    comparator either has both endpoints in `S` or both endpoints outside `S`. -/
private theorem foldl_comparators_preserves_interval {n : ℕ}
    (cs : List (Comparator n)) (v : Fin n → Fin n)
    (S : Finset (Fin n)) (lo hi : ℕ)
    (hv : ∀ s ∈ S, lo ≤ (v s).val ∧ (v s).val < hi)
    (hcs : ∀ c ∈ cs, (c.i ∈ S ∧ c.j ∈ S) ∨ (c.i ∉ S ∧ c.j ∉ S)) :
    ∀ s ∈ S, lo ≤ (cs.foldl (fun acc c ↦ c.apply acc) v s).val ∧
             (cs.foldl (fun acc c ↦ c.apply acc) v s).val < hi := by
  induction cs generalizing v with
  | nil => exact hv
  | cons c cs ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro s hs
      rcases hcs c List.mem_cons_self with ⟨hi_in, hj_in⟩ | ⟨hi_out, hj_out⟩
      · exact Comparator.apply_preserves_interval_inside c v S lo hi hv hi_in hj_in s hs
      · simp only [Comparator.apply]
        have hne_i : s ≠ c.i := fun h => hi_out (h ▸ hs)
        have hne_j : s ≠ c.j := fun h => hj_out (h ▸ hs)
        rw [if_neg hne_i, if_neg hne_j]
        exact hv s hs
    · exact fun c' hc' ↦ hcs c' (List.mem_cons_of_mem _ hc')

/-- Every comparator in a scatter-embedded network has both endpoints
    in the embedding's range. -/
private theorem scatterEmbed_comparators_in_range {m n : ℕ}
    (net : ComparatorNetwork m) (f : Fin m ↪o Fin n)
    (c : Comparator n) (hc : c ∈ (net.scatterEmbed n f).comparators) :
    c.i ∈ Set.range f ∧ c.j ∈ Set.range f := by
  simp only [ComparatorNetwork.scatterEmbed, List.mem_map] at hc
  obtain ⟨c', _, rfl⟩ := hc
  exact ⟨⟨c'.i, rfl⟩, ⟨c'.j, rfl⟩⟩

/-- Every bag in `bagsAt k l hl` has level `l`. -/
theorem bagsAt_level {k l : ℕ} {hl : l ≤ k} {b : Bag k}
    (hb : b ∈ bagsAt k l hl) : b.l = l := by
  simp only [bagsAt, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hb
  obtain ⟨x, _, rfl⟩ := hb; rfl

/-! **Native partition + bitonic sort → sorted**

When all wires at level k-2 are native to their subtree root, the wires
are correctly partitioned by rank: all items in subtree `(k-2, x)` have
sorted rank in `[x · bagSize, (x+1) · bagSize)`, ranking below all items
in subtree `(k-2, x+1)`.  `finishAt` applies `bitonicNetwork` (a proved
sorting network) to each subtree, sorting items locally.  The global
ordering follows from the partition.

Thanks to `perm_principle`, it suffices to sort permutations `σ : Fin (2^k) → Fin (2^k)`.
The values ARE the ranks, so `Converged` directly gives the interval partition. -/

/-- After `finishAt`, values at positions in each bag's `subregs` remain
    in the bag's native interval `[b.lo, b.hi)`.

    Each comparator in `finishAt.net` connects two positions within the same
    bag's `subregs` (via scatter embedding).  Since `min`/`max` of values in
    an interval stay in the interval, the per-bag containment is preserved
    across all comparators. -/
private theorem finishAt_value_in_range (p : Params) (k : ℕ)
    (pl : Placement k) (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (hconv : pl.Converged ((k - 3)) perm)
    (b : Bag k) (hbl : b.l = (k - 3))
    (r : Fin (2 ^ k)) (hr : r ∈ subregs pl b) :
    b.lo ≤ ((finishAt p pl).net.exec perm r).val ∧
    ((finishAt p pl).net.exec perm r).val < b.hi := by
  -- finishAt.net.exec is foldl of comparators
  show b.lo ≤ ((finishAt p pl).net.comparators.foldl
    (fun acc c ↦ c.apply acc) perm r).val ∧
    ((finishAt p pl).net.comparators.foldl (fun acc c ↦ c.apply acc) perm r).val < b.hi
  apply foldl_comparators_preserves_interval _ _ (subregs pl b) b.lo b.hi _ _ r hr
  · -- Initial: convergence gives values in [b.lo, b.hi)
    intro s hs
    exact converged_rank_in_range pl perm b ((k - 3)) hbl hconv s hs
  · -- Each comparator respects subregs(b): both in or both out
    intro c hc
    -- c ∈ finishAt.net.comparators = (bags.map mkNet).flatMap comparators
    simp only [finishAt, Build.emit] at hc
    rw [List.mem_flatMap] at hc
    obtain ⟨net', hnet', hc'⟩ := hc
    rw [List.mem_map] at hnet'
    obtain ⟨b', hb'mem, rfl⟩ := hnet'
    -- c comes from bag b', both endpoints in subregs pl b'
    have ⟨hi_range, hj_range⟩ := scatterEmbed_comparators_in_range _ _ c hc'
    rw [Finset.range_orderEmbOfFin] at hi_range hj_range
    have hi_sub : c.i ∈ subregs pl b' := Finset.mem_coe.mp hi_range
    have hj_sub : c.j ∈ subregs pl b' := Finset.mem_coe.mp hj_range
    by_cases heq : b' = b
    · -- Same bag: both endpoints in subregs pl b
      left; subst heq; exact ⟨hi_sub, hj_sub⟩
    · -- Different bag: disjoint subregs, so both outside
      have hb'l : b'.l = (k - 3) := bagsAt_level hb'mem
      right
      have hdisj := subregs_disjoint pl b' b heq (by omega)
      exact ⟨Finset.disjoint_left.mp hdisj hi_sub, Finset.disjoint_left.mp hdisj hj_sub⟩

/-- `bagsAt` produces a list with no duplicates. -/
theorem bagsAt_nodup {k l : ℕ} (hl : l ≤ k) : (bagsAt k l hl).Nodup := by
  simp only [bagsAt]
  apply List.Nodup.map
  · intro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ heq
    simp only [Bag.mk.injEq] at heq
    exact Subtype.ext heq.2
  · exact List.nodup_attach.mpr List.nodup_range

/-- A bag at level `l` is in `bagsAt k l hl`. -/
theorem mem_bagsAt_of_level {k l : ℕ} (hl : l ≤ k) (b : Bag k) (hbl : b.l = l) :
    b ∈ bagsAt k l hl := by
  simp only [bagsAt, List.mem_map, List.mem_attach, true_and, Subtype.exists]
  refine ⟨b.x, List.mem_range.mpr (by subst hbl; exact b.hx), ?_⟩
  subst hbl; cases b; rfl

/-- In a sequential execution of scatter-embedded bitonic networks on pairwise
    disjoint register sets, position `f(i)` (where `f` is bag `b`'s embedding)
    gets value `bitonicNetwork.exec (v ∘ f) i`.

    Proof by induction on the bag list:
    - If `b` is head: `scatterEmbed_exec_inside` + later bags don't touch `f(i)`.
    - If `b` is in tail: head doesn't touch `f(i)` + IH with composition unchanged. -/
private theorem foldl_disjoint_scatter_inside {k : ℕ}
    (bags : List (Bag k)) (pl : Placement k)
    (v : Fin (2 ^ k) → Fin (2 ^ k))
    (b : Bag k) (hb : b ∈ bags) (hnodup : bags.Nodup)
    (hdisjoint : ∀ b₁ ∈ bags, ∀ b₂ ∈ bags, b₁ ≠ b₂ →
      Disjoint (subregs pl b₁) (subregs pl b₂))
    (i : Fin (subregs pl b).card) :
    let mkNet := fun b' ↦
      (bitonicNetwork (subregs pl b').card).scatterEmbed (2 ^ k)
        ((subregs pl b').orderEmbOfFin rfl)
    bags.foldl (fun v' b' ↦ (mkNet b').exec v') v
      ((subregs pl b).orderEmbOfFin rfl i) =
    (bitonicNetwork (subregs pl b).card).exec
      (v ∘ (subregs pl b).orderEmbOfFin rfl) i := by
  intro mkNet
  induction bags generalizing v with
  | nil => exact absurd hb List.not_mem_nil
  | cons b' rest ih =>
    simp only [List.foldl_cons]
    have fi_mem : (subregs pl b).orderEmbOfFin rfl i ∈ subregs pl b :=
      Finset.orderEmbOfFin_mem _ rfl i
    rcases List.mem_cons.mp hb with rfl | hb_rest
    · -- b' = b: apply scatterEmbed_exec_inside, then rest doesn't change
      have hb_notin : b ∉ rest := (List.nodup_cons.mp hnodup).1
      rw [ComparatorNetwork.foldl_exec_outside rest mkNet _ _ (fun b'' hb'' c hc ↦ ?_)]
      · exact ComparatorNetwork.scatterEmbed_exec_inside _ _ _ v i
      · -- comparators of mkNet(b'') don't touch fi
        have hne : b'' ≠ b := fun h ↦ hb_notin (h ▸ hb'')
        have hdisj := hdisjoint b'' (List.mem_cons_of_mem _ hb'') b
          List.mem_cons_self hne
        change c ∈ ((bitonicNetwork _).scatterEmbed _ _).comparators at hc
        simp only [ComparatorNetwork.scatterEmbed, List.mem_map] at hc
        obtain ⟨c', _, rfl⟩ := hc
        constructor
        · intro h
          exact absurd fi_mem (Finset.disjoint_left.mp hdisj
            (by rw [h]; exact Finset.orderEmbOfFin_mem _ rfl c'.i))
        · intro h
          exact absurd fi_mem (Finset.disjoint_left.mp hdisj
            (by rw [h]; exact Finset.orderEmbOfFin_mem _ rfl c'.j))
    · -- b' ≠ b: mkNet(b') doesn't change subregs(b) positions
      have hne : b' ≠ b := fun h ↦ (List.nodup_cons.mp hnodup).1 (h ▸ hb_rest)
      have hdisj' := hdisjoint b' List.mem_cons_self b
        (List.mem_cons.mpr (Or.inr hb_rest)) hne
      have hcomp : (mkNet b').exec v ∘ (subregs pl b).orderEmbOfFin rfl =
          v ∘ (subregs pl b).orderEmbOfFin rfl := by
        funext j; simp only [Function.comp]
        apply ComparatorNetwork.scatterEmbed_exec_outside
        rw [Finset.range_orderEmbOfFin]
        intro hmem
        exact absurd (Finset.mem_coe.mp hmem)
          (Finset.disjoint_right.mp hdisj' (Finset.orderEmbOfFin_mem _ rfl j))
      have step := ih ((mkNet b').exec v) hb_rest (List.nodup_cons.mp hnodup).2
        (fun b₁ hb₁ b₂ hb₂ h ↦ hdisjoint b₁ (List.mem_cons_of_mem _ hb₁) b₂
          (List.mem_cons_of_mem _ hb₂) h)
      rw [hcomp] at step; exact step

/-- After `finishAt`, each bag at the finish level is locally sorted:
    for `r₁ ≤ r₂` both in the same bag's `subregs`,
    `finishAt.exec perm r₁ ≤ finishAt.exec perm r₂`.

    Uses `foldl_disjoint_scatter_inside` to reduce to `bitonicNetwork.exec`,
    then `bitonicNetwork_sorts` for monotonicity. -/
private theorem finishAt_locally_sorted (p : Params) (k : ℕ)
    (pl : Placement k) (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (b : Bag k) (hbl : b.l = (k - 3))
    (r₁ r₂ : Fin (2 ^ k)) (hr₁ : r₁ ∈ subregs pl b) (hr₂ : r₂ ∈ subregs pl b)
    (hle : r₁ ≤ r₂) :
    (finishAt p pl).net.exec perm r₁ ≤ (finishAt p pl).net.exec perm r₂ := by
  -- Get preimage indices under orderEmbOfFin
  set f := (subregs pl b).orderEmbOfFin rfl
  set iso := (subregs pl b).orderIsoOfFin rfl
  set i₁ := iso.symm ⟨r₁, hr₁⟩
  set i₂ := iso.symm ⟨r₂, hr₂⟩
  have hr₁_eq : f i₁ = r₁ := by show (iso (iso.symm ⟨r₁, hr₁⟩)).val = r₁; simp
  have hr₂_eq : f i₂ = r₂ := by show (iso (iso.symm ⟨r₂, hr₂⟩)).val = r₂; simp
  have hi_le : i₁ ≤ i₂ := iso.symm.monotone (Subtype.mk_le_mk.mpr hle)
  -- finishAt.net.exec = foldl of scatter-embedded networks
  set bags := bagsAt k ((k - 3)) ((by omega))
  set mkNet := fun b' ↦
    (bitonicNetwork (subregs pl b').card).scatterEmbed (2 ^ k)
      ((subregs pl b').orderEmbOfFin rfl)
  -- Show finishAt.net = ⟨(bags.map mkNet).flatMap comparators⟩
  have hnet : (finishAt p pl).net = ⟨(bags.map mkNet).flatMap ComparatorNetwork.comparators⟩ := by
    simp only [finishAt, Build.emit]; rfl
  -- Convert exec to foldl
  have hexec : ∀ r, (finishAt p pl).net.exec perm r =
      (bags.map mkNet).foldl (fun v' net ↦ net.exec v') perm r := by
    intro r; show (finishAt p pl).net.exec perm r = _
    rw [hnet, ComparatorNetwork.exec_flatMap]
  -- Convert (bags.map mkNet).foldl to bags.foldl
  have hfoldl_map : ∀ r, (bags.map mkNet).foldl (fun v' net ↦ net.exec v') perm r =
      bags.foldl (fun v' b' ↦ (mkNet b').exec v') perm r := by
    intro r; rw [List.foldl_map]
  -- Apply the disjoint scatter lemma
  have hb_mem : b ∈ bags := mem_bagsAt_of_level _ b hbl
  have hnodup : bags.Nodup := bagsAt_nodup _
  have hdisjoint : ∀ b₁ ∈ bags, ∀ b₂ ∈ bags, b₁ ≠ b₂ →
      Disjoint (subregs pl b₁) (subregs pl b₂) := by
    intro b₁ hb₁ b₂ hb₂ hne
    exact subregs_disjoint pl b₁ b₂ hne (by rw [bagsAt_level hb₁, bagsAt_level hb₂])
  rw [hexec, hfoldl_map, ← hr₁_eq,
    foldl_disjoint_scatter_inside bags pl perm b hb_mem hnodup hdisjoint i₁]
  rw [hexec, hfoldl_map, ← hr₂_eq,
    foldl_disjoint_scatter_inside bags pl perm b hb_mem hnodup hdisjoint i₂]
  -- Now: bitonicNetwork.exec (perm ∘ f) i₁ ≤ bitonicNetwork.exec (perm ∘ f) i₂
  exact bitonicNetwork_sorts _ _ (perm ∘ f) hi_le

/-- A converged placement at the finish level, followed by `finishAt`,
    produces a sorted permutation.  Since we work at type `Fin (2^k)`,
    the values are the ranks — no separate rank permutation needed.

    The proof uses:
    - Ordering ⇒ for distinct bags b₁.x < b₂.x, all wires in
      `subregs b₁` are < all wires in `subregs b₂`
    - Convergence + value preservation ⇒ output values stay in `[b.lo, b.hi)`
    - `bitonicNetwork_sorts` ⇒ local sort within each subtree
    - Rank partition + local sort + ordering ⇒ global monotonicity -/
theorem finishAt_sorts_perm (p : Params) (k : ℕ)
    (pl : Placement k)
    (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (hconv : pl.Converged ((k - 3)) perm)
    (hempty : ∀ b : Bag k, b.l < (k - 3) → pl.regs b = ∅)
    (hordered : ∀ (b₁ b₂ : Bag k), b₁.l = (k - 3) →
      b₂.l = (k - 3) → b₁.x < b₂.x →
      ∀ r₁ ∈ subregs pl b₁, ∀ r₂ ∈ subregs pl b₂,
        r₁.val < r₂.val) :
    Monotone ((finishAt p pl).net.exec perm) := by
  set result := (finishAt p pl).net.exec perm
  intro i j hij
  -- Find the bags containing wires i and j
  obtain ⟨bi, hbli, hri⟩ := subregs_cover pl ((k - 3)) hempty i
  obtain ⟨bj, hblj, hrj⟩ := subregs_cover pl ((k - 3)) hempty j
  by_cases hbag : bi = bj
  · -- Same bag: local sorting gives result i ≤ result j
    subst hbag
    exact finishAt_locally_sorted p k pl perm bi hbli i j hri hrj hij
  · -- Different bags: use ordering + value separation
    -- bi.x < bj.x (from i ≤ j + ordering, by contradiction)
    have hbi_lt_bj : bi.x < bj.x := by
      by_contra h
      push_neg at h
      -- bi.x ≥ bj.x and bi ≠ bj at same level → bi.x > bj.x
      have hgt : bi.x > bj.x := by
        rcases Nat.lt_or_eq_of_le h with h | h
        · exact h
        · exact absurd (Bag.ext (by omega) h.symm) hbag
      -- By ordering: j ∈ subregs(bj) and i ∈ subregs(bi) with bj.x < bi.x
      -- → j.val < i.val, contradicting i ≤ j
      have : j.val < i.val := hordered bj bi hblj hbli hgt j hrj i hri
      omega
    -- Values are in their bags' ranges (value preservation)
    have ⟨_, hvi_hi⟩ := finishAt_value_in_range p k pl perm hconv bi hbli i hri
    have ⟨hvj_lo, _⟩ := finishAt_value_in_range p k pl perm hconv bj hblj j hrj
    -- bi.hi ≤ bj.lo (from bi.x < bj.x at the same level)
    have hgap : bi.hi ≤ bj.lo := by
      simp only [Bag.lo, Bag.hi, Bag.size]
      rw [show bi.l = bj.l from by omega]
      exact Nat.mul_le_mul_right _ (by omega)
    -- result i < bi.hi ≤ bj.lo ≤ result j
    show result i ≤ result j
    exact_mod_cast (show (result i).val ≤ (result j).val from
      le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hvi_hi hgap) hvj_lo))

/-! **Subregs ordering at the finish level**

Wire indices in `subregs` are ordered across finish-level bags.  The proof
instantiates `converged_of_stranger_bound` with the identity permutation:
since `net.exec id = id` (monotone inputs are fixed by comparator networks),
convergence gives `r.val ∈ [b.lo, b.hi)` for each wire `r` in `subregs b`.
The gap `b₁.hi ≤ b₂.lo` for `b₁.x < b₂.x` at the same level then gives
`r₁.val < r₂.val`. -/

/-- Wire indices in `subregs` are ordered across finish-level bags:
    for `b₁.x < b₂.x`, every wire in `subregs b₁` is strictly less
    than every wire in `subregs b₂`.

    Proved by instantiating convergence with the identity permutation.
    Since `net.exec id = id` (`exec_eq_of_monotone`), convergence gives
    `r.val ∈ [b.lo, b.hi)`.  The interval gap for `b₁.x < b₂.x`
    yields `r₁.val < b₁.hi ≤ b₂.lo ≤ r₂.val`. -/
theorem stages_subregs_ordered (p : Params) (k : ℕ) (hk : 10 ≤ k)
    (hconv : p.γ * capacity p k (numStages p k) ((k - 3)) < 1)
    (b₁ b₂ : Bag k) (hbl₁ : b₁.l = (k - 3))
    (hbl₂ : b₂.l = (k - 3)) (hx : b₁.x < b₂.x)
    {r₁ r₂ : Fin (2 ^ k)}
    (hr₁ : r₁ ∈ subregs (stages p k (numStages p k)).value b₁)
    (hr₂ : r₂ ∈ subregs (stages p k (numStages p k)).value b₂) :
    r₁.val < r₂.val := by
  set t := numStages p k
  set pl := (stages p k t).value
  -- Instantiate convergence with the identity permutation
  have hid_bij : Function.Bijective (id : Fin (2 ^ k) → Fin (2 ^ k)) :=
    Function.bijective_id
  have hconv_id := converged_of_stranger_bound p k hk id hid_bij
    t (le_refl _) hconv
  -- net.exec id = id (monotone inputs are fixed by comparator networks)
  have hexec_id : (stages p k t).net.exec id = id :=
    ComparatorNetwork.exec_eq_of_monotone _ fun _ _ h ↦ h
  -- So pl.Converged ((k - 3)) id
  rw [hexec_id] at hconv_id
  -- Wire indices are in [b.lo, b.hi) (since id r = r)
  have ⟨h1lo, h1hi⟩ := converged_rank_in_range pl id b₁ _ hbl₁ hconv_id r₁ hr₁
  have ⟨h2lo, _⟩ := converged_rank_in_range pl id b₂ _ hbl₂ hconv_id r₂ hr₂
  simp only [Function.id_def] at h1lo h1hi h2lo
  -- b₁.hi ≤ b₂.lo (from b₁.x < b₂.x at the same level)
  have hgap : b₁.hi ≤ b₂.lo := by
    simp only [Bag.lo, Bag.hi, Bag.size]
    rw [show b₁.l = b₂.l from by omega]
    exact Nat.mul_le_mul_right _ (by omega)
  -- r₁.val < b₁.hi ≤ b₂.lo ≤ r₂.val
  omega

/-! **Top-level assembly** -/

/-- The full Seiferas sorting network sorts all inputs.

    Uses `perm_principle` to reduce to sorting permutations of `Fin (2^k)`.
    For each permutation `σ`:
    1. `converged_of_stranger_bound` shows all subtrees at the finish level
       are converged (wires native to their subtree root).
    2. `ancestor_bags_empty` shows all ancestor bags are empty.
    3. `stages_subregs_ordered` shows wire indices are ordered across
       finish-level bags (smaller `x` ⟹ smaller wire indices).
    4. `finishAt_sorts_perm` shows `finishAt` then sorts the permutation.

    Hypotheses (all on the abstract parameters `p`):
    - `hk`: k ≥ 10 (capacity base condition + tree structure)
    - Parameter constraints are fields of `Params` (including `hC_bound`, `hA2_le`) -/
theorem seiferasNetwork_sorts (p : Params) (k : ℕ) (hk : 10 ≤ k) :
    (seiferasNetwork p k).Sorts := by
  apply perm_principle
  intro σ
  set t := numStages p k
  have hconv := numStages_hconv p k
  -- converged_of_stranger_bound needs Function.Bijective, not Equiv.Perm
  have hσ_bij : Function.Bijective (σ : Fin (2 ^ k) → Fin (2 ^ k)) := σ.bijective
  have hconverged := converged_of_stranger_bound p k hk σ hσ_bij
    t (le_refl _) hconv
  -- Ancestor bags are empty (uses convergence at level k-2)
  have hconv_cl := numStages_hconv_cl p k
  have hempty := ancestor_bags_empty p k hk t (le_refl _) hconv_cl
  -- seiferasNetwork = (stages >>= finishAt).net
  -- exec decomposes: seiferasNetwork.exec σ = finishAt.exec (stages.exec σ)
  set pl := (stages p k t).value
  set perm := (stages p k t).net.exec (σ : Fin (2 ^ k) → Fin (2 ^ k))
  show Monotone ((stages p k t >>= fun pl ↦ finishAt p pl).net.exec σ)
  rw [Build.exec_bind]
  -- Goal: Monotone ((finishAt p pl).net.exec perm)
  -- Ordering: wire indices in subregs are ordered across finish-level bags
  have hordered : ∀ (b₁ b₂ : Bag k), b₁.l = (k - 3) →
      b₂.l = (k - 3) → b₁.x < b₂.x →
      ∀ r₁ ∈ subregs pl b₁, ∀ r₂ ∈ subregs pl b₂,
        r₁.val < r₂.val :=
    fun b₁ b₂ hbl₁ hbl₂ hx r₁ hr₁ r₂ hr₂ ↦
      stages_subregs_ordered p k hk hconv b₁ b₂ hbl₁ hbl₂ hx hr₁ hr₂
  exact finishAt_sorts_perm p k pl perm hconverged hempty hordered

end


