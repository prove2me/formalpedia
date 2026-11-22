-- Prove2me | Definitions.Def_GirvingAKS_Bags_Network
-- name    : GirvingAKS_Bags_Network
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:56:11.853286+00:00
-- url     : https://prove2.me/theorems/0387f9f2-6d92-4ac9-a29d-2ee0b282ed15
-- title:
--   AKS sorting networks (Seiferas port) — Bag Network Construction
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bags/Network.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Per-bag separator + split, and the `stage` function that applies one round of separation to all bags.
--
--   Key definitions:
--
--   - `BagSplit`: result of splitting a bag (three register sets)
--   - `split`: pure positional split of a register set by fringe size
--   - `separate`: emit a scatter-embedded separator via `Build` monad
--   - `separateAndSplit`: combine separator + positional split
--   - `allBags`: enumeration of all bags at depth `k`
--   - `stageRegs`: register reassignment after one stage
--   - `stage`: one stage of the sorting network construction
--   - `stages`: iterated stages from initial placement
--   - `seiferasNetwork`: full sorting network (stages + finish)
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bags/Network.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bags_Params
import Definitions.Def_GirvingAKS_Bags_Defs
import Definitions.Def_GirvingAKS_Separator_SepProof
import Definitions.Def_GirvingAKS_Sort_Build
import Definitions.Def_GirvingAKS_Bitonic_Shrink

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bags/Network.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bag Network Construction

  Per-bag separator + split, and the `stage` function that applies one
  round of separation to all bags.

  Key definitions:
  - `BagSplit`: result of splitting a bag (three register sets)
  - `split`: pure positional split of a register set by fringe size
  - `separate`: emit a scatter-embedded separator via `Build` monad
  - `separateAndSplit`: combine separator + positional split
  - `allBags`: enumeration of all bags at depth `k`
  - `stageRegs`: register reassignment after one stage
  - `stage`: one stage of the sorting network construction
  - `stages`: iterated stages from initial placement
  - `seiferasNetwork`: full sorting network (stages + finish)
-/


section


open Finset

variable {k : ℕ}

/-! **Split Result** -/

/-- Result of splitting a bag's registers into three disjoint groups:
    fringe items sent to parent, and middle items sent to left/right children. -/
structure BagSplit (k : ℕ) where
  toParent : Finset (Fin (2 ^ k))
  toLeft : Finset (Fin (2 ^ k))
  toRight : Finset (Fin (2 ^ k))

/-! **Positional Split** -/

/-- Split a register set into three groups by sorted position and fringe size.

    Registers are sorted by their `Fin` value (via `orderEmbOfFin`), giving
    a canonical wire ordering. With `s = regs.card` and `h = s / 2 - f`:
    - `toParent`: sorted positions `< f` or `≥ f + 2h` (fringe from both ends)
    - `toLeft`: sorted positions in `[f, f + h)` (middle-left)
    - `toRight`: sorted positions in `[f + h, f + 2h)` (middle-right)

    The caller chooses `f` based on Seiferas parameters:
    - **Root** (`level = 0`): `f = 0` — no fringe, even split
    - **Interior**: `f = ⌊λ·cap⌋` — fringe captures strangers
    - **Leaf**: `f = s / 2` — everything to parent -/
def split (regs : Finset (Fin (2 ^ k))) (f : ℕ) : BagSplit k :=
  let wm := regs.orderEmbOfFin rfl
  let s := regs.card
  let h := s / 2 - f
  { toParent := (univ.filter (fun j : Fin s ↦ j.val < f ∨ f + 2 * h ≤ j.val)).image wm
    toLeft := (univ.filter (fun j : Fin s ↦ f ≤ j.val ∧ j.val < f + h)).image wm
    toRight := (univ.filter (fun j : Fin s ↦ f + h ≤ j.val ∧ j.val < f + 2 * h)).image wm }

/-! **Split Partition Lemmas** -/

private theorem split_image_subset (regs : Finset (Fin (2 ^ k)))
    (P : Fin regs.card → Prop) [DecidablePred P] :
    (univ.filter P).image (regs.orderEmbOfFin rfl) ⊆ regs := by
  intro x hx
  simp only [mem_image, mem_filter, mem_univ, true_and] at hx
  obtain ⟨j, _, rfl⟩ := hx
  exact orderEmbOfFin_mem regs rfl j

/-- Every element of `regs` lands in one of the three parts of `split`. -/
theorem split_covers (regs : Finset (Fin (2 ^ k))) (f : ℕ)
    {i : Fin (2 ^ k)} (hi : i ∈ regs) :
    i ∈ (split regs f).toParent ∨ i ∈ (split regs f).toLeft ∨
    i ∈ (split regs f).toRight := by
  simp only [split, mem_image, mem_filter, mem_univ, true_and]
  have hmem : i ∈ Set.range (regs.orderEmbOfFin rfl) := by
    rw [range_orderEmbOfFin]; exact hi
  obtain ⟨j, hj⟩ := hmem
  by_cases hlt : j.val < f
  · exact .inl ⟨j, .inl hlt, hj⟩
  · by_cases hlt2 : j.val < f + (regs.card / 2 - f)
    · exact .inr (.inl ⟨j, ⟨by omega, hlt2⟩, hj⟩)
    · by_cases hlt3 : j.val < f + 2 * (regs.card / 2 - f)
      · exact .inr (.inr ⟨j, ⟨by omega, hlt3⟩, hj⟩)
      · exact .inl ⟨j, .inr (by omega), hj⟩

theorem split_toParent_subset (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    (split regs f).toParent ⊆ regs := split_image_subset regs _

theorem split_toLeft_subset (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    (split regs f).toLeft ⊆ regs := split_image_subset regs _

theorem split_toRight_subset (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    (split regs f).toRight ⊆ regs := split_image_subset regs _

/-- When `f ≥ s/2`, both `toLeft` and `toRight` are empty (the middle has width 0). -/
theorem split_leaf (regs : Finset (Fin (2 ^ k))) (f : ℕ) (hf : regs.card / 2 ≤ f) :
    (split regs f).toLeft = ∅ ∧ (split regs f).toRight = ∅ := by
  simp only [split, Nat.sub_eq_zero_of_le hf, Nat.add_zero]
  constructor <;> (rw [image_eq_empty, filter_eq_empty_iff]; intro j _; omega)

private theorem split_image_disjoint (regs : Finset (Fin (2 ^ k)))
    (P Q : Fin regs.card → Prop) [DecidablePred P] [DecidablePred Q]
    (hdisj : ∀ j, P j → Q j → False) :
    Disjoint ((univ.filter P).image (regs.orderEmbOfFin rfl))
             ((univ.filter Q).image (regs.orderEmbOfFin rfl)) := by
  rw [disjoint_left]
  intro x hxP hxQ
  simp only [mem_image, mem_filter, mem_univ, true_and] at hxP hxQ
  obtain ⟨j₁, hj₁P, rfl⟩ := hxP
  obtain ⟨j₂, hj₂Q, hj₂eq⟩ := hxQ
  exact hdisj j₁ hj₁P ((regs.orderEmbOfFin rfl).injective hj₂eq.symm ▸ hj₂Q)

theorem split_toParent_toLeft_disjoint (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    Disjoint (split regs f).toParent (split regs f).toLeft :=
  split_image_disjoint regs _ _ (fun _ h1 h2 ↦ by obtain h1 | h1 := h1 <;> omega)

theorem split_toParent_toRight_disjoint (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    Disjoint (split regs f).toParent (split regs f).toRight :=
  split_image_disjoint regs _ _ (fun _ h1 h2 ↦ by obtain h1 | h1 := h1 <;> omega)

theorem split_toLeft_toRight_disjoint (regs : Finset (Fin (2 ^ k))) (f : ℕ) :
    Disjoint (split regs f).toLeft (split regs f).toRight :=
  split_image_disjoint regs _ _ (fun _ h1 h2 ↦ by omega)

/-! **Separator Application** -/

/-- Apply a separator to a register set via scatter embedding.
    Uses `separatorNet γₑ ε` directly (not via `SeparatorFamily`), where `γₑ`
    is the effective separator fraction for this bag. The caller computes `γₑ`
    to absorb the capacity/bagCard gap (Seiferas 2009, p.7). -/
def separate (γₑ ε : ℚ) (hγₑ : 0 < γₑ) (hε : 0 < ε)
    (regs : Finset (Fin (2 ^ k))) :
    Build (2 ^ k) Unit :=
  let s := regs.card
  let emb : Fin (2 * (s / 2)) ↪o Fin (2 ^ k) :=
    (Fin.castLEOrderEmb (by omega : 2 * (s / 2) ≤ s)).trans (regs.orderEmbOfFin rfl)
  Build.emit ((separatorNet γₑ ε hγₑ hε (s / 2)).scatterEmbed (2 ^ k) emb)

/-- Apply a separator to a register set, then split by sorted position.
    Emits the separator comparators via `Build` and returns the split. -/
def separateAndSplit (γₑ ε : ℚ) (hγₑ : 0 < γₑ) (hε : 0 < ε)
    (regs : Finset (Fin (2 ^ k))) (f : ℕ) : Build (2 ^ k) (BagSplit k) := do
  separate γₑ ε hγₑ hε regs
  return split regs f

/-! **Rebag after Stage** -/

/-- Reassign registers after one stage. Each bag receives:
    - `toParent` from its left and right children
    - `toLeft` or `toRight` from its parent (depending on parity of `b.x`)
    - Root keeps its own `toParent` (no parent to receive it) -/
def stageRegs (splitOf : Bag k → BagSplit k) (b : Bag k) : Finset (Fin (2 ^ k)) :=
  let fromChildren :=
    if h : b.l < k then
      (splitOf (b.left h)).toParent ∪ (splitOf (b.right h)).toParent
    else ∅
  let fromParent :=
    if b.l = 0 then (splitOf b).toParent
    else if b.x % 2 = 0 then (splitOf b.parent).toLeft
    else (splitOf b.parent).toRight
  fromChildren ∪ fromParent

/-! **Rebag Correctness** -/

/-- Completeness: every wire ends up in some bag after stageRegs. -/
theorem stageRegs_complete (pl : Placement k) (splitOf : Bag k → BagSplit k)
    (hcovers : ∀ c, ∀ i ∈ pl.regs c,
      i ∈ (splitOf c).toParent ∨ i ∈ (splitOf c).toLeft ∨
      i ∈ (splitOf c).toRight)
    (hleaf : ∀ c : Bag k, ¬(c.l < k) →
      (splitOf c).toLeft = ∅ ∧ (splitOf c).toRight = ∅) :
    ∀ i, ∃ b, i ∈ stageRegs splitOf b := by
  intro i
  obtain ⟨c, hc⟩ := pl.complete i
  rcases hcovers c i hc with hp | hl | hr
  · -- toParent: root keeps it, non-root → parent receives via fromChildren
    by_cases hcl : c.l = 0
    · exact ⟨c, by simp only [stageRegs, hcl, ite_true, mem_union]; right; exact hp⟩
    · have hcl' : 1 ≤ c.l := by omega
      have hpl : c.parent.l < k := by
        have := c.hl; unfold Bag.parent; simp; omega
      refine ⟨c.parent, ?_⟩
      simp only [stageRegs, mem_union]
      left; rw [dif_pos hpl]
      by_cases heven : c.x % 2 = 0
      · rw [Bag.parent_left_eq c hcl' heven hpl]; exact mem_union_left _ hp
      · rw [Bag.parent_right_eq c hcl' heven hpl]; exact mem_union_right _ hp
  · -- toLeft: goes to c.left via fromParent
    by_cases hclk : c.l < k
    · refine ⟨c.left hclk, ?_⟩
      simp only [stageRegs, mem_union]; right
      have h1 : ¬((c.left hclk).l = 0) := by show ¬(c.l + 1 = 0); omega
      rw [if_neg h1, if_pos (Bag.left_x_mod c hclk), Bag.left_parent_eq]; exact hl
    · exact absurd ((hleaf c hclk).1 ▸ hl) (notMem_empty i)
  · -- toRight: goes to c.right via fromParent
    by_cases hclk : c.l < k
    · refine ⟨c.right hclk, ?_⟩
      simp only [stageRegs, mem_union]; right
      have h1 : ¬((c.right hclk).l = 0) := by show ¬(c.l + 1 = 0); omega
      rw [if_neg h1, if_neg (Bag.right_x_mod c hclk), Bag.right_parent_eq]; exact hr
    · exact absurd ((hleaf c hclk).2 ▸ hr) (notMem_empty i)

/-- If `x ∈ stageRegs splitOf b` and `x ∈ pl.regs c`, then `x` belongs to
    one of the three parts of `splitOf c`. -/
private theorem stageRegs_mem_part (pl : Placement k) (splitOf : Bag k → BagSplit k)
    (hsub_p : ∀ c, (splitOf c).toParent ⊆ pl.regs c)
    (hsub_l : ∀ c, (splitOf c).toLeft ⊆ pl.regs c)
    (hsub_r : ∀ c, (splitOf c).toRight ⊆ pl.regs c)
    {b : Bag k} {x : Fin (2 ^ k)} (hx : x ∈ stageRegs splitOf b)
    {c : Bag k} (hc : x ∈ pl.regs c) :
    x ∈ (splitOf c).toParent ∨ x ∈ (splitOf c).toLeft ∨
    x ∈ (splitOf c).toRight := by
  have src_eq : ∀ s, x ∈ pl.regs s → s = c :=
    fun s hs ↦ by_contra fun hne ↦ disjoint_left.mp (pl.disjoint s c hne) hs hc
  simp only [stageRegs, mem_union] at hx
  rcases hx with hfc | hfp
  · -- fromChildren
    by_cases h : b.l < k
    · rw [dif_pos h] at hfc
      rcases mem_union.mp hfc with hl | hr
      · left; rwa [src_eq _ (hsub_p _ hl)] at hl
      · left; rwa [src_eq _ (hsub_p _ hr)] at hr
    · rw [dif_neg h] at hfc; exact absurd hfc (notMem_empty _)
  · -- fromParent
    by_cases h0 : b.l = 0
    · rw [if_pos h0] at hfp; left; rwa [src_eq _ (hsub_p _ hfp)] at hfp
    · rw [if_neg h0] at hfp
      by_cases he : b.x % 2 = 0
      · rw [if_pos he] at hfp; right; left; rwa [src_eq _ (hsub_l _ hfp)] at hfp
      · rw [if_neg he] at hfp; right; right; rwa [src_eq _ (hsub_r _ hfp)] at hfp

/-- If `x ∈ (splitOf c).toParent` and `x ∈ stageRegs splitOf b`, then `b` is uniquely
    determined: `b = c` when `c` is root, `b = c.parent` otherwise. -/
private theorem toParent_dest (pl : Placement k) (splitOf : Bag k → BagSplit k)
    (hsub_p : ∀ c, (splitOf c).toParent ⊆ pl.regs c)
    (hsub_l : ∀ c, (splitOf c).toLeft ⊆ pl.regs c)
    (hsub_r : ∀ c, (splitOf c).toRight ⊆ pl.regs c)
    (hdisj_pl : ∀ c, Disjoint (splitOf c).toParent (splitOf c).toLeft)
    (hdisj_pr : ∀ c, Disjoint (splitOf c).toParent (splitOf c).toRight)
    {b : Bag k} {x : Fin (2 ^ k)} (hxb : x ∈ stageRegs splitOf b)
    {c : Bag k} (hc : x ∈ pl.regs c) (hxp : x ∈ (splitOf c).toParent) :
    if c.l = 0 then b = c else b = c.parent := by
  have src_eq : ∀ s, x ∈ pl.regs s → s = c :=
    fun s hs ↦ by_contra fun hne ↦ disjoint_left.mp (pl.disjoint s c hne) hs hc
  simp only [stageRegs, mem_union] at hxb
  rcases hxb with hfc | hfp
  · -- fromChildren: source is b.left or b.right = c, so b = c.parent
    by_cases h : b.l < k
    · rw [dif_pos h] at hfc
      rcases mem_union.mp hfc with hl | hr
      · have heq := src_eq _ (hsub_p _ hl) -- b.left h = c
        rw [if_neg (show ¬(c.l = 0) from by rw [← heq]; show ¬(b.l + 1 = 0); omega)]
        exact (heq ▸ Bag.left_parent_eq b h).symm
      · have heq := src_eq _ (hsub_p _ hr) -- b.right h = c
        rw [if_neg (show ¬(c.l = 0) from by rw [← heq]; show ¬(b.l + 1 = 0); omega)]
        exact (heq ▸ Bag.right_parent_eq b h).symm
    · rw [dif_neg h] at hfc; exact absurd hfc (notMem_empty _)
  · -- fromParent
    by_cases h0 : b.l = 0
    · rw [if_pos h0] at hfp
      have heq := src_eq _ (hsub_p _ hfp) -- b = c
      rw [if_pos (show c.l = 0 from by rw [← heq]; exact h0)]
      exact heq
    · rw [if_neg h0] at hfp
      by_cases he : b.x % 2 = 0
      · rw [if_pos he] at hfp
        have hxl : x ∈ (splitOf c).toLeft := by rwa [src_eq _ (hsub_l _ hfp)] at hfp
        exact absurd hxl (disjoint_left.mp (hdisj_pl c) hxp)
      · rw [if_neg he] at hfp
        have hxr : x ∈ (splitOf c).toRight := by rwa [src_eq _ (hsub_r _ hfp)] at hfp
        exact absurd hxr (disjoint_left.mp (hdisj_pr c) hxp)

/-- If `x ∈ (splitOf c).toLeft` and `x ∈ stageRegs splitOf b`, then `b = c.left`. -/
private theorem toLeft_dest (pl : Placement k) (splitOf : Bag k → BagSplit k)
    (hsub_p : ∀ c, (splitOf c).toParent ⊆ pl.regs c)
    (hsub_l : ∀ c, (splitOf c).toLeft ⊆ pl.regs c)
    (hsub_r : ∀ c, (splitOf c).toRight ⊆ pl.regs c)
    (hdisj_pl : ∀ c, Disjoint (splitOf c).toParent (splitOf c).toLeft)
    (hdisj_lr : ∀ c, Disjoint (splitOf c).toLeft (splitOf c).toRight)
    {b : Bag k} {x : Fin (2 ^ k)} (hxb : x ∈ stageRegs splitOf b)
    {c : Bag k} (hc : x ∈ pl.regs c) (hxl : x ∈ (splitOf c).toLeft) :
    ∃ h : c.l < k, b = c.left h := by
  have src_eq : ∀ s, x ∈ pl.regs s → s = c :=
    fun s hs ↦ by_contra fun hne ↦ disjoint_left.mp (pl.disjoint s c hne) hs hc
  simp only [stageRegs, mem_union] at hxb
  rcases hxb with hfc | hfp
  · by_cases h : b.l < k
    · rw [dif_pos h] at hfc
      rcases mem_union.mp hfc with hl | hr
      · exact absurd hxl (disjoint_left.mp (hdisj_pl c)
          (by rwa [src_eq _ (hsub_p _ hl)] at hl))
      · exact absurd hxl (disjoint_left.mp (hdisj_pl c)
          (by rwa [src_eq _ (hsub_p _ hr)] at hr))
    · rw [dif_neg h] at hfc; exact absurd hfc (notMem_empty _)
  · by_cases h0 : b.l = 0
    · rw [if_pos h0] at hfp
      exact absurd hxl (disjoint_left.mp (hdisj_pl c)
        (by rwa [src_eq _ (hsub_p _ hfp)] at hfp))
    · rw [if_neg h0] at hfp
      by_cases he : b.x % 2 = 0
      · rw [if_pos he] at hfp
        have heq := src_eq _ (hsub_l _ hfp) -- b.parent = c
        have hlev := congr_arg Bag.l heq
        have hidx := congr_arg Bag.x heq
        simp [Bag.parent] at hlev hidx
        have := b.hl
        exact ⟨by omega, Bag.ext (by show b.l = c.l + 1; omega)
                                   (by show b.x = 2 * c.x; omega)⟩
      · rw [if_neg he] at hfp
        have hxr : x ∈ (splitOf c).toRight := by rwa [src_eq _ (hsub_r _ hfp)] at hfp
        exact absurd hxr (disjoint_left.mp (hdisj_lr c) hxl)

/-- If `x ∈ (splitOf c).toRight` and `x ∈ stageRegs splitOf b`, then `b = c.right`. -/
private theorem toRight_dest (pl : Placement k) (splitOf : Bag k → BagSplit k)
    (hsub_p : ∀ c, (splitOf c).toParent ⊆ pl.regs c)
    (hsub_l : ∀ c, (splitOf c).toLeft ⊆ pl.regs c)
    (hsub_r : ∀ c, (splitOf c).toRight ⊆ pl.regs c)
    (hdisj_pr : ∀ c, Disjoint (splitOf c).toParent (splitOf c).toRight)
    (hdisj_lr : ∀ c, Disjoint (splitOf c).toLeft (splitOf c).toRight)
    {b : Bag k} {x : Fin (2 ^ k)} (hxb : x ∈ stageRegs splitOf b)
    {c : Bag k} (hc : x ∈ pl.regs c) (hxr : x ∈ (splitOf c).toRight) :
    ∃ h : c.l < k, b = c.right h := by
  have src_eq : ∀ s, x ∈ pl.regs s → s = c :=
    fun s hs ↦ by_contra fun hne ↦ disjoint_left.mp (pl.disjoint s c hne) hs hc
  simp only [stageRegs, mem_union] at hxb
  rcases hxb with hfc | hfp
  · by_cases h : b.l < k
    · rw [dif_pos h] at hfc
      rcases mem_union.mp hfc with hl | hr
      · exact absurd hxr (disjoint_left.mp (hdisj_pr c)
          (by rwa [src_eq _ (hsub_p _ hl)] at hl))
      · exact absurd hxr (disjoint_left.mp (hdisj_pr c)
          (by rwa [src_eq _ (hsub_p _ hr)] at hr))
    · rw [dif_neg h] at hfc; exact absurd hfc (notMem_empty _)
  · by_cases h0 : b.l = 0
    · rw [if_pos h0] at hfp
      exact absurd hxr (disjoint_left.mp (hdisj_pr c)
        (by rwa [src_eq _ (hsub_p _ hfp)] at hfp))
    · rw [if_neg h0] at hfp
      by_cases he : b.x % 2 = 0
      · rw [if_pos he] at hfp
        have hxl : x ∈ (splitOf c).toLeft := by rwa [src_eq _ (hsub_l _ hfp)] at hfp
        exact absurd hxl (disjoint_left.mp ((hdisj_lr c).symm) hxr)
      · rw [if_neg he] at hfp
        have heq := src_eq _ (hsub_r _ hfp) -- b.parent = c
        have hlev := congr_arg Bag.l heq
        have hidx := congr_arg Bag.x heq
        simp [Bag.parent] at hlev hidx
        have := b.hl
        exact ⟨by omega, Bag.ext (by show b.l = c.l + 1; omega)
                                   (by show b.x = 2 * c.x + 1; omega)⟩

/-- Disjointness: distinct bags have disjoint registers after stageRegs.
    Requires that each split part is a subset of the original bag's registers
    and that the three parts are pairwise disjoint. -/
theorem stageRegs_disjoint (pl : Placement k) (splitOf : Bag k → BagSplit k)
    (hsub_p : ∀ c, (splitOf c).toParent ⊆ pl.regs c)
    (hsub_l : ∀ c, (splitOf c).toLeft ⊆ pl.regs c)
    (hsub_r : ∀ c, (splitOf c).toRight ⊆ pl.regs c)
    (hdisj_pl : ∀ c, Disjoint (splitOf c).toParent (splitOf c).toLeft)
    (hdisj_pr : ∀ c, Disjoint (splitOf c).toParent (splitOf c).toRight)
    (hdisj_lr : ∀ c, Disjoint (splitOf c).toLeft (splitOf c).toRight) :
    ∀ a b, a ≠ b → Disjoint (stageRegs splitOf a) (stageRegs splitOf b) := by
  intro a b hab
  rw [disjoint_left]
  intro x hxa hxb
  obtain ⟨c, hc⟩ := pl.complete x
  have hpart := stageRegs_mem_part pl splitOf hsub_p hsub_l hsub_r hxa hc
  rcases hpart with hxp | hxl | hxr
  · -- x ∈ (splitOf c).toParent
    have ha := toParent_dest pl splitOf hsub_p hsub_l hsub_r hdisj_pl hdisj_pr hxa hc hxp
    have hb := toParent_dest pl splitOf hsub_p hsub_l hsub_r hdisj_pl hdisj_pr hxb hc hxp
    exact hab (by split_ifs at ha hb <;> (rw [ha]; exact hb.symm))
  · -- x ∈ (splitOf c).toLeft
    obtain ⟨_, ha⟩ := toLeft_dest pl splitOf hsub_p hsub_l hsub_r hdisj_pl hdisj_lr hxa hc hxl
    obtain ⟨_, hb⟩ := toLeft_dest pl splitOf hsub_p hsub_l hsub_r hdisj_pl hdisj_lr hxb hc hxl
    exact hab (ha ▸ hb ▸ rfl)
  · -- x ∈ (splitOf c).toRight
    obtain ⟨_, ha⟩ := toRight_dest pl splitOf hsub_p hsub_l hsub_r hdisj_pr hdisj_lr hxa hc hxr
    obtain ⟨_, hb⟩ := toRight_dest pl splitOf hsub_p hsub_l hsub_r hdisj_pr hdisj_lr hxb hc hxr
    exact hab (ha ▸ hb ▸ rfl)

/-! **Initial Placement** -/

/-- The initial placement: all `2^k` wires at the root bag, nothing elsewhere. -/
def start (k : ℕ) : Placement k where
  regs b := if b.l = 0 ∧ b.x = 0 then univ else ∅
  disjoint a b hab := by
    by_cases ha : a.l = 0 ∧ a.x = 0 <;> by_cases hb : b.l = 0 ∧ b.x = 0
    · exact absurd (Bag.ext (by omega) (by omega)) hab
    · rw [if_neg hb]; exact disjoint_bot_right
    · rw [if_neg ha]; exact disjoint_bot_left
    · rw [if_neg ha]; exact disjoint_bot_left
  complete i := ⟨Bag.root k, by simp [Bag.root]⟩

/-! **One Stage** -/

/-- One stage of the Seiferas sorting network (Section 5).
    Applies `separateAndSplit` to every bag, emitting the combined
    comparator network, then rebags via `stageRegs`.
    Each bag uses an effective separator fraction `γₑ = γ · capacity / n_local`
    where `n_local = 2 * (C / 2)` is the actual separator wire count.
    (Seiferas 2009, p.7: "various fractions λ, each at least as large"). -/
def stage (p : Params)
    (pl : Placement k) (t : ℕ) : Build (2 ^ k) (Placement k) := do
  let built : Bag k → Build (2 ^ k) (BagSplit k) := fun b ↦
    let regs := pl.regs b
    let γₑ := effectiveGamma p.γ (capacity p k t b.l) (2 * (regs.card / 2))
    separateAndSplit γₑ p.ε (effectiveGamma_pos p.hγ_pos (capacity_pos p k t b.l) _) p.hε_pos
      regs (fringe p k t b.l regs.card)
  let net : ComparatorNetwork (2 ^ k) :=
    ⟨(allBags k).flatMap fun b ↦ (built b).net.comparators⟩
  Build.emit net
  let splitOf := fun b ↦ (built b).value
  return ⟨stageRegs splitOf,
    stageRegs_disjoint pl splitOf
      (fun _ ↦ split_toParent_subset _ _)
      (fun _ ↦ split_toLeft_subset _ _)
      (fun _ ↦ split_toRight_subset _ _)
      (fun _ ↦ split_toParent_toLeft_disjoint _ _)
      (fun _ ↦ split_toParent_toRight_disjoint _ _)
      (fun _ ↦ split_toLeft_toRight_disjoint _ _),
    stageRegs_complete pl splitOf
      (fun _ _ hi ↦ split_covers _ _ hi)
      (fun c hc ↦ by
        apply split_leaf
        simp only [fringe]
        by_cases hcl : c.l = 0
        · simp only [hcl, ite_true]
          have hk : k = 0 := by have := c.hl; omega
          have hcard := (pl.regs c).card_le_univ
          subst hk; simp at hcard; omega
        · simp only [hcl, ite_false,
            show k ≤ c.l + 1 from by have := c.hl; omega, ite_true]
          omega)⟩

/-! **Stage Iteration** -/

/-- Run `t` stages from the initial placement, accumulating the
    combined comparator network. -/
def stages (p : Params) (k : ℕ) : ℕ → Build (2 ^ k) (Placement k)
  | 0 => pure (start k)
  | t + 1 => do
    let pl ← stages p k t
    stage p pl t

/-! **Finish Construction**

After running enough stages, all items converge toward their native positions.
The `finish` step picks a level, collects registers from each bag's subtree
into a single set, then applies bitonic sort to each subtree. Since subtrees
at the same level are disjoint, all sorts run in parallel. -/

/-- Collect all registers in bag `b` and its descendants (the subtree rooted at `b`). -/
def subregs (pl : Placement k) (b : Bag k) : Finset (Fin (2 ^ k)) :=
  if h : b.l < k then
    pl.regs b ∪ subregs pl (b.left h) ∪ subregs pl (b.right h)
  else
    pl.regs b
termination_by k - b.l
decreasing_by all_goals show k - (b.l + 1) < k - b.l; omega

/-- All bags at a fixed level `l`. -/
def bagsAt (k l : ℕ) (hl : l ≤ k) : List (Bag k) :=
  ((List.range (2 ^ l)).attach).map fun ⟨x, hx⟩ ↦
    ⟨l, x, hl, by rwa [List.mem_range] at hx⟩

/-- Apply bitonic sort to each subtree rooted at level `k - 3`. -/
def finishAt (_ : Params) (pl : Placement k) : Build (2 ^ k) Unit :=
  let bags := bagsAt k (k - 3) (by omega)
  let nets := bags.map fun b ↦
    let regs := subregs pl b
    ((bitonicNetwork regs.card).scatterEmbed (2 ^ k) (regs.orderEmbOfFin rfl))
  Build.emit ⟨nets.flatMap ComparatorNetwork.comparators⟩

/-! **Full Seiferas Network** -/

/-- The full Seiferas sorting network: run separator stages, then finish
    with bitonic sort on subtrees. Returns the accumulated comparator network. -/
def seiferasNetwork (p : Params) (k : ℕ) : ComparatorNetwork (2 ^ k) :=
  let build : Build (2 ^ k) Unit := do
    let pl ← stages p k (numStages p k)
    finishAt p pl
  build.net

end


