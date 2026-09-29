-- Prove2me | Definitions.Def_CK_CKLaneA1_BSCover
-- name    : CK_CKLaneA1_BSCover
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:35:43.971023+00:00
-- url     : https://prove2.me/theorems/8514a5de-fdca-474e-b4f4-e74b5ed7f9f1
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSCover` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSCover` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSCover` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSCover (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSCover.lean)

import Definitions.Def_CK_CKLaneA1_BSCellAtoms

/-!
# CKLaneA1.BSCover — strips, cover checker, and the both-small pointwise theorem
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
open GeneralCK.Certificates

local notation "sc" => (DyadicInterval.scale 64 : ℝ)

def r0 : RNode := ⟨0, 0⟩

def bsCellsCheck (n : ℕ) (L2 : DI) (s : BSStrip) : RNode → List BSCell → Bool
  | _, [] => true
  | A, c :: rest => bsCellCheck n L2 s A c.r c.two c.cd && bsCellsCheck n L2 s c.r rest

def rLast : RNode → List BSCell → RNode
  | A, [] => A
  | _, c :: rest => rLast c.r rest

theorem bsCellsCheck_sound {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {s : BSStrip}
    (hs : bsStripOK n L2 s = true) :
    ∀ (cells : List BSCell) (A : RNode), bsCellsCheck n L2 s A cells = true →
    ∀ {u w : ℝ}, 0 < u → u < w → s.lo ≤ w → w ≤ s.hi → (A.ra:ℝ)/sc ≤ u/w →
      u/w ≤ ((rLast A cells).ra:ℝ)/sc → cells ≠ [] →
      0 < actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  intro cells
  induction cells with
  | nil => intro A _ u w _ _ _ _ _ _ hne; exact absurd rfl hne
  | cons c rest ih =>
    intro A h u w hu huw hw1 hw2 hr1 hr2 _
    have h1 := Bool.and_eq_true_iff.mp h
    by_cases hrc : u/w ≤ (c.r.ra:ℝ)/sc
    · exact bs_cell_sound hL hs h1.1 hu huw hw1 hw2 hr1 hrc
    · have hlt : (c.r.ra:ℝ)/sc < u/w := lt_of_not_ge hrc
      cases rest with
      | nil =>
        change u/w ≤ (c.r.ra:ℝ)/sc at hr2
        linarith
      | cons c' rest' =>
        exact ih c.r h1.2 hu huw hw1 hw2 hlt.le hr2 (List.cons_ne_nil _ _)

def bsStripFull (n : ℕ) (L2 : DI) (s : BSStrip) : Bool :=
  bsStripOK n L2 s && decide (s.cells ≠ []) && decide ((rLast r0 s.cells).ra = SCz) &&
    bsCellsCheck n L2 s r0 s.cells

theorem bsStrip_sound {n : ℕ} {s : BSStrip} (h : bsStripFull n (ln2Iv n) s = true)
    {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw1 : s.lo ≤ w) (hw2 : w ≤ s.hi) :
    0 < actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  have hL := ln2Iv_contains n
  have hsc := SC_pos
  simp only [bsStripFull, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs, hne⟩, hlast⟩, hcells⟩ := h
  have hw0 : 0 < w := hu.trans huw
  have hr1 : ((r0.ra:ℤ):ℝ)/sc ≤ u/w := by
    show ((0:ℤ):ℝ)/sc ≤ u/w
    rw [Int.cast_zero, zero_div]; exact (div_pos hu hw0).le
  have hr2 : u/w ≤ ((rLast r0 s.cells).ra:ℝ)/sc := by
    rw [hlast, SCz_real, div_self hsc.ne']
    exact ((div_lt_one hw0).mpr huw).le
  exact bsCellsCheck_sound hL hs s.cells r0 hcells hu huw hw1 hw2 hr1 hr2 hne

def bsChainOK : ℤ → List BSStrip → Bool
  | _, [] => true
  | a, s :: rest => decide (s.w1.xa = a) && bsChainOK s.w2.xa rest

def bsLastW : ℤ → List BSStrip → ℤ
  | a, [] => a
  | _, s :: rest => bsLastW s.w2.xa rest

def bsCoverOK (n : ℕ) (strips : List BSStrip) : Bool :=
  bsChainOK 0 strips && decide (SCz ≤ 40 * bsLastW 0 strips) && decide (strips ≠ []) &&
    strips.all (bsStripFull n (ln2Iv n))

theorem bs_chain_cover : ∀ (strips : List BSStrip) (a : ℤ), bsChainOK a strips = true →
    strips ≠ [] → ∀ {w : ℝ}, (a:ℝ)/sc ≤ w → w ≤ (bsLastW a strips : ℝ)/sc →
      ∃ s ∈ strips, s.lo ≤ w ∧ w ≤ s.hi := by
  intro strips
  induction strips with
  | nil => intro a _ hne; exact absurd rfl hne
  | cons s rest ih =>
    intro a h _ w hw1 hw2
    have h1 := Bool.and_eq_true_iff.mp h
    have hs1 : s.w1.xa = a := of_decide_eq_true h1.1
    by_cases hws : w ≤ s.hi
    · refine ⟨s, List.mem_cons_self .., ?_, hws⟩
      unfold BSStrip.lo; rw [hs1]; exact hw1
    · cases rest with
      | nil =>
        change w ≤ (s.w2.xa:ℝ)/sc at hw2
        exact absurd hw2 hws
      | cons s' rest' =>
        obtain ⟨t, ht, h1t, h2t⟩ := ih s.w2.xa h1.2 (List.cons_ne_nil _ _)
          (lt_of_not_ge hws).le hw2
        exact ⟨t, List.mem_cons_of_mem _ ht, h1t, h2t⟩

/-- **Pointwise both-small positivity from a checked cover.** -/
theorem bs_pointwise_of_cover {n : ℕ} {strips : List BSStrip} (h : bsCoverOK n strips = true) :
    ∀ u w : ℝ, 0 < u → u < w → w ≤ 1/40 →
      0 < actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  intro u w hu huw hw40
  have hsc := SC_pos
  simp only [bsCoverOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hchain, hlast⟩, hne⟩, hall⟩ := h
  have hw0 : 0 < w := hu.trans huw
  have hw1 : ((0:ℤ):ℝ) / sc ≤ w := by rw [Int.cast_zero, zero_div]; exact hw0.le
  have hw2 : w ≤ (bsLastW 0 strips : ℝ) / sc := by
    rw [le_div_iff₀ hsc]
    have : (SCz:ℝ) ≤ 40 * (bsLastW 0 strips : ℝ) := by exact_mod_cast hlast
    rw [SCz_real] at this
    nlinarith
  obtain ⟨s, hs, hsw1, hsw2⟩ := bs_chain_cover strips 0 hchain hne hw1 hw2
  exact bsStrip_sound (hall s hs) hu huw hsw1 hsw2

#print axioms bsCellsCheck_sound
#print axioms bsStrip_sound
#print axioms bs_chain_cover
#print axioms bs_pointwise_of_cover

end CKLaneA1


