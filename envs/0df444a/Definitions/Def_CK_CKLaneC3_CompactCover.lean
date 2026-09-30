-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactCover
-- name    : CK_CKLaneC3_CompactCover
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:53:52.47129+00:00
-- url     : https://prove2.me/theorems/867b9b2e-0247-4b99-943c-d4f61ac5bbc9
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactCover` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactCover` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactCover` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactCover (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactCover.lean)

import Definitions.Def_CK_CKLaneC3_CompactCell
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRationalTreeBridgeKernel

-- ===== source module CKLaneC3.CompactCover =====
section

/-!
# Lane C3 — exact rational cover of a rectangle by certified cells and origin cells

A binary split tree over a rational domain (`qValid`, checked by `decide`) whose leaves,
in traversal order, are the rectangles of a list of tags.  A tag is either an origin
rectangle (`s1 + t1 ≤ 2/25`, owned by the origin owner) or a cubic cell certificate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.CompactCover

open Set GeneralCK GeneralCK.Certificates
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry E8TAxisRationalTreeBridgeKernel
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain CKLaneC3.CompactCell

abbrev Tag := RatRect ⊕ CellW

def tagRect : Tag → RatRect
  | .inl q => q
  | .inr w => ⟨w.s0, w.s1, w.t0, w.t1⟩

def tagOK (T : List (List Piece)) : Tag → Bool
  | .inl q => decide (q.s1 + q.t1 ≤ 2 / 25)
  | .inr w => w.check T

theorem qcover : ∀ (tree : Tree) (r : RatRect), qValid tree r →
    ∀ s t : ℝ, r.real.Covers s t → ∃ q ∈ qLeaves tree r, q.real.Covers s t := by
  intro tree
  induction tree with
  | leaf =>
    intro r _ s t h
    exact ⟨r, by simp [qLeaves], h⟩
  | splitS x left right ihl ihr =>
    intro r hv s t h
    rcases hv with ⟨_, _, hvl, hvr⟩
    by_cases hs : s ≤ (x : ℝ)
    · obtain ⟨q, hq, hc⟩ := ihl (qLeftS r x) hvl s t ⟨h.1, hs, h.2.2⟩
      exact ⟨q, by simp only [qLeaves, List.mem_append]; exact Or.inl hq, hc⟩
    · obtain ⟨q, hq, hc⟩ := ihr (qRightS r x) hvr s t ⟨le_of_lt (lt_of_not_ge hs), h.2.1, h.2.2⟩
      exact ⟨q, by simp only [qLeaves, List.mem_append]; exact Or.inr hq, hc⟩
  | splitT x lower upper ihl ihu =>
    intro r hv s t h
    rcases hv with ⟨_, _, hvl, hvu⟩
    by_cases ht : t ≤ (x : ℝ)
    · obtain ⟨q, hq, hc⟩ := ihl (qLowerT r x) hvl s t ⟨h.1, h.2.1, h.2.2.1, ht⟩
      exact ⟨q, by simp only [qLeaves, List.mem_append]; exact Or.inl hq, hc⟩
    · obtain ⟨q, hq, hc⟩ := ihu (qUpperT r x) hvu s t
        ⟨h.1, h.2.1, le_of_lt (lt_of_not_ge ht), h.2.2.2⟩
      exact ⟨q, by simp only [qLeaves, List.mem_append]; exact Or.inr hq, hc⟩

theorem positive_of_cover {T : List (List Piece)} (hT : TableValid T) {tree : Tree} {D : RatRect}
    {L : List Tag}
    (horigin : E8PositiveOn fun s t => s + t ≤ 2 / 25)
    (hv : qValid tree D) (hleaves : qLeaves tree D = L.map tagRect)
    (hok : L.all (tagOK T) = true) :
    ∀ s t : ℝ, E8Admissible s t → D.real.Covers s t → 0 < e8Delta e8Q s t := by
  intro s t hadm hcov
  obtain ⟨q, hq, hqc⟩ := qcover tree D hv s t hcov
  rw [hleaves] at hq
  obtain ⟨tag, htag, hrect⟩ := List.mem_map.mp hq
  have htok := List.all_eq_true.mp hok tag htag
  cases tag with
  | inl q' =>
    simp only [tagRect] at hrect
    subst hrect
    simp only [tagOK, decide_eq_true_eq] at htok
    apply horigin s t hadm
    have h1 : ((q'.s1 + q'.t1 : ℚ) : ℝ) ≤ ((2 / 25 : ℚ) : ℝ) := by exact_mod_cast htok
    push_cast at h1
    have hs := hqc.2.1
    have ht := hqc.2.2.2
    simp only [RatRect.real] at hs ht
    linarith
  | inr w =>
    simp only [tagRect] at hrect
    subst hrect
    simp only [tagOK] at htok
    apply CellW.check_sound hT htok s t
    simp only [RatRect.real, Rect.Covers] at hqc
    exact hqc

#print axioms qcover
#print axioms positive_of_cover

end CKLaneC3.CompactCover

end


