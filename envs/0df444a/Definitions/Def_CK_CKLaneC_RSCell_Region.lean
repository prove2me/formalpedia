-- Prove2me | Definitions.Def_CK_CKLaneC_RSCell_Region
-- name    : CK_CKLaneC_RSCell_Region
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:41:39.903014+00:00
-- url     : https://prove2.me/theorems/7ceac801-0ed8-4d2a-9f31-9378a7512e29
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSCell.Region` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSCell.Region` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSCell.Region` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSCell.Region (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSCell/Region.lean)

import Definitions.Def_CK_CKLaneC_RSCell_Union
import Definitions.Def_CK_CKLaneC_RSCell_CellAPI

-- ===== source module CKLaneC.RSCell.Region =====
section

/-!
# Lane C, RA-stat interior: box predicate `RegionPos`, split-tree lemmas, and the bulk piece

`RegionPos blo bhi tlo thi slo shi` says that `rayGamma b t (b - bσ) > 0` at every point of the box with
`σ < 1` and `bσ ≤ 9/20` (the non-corner condition for `εc = 1/20`).

The cover proof is a tree of three constructors:
* `RegionPos.split_b`, `split_t` and `split_s` split a box at a midpoint;
* `RegionPos.excl` closes leaves that lie wholly inside the corner;
* the cell theorems close the certified leaves.
-/

namespace CKLaneC.RSCell

def RegionPos (blo bhi tlo thi slo shi : ℝ) : Prop :=
  ∀ b t σ : ℝ, blo ≤ b → b ≤ bhi → tlo ≤ t → t ≤ thi → slo ≤ σ → σ ≤ shi → σ < 1 → b * σ ≤ 9 / 20 →
    0 < CKLaneN23.RS.rayGamma b t (b - b * σ)

theorem RegionPos.split_b {blo bhi tlo thi slo shi : ℝ} (m : ℝ) (h1 : RegionPos blo m tlo thi slo shi)
    (h2 : RegionPos m bhi tlo thi slo shi) : RegionPos blo bhi tlo thi slo shi := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs hu
  rcases le_total b m with h | h
  · exact h1 b t σ hb0 h ht0 ht1 hs0 hs1 hs hu
  · exact h2 b t σ h hb1 ht0 ht1 hs0 hs1 hs hu

theorem RegionPos.split_t {blo bhi tlo thi slo shi : ℝ} (m : ℝ) (h1 : RegionPos blo bhi tlo m slo shi)
    (h2 : RegionPos blo bhi m thi slo shi) : RegionPos blo bhi tlo thi slo shi := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs hu
  rcases le_total t m with h | h
  · exact h1 b t σ hb0 hb1 ht0 h hs0 hs1 hs hu
  · exact h2 b t σ hb0 hb1 h ht1 hs0 hs1 hs hu

theorem RegionPos.split_s {blo bhi tlo thi slo shi : ℝ} (m : ℝ) (h1 : RegionPos blo bhi tlo thi slo m)
    (h2 : RegionPos blo bhi tlo thi m shi) : RegionPos blo bhi tlo thi slo shi := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs hu
  rcases le_total σ m with h | h
  · exact h1 b t σ hb0 hb1 ht0 ht1 hs0 h hs hu
  · exact h2 b t σ hb0 hb1 ht0 ht1 h hs1 hs hu

/-- A box wholly inside the corner (`blo · slo > 9/20`) has no admissible points. -/
theorem RegionPos.excl {blo bhi tlo thi slo shi : ℝ} (hb : 0 ≤ blo) (hs : 0 ≤ slo) (h : 9 / 20 < blo * slo) :
    RegionPos blo bhi tlo thi slo shi := by
  intro b t σ hb0 _ _ _ hs0 _ _ hu
  exfalso
  have : blo * slo ≤ b * σ := mul_le_mul hb0 hs0 hs (le_trans hb hb0)
  linarith

/-- A certified cell closes a leaf. -/
theorem RegionPos.of_cell {blo bhi tlo thi slo shi : ℝ}
    (h : ∀ b t σ : ℝ, blo ≤ b → b ≤ bhi → tlo ≤ t → t ≤ thi → slo ≤ σ → σ ≤ shi → σ < 1 →
      0 < CKLaneN23.RS.rayGamma b t (b - b * σ)) : RegionPos blo bhi tlo thi slo shi :=
  fun b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs _ => h b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs

/-- The bulk piece from a `RegionPos` on the root box `[b1,1/2] × [0,1] × [σ0,1]`. -/
theorem gammaBulk_of_region {S b1 σ0 : ℝ} (hσ0 : 0 ≤ σ0) (h : RegionPos b1 (1 / 2) 0 1 σ0 1) :
    GammaBulk S (1 / 20) b1 σ0 := by
  intro b t d ht0 ht1 hd0 hdb hb12 _ hεc hb1 hσ
  have hb0 : 0 < b := lt_trans hd0 hdb
  set σ := (b - d) / b with hσdef
  have hbσ : b * σ = b - d := by rw [hσdef]; field_simp
  have hd : b - b * σ = d := by rw [hbσ]; ring
  have hs0 : σ0 ≤ σ := by rw [hσdef, le_div_iff₀ hb0]; linarith
  have hs1 : σ < 1 := by rw [hσdef, div_lt_one hb0]; linarith
  have hu : b * σ ≤ 9 / 20 := by rw [hbσ]; linarith
  have := h b t σ hb1 hb12 ht0 ht1 hs0 hs1.le hs1 hu
  rw [hd] at this
  exact this.le

end CKLaneC.RSCell

end


