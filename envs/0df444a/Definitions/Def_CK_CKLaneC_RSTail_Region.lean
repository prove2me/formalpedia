-- Prove2me | Definitions.Def_CK_CKLaneC_RSTail_Region
-- name    : CK_CKLaneC_RSTail_Region
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:55:59.331506+00:00
-- url     : https://prove2.me/theorems/2f2e3783-af76-4549-b7e0-62bac26536e5
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSTail.Region` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSTail.Region` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSTail.Region` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSTail.Region (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSTail/Region.lean)

import Definitions.Def_CK_CKLaneC_RSCell_Union
import Definitions.Def_CK_CKLaneC_RSCell_Defs

-- ===== source module CKLaneC.RSTail.Region =====
section

/-!
# Lane C, RA-stat u-tail: region layer (shared with Lane R2b)

`TailPos b0 b1 t0 t1 s0 s1`: `rayGamma b t (b - bσ) > 0` on the box `b ∈ [b0,b1], t ∈ [t0,t1], σ ∈ [s0,s1]`, `σ > 0`
(`σ = u/b`; limit-layer boxes may start at `s0 = 0`). `TailPosI` is the integer-coded version (scale `one = 2^64`)
used by the compact cover: leaves are R2's cell theorems, splits share literal integer midpoints, and the root is
converted to real endpoints once. `gammaUTail_of_region` turns the root box `[3/65536,1/2] × [0,1] × [0,1/8]` into
`GammaUTail S εc (1/8)` for every `S ≥ 2·(3/65536)` (in particular `retainedCutoff = 1/10000`).
-/

namespace CKLaneC.RSTail

open CKLaneC.RSCell

def TailPos (b0 b1 t0 t1 s0 s1 : ℝ) : Prop :=
  ∀ b t σ : ℝ, b0 ≤ b → b ≤ b1 → t0 ≤ t → t ≤ t1 → s0 ≤ σ → σ ≤ s1 → 0 < σ →
    0 < CKLaneN23.RS.rayGamma b t (b - b * σ)

theorem TailPos.split_b {b0 b1 t0 t1 s0 s1 : ℝ} (m : ℝ) (h1 : TailPos b0 m t0 t1 s0 s1)
    (h2 : TailPos m b1 t0 t1 s0 s1) : TailPos b0 b1 t0 t1 s0 s1 := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs
  rcases le_total b m with h | h
  · exact h1 b t σ hb0 h ht0 ht1 hs0 hs1 hs
  · exact h2 b t σ h hb1 ht0 ht1 hs0 hs1 hs

theorem TailPos.split_t {b0 b1 t0 t1 s0 s1 : ℝ} (m : ℝ) (h1 : TailPos b0 b1 t0 m s0 s1)
    (h2 : TailPos b0 b1 m t1 s0 s1) : TailPos b0 b1 t0 t1 s0 s1 := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs
  rcases le_total t m with h | h
  · exact h1 b t σ hb0 hb1 ht0 h hs0 hs1 hs
  · exact h2 b t σ hb0 hb1 h ht1 hs0 hs1 hs

theorem TailPos.split_s {b0 b1 t0 t1 s0 s1 : ℝ} (m : ℝ) (h1 : TailPos b0 b1 t0 t1 s0 m)
    (h2 : TailPos b0 b1 t0 t1 m s1) : TailPos b0 b1 t0 t1 s0 s1 := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs
  rcases le_total σ m with h | h
  · exact h1 b t σ hb0 hb1 ht0 ht1 hs0 h hs
  · exact h2 b t σ hb0 hb1 ht0 ht1 h hs1 hs

/-- Integer-coded boxes (fixed point, scale `one = 2^64`). -/
def TailPosI (b0 b1 t0 t1 s0 s1 : Int) : Prop :=
  TailPos ((b0 : ℝ) / one) ((b1 : ℝ) / one) ((t0 : ℝ) / one) ((t1 : ℝ) / one) ((s0 : ℝ) / one) ((s1 : ℝ) / one)

theorem TailPosI.split_b {b0 b1 t0 t1 s0 s1 : Int} (m : Int) (h1 : TailPosI b0 m t0 t1 s0 s1)
    (h2 : TailPosI m b1 t0 t1 s0 s1) : TailPosI b0 b1 t0 t1 s0 s1 :=
  TailPos.split_b _ h1 h2

theorem TailPosI.split_t {b0 b1 t0 t1 s0 s1 : Int} (m : Int) (h1 : TailPosI b0 b1 t0 m s0 s1)
    (h2 : TailPosI b0 b1 m t1 s0 s1) : TailPosI b0 b1 t0 t1 s0 s1 :=
  TailPos.split_t _ h1 h2

theorem TailPosI.split_s {b0 b1 t0 t1 s0 s1 : Int} (m : Int) (h1 : TailPosI b0 b1 t0 t1 s0 m)
    (h2 : TailPosI b0 b1 t0 t1 m s1) : TailPosI b0 b1 t0 t1 s0 s1 :=
  TailPos.split_s _ h1 h2

theorem TailPosI.toReal {b0 b1 t0 t1 s0 s1 : Int} {B0 B1 T0 T1 S0 S1 : ℝ} (h : TailPosI b0 b1 t0 t1 s0 s1)
    (e1 : (b0 : ℝ) / one = B0) (e2 : (b1 : ℝ) / one = B1) (e3 : (t0 : ℝ) / one = T0) (e4 : (t1 : ℝ) / one = T1)
    (e5 : (s0 : ℝ) / one = S0) (e6 : (s1 : ℝ) / one = S1) : TailPos B0 B1 T0 T1 S0 S1 := by
  unfold TailPosI at h
  rw [e1, e2, e3, e4, e5, e6] at h
  exact h

/-- The u-tail piece from the root box. -/
theorem gammaUTail_of_region {S εc : ℝ} (hS : 2 * (3 / 65536 : ℝ) ≤ S)
    (h : TailPos (3 / 65536) (1 / 2) 0 1 0 (1 / 8)) : GammaUTail S εc (1 / 8) := by
  intro b t d ht0 ht1 hd0 hdb hb12 hS' _ hσ
  have hb0 : 0 < b := lt_trans hd0 hdb
  set σ := (b - d) / b with hσdef
  have hbσ : b * σ = b - d := by rw [hσdef]; field_simp
  have hd : b - b * σ = d := by rw [hbσ]; ring
  have hs0 : 0 < σ := by rw [hσdef]; exact div_pos (by linarith) hb0
  have hs1 : σ ≤ 1 / 8 := by rw [hσdef, div_le_iff₀ hb0]; linarith
  have htd : 0 ≤ t * d := mul_nonneg ht0 hd0.le
  have hbl : (3 / 65536 : ℝ) ≤ b := by linarith
  have := h b t σ hbl hb12 ht0 ht1 hs0.le hs1 hs0
  rw [hd] at this
  exact this.le

end CKLaneC.RSTail

end


