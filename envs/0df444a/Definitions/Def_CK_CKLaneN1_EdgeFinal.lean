-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeFinal
-- name    : CK_CKLaneN1_EdgeFinal
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T18:24:53.639519+00:00
-- url     : https://prove2.me/theorems/14228757-1c64-445d-a77a-daff4f26fa09
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeFinal.lean)

import Definitions.Def_CK_CKLaneN1_EdgeFinal_q02

set_option autoImplicit false
namespace CKLaneN1.Edge
open GeneralCK SmallMeanPhiCutoff
/-- **leftEdge (CLOSED)**: the cutoff-edge value is nonnegative (indeed positive) on the strict
edge `0 < a < b < S - a` for `S = retainedCutoff`. -/
theorem leftEdge_retained : ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 / 2 →
    b < retainedCutoff - a → retainedCutoff - a ≤ 1 / 2 →
    0 ≤ canonicalPureGap a (retainedCutoff - a) (H a) (H b) := by
  intro a b ha hab _ hbc _
  have hS : retainedCutoff = 1 / 10000 := rfl
  rw [hS] at hbc ⊢
  have hy : 0 < 1 / 10000 - 2 * a := by linarith
  set t : ℝ := (1 / 10000 - 2 * a) / (1 / 10000) with htdef
  set z : ℝ := (b - a) / (1 / 10000 - 2 * a) with hzdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t < 1 := by rw [htdef, div_lt_one (by norm_num)]; linarith
  have hz0 : 0 < z := by rw [hzdef]; exact div_pos (by linarith) hy
  have hz1 : z < 1 := by rw [hzdef, div_lt_one hy]; linarith
  have key := edge_pos_tz ht0 ht1 hz0 hz1
  have ht' : t = 10000 * (1 / 10000 - 2 * a) := by rw [htdef]; ring
  have hz' : z * (1 / 10000 - 2 * a) = b - a := by rw [hzdef]; exact div_mul_cancel₀ _ hy.ne'
  have htz : t * z = 10000 * (b - a) := by
    calc t * z = 10000 * (z * (1 / 10000 - 2 * a)) := by rw [ht']; ring
      _ = 10000 * (b - a) := by rw [hz']
  have ea : 1 / 20000 * (1 - t) = a := by rw [ht']; ring
  have eb : 1 / 20000 * (1 + t * (2 * z - 1)) = b := by
    have e1 : 1 / 20000 * (1 + t * (2 * z - 1)) = 1 / 20000 * (1 + 2 * (t * z) - t) := by ring
    rw [e1, htz, ht']
    ring
  rw [ea, eb] at key
  exact key.le

end CKLaneN1.Edge


