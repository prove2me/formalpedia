-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_Leaf
-- name    : CK_CKLaneR2_Tail_Leaf
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:25:31.107036+00:00
-- url     : https://prove2.me/theorems/1cea91a2-91ac-451f-b3f3-a6165a66debf
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.Leaf` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.Leaf` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.Leaf` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.Leaf (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/Leaf.lean)

import Definitions.Def_CK_CKLaneR2_Tail_Chart

-- ===== source module CKLaneR2.Tail.Leaf =====
section

/-!
# Lane R2b — u-tail leaf theorems (the only premise is the Boolean check)

`leafS` / `leafL`: a passing `domS/domL && tailCheck` closes the integer-coded box
`[b0,b1] × [t0,t1] × [s0,s1]` (fixed point, `one = 2^64`), i.e. `0 < rayGamma b t (b - bσ)` on it for `σ > 0`.
The conclusion is Lane C's `CKLaneC.RSTail.TailPosI b0 b1 t0 t1 s0 s1` unfolded (defeq).
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

theorem leafS (c : SCell) (q : TCert) (sMode : Bool) (b0 b1 t0 t1 s0 s1 : Int)
    (h : (domS c b0 b1 t0 t1 s0 s1 && tailCheck (frontS c) q sMode) = true) :
    ∀ b t σ : ℝ, (b0 : ℝ) / one ≤ b → b ≤ (b1 : ℝ) / one → (t0 : ℝ) / one ≤ t → t ≤ (t1 : ℝ) / one →
      (s0 : ℝ) / one ≤ σ → σ ≤ (s1 : ℝ) / one → 0 < σ → 0 < CKLaneN23.RS.rayGamma b t (b - b * σ) := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 _
  simp only [Bool.and_eq_true] at h
  obtain ⟨hd, hc⟩ := h
  have hF := fokS c hd
  obtain ⟨hb, ht, hs, _⟩ := domS_parts hd
  obtain ⟨x, hx, hbx⟩ := b_coord c.bch hb hb0 hb1
  obtain ⟨y, hy, hty⟩ := lin_coord (tDom_parts ht |> fun h => by
    simp only [tDomOK, Bool.and_eq_true] at ht; exact ht.1.1) ht0 ht1
  obtain ⟨z, hz, hsz⟩ := exp_coord hs hs0 hs1
  have hbpos : 0 < bF c.bch x := (bF_bounds c.bch hb x hx).1
  have hspos : 0 < sgF c z := expF_pos (expBoxOK_parts hs).1 _ _ _
  have hph : Phys (semS c) x y z := ⟨mul_pos hbpos hspos, rfl, rfl, rfl, rfl⟩
  have key := tail_sound (frontS c) (semS c) hF q sMode hc x y z hx hy hz hph
  have e1 : (semS c).b x y z = b := hbx
  have e2 : (semS c).t x y z = t := hty
  have e3 : (semS c).u x y z = b * σ := by
    show bF c.bch x * sgF c z = b * σ
    rw [hbx]; exact congrArg (b * ·) hsz
  rw [e1, e2, e3] at key
  exact key

theorem leafL (c : LCell) (q : TCert) (sMode : Bool) (b0 b1 t0 t1 s0 s1 : Int)
    (h : (domL c b0 b1 t0 t1 s1 && tailCheck (frontL c) q sMode) = true) :
    ∀ b t σ : ℝ, (b0 : ℝ) / one ≤ b → b ≤ (b1 : ℝ) / one → (t0 : ℝ) / one ≤ t → t ≤ (t1 : ℝ) / one →
      (s0 : ℝ) / one ≤ σ → σ ≤ (s1 : ℝ) / one → 0 < σ → 0 < CKLaneN23.RS.rayGamma b t (b - b * σ) := by
  intro b t σ hb0 hb1 ht0 ht1 _ hs1 hs
  simp only [Bool.and_eq_true] at h
  obtain ⟨hd, hc⟩ := h
  have hF := fokL c hd
  obtain ⟨hb, ht, _, _, _, _, _, _, _, _, _⟩ := domL_parts hd
  obtain ⟨x, hx, hbx⟩ := b_coord c.bch hb hb0 hb1
  obtain ⟨y, hy, hty⟩ := lin_coord (by simp only [tDomOK, Bool.and_eq_true] at ht; exact ht.1.1) ht0 ht1
  have hbpos : 0 < b := by rw [← hbx]; exact (bF_bounds c.bch hb x hx).1
  obtain ⟨z, hz, hlam, huz⟩ := lamL_coord hd hbpos hb1 hs hs1
  have hu0 : 0 < uLF c z := by rw [huz]; exact mul_pos hbpos hs
  have hph : Phys (semL c) x y z := by
    refine ⟨hu0, ?_, rfl, rfl, rfl⟩
    show lamF c z = (-Real.log (uLF c z))⁻¹
    have e : uLF c z = Real.exp (-1 / lamF c z) := by unfold uLF; rw [if_pos hlam]
    rw [e, Real.log_exp]
    field_simp
  have key := tail_sound (frontL c) (semL c) hF q sMode hc x y z hx hy hz hph
  have e1 : (semL c).b x y z = b := hbx
  have e2 : (semL c).t x y z = t := hty
  have e3 : (semL c).u x y z = b * σ := huz
  rw [e1, e2, e3] at key
  exact key

end CKLaneR2.Tail

end


