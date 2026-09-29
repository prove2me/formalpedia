-- Prove2me | Definitions.Def_CK_CKLaneP_LogQ
-- name    : CK_CKLaneP_LogQ
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:01:29.420575+00:00
-- url     : https://prove2.me/theorems/7b8b1146-1cd8-4c5f-a3fa-449bdb26d0eb
-- title:
--   Courtade–Kumar proof module `CKLaneP.LogQ` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.LogQ` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.LogQ` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.LogQ (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/LogQ.lean)

import Definitions.Def_CK_CKLaneP_EvalDy

-- ===== source module CKLaneP.LogQ =====
section
/-
Lane P — fast certified logarithm bounds of positive rationals via dyadic rounding and `lnDy`.

* `logUpQ x` : `log x ≤ logUpQ x`   (`x > 0`), using `N = ⌈x·2^60⌉`.
* `logDnQ x` : `logDnQ x ≤ log x`   (`⌊x·2^60⌋ ≥ 1`), using `N = ⌊x·2^60⌋`.
-/

set_option autoImplicit false

namespace CKLaneP

def logUpQ (x : ℚ) : ℚ :=
  ((lnDy 60 64 20 l2c (⌈x * 2 ^ 60⌉₊)).2 : ℚ) / 2 ^ 64

def logDnQ (x : ℚ) : ℚ :=
  ((lnDy 60 64 20 l2c (⌊x * 2 ^ 60⌋₊)).1 : ℚ) / 2 ^ 64

theorem logUpQ_sound {x : ℚ} (hx : 0 < x) : Real.log (x : ℝ) ≤ ((logUpQ x : ℚ) : ℝ) := by
  set N := ⌈x * 2 ^ 60⌉₊ with hN
  have hxN : x * 2 ^ 60 ≤ (N : ℚ) := Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    have : 0 < x * 2 ^ 60 := by positivity
    have h := Nat.ceil_pos.mpr this
    omega
  have h := (lnDy_sound (P := 60) (Q := 64) (n := 20) (N := N) l2c_sound hN1).2
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hxN' : (x : ℝ) ≤ (N : ℝ) / 2 ^ 60 := by
    rw [le_div_iff₀ (by positivity)]
    have := (Rat.cast_le (K := ℝ)).mpr hxN
    push_cast at this
    exact this
  have hlog : Real.log (x : ℝ) ≤ Real.log ((N : ℝ) / 2 ^ 60) := Real.log_le_log hxR hxN'
  unfold logUpQ
  rw [← hN]
  push_cast
  rw [le_div_iff₀ (by positivity)]
  have hq : (0 : ℝ) < 2 ^ 64 := by positivity
  nlinarith

theorem logDnQ_sound {x : ℚ} (hx : 1 ≤ ⌊x * 2 ^ 60⌋₊) : ((logDnQ x : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  set N := ⌊x * 2 ^ 60⌋₊ with hN
  have hNx : (N : ℚ) ≤ x * 2 ^ 60 := Nat.floor_le (by
    by_contra hneg
    push Not at hneg
    have : ⌊x * 2 ^ 60⌋₊ = 0 := Nat.floor_of_nonpos hneg.le
    omega)
  have h := (lnDy_sound (P := 60) (Q := 64) (n := 20) (N := N) l2c_sound hx).1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hx
  have hNx' : (N : ℝ) / 2 ^ 60 ≤ (x : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have := (Rat.cast_le (K := ℝ)).mpr hNx
    push_cast at this
    exact this
  have hlog : Real.log ((N : ℝ) / 2 ^ 60) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by positivity) hNx'
  unfold logDnQ
  rw [← hN]
  push_cast
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end CKLaneP

end


