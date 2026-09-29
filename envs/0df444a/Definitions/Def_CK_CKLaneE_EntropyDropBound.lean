-- Prove2me | Definitions.Def_CK_CKLaneE_EntropyDropBound
-- name    : CK_CKLaneE_EntropyDropBound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:02:53.02082+00:00
-- url     : https://prove2.me/theorems/4312ad30-8108-494b-923d-2229cd796e5a
-- title:
--   Courtade–Kumar proof module `CKLaneE.EntropyDropBound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.EntropyDropBound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.EntropyDropBound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.EntropyDropBound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/EntropyDropBound.lean)

import Definitions.Def_CK_GeneralCK_DeterministicCap
import Definitions.Def_CK_CKLaneE_SlopeBounds

-- ===== source module CKLaneE.EntropyDropBound =====
section

/-!
# Lane E: a normalized upper bound for the entropy drop

`entropyDrop_le_normalized`:
  `H((a+b)/2) - (H a + H b)/2 ≤ (b-a)^2/(8 log 2) * ((1 + 2/3 ρ^2)/m + (1 + 2/3 κ^2)/(1-m))`
with `m = (a+b)/2`, `ρ = (b-a)/(a+b)`, `κ = (b-a)/(2-a-b)`.
It is exact to first order at the diagonal, which is what makes a finite cover possible there.
Proof: the corpus identity `deterministic_entropy_chain` and the elementary cubic log bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE

open GeneralCK Set

theorem log_one_add_le_cubic {z : ℝ} (hz : 0 ≤ z) :
    Real.log (1 + z) ≤ z - z ^ 2 / 2 + z ^ 3 / 3 := by
  have key : MonotoneOn (fun t : ℝ => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t)) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => t ^ 3 / (1 + t))
    · intro t ht
      have h1 : (1 + t) ≠ 0 := by have := ht.out; linarith
      exact (((continuousAt_id.sub ((continuousAt_id.pow 2).div_const 2)).add
        ((continuousAt_id.pow 3).div_const 3)).sub
        ((continuousAt_const.add continuousAt_id).log h1)).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : (0 : ℝ) < t := ht
      have h1 : (0 : ℝ) < 1 + t := by linarith
      have hd := ((((hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 3 t).div_const 3)).sub
        (((hasDerivAt_id' t).const_add 1).log h1.ne'))
      have h1' : (1 + t) ≠ 0 := h1.ne'
      exact (hd.congr_deriv (by
        rw [show (2:ℕ) - 1 = 1 from rfl, show (3:ℕ) - 1 = 2 from rfl]
        push_cast
        field_simp
        ring)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : (0 : ℝ) < t := ht
      positivity
  have h := key (show (0 : ℝ) ∈ Ici (0 : ℝ) from Set.mem_Ici.mpr le_rfl) (show z ∈ Ici (0 : ℝ) from hz) hz
  simp only [add_zero, Real.log_one] at h
  norm_num at h
  linarith

theorem log_one_sub_le_cubic {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    Real.log (1 - z) ≤ -z - z ^ 2 / 2 - z ^ 3 / 3 := by
  have key : MonotoneOn (fun t : ℝ => -t - t ^ 2 / 2 - t ^ 3 / 3 - Real.log (1 - t)) (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1) (f' := fun t => t ^ 3 / (1 - t))
    · intro t ht
      have h1 : (1 - t) ≠ 0 := by have := ht.2; linarith
      exact ((((continuousAt_id.neg).sub ((continuousAt_id.pow 2).div_const 2)).sub
        ((continuousAt_id.pow 3).div_const 3)).sub
        ((continuousAt_const.sub continuousAt_id).log h1)).continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
      have hd := (((((hasDerivAt_id' t).neg).sub ((hasDerivAt_pow 2 t).div_const 2)).sub
        ((hasDerivAt_pow 3 t).div_const 3)).sub
        (((hasDerivAt_id' t).const_sub 1).log h1.ne'))
      have h1' : (1 - t) ≠ 0 := h1.ne'
      exact (hd.congr_deriv (by
        rw [show (2:ℕ) - 1 = 1 from rfl, show (3:ℕ) - 1 = 2 from rfl]
        push_cast
        field_simp
        ring)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have h0 : (0 : ℝ) < t := ht.1
      have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
      positivity
  have h := key (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 from ⟨le_refl 0, by norm_num⟩)
    (show z ∈ Ico (0 : ℝ) 1 from ⟨hz, hz1⟩) hz
  simp only [neg_zero, sub_zero, Real.log_one] at h
  norm_num at h
  linarith

/-- `1 - H((1-z)/2) ≤ (z^2 + 2/3 z^4)/(2 log 2)` on `[0,1)`. -/
theorem biasDeficit_le_poly {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    1 - H ((1 - z) / 2) ≤ (z ^ 2 + 2 / 3 * z ^ 4) / (2 * Real.log 2) := by
  have hL := log_two_pos
  have h1z : 0 < 1 - z := by linarith
  have h1z' : 0 < 1 + z := by linarith
  have hq : Real.log ((1 - z) / 2) = Real.log (1 - z) - Real.log 2 :=
    Real.log_div h1z.ne' (by norm_num)
  have hq' : Real.log (1 - (1 - z) / 2) = Real.log (1 + z) - Real.log 2 := by
    rw [show 1 - (1 - z) / 2 = (1 + z) / 2 by ring]
    exact Real.log_div h1z'.ne' (by norm_num)
  have hH : 1 - H ((1 - z) / 2) =
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)) / (2 * Real.log 2) := by
    rw [H_eq_logs, hq, hq']
    field_simp
    ring
  rw [hH]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have ha := mul_le_mul_of_nonneg_left (log_one_add_le_cubic hz) h1z'.le
  have hb := mul_le_mul_of_nonneg_left (log_one_sub_le_cubic hz hz1) h1z.le
  nlinarith [ha, hb]

/-- Normalized entropy-drop bound, first-order exact at the diagonal. -/
theorem entropyDrop_le_normalized {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤
      (b - a) ^ 2 / (8 * Real.log 2) *
        ((1 + 2 / 3 * ((b - a) / (a + b)) ^ 2) / ((a + b) / 2) +
          (1 + 2 / 3 * ((b - a) / (2 - a - b)) ^ 2) / (1 - (a + b) / 2)) := by
  have hL := log_two_pos
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hchain := deterministic_entropy_chain ha (hab.trans hb) (ha.trans hab) hb
  set ρ := (b - a) / (a + b) with hρ
  set κ := (b - a) / (2 - a - b) with hκ
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) hs.le
  have hρ1 : ρ < 1 := (div_lt_one hs).mpr (by linarith)
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) ht.le
  have hκ1 : κ < 1 := (div_lt_one ht).mpr (by linarith)
  have hpa : a / (a + b) = (1 - ρ) / 2 := by
    rw [hρ]; field_simp; ring
  have hpb : (1 - b) / (2 - a - b) = (1 - κ) / 2 := by
    rw [hκ]; field_simp; ring
  rw [hchain, hpa, hpb]
  have h1 := biasDeficit_le_poly hρ0 hρ1
  have h2 := biasDeficit_le_poly hκ0 hκ1
  have hm : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  have hsne : a + b ≠ 0 := hs.ne'
  have htne : 2 - a - b ≠ 0 := ht.ne'
  have htne' : 2 - (a + b) ≠ 0 := by intro h; linarith
  have hm1ne : 1 - (a + b) / 2 ≠ 0 := hm1.ne'
  have e1 : (a + b) / 2 * ((ρ ^ 2 + 2 / 3 * ρ ^ 4) / (2 * Real.log 2)) =
      (b - a) ^ 2 / (8 * Real.log 2) * ((1 + 2 / 3 * ρ ^ 2) / ((a + b) / 2)) := by
    rw [hρ]; field_simp; ring
  have e2 : (1 - (a + b) / 2) * ((κ ^ 2 + 2 / 3 * κ ^ 4) / (2 * Real.log 2)) =
      (b - a) ^ 2 / (8 * Real.log 2) * ((1 + 2 / 3 * κ ^ 2) / (1 - (a + b) / 2)) := by
    rw [hκ]; field_simp; ring
  have k1 := mul_le_mul_of_nonneg_left h1 hm.le
  have k2 := mul_le_mul_of_nonneg_left h2 hm1.le
  rw [e1] at k1
  rw [e2] at k2
  rw [mul_add]
  linarith

end CKLaneE

#check @CKLaneE.log_one_add_le_cubic
#check @CKLaneE.log_one_sub_le_cubic
#check @CKLaneE.biasDeficit_le_poly
#check @CKLaneE.entropyDrop_le_normalized
#print axioms CKLaneE.log_one_add_le_cubic
#print axioms CKLaneE.log_one_sub_le_cubic
#print axioms CKLaneE.biasDeficit_le_poly
#print axioms CKLaneE.entropyDrop_le_normalized

end


