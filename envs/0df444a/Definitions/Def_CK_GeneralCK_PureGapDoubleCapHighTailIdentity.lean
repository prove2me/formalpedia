-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailIdentity
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailIdentity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:03:54.799561+00:00
-- url     : https://prove2.me/theorems/3d6777af-2ca5-4025-acbd-9d66ed400da2
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailIdentity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailIdentity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailIdentity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailIdentity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailIdentity.lean)

import Definitions.Def_CK_GeneralCK_SmallMeanCapTailBounds
import Definitions.Def_CK_GeneralCK_ReflectionRegularContact
import Definitions.Def_CK_GeneralCK_ProfileBasics
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction

-- ===== source module GeneralCK.PureGapDoubleCapHighTailIdentity =====
section

/-! Exact entropy and contact equations on the high double-cap tail.
No sign is asserted by these identities. -/

namespace GeneralCK

noncomputable def doubleCapHighTailFloor (x : ℝ) : ℝ :=
  (1 + H ((1 - 2 * x) / 2)) / 2

noncomputable def doubleCapHighTailY (x : ℝ) : ℝ :=
  1 - 2 * entropyInverse (doubleCapHighTailFloor x)

noncomputable def doubleCapHighTailC (x : ℝ) : ℝ :=
  Reflection.regularContact
    (x / (Real.log 2 * doubleCapHighTailFloor x))

theorem capEntropyFloor_eq_doubleCapHighTailFloor {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1 / 2) :
    capEntropyFloor ((1 - x) / 2) = doubleCapHighTailFloor x := by
  have hquarter : ¬ (1 - x) / 2 ≤ (1 / 4 : ℝ) := by linarith
  unfold capEntropyFloor doubleCapHighTailFloor
  simp only [if_neg hquarter]
  rw [show 2 * ((1 - x) / 2) - 1 / 2 = (1 - 2 * x) / 2 by ring]

theorem doubleCapHighTailFloor_pos {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1 / 2) :
    0 < doubleCapHighTailFloor x := by
  have hh := H_pos (show 0 < (1 - 2 * x) / 2 by linarith)
    (show (1 - 2 * x) / 2 < 1 by linarith)
  unfold doubleCapHighTailFloor
  linarith

theorem doubleCapHighTailFloor_le_one {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1 / 2) :
    doubleCapHighTailFloor x ≤ 1 := by
  have hh := H_le_one ((1 - 2 * x) / 2)
  unfold doubleCapHighTailFloor
  linarith

/-- The true inverse-entropy bias has exactly half the natural entropy
deficit of the direct mean bias `2*x`; this is the high cap entropy floor. -/
theorem doubleCapHighTailY_deficit {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1 / 2) :
    SmallMean.Cn (doubleCapHighTailY x) = SmallMean.Cn (2 * x) / 2 := by
  have hh := doubleCapHighTailFloor_pos hx hx1
  have hh1 := doubleCapHighTailFloor_le_one hx hx1
  have hv := entropyInverse_spec hh.le hh1
  unfold SmallMean.Cn doubleCapHighTailY doubleCapHighTailFloor
  rw [show (1 - (1 - 2 * entropyInverse
      ((1 + H ((1 - 2 * x) / 2)) / 2))) / 2 =
      entropyInverse ((1 + H ((1 - 2 * x) / 2)) / 2) by ring]
  have hvH : H (entropyInverse ((1 + H ((1 - 2 * x) / 2)) / 2)) =
      (1 + H ((1 - 2 * x) / 2)) / 2 := by
    simpa only [doubleCapHighTailFloor] using hv.2.2
  rw [hvH]
  ring

/-- An explicit rational square bound on the actual inverse-entropy bias. -/
theorem doubleCapHighTailY_sq_le {x : ℝ}
    (hx : 0 < x) (hx32 : x ≤ 1 / 32) :
    0 ≤ doubleCapHighTailY x ∧
    doubleCapHighTailY x ^ 2 ≤ (512 / 255 : ℝ) * x ^ 2 ∧
    doubleCapHighTailY x ^ 2 ≤ 1 / 510 := by
  have hx1 : x < 1 / 2 := by linarith
  have hh := doubleCapHighTailFloor_pos hx hx1
  have hh1 := doubleCapHighTailFloor_le_one hx hx1
  have hy0 : 0 ≤ doubleCapHighTailY x := by
    unfold doubleCapHighTailY
    linarith [(entropyInverse_spec hh.le hh1).2.1]
  have hy1 : doubleCapHighTailY x < 1 := by
    unfold doubleCapHighTailY
    linarith [entropyInverse_pos hh hh1]
  have hY := SmallMean.Cn_ge_half_sq hy0 hy1.le
  have hX := SmallMean.Cn_le_half_sq_over_gap
    (show 0 ≤ 2 * x by positivity) (show 2 * x < 1 by linarith)
  have hEq := doubleCapHighTailY_deficit hx hx1
  have hu : x ^ 2 ≤ 1 / 1024 := by
    have hsq := (sq_le_sq₀ hx.le
      (by norm_num : (0 : ℝ) ≤ 1 / 32)).2 hx32
    norm_num at hsq
    exact hsq
  have hgap : 0 < 1 - 4 * x ^ 2 := by nlinarith [hu]
  have hgap2 : 0 < 1 - (2 * x) ^ 2 := by nlinarith [hgap]
  have hYraw : doubleCapHighTailY x ^ 2 / 2 ≤
      x ^ 2 / (1 - 4 * x ^ 2) := by
    have hX2 : SmallMean.Cn (2 * x) / 2 ≤
        (2 * x) ^ 2 / (4 * (1 - (2 * x) ^ 2)) := by
      calc
        _ ≤ ((2 * x) ^ 2 / (2 * (1 - (2 * x) ^ 2))) / 2 :=
          div_le_div_of_nonneg_right hX (by norm_num : (0 : ℝ) ≤ 2)
        _ = (2 * x) ^ 2 / (4 * (1 - (2 * x) ^ 2)) := by
          field_simp [hgap2.ne']
          ring
    calc
      _ ≤ SmallMean.Cn (doubleCapHighTailY x) := hY
      _ = SmallMean.Cn (2 * x) / 2 := hEq
      _ ≤ (2 * x) ^ 2 / (4 * (1 - (2 * x) ^ 2)) := hX2
      _ = x ^ 2 / (1 - 4 * x ^ 2) := by
        field_simp [hgap.ne']
        ring
  have hgapLo : (255 / 256 : ℝ) ≤ 1 - 4 * x ^ 2 := by nlinarith [hu]
  have hraw : doubleCapHighTailY x ^ 2 ≤
      2 * x ^ 2 / (1 - 4 * x ^ 2) := by
    have heq : 2 * (x ^ 2 / (1 - 4 * x ^ 2)) =
        2 * x ^ 2 / (1 - 4 * x ^ 2) := by ring
    rw [← heq]
    linarith [hYraw]
  have hrat : 2 * x ^ 2 / (1 - 4 * x ^ 2) ≤
      (512 / 255 : ℝ) * x ^ 2 := by
    apply (div_le_iff₀ hgap).2
    have hm := mul_le_mul_of_nonneg_left hgapLo
      (show 0 ≤ (512 / 255 : ℝ) * x ^ 2 by positivity)
    nlinarith [hm]
  have hsq : doubleCapHighTailY x ^ 2 ≤
      (512 / 255 : ℝ) * x ^ 2 := hraw.trans hrat
  refine ⟨hy0, hsq, ?_⟩
  nlinarith [hsq, hu]

/-- The same true contact used by the checked slope identity. -/
theorem doubleCapHighTailC_equation (x : ℝ) :
    doubleCapHighTailC x =
      (x / (Real.log 2 * doubleCapHighTailFloor x)) *
        Certificates.Reflection.biasE (doubleCapHighTailC x) := by
  unfold doubleCapHighTailC
  exact Reflection.regularContact_equation _

/-- A rational upper bound for the bias logarithm, using the elementary
logarithm inequality at the reciprocal of `1-z²`. -/
theorem doubleCap_biasB_le_log_add_over_gap {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Certificates.Reflection.biasB z ≤ Real.log 2 +
      z ^ 2 / (2 * (1 - z ^ 2)) := by
  have hgap : 0 < 1 - z ^ 2 := by nlinarith [hz0, hz1]
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hgap)
  rw [Real.log_inv] at hlog
  have hrat : (1 - z ^ 2)⁻¹ - 1 = z ^ 2 / (1 - z ^ 2) := by
    field_simp [hgap.ne']
    ring
  rw [hrat] at hlog
  unfold Certificates.Reflection.biasB
  rw [show z * z = z ^ 2 by ring]
  rw [show z ^ 2 / (2 * (1 - z ^ 2)) =
      (z ^ 2 / (1 - z ^ 2)) / 2 by
        field_simp [hgap.ne']]
  linarith

#print axioms doubleCapHighTailY_deficit
#print axioms capEntropyFloor_eq_doubleCapHighTailFloor
#print axioms doubleCapHighTailY_sq_le
#print axioms doubleCapHighTailC_equation
#print axioms doubleCap_biasB_le_log_add_over_gap

end GeneralCK

end


