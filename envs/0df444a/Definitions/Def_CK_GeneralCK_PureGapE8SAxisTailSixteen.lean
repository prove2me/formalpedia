-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8SAxisTailSixteen
-- name    : CK_GeneralCK_PureGapE8SAxisTailSixteen
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T02:45:53.71281+00:00
-- url     : https://prove2.me/theorems/829ce39e-db6c-4e6e-b3e8-5175b5e63f73
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8SAxisTailSixteen` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8SAxisTailSixteen` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8SAxisTailSixteen` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8SAxisTailSixteen (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8SAxisTailSixteen.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8TailSixteenDerivatives
import Definitions.Def_CK_GeneralCK_PureGapE8SAxisOriginClosure

-- ===== source module GeneralCK.PureGapE8SAxisTailSixteen =====
section

namespace GeneralCK

open Set

theorem e8SecondSJet_pos_of_axis_tail_bounds {A B C D B1 C1 D1 B2 C2 D2 : ℝ}
    (hA : 100 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 21/20*A) (hAC : A ≤ C)
    (hD : D ≤ 1) (hD1 : D1 ≤ 1) (hD2 : D2 ≤ 1)
    (hB1l : 3/5*A ≤ B1) (hB1u : B1 ≤ 4/5*A) (hC1l : 3/5*A ≤ C1)
    (hB2l : 0 ≤ B2) (hB2u : B2 ≤ 53/100*A) (hC2l : 2/5*A ≤ C2) :
    0 < e8SecondSJet A B C D B1 C1 D1 B2 C2 D2 := by
  have hAp : 0 ≤ A := by linarith
  have hB1p : 0 ≤ B1 := by linarith
  have hC2p : 0 ≤ C2 := by linarith
  have hp := mul_le_mul hB1l hC1l (by positivity : (0 : ℝ) ≤ 3/5*A) hB1p
  have he1 := mul_le_mul_of_nonneg_right hD1 hB1p
  have he2 := mul_le_mul_of_nonneg_left (show -(A+1) ≤ C-2*A-D by linarith) hB2l
  have he3 := mul_le_mul_of_nonneg_right hB2u (show 0 ≤ A+1 by linarith)
  have hp2 := mul_le_mul hC2l (show 2*A ≤ A+B by linarith)
    (by positivity : (0 : ℝ) ≤ 2*A) hC2p
  have he4 := mul_le_mul_of_nonpos_right hD2 (show A-B ≤ 0 by linarith)
  have hmargin : 0 < 3/25*A^2-537/100*A := by
    nlinarith [mul_nonneg (show 0 ≤ A-100 by linarith) hAp]
  unfold e8SecondSJet
  nlinarith

theorem e8RegularQ_axis_shift_sixteen {s t : ℝ}
    (hadm : E8Admissible s t) (hs : s ≤ 1/50) (ht : 16 ≤ t) :
    e8RegularQ (2*s+t) ≤ 21/20*e8RegularQ t := by
  have grow (u z : ℝ) (hu : t ≤ u) (huz : u ≤ z)
      (hz : z ≤ 2*s+t) (hd : z-u ≤ 1/100) :
      e8RegularQ z ≤ 101/100*e8RegularQ u := by
    apply e8RegularQ_short_shift_le (by linarith) huz
      (e8SlopeRange_downward hadm.2.2.2.2.2 (by linarith) hz) hd
    intro w hw
    exact (e8_sixteen_inverse_first_bounds
      (e8SlopeRange_downward hadm.2.2.2.2.2 (by linarith [hw.1]) (by linarith [hw.2]))
      (by linarith [hw.1])).2
  have h1 := grow t (t+s/2) le_rfl (by linarith [hadm.1]) (by linarith [hadm.1]) (by linarith)
  have h2 := grow (t+s/2) (t+s) (by linarith [hadm.1]) (by linarith [hadm.1])
    (by linarith [hadm.1]) (by linarith)
  have h3 := grow (t+s) (t+3*s/2) (by linarith [hadm.1]) (by linarith [hadm.1])
    (by linarith [hadm.1]) (by linarith)
  have h4 := grow (t+3*s/2) (2*s+t) (by linarith [hadm.1]) (by linarith [hadm.1]) le_rfl (by linarith)
  have hp := e8_sixteen_inverse_value hadm.2.2.2.1 ht
  linarith only [h1, h2, h3, h4, hp]

/-- The entire upper s-axis strip is now unconditional; no upper t cutoff
is needed. This also widens the proved infinite tail from s≤1/200 to s≤1/50. -/
theorem e8_sAxis_tail_sixteen_derivative {s t : ℝ}
    (hadm : E8Admissible s t) (hs : s ≤ 1/50) (ht : 16 ≤ t) :
    0 < e8RegularDeltaSS s t := by
  have hsmall := e8RegularQ_small_jet_upper hadm.2.2.1 hs
  have htB : 16 ≤ 2*s+t := by linarith [hadm.1]
  have htC : 16 ≤ s+t := by linarith [hadm.1]
  have hA := e8_sixteen_inverse_value hadm.2.2.2.1 ht
  have hAB := e8RegularQ_mono_of_mem hadm.2.2.2.1 hadm.2.2.2.2.2 (by linarith [hadm.1])
  have hAC := e8RegularQ_mono_of_mem hadm.2.2.2.1 hadm.2.2.2.2.1 (by linarith [hadm.1])
  have hBA := e8RegularQ_axis_shift_sixteen hadm hs ht
  have hB1 := e8_sixteen_inverse_first_bounds hadm.2.2.2.2.2 htB
  have hC1 := e8_sixteen_inverse_first_bounds hadm.2.2.2.2.1 htC
  have hB2 := e8_sixteen_inverse_second_bounds hadm.2.2.2.2.2 htB
  have hC2 := e8_sixteen_inverse_second_bounds hadm.2.2.2.2.1 htC
  rw [e8RegularDeltaSS_eq_jet hadm]
  apply e8SecondSJet_pos_of_axis_tail_bounds hA hAB hBA hAC
    hsmall.1 hsmall.2.1 hsmall.2.2 <;> linarith

theorem e8_sAxis_tail_sixteen : E8PositiveOn (fun s t => 16 ≤ t ∧ s ≤ 1/50) := by
  intro s t hadm hr
  apply e8Delta_pos_of_second_s_derivative hadm
  intro u hu
  exact e8_sAxis_tail_sixteen_derivative (hadm.mono_s hu.1 hu.2.le) (hu.2.le.trans hr.2) hr.1

def E8SAxisDerivativeRemainderSixteen : Prop :=
  ∀ s t : ℝ, E8Admissible s t → s ≤ 1/50 →
    3/50 ≤ t → t < 16 → 2/25 < s+t → 0 < e8RegularDeltaSS s t

theorem e8_sAxis_remainder_of_sixteen (h : E8SAxisDerivativeRemainderSixteen) :
    E8SAxisDerivativeRemainder := by
  intro s t hadm hs ht0 _ hsum
  by_cases ht : 16 ≤ t
  · exact e8_sAxis_tail_sixteen_derivative hadm hs ht
  · exact h s t hadm hs ht0 (lt_of_not_ge ht) hsum

theorem e8_sAxis_derivative_of_sixteen_remainder (h : E8SAxisDerivativeRemainderSixteen) :
    E8SAxisDerivativeBound :=
  e8_sAxis_derivative_of_remainder (e8_sAxis_remainder_of_sixteen h)

theorem e8_sAxis_of_sixteen_remainder (h : E8SAxisDerivativeRemainderSixteen) :
    E8PositiveOn (fun s t => s ≤ 1/50 ∧ 3/50 ≤ t ∧ t ≤ 20) :=
  e8_sAxis_of_derivative_bound (e8_sAxis_derivative_of_sixteen_remainder h)

#print axioms e8SecondSJet_pos_of_axis_tail_bounds
#print axioms e8RegularQ_axis_shift_sixteen
#print axioms e8_sAxis_tail_sixteen_derivative
#print axioms e8_sAxis_tail_sixteen
#print axioms e8_sAxis_remainder_of_sixteen
#print axioms e8_sAxis_derivative_of_sixteen_remainder
#print axioms e8_sAxis_of_sixteen_remainder

end GeneralCK

end


