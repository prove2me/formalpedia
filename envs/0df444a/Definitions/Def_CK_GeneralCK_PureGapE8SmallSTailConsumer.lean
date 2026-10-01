-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8SmallSTailConsumer
-- name    : CK_GeneralCK_PureGapE8SmallSTailConsumer
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:49:17.873973+00:00
-- url     : https://prove2.me/theorems/21007cbf-5517-49ae-95ed-c0880287d38d
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8SmallSTailConsumer` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8SmallSTailConsumer` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8SmallSTailConsumer` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8SmallSTailConsumer (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8SmallSTailConsumer.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8SecondSJet
import Definitions.Def_CK_GeneralCK_PureGapE8SmallJetBounds

-- ===== source module GeneralCK.PureGapE8SmallSTailConsumer =====
section

/-!
# A one-variable analytic reduction for the infinite small-s E8 tail

Only three coarse one-variable inverse-jet enclosures remain.  Local jets,
short-shift growth, the second derivative formula, and integration to the
original equation (8) are discharged here.
-/

namespace GeneralCK

open Set

theorem e8RegularQ_mono_of_mem {x y : ℝ} (hx : x ∈ e8SlopeRange)
    (hy : y ∈ e8SlopeRange) (hxy : x ≤ y) : e8RegularQ x ≤ e8RegularQ y := by
  rw [e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hx).le,
    e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hy).le]
  exact strictMonoOn_e8Q_range.monotoneOn hx hy hxy

/-- A differential upper bound controls a short multiplicative shift without
using any transcendental numerical enclosure. -/
theorem e8RegularQ_short_shift_le {t z : ℝ} (ht : 0 < t)
    (htz : t ≤ z) (hz : z ∈ e8SlopeRange) (hwidth : z - t ≤ 1 / 100)
    (hupper : ∀ u ∈ Icc t z, deriv e8RegularQ u ≤ 3 / 4 * e8RegularQ u) :
    e8RegularQ z ≤ 101 / 100 * e8RegularQ t := by
  have hrange (u : ℝ) (hu : u ∈ Icc t z) : u ∈ e8SlopeRange :=
    e8SlopeRange_downward hz (ht.trans_le hu.1) hu.2
  let g : ℝ → ℝ := fun u => 3 / 4 * e8RegularQ z * u - e8RegularQ u
  have hd (u : ℝ) (hu : u ∈ Icc t z) :
      HasDerivAt g (3 / 4 * e8RegularQ z - deriv e8RegularQ u) u := by
    have hq := (e8RegularQ_contDiffAt_of_mem (hrange u hu)).differentiableAt (by norm_num)
    convert! ((hasDerivAt_id u).const_mul (3 / 4 * e8RegularQ z)).sub hq.hasDerivAt using 1
    simp
  have hg : MonotoneOn g (Icc t z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t z)
    · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Icc t z := interior_subset hu
      rw [(hd u hu').deriv]
      have hmono := e8RegularQ_mono_of_mem (hrange u hu') hz hu'.2
      linarith [hupper u hu']
  have hgap := hg ⟨le_rfl, htz⟩ ⟨htz, le_rfl⟩ htz
  have hpos : 0 ≤ e8RegularQ z := by
    rw [e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hz).le]
    exact (e8Q_pos hz).le
  have htpos : 0 ≤ e8RegularQ t := by
    rw [e8RegularQ_eq_e8Q ht.le]
    exact (e8Q_pos (hrange t ⟨le_rfl, htz⟩)).le
  have hwidth' := mul_nonneg hpos (sub_nonneg.mpr hwidth)
  dsimp [g] at hgap
  nlinarith

/-- Exact residual analytic inputs for the entire infinite small-s tail.
All arguments refer to the concrete regularized inverse on its positive
slope range.  These are one-variable bounds, with no E8 determinant premise. -/
structure E8SmallSTailShapeBounds : Prop where
  value : ∀ y ∈ e8SlopeRange, 20 ≤ y → 100 ≤ e8RegularQ y
  first : ∀ y ∈ e8SlopeRange, 20 ≤ y →
    3 / 5 * e8RegularQ y ≤ deriv e8RegularQ y ∧
      deriv e8RegularQ y ≤ 3 / 4 * e8RegularQ y
  second : ∀ y ∈ e8SlopeRange, 20 ≤ y →
    2 / 5 * e8RegularQ y ≤ deriv (deriv e8RegularQ) y ∧
      deriv (deriv e8RegularQ) y ≤ 1 / 2 * e8RegularQ y

theorem e8_smallSTail_derivative_of_shape_bounds (h : E8SmallSTailShapeBounds) :
    E8SmallSTailDerivativeBound := by
  intro s t hadm ht hs
  have hsmall := e8RegularQ_small_jet_upper hadm.2.2.1 (by linarith)
  have htB : 20 ≤ 2 * s + t := by linarith [hadm.1]
  have htC : 20 ≤ s + t := by linarith [hadm.1]
  have hA := h.value t hadm.2.2.2.1 ht
  have hAB := e8RegularQ_mono_of_mem hadm.2.2.2.1 hadm.2.2.2.2.2 (by linarith [hadm.1])
  have hAC := e8RegularQ_mono_of_mem hadm.2.2.2.1 hadm.2.2.2.2.1 (by linarith [hadm.1])
  have hBA : e8RegularQ (2 * s + t) ≤ 101 / 100 * e8RegularQ t := by
    apply e8RegularQ_short_shift_le hadm.2.1 (by linarith [hadm.1])
      hadm.2.2.2.2.2 (by linarith)
    intro u hu
    exact (h.first u (e8SlopeRange_downward hadm.2.2.2.2.2
      (by linarith [hu.1]) hu.2) (by linarith [hu.1])).2
  have hB1 := h.first (2 * s + t) hadm.2.2.2.2.2 htB
  have hC1 := h.first (s + t) hadm.2.2.2.2.1 htC
  have hB2 := h.second (2 * s + t) hadm.2.2.2.2.2 htB
  have hC2 := h.second (s + t) hadm.2.2.2.2.1 htC
  rw [e8RegularDeltaSS_eq_jet hadm]
  apply e8SecondSJet_pos_of_tail_bounds hA hAB hBA hAC
    hsmall.1 hsmall.2.1 hsmall.2.2 <;> linarith

theorem e8_smallSTail_of_shape_bounds (h : E8SmallSTailShapeBounds) :
    E8PositiveOn (fun s t => 20 ≤ t ∧ s ≤ 1 / 200) :=
  e8_smallSTail_of_derivative_bound (e8_smallSTail_derivative_of_shape_bounds h)

#print axioms e8RegularQ_mono_of_mem
#print axioms e8RegularQ_short_shift_le
#print axioms e8_smallSTail_derivative_of_shape_bounds
#print axioms e8_smallSTail_of_shape_bounds

end GeneralCK

end


