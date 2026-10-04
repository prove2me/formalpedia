-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapAnalyticClosure
-- name    : CK_GeneralCK_PureGapAnalyticClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:31:25.175773+00:00
-- url     : https://prove2.me/theorems/106e848c-cf7a-46ea-84ae-ef8eaa899f70
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapAnalyticClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapAnalyticClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapAnalyticClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapAnalyticClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapAnalyticClosure.lean)

import Definitions.Def_CK_GeneralCK_PureGapD0Origin
import Definitions.Def_CK_GeneralCK_PureGapCapAnalytic
import Definitions.Def_CK_GeneralCK_PureGapE8LargeSConsumer

-- ===== source module GeneralCK.PureGapAnalyticClosure =====
section

/-! Root-facing pure-gap assembly after the analytic half-mean identity,
its origin interval, and the equal-mean cap endpoint have been discharged. -/

namespace GeneralCK
open Set

theorem pureGapQ0_pos : 0 < pureGapQ0 := by
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- The finite scalar interval and derivative tail that remain after the
checked origin replay. Domain restrictions are exactly those produced by
the stationary half-mean equations. -/
structure PureGapD0RemainingOwners : Prop where
  compact : ∀ s : ℝ, s ∈ Icc (2 / 25 : ℝ) (63 / 20) →
    s ∈ e8SlopeRange → 2 * s ∈ e8SlopeRange →
    0 < e8D0 e8Q pureGapQ0 s
  tailDerivative : ∀ s : ℝ, (63 / 20 : ℝ) ≤ s → s ∈ e8SlopeRange →
    2 * pureGapQ0 < deriv e8Q s

/-- The sole independent D0 certificate after sharing the large-s E8
structure: positivity on the retained compact scalar interval. -/
def PureGapD0CompactOwner : Prop :=
  ∀ s : ℝ, s ∈ Icc (2 / 25 : ℝ) (63 / 20) →
    s ∈ e8SlopeRange → 2 * s ∈ e8SlopeRange →
    0 < e8D0 e8Q pureGapQ0 s

/-- The D0 derivative tail is already contained in the one-variable
large-s structure used by equation (8).  This bridge prevents the same
monotonicity and anchor certificate from becoming two independent owners. -/
theorem pureGapD0_tailDerivative_of_largeSStructure
    (h : E8LargeSStructure) :
    ∀ s : ℝ, (63 / 20 : ℝ) ≤ s → s ∈ e8SlopeRange →
      2 * pureGapQ0 < deriv e8Q s := by
  intro s hs hsRange
  have hmono := h.derivative_mono s hsRange
    (show (63 / 20 : ℝ) ∈ Icc 0 s by constructor <;> linarith)
    (show s ∈ Icc 0 s by exact ⟨e8SlopeRange_subset_pos hsRange |>.le, le_rfl⟩) hs
  have hanchor : 2 * pureGapQ0 < deriv e8RegularQ (63 / 20) := by
    simpa only [pureGapQ0] using h.shift
  have hregular : deriv e8RegularQ s = deriv e8Q s :=
    deriv_e8RegularQ_eq (e8SlopeRange_subset_pos hsRange)
  rw [hregular] at hmono
  exact hanchor.trans_le hmono

/-- Once the shared large-s structure is available, only the compact D0
interval remains as an independent pure-gap scalar owner. -/
theorem pureGapD0RemainingOwners_of_compact_and_largeSStructure
    (hcompact : PureGapD0CompactOwner)
    (hlargeS : E8LargeSStructure) : PureGapD0RemainingOwners where
  compact := hcompact
  tailDerivative := pureGapD0_tailDerivative_of_largeSStructure hlargeS

theorem e8D0_pos_of_deriv_gt {s : ℝ}
    (hs : s ∈ e8SlopeRange) (h2s : 2 * s ∈ e8SlopeRange)
    (hd : 2 * pureGapQ0 < deriv e8Q s) :
    0 < e8D0 e8Q pureGapQ0 s := by
  have hp := mul_pos (sub_pos.mpr hd) (e8Q_pos h2s)
  have hq := mul_pos (mul_pos two_pos pureGapQ0_pos) (e8Q_pos hs)
  unfold e8D0
  nlinarith

theorem PureGapD0RemainingOwners.positive (owners : PureGapD0RemainingOwners)
    {s : ℝ} (hs : 0 < s) (hsRange : s ∈ e8SlopeRange)
    (h2sRange : 2 * s ∈ e8SlopeRange) : 0 < e8D0 e8Q pureGapQ0 s := by
  by_cases horigin : s ≤ (2 / 25 : ℝ)
  · exact PureGapD0Origin.D0_e8Q_pos_on_origin hs horigin hsRange h2sRange
  by_cases hcompact : s ≤ (63 / 20 : ℝ)
  · exact owners.compact s ⟨(lt_of_not_ge horigin).le, hcompact⟩ hsRange h2sRange
  exact e8D0_pos_of_deriv_gt hsRange h2sRange
    (owners.tailDerivative s (lt_of_not_ge hcompact).le hsRange)

/-- The proved formula and scalar origin interval remove both of those
premises from the half-mean curvature owner. -/
theorem halfMeanCurvatureNegative_of_remainingD0 (owners : PureGapD0RemainingOwners) :
    HalfMeanCurvatureNegative := by
  intro a e f ha he hf _ _ hstationary
  let x : ℝ := (1 / 2 - a) / (e + f)
  let y : ℝ := (1 / 2 - a) / e
  let s : ℝ := e8Theta x
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hspos : 0 < s := e8Theta_pos hx
  have hstat : e8Theta y = 2 * s := by
    simpa only [x, y, s] using hstationary
  have hs : s ∈ e8SlopeRange := ⟨x, hx, rfl⟩
  have h2s : 2 * s ∈ e8SlopeRange := ⟨y, hy, hstat⟩
  have hgapQ := e8D0_pos_implies_halfMean_slope_lt hs h2s
    pureGapTheta0_pos pureGapQ0_eq_inv (owners.positive hspos hs h2s)
  have hcoords := halfMean_stationarity_e8Q_coordinates hx hy hstat
  have hgap : 2 * deriv e8Theta x * (1 - x / y) < pureGapTheta0 := by
    simpa only [s, hcoords.1, hcoords.2] using hgapQ
  rw [halfMeanSecondDerivativeFormula_actual a e f ha he hf hstationary]
  exact halfMean_transverse_curvature_neg hf hgap

/-- Exact remaining pure-gap input after this analytic pass. The correction
Hessian assumptions are shared with the existing global assembly, and do
not add a new certificate obligation. -/
theorem pureGapMinimizerLedger_of_analytic_owners {S : ℝ}
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2)
    (hsmall : ∀ e f p, 0 < e → 0 < f → e < f →
      p ∈ canonicalMeanSet e f → p.1 + p.2 < S →
      0 ≤ canonicalPureGap p.1 p.2 e f)
    (hseam : StrictSeamMinimizerExclusion S)
    (hcaps : CanonicalPureGapCapFiberOwnersExceptEqual S)
    (hD0 : PureGapD0RemainingOwners) : CanonicalPureGapMinimizerExclusions S :=
  ((nonCapExclusions_of_small_and_strictSeam hsmall hseam).withCapFiberOwners
    (hcaps.toOwners hleft hdet)).withHalfMeanCurvature
      (halfMeanCurvatureNegative_of_remainingD0 hD0)

/-- Pure-gap ledger with the D0 tail shared with the large-s equation-(8)
structure.  Its only independent D0 premise is the compact interval owner. -/
theorem pureGapMinimizerLedger_of_compactD0_and_largeSStructure {S : ℝ}
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2)
    (hsmall : ∀ e f p, 0 < e → 0 < f → e < f →
      p ∈ canonicalMeanSet e f → p.1 + p.2 < S →
      0 ≤ canonicalPureGap p.1 p.2 e f)
    (hseam : StrictSeamMinimizerExclusion S)
    (hcaps : CanonicalPureGapCapFiberOwnersExceptEqual S)
    (hD0Compact : PureGapD0CompactOwner)
    (hlargeS : E8LargeSStructure) : CanonicalPureGapMinimizerExclusions S :=
  pureGapMinimizerLedger_of_analytic_owners hleft hdet hsmall hseam hcaps
    (pureGapD0RemainingOwners_of_compact_and_largeSStructure hD0Compact hlargeS)

/-- Optional full-cap route: the zero cutoff removes the artificial small
region and seam, while its five cap domains must be proved at cutoff zero. -/
theorem pureGapMinimizerLedger_zero_of_analytic_owners
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2)
    (hcaps : CanonicalPureGapCapFiberOwnersExceptEqual 0)
    (hD0 : PureGapD0RemainingOwners) : CanonicalPureGapMinimizerExclusions 0 :=
  pureGapMinimizerLedger_of_analytic_owners hleft hdet canonicalPureGap_small_zero
    strictSeamMinimizerExclusion_zero hcaps hD0

#print axioms PureGapD0RemainingOwners.positive
#print axioms pureGapD0_tailDerivative_of_largeSStructure
#print axioms pureGapD0RemainingOwners_of_compact_and_largeSStructure
#print axioms halfMeanCurvatureNegative_of_remainingD0
#print axioms pureGapMinimizerLedger_of_analytic_owners
#print axioms pureGapMinimizerLedger_of_compactD0_and_largeSStructure
#print axioms pureGapMinimizerLedger_zero_of_analytic_owners

end GeneralCK

end


