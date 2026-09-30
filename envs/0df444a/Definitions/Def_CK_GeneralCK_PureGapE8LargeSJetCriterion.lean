-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8LargeSJetCriterion
-- name    : CK_GeneralCK_PureGapE8LargeSJetCriterion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:32:04.234658+00:00
-- url     : https://prove2.me/theorems/00fd2e52-dffa-4e6e-8b67-a0bf9466acd3
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8LargeSJetCriterion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8LargeSJetCriterion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8LargeSJetCriterion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8LargeSJetCriterion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8LargeSJetCriterion.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8LargeSLogConvex
import Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorRegularJetDerivatives

-- ===== source module GeneralCK.PureGapE8LargeSJetCriterion =====
section

/-!
# A certificate-facing criterion for the large-s logarithmic convexity

The historical one-variable E8 certificate checks positivity of the second
derivative of `log Q'`.  The canonical inverse jet already represents the
first three derivatives of the regular inverse on the positive slope range.
This file identifies the exact algebraic numerator which a finite interval
certificate has to prove and turns its pointwise nonnegativity into the
`ConvexOn` field required by `E8LargeSStructure`.
-/

namespace GeneralCK

open Set Filter
open Certificates.E8TAxisDeltaDirectionalJet
open Certificates.E8CompactAnchorRegularJetDerivatives

/-- Numerator of `(log Q')''`, expressed in the canonical inverse jet. -/
noncomputable def e8LogDerivativeJetNumerator (y : ℝ) : ℝ :=
  qJet.d1 y * qJet.d3 y - qJet.d2 y ^ 2

theorem hasDerivAt_log_deriv_e8RegularQ_of_mem {y : ℝ}
    (hy : y ∈ e8SlopeRange) :
    HasDerivAt (fun z => Real.log (deriv e8RegularQ z))
      (qJet.d2 y / qJet.d1 y) y := by
  have heq : qJet.d1 =ᶠ[nhds y] deriv e8RegularQ := by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    exact qJet_d1_eq_deriv_regular hz
  have hd : HasDerivAt (deriv e8RegularQ) (qJet.d2 y) y :=
    (qJet_soundAt hy).2.1.congr_of_eventuallyEq heq.symm
  have hp : 0 < deriv e8RegularQ y := deriv_e8RegularQ_pos (Or.inr hy)
  simpa only [qJet_d1_eq_deriv_regular hy] using hd.log hp.ne'

theorem hasDerivAt_deriv_log_deriv_e8RegularQ_of_mem {y : ℝ}
    (hy : y ∈ e8SlopeRange) :
    HasDerivAt (deriv (fun z => Real.log (deriv e8RegularQ z)))
      (e8LogDerivativeJetNumerator y / qJet.d1 y ^ 2) y := by
  have hp : 0 < qJet.d1 y := by
    rw [qJet_d1_eq_deriv_regular hy]
    exact deriv_e8RegularQ_pos (Or.inr hy)
  have hratio := (qJet_soundAt hy).2.2.1.div (qJet_soundAt hy).2.1 hp.ne'
  have heq :
      deriv (fun z => Real.log (deriv e8RegularQ z)) =ᶠ[nhds y]
        (fun z => qJet.d2 z / qJet.d1 z) := by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    exact (hasDerivAt_log_deriv_e8RegularQ_of_mem hz).deriv
  have h := hratio.congr_of_eventuallyEq heq
  simpa only [e8LogDerivativeJetNumerator, pow_two, mul_comm] using h

/-- The single sign condition to be supplied by the finite/tail E8
certificate.  It is deliberately phrased using the already-sound canonical
inverse jet, so the numerical layer need not reason about Lean's `deriv`.
-/
def E8LogDerivativeJetNumeratorNonnegative : Prop :=
  ∀ y ∈ e8SlopeRange, 0 ≤ e8LogDerivativeJetNumerator y

theorem e8_log_derivative_convex_of_jet_numerator
    (hnum : E8LogDerivativeJetNumeratorNonnegative) :
    ∀ x ∈ e8SlopeRange,
      ConvexOn ℝ (Icc 0 x) (fun y => Real.log (deriv e8RegularQ y)) := by
  intro x hx
  let f : ℝ → ℝ := fun y => Real.log (deriv e8RegularQ y)
  let f' : ℝ → ℝ := qJet.d2 / qJet.d1
  let f'' : ℝ → ℝ := fun y => e8LogDerivativeJetNumerator y / qJet.d1 y ^ 2
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 x)
    (f' := f') (f'' := f'')
  · intro y hy
    rcases hy.1.eq_or_lt with rfl | hypos
    · simpa only [f] using
        hasDerivAt_log_deriv_e8RegularQ_zero.continuousAt.continuousWithinAt
    · have hyrange := e8SlopeRange_downward hx hypos hy.2
      simpa only [f] using
        (hasDerivAt_log_deriv_e8RegularQ_of_mem hyrange).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : y ∈ Ioo 0 x := by simpa using hy
    have hyrange := e8SlopeRange_downward hx hy'.1 hy'.2.le
    -- The imported jet calculus and the current convexity API choose two
    -- definitionally different `Module ℝ ℝ` paths.  Passing through the
    -- little-o characterization removes that irrelevant instance diamond.
    rw [hasDerivWithinAt_iff_isLittleO]
    have hold :=
      (hasDerivAt_log_deriv_e8RegularQ_of_mem hyrange).hasDerivWithinAt
        (s := interior (Icc 0 x))
    rw [hasDerivWithinAt_iff_isLittleO] at hold
    simpa only [f, f', Pi.div_apply, smul_eq_mul] using hold
  · intro y hy
    have hy' : y ∈ Ioo 0 x := by simpa using hy
    have hyrange := e8SlopeRange_downward hx hy'.1 hy'.2.le
    have hp : 0 < qJet.d1 y := by
      rw [qJet_d1_eq_deriv_regular hyrange]
      exact deriv_e8RegularQ_pos (Or.inr hyrange)
    have hratio :=
      (qJet_soundAt hyrange).2.2.1.div (qJet_soundAt hyrange).2.1 hp.ne'
    rw [hasDerivWithinAt_iff_isLittleO]
    have hold := hratio.hasDerivWithinAt (s := interior (Icc 0 x))
    rw [hasDerivWithinAt_iff_isLittleO] at hold
    simpa only [f', f'', e8LogDerivativeJetNumerator, Pi.div_apply,
      pow_two, mul_comm, smul_eq_mul] using hold
  · intro y hy
    have hy' : y ∈ Ioo 0 x := by simpa using hy
    have hyrange := e8SlopeRange_downward hx hy'.1 hy'.2.le
    exact div_nonneg (hnum y hyrange) (sq_nonneg _)

theorem e8LargeSStructure_of_jet_numerator
    (hnum : E8LogDerivativeJetNumeratorNonnegative) :
    E8LargeSStructure :=
  e8LargeSStructure_of_log_derivative_convex
    (e8_log_derivative_convex_of_jet_numerator hnum)

theorem e8_largeS_of_jet_numerator
    (hnum : E8LogDerivativeJetNumeratorNonnegative) :
    E8PositiveOn (fun s _ => (63 / 20 : ℝ) ≤ s) :=
  e8_largeS_of_structure (e8LargeSStructure_of_jet_numerator hnum)

#print axioms hasDerivAt_log_deriv_e8RegularQ_of_mem
#print axioms hasDerivAt_deriv_log_deriv_e8RegularQ_of_mem
#print axioms e8_log_derivative_convex_of_jet_numerator
#print axioms e8LargeSStructure_of_jet_numerator
#print axioms e8_largeS_of_jet_numerator

end GeneralCK

end


