-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginPilot
-- name    : CK_GeneralCK_Certificates_E8OriginPilot
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:57:03.47638+00:00
-- url     : https://prove2.me/theorems/b2602680-929c-4938-abb3-967ffb0a6320
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginPilot` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginPilot` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginPilot` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginPilot (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginPilot.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8CertificateReduction

-- ===== source module GeneralCK.Certificates.E8OriginPilot =====
section

/-!
# Exact rational pilot for the E8 origin summary

The retained `local_K_origin_R008.json` is a summary of an MPFR/Taylor
calculation.  This module gives its exact rational schema and checks the
arithmetic relation between the polynomial lower bound, remainder upper
bound, and claimed normalized lower bound.  The soundness theorem states the
remaining analytic enclosure premise explicitly.
-/

namespace GeneralCK.Certificates.E8OriginPilot

/-- Exact-rational form of the retained origin summary fields. -/
structure OriginSummary where
  degree : ℕ
  negativeCoefficientCount : ℕ
  anchorLower : ℚ
  anchorUpper : ℚ
  polynomialLower : ℚ
  polynomialUpper : ℚ
  q17AbsBound : ℚ
  remainderLower : ℚ
  remainderUpper : ℚ
  kLower : ℚ
  kUpper : ℚ
  certified : Bool
  deriving Repr

/-- Arithmetic acceptance rule for an origin summary.  Parsing decimal
strings into these rationals is an external data-loading step; all checks
below are exact. -/
def OriginSummary.check (c : OriginSummary) : Bool :=
  decide (c.degree = 15 ∧
    c.negativeCoefficientCount = 74 ∧
    c.certified = true ∧
    c.anchorLower ≤ c.anchorUpper ∧
    0 < c.anchorLower ∧
    c.polynomialLower ≤ c.polynomialUpper ∧
    0 ≤ c.q17AbsBound ∧
    0 ≤ c.remainderLower ∧
    c.remainderLower ≤ c.remainderUpper ∧
    c.kLower ≤ c.kUpper ∧
    c.kLower ≤ c.polynomialLower - c.remainderUpper ∧
    0 < c.kLower)

theorem OriginSummary.check_kLower_pos {c : OriginSummary}
    (hc : c.check = true) : 0 < c.kLower := by
  simp only [OriginSummary.check, decide_eq_true_eq] at hc
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, hpos⟩
  exact hpos

theorem OriginSummary.check_subtraction_sound {c : OriginSummary}
    (hc : c.check = true) :
    c.kLower ≤ c.polynomialLower - c.remainderUpper := by
  simp only [OriginSummary.check, decide_eq_true_eq] at hc
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hsub, _⟩
  exact hsub

/-- If the analytic Taylor replay encloses the normalized mixed derivative
above the checked rational endpoint, the endpoint check proves strict
positivity of that derivative. -/
theorem OriginSummary.proves_mixedDerivative_pos {c : OriginSummary}
    (hc : c.check = true) {K s t : ℝ} (hst : 0 < s + t)
    (henclosure : (c.kLower : ℝ) ≤ K / (s + t) ^ 3) : 0 < K := by
  have hkq : 0 < c.kLower := c.check_kLower_pos hc
  have hk : (0 : ℝ) < (c.kLower : ℝ) := by exact_mod_cast hkq
  have hquot : 0 < K / (s + t) ^ 3 := hk.trans_le henclosure
  rcases div_pos_iff.mp hquot with hpos | hneg
  · exact hpos.1
  · exact False.elim ((not_lt_of_ge (pow_nonneg hst.le 3)) hneg.2)

/-- A compact exact-rational representative of the retained accepted origin
summary.  The endpoints are conservative rational roundings of the JSON
values, while preserving its field layout and certified inequalities. -/
def acceptedPilot : OriginSummary where
  degree := 15
  negativeCoefficientCount := 74
  anchorLower := 599 / 10000000
  anchorUpper := 601 / 10000000
  polynomialLower := 599 / 10000000
  polynomialUpper := 601 / 10000000
  q17AbsBound := 290000000000000
  remainderLower := 129 / 10000000
  remainderUpper := 13 / 1000000
  kLower := 46 / 1000000
  kUpper := 48 / 1000000
  certified := true

theorem acceptedPilot_accepts : acceptedPilot.check = true := by
  norm_num [acceptedPilot, OriginSummary.check]

/-- The same layout with a claimed lower bound exceeding polynomial minus
remainder.  It is deliberately rejected by exact evaluation. -/
def rejectedPilot : OriginSummary where
  degree := 15
  negativeCoefficientCount := 74
  anchorLower := 599 / 10000000
  anchorUpper := 601 / 10000000
  polynomialLower := 599 / 10000000
  polynomialUpper := 601 / 10000000
  q17AbsBound := 290000000000000
  remainderLower := 129 / 10000000
  remainderUpper := 13 / 1000000
  kLower := 48 / 1000000
  kUpper := 49 / 1000000
  certified := true

theorem rejectedPilot_rejects : rejectedPilot.check = false := by
  norm_num [rejectedPilot, OriginSummary.check]

end GeneralCK.Certificates.E8OriginPilot

end


