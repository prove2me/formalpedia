-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8HistoricalLogConvexityBridge
-- name    : CK_GeneralCK_Certificates_E8HistoricalLogConvexityBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:39:58.224301+00:00
-- url     : https://prove2.me/theorems/8599968a-ab21-4db6-8a57-f2514d2bb35b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8HistoricalLogConvexityBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8HistoricalLogConvexityBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8HistoricalLogConvexityBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8HistoricalLogConvexityBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8HistoricalLogConvexityBridge.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8LargeSStableCriterion
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableJet5
import Definitions.Def_CK_GeneralCK_Certificates_E8HistoricalTailFormula

-- ===== source module GeneralCK.Certificates.E8HistoricalLogConvexityBridge =====
section

/-!
# Exact bridge for the historical E8 `E,L` certificate

The retained `cert_theta.cpp` checks

`L = E^2 - E' + E * X₀`

in the stable parameter `a`.  This file isolates the algebraic content of
that check.  In terms of the exact stable parameter jets `xJet` and `yJet`,
`L` differs from the canonical inverse-jet numerator

`Q' * Q''' - (Q'')^2`

only by positive square factors.  Consequently a future generated
finite/tail certificate only has to prove signs of explicit scalar
expressions; it does not have to repeat any inverse-function calculus.
-/

namespace GeneralCK.Certificates.E8HistoricalLogConvexityBridge

open E8InverseJet5Bridge
open E8TAxisDeltaDirectionalJet
open E8TAxisStableJet5
open E8TAxisStableScalar

/-- `(log P)'` for `P = Y' / X'`, written only in terms of the exact stable
parameter jets. -/
noncomputable def stableE (a : ℝ) : ℝ :=
  yJet.d2 a / yJet.d1 a - xJet.d2 a / xJet.d1 a

/-- The stable-parameter derivative of `stableE`, expanded algebraically. -/
noncomputable def stableEPrime (a : ℝ) : ℝ :=
  (yJet.d3 a * yJet.d1 a - yJet.d2 a ^ 2) / yJet.d1 a ^ 2 -
    (xJet.d3 a * xJet.d1 a - xJet.d2 a ^ 2) / xJet.d1 a ^ 2

/-- `X₀ = (log X')'` in the notation of the historical report. -/
noncomputable def stableX0 (a : ℝ) : ℝ :=
  xJet.d2 a / xJet.d1 a

/-- The exact scalar `L` whose positive interval lower bound is recorded by
the historical finite and tail certificates. -/
noncomputable def stableL (a : ℝ) : ℝ :=
  stableE a ^ 2 - stableEPrime a + stableE a * stableX0 a

/-- Denominator-cleared form of `stableL`.  This is the best expression for
an executable tail checker: it uses only addition and multiplication after
the stable graph has been enclosed. -/
noncomputable def stableLCleared (a : ℝ) : ℝ :=
  -(xJet.d1 a ^ 2 * yJet.d1 a * yJet.d3 a) +
    2 * xJet.d1 a ^ 2 * yJet.d2 a ^ 2 -
    xJet.d1 a * xJet.d2 a * yJet.d1 a * yJet.d2 a +
    xJet.d1 a * xJet.d3 a * yJet.d1 a ^ 2 -
    xJet.d2 a ^ 2 * yJet.d1 a ^ 2

theorem stableLCleared_eq_stableL_mul {a : ℝ}
    (hx : xJet.d1 a ≠ 0) (hy : yJet.d1 a ≠ 0) :
    stableLCleared a = stableL a * (xJet.d1 a ^ 2 * yJet.d1 a ^ 2) := by
  simp only [stableLCleared, stableL, stableE, stableEPrime, stableX0]
  field_simp [hx, hy]
  <;> ring

/-- Direct algebraic replay of the first three entries of the retained
`qdata5` inverse recurrence. -/
theorem inverseJet_numerator_eq_cleared_div {a : ℝ}
    (hy : yJet.d1 a ≠ 0) :
    inverseJet.d1 a * inverseJet.d3 a - inverseJet.d2 a ^ 2 =
      stableLCleared a / yJet.d1 a ^ 6 := by
  simp only [inverseJet, E8TAxisReparamJet5.qdata5, stableLCleared]
  field_simp [hy]
  <;> ring

/-- The historical cleared scalar is exactly the canonical numerator, up to
the positive sixth power of the parameter derivative. -/
theorem canonical_numerator_eq_cleared_div {a : ℝ}
    (ha : 0 < a) (hy : yJet.d1 a ≠ 0) :
    e8LogDerivativeJetNumerator (Y a) =
      stableLCleared a / yJet.d1 a ^ 6 := by
  rcases inverseJet_components ha hy with ⟨_, h1, h2, h3, _, _⟩
  change
    (e8QJet5 e8ThetaCanonicalJet5).d1 (Y a) *
        (e8QJet5 e8ThetaCanonicalJet5).d3 (Y a) -
      (e8QJet5 e8ThetaCanonicalJet5).d2 (Y a) ^ 2 = _
  rw [← h1, ← h2, ← h3]
  exact inverseJet_numerator_eq_cleared_div hy

theorem canonical_numerator_nonnegative_of_cleared {a : ℝ}
    (ha : 0 < a) (hy : yJet.d1 a ≠ 0)
    (hL : 0 ≤ stableLCleared a) :
    0 ≤ e8LogDerivativeJetNumerator (Y a) := by
  rw [canonical_numerator_eq_cleared_div ha hy]
  exact div_nonneg hL (by positivity)

/-- This version matches the literal `L > 0` field in the historical
certificate.  Positivity of the two squared denominator factors converts it
to the cleared certificate consumed above. -/
theorem canonical_numerator_nonnegative_of_stableL {a : ℝ}
    (ha : 0 < a) (hx : xJet.d1 a ≠ 0) (hy : yJet.d1 a ≠ 0)
    (hL : 0 ≤ stableL a) :
    0 ≤ e8LogDerivativeJetNumerator (Y a) := by
  apply canonical_numerator_nonnegative_of_cleared ha hy
  rw [stableLCleared_eq_stableL_mul hx hy]
  exact mul_nonneg hL (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Exact tail contract for a generated `(v,u)` checker.  The historical JSON
is evidence for these fields, but is not itself accepted as their proof. -/
structure TailCertificate (cut : ℝ) : Prop where
  xPrime_ne : ∀ a, cut ≤ a → xJet.d1 a ≠ 0
  yPrime_ne : ∀ a, cut ≤ a → yJet.d1 a ≠ 0
  L_nonnegative : ∀ a, cut ≤ a → 0 ≤ stableL a

/-- Certificate-facing form of the retained `(v,u)` tail computation.

The first field makes the removable logarithm enclosure explicit.  The
agreement field is an exact symbolic identity, not a numerical assertion;
the fleet is then responsible only for a rational interval proof of `L ≥ 0`
on the compact rectangle. -/
structure VUTailCertificate (cut uMax : ℝ) : Prop where
  cut_pos : 0 < cut
  uMax_nonnegative : 0 ≤ uMax
  exp_cut_le : Real.exp (-2 * cut) ≤ uMax
  logBox : E8RegularizedLog1p.FirstOrderBox (1 / (1 + uMax)) uMax
  L_agrees : ∀ a, cut ≤ a →
    E8HistoricalTailFormula.L (1 / a) (Real.exp (-2 * a)) = stableL a
  L_box_nonnegative : ∀ v u,
    0 < v → v ≤ 1 / cut → 0 < u → u ≤ uMax →
      0 ≤ E8HistoricalTailFormula.L v u
  xPrime_ne : ∀ a, cut ≤ a → xJet.d1 a ≠ 0
  yPrime_ne : ∀ a, cut ≤ a → yJet.d1 a ≠ 0

/-- Reduce the compact `(v,u)` arithmetic certificate to the one-variable
tail contract consumed by the global aggregation theorem. -/
theorem VUTailCertificate.toTailCertificate {cut uMax : ℝ}
    (h : VUTailCertificate cut uMax) : TailCertificate cut := by
  refine ⟨h.xPrime_ne, h.yPrime_ne, ?_⟩
  intro a ha
  have ha0 : 0 < a := h.cut_pos.trans_le ha
  have hv0 : 0 < 1 / a := one_div_pos.mpr ha0
  have hvU : 1 / a ≤ 1 / cut :=
    one_div_le_one_div_of_le h.cut_pos ha
  have hu0 : 0 < Real.exp (-2 * a) := Real.exp_pos _
  have huCut : Real.exp (-2 * a) ≤ Real.exp (-2 * cut) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [← h.L_agrees a ha]
  exact h.L_box_nonnegative (1 / a) (Real.exp (-2 * a))
    hv0 hvU hu0 (huCut.trans h.exp_cut_le)

theorem tail_numerator_nonnegative {cut a : ℝ}
    (hcut : 0 < cut) (h : TailCertificate cut) (ha : cut ≤ a) :
    0 ≤ e8LogDerivativeJetNumerator (Y a) :=
  canonical_numerator_nonnegative_of_stableL
    (hcut.trans_le ha) (h.xPrime_ne a ha) (h.yPrime_ne a ha)
      (h.L_nonnegative a ha)

theorem vu_tail_numerator_nonnegative {cut uMax a : ℝ}
    (h : VUTailCertificate cut uMax) (ha : cut ≤ a) :
    0 ≤ e8LogDerivativeJetNumerator (Y a) :=
  tail_numerator_nonnegative h.cut_pos h.toTailCertificate ha

/-- Combine a direct finite interval family on `(0,cut]` with the exact tail
contract.  This is the smallest final aggregation theorem needed by the
fleet output. -/
theorem stable_global_of_finite_and_tail {cut : ℝ}
    (hcut : 0 < cut)
    (hfinite : ∀ a : ℝ, 0 < a → a ≤ cut →
      0 ≤ e8LogDerivativeJetNumerator (Y a))
    (htail : TailCertificate cut) :
    E8StableLogDerivativeJetNumeratorNonnegative := by
  intro a ha
  by_cases hacut : a ≤ cut
  · exact hfinite a ha hacut
  · exact tail_numerator_nonnegative hcut htail (le_of_not_ge hacut)

#print axioms stableLCleared_eq_stableL_mul
#print axioms inverseJet_numerator_eq_cleared_div
#print axioms canonical_numerator_eq_cleared_div
#print axioms canonical_numerator_nonnegative_of_stableL
#print axioms VUTailCertificate.toTailCertificate
#print axioms vu_tail_numerator_nonnegative
#print axioms stable_global_of_finite_and_tail

end GeneralCK.Certificates.E8HistoricalLogConvexityBridge

end


