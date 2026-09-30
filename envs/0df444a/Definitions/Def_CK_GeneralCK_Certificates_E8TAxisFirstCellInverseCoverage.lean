-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage
-- name    : CK_GeneralCK_Certificates_E8TAxisFirstCellInverseCoverage
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:31:30.168749+00:00
-- url     : https://prove2.me/theorems/2b8c81b1-dee8-455d-91ca-5d67f187b946
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisFirstCellInverseCoverage.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisOneCellGeometry
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_GeneralCK_E8_first_cell_inputs

-- ===== source module GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage =====
section

/-!
# Checked endpoint enclosures imply inverse-slope coverage

The interval may be wider than the original inverse bracket.  Coverage uses
continuity and checked endpoint inequalities, so no injectivity or exact
endpoint preimage identity is required.
-/

namespace GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage

open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar







theorem point_contains (p : ℕ) (n : ℤ) :
    (⟨n, n⟩ : DyadicInterval p).Contains ((n : ℝ) / (scale p : ℝ)) := by
  have he : (scale p : ℝ) * ((n : ℝ) / (scale p : ℝ)) = n := by
    field_simp [(scale_cast_pos p).ne']
  simpa only [Contains, he] using And.intro (le_refl (n : ℝ)) (le_refl (n : ℝ))

theorem contains_of_between {p : ℕ} {alpha : DyadicInterval p} {a : ℝ}
    (ha : a ∈ Icc (lower alpha) (upper alpha)) : alpha.Contains a := by
  constructor
  · have hh := (div_le_iff₀ (scale_cast_pos p)).mp ha.1
    simpa only [mul_comm] using hh
  · have hh := (le_div_iff₀ (scale_cast_pos p)).mp ha.2
    simpa only [mul_comm] using hh

theorem Y_continuousAt {a : ℝ} (ha : 0 < a) : ContinuousAt Y a := by
  have he : E8TAxisStableJet5.yJet.d0 = Y :=
    funext E8TAxisStableJet5.yJet_d0
  rw [← he]
  exact (E8TAxisStableJet5.yJet_soundAt ha).1.continuousAt

theorem covers_of_endpoint_bounds {p : ℕ} {alpha : DyadicInterval p}
    {sLower sUpper : ℝ}
    (hpos : 0 < alpha.lo) (horder : alpha.lo ≤ alpha.hi)
    (hlo : Y (lower alpha) ≤ sLower) (hhi : sUpper ≤ Y (upper alpha))
    {s : ℝ} (hs : s ∈ Icc sLower sUpper) :
    ∃ a : ℝ, alpha.Contains a ∧ 0 < a ∧ Y a = s := by
  have hloPos : 0 < lower alpha := by
    apply div_pos _ (scale_cast_pos p)
    exact_mod_cast hpos
  have hordered : lower alpha ≤ upper alpha := by
    apply div_le_div_of_nonneg_right _ (scale_cast_pos p).le
    exact_mod_cast horder
  have hcont : ContinuousOn Y (Icc (lower alpha) (upper alpha)) := by
    intro a ha
    exact (Y_continuousAt (hloPos.trans_le ha.1)).continuousWithinAt
  obtain ⟨a, ha, hay⟩ := (intermediate_value_Icc hordered hcont)
    (show s ∈ Icc (Y (lower alpha)) (Y (upper alpha)) from
      ⟨hlo.trans hs.1, hs.2.trans hhi⟩)
  exact ⟨a, contains_of_between ha, hloPos.trans_le ha.1, hay⟩

/-- The endpoint comparisons are scaled inequalities suitable for exact
rational targets and integer interval endpoints. -/
theorem covers_of_endpoint_enclosures {p : ℕ} {alpha loBox hiBox : DyadicInterval p}
    {sLower sUpper : ℝ}
    (hpos : 0 < alpha.lo) (horder : alpha.lo ≤ alpha.hi)
    (hl : loBox.Contains (Y (lower alpha)))
    (hu : hiBox.Contains (Y (upper alpha)))
    (hlo : (loBox.hi : ℝ) ≤ (scale p : ℝ) * sLower)
    (hhi : (scale p : ℝ) * sUpper ≤ (hiBox.lo : ℝ))
    {s : ℝ} (hs : s ∈ Icc sLower sUpper) :
    ∃ a : ℝ, alpha.Contains a ∧ 0 < a ∧ Y a = s := by
  apply covers_of_endpoint_bounds hpos horder (s := s) (hs := hs)
  · exact (mul_le_mul_iff_right₀ (scale_cast_pos p)).mp (by simpa [mul_comm] using hl.2.trans hlo)
  · exact (mul_le_mul_iff_right₀ (scale_cast_pos p)).mp (by simpa [mul_comm] using hhi.trans hu.1)

/-- Primitive certificates and denominator checks suffice to enclose the
value of Y. This uses only the zero-order component of the stable graph. -/
theorem checked_yBox_d0_contains {p : ℕ} {i : Inputs p}
    {we : ExpWitness p} {wl wL : FastLogBoxWitness}
    (he : expBoxCheck ((ofInt p (-2)).mul i.alpha) i.expNegTwo we = true)
    (hl : logBoxCheck ((ofInt p 1).add i.expNegTwo) i.logOnePlusExp wl = true)
    (hL : logBoxCheck (ofInt p 2) i.logTwo wL = true)
    (hp : DenominatorsPositive i) {a : ℝ} (ha : i.alpha.Contains a) :
    (yBox i).d0.Contains (Y a) := by
  have hz : i.expNegTwo.Contains (Real.exp (-2 * a)) := by
    simpa using expBoxCheck_sound he (mul_sound (ofInt_sound p (-2)) ha)
  have hc1 : (ofInt p 1).Contains (1 : ℝ) := by simpa using ofInt_sound p 1
  have hc2 : (ofInt p 2).Contains (2 : ℝ) := by simpa using ofInt_sound p 2
  have hlog := logBoxCheck_sound hl (add_sound hc1 hz)
  have htwo := logBoxCheck_sound hL hc2
  simpa only [E8TAxisStableJet5.yJet_d0] using (xyBox_sound ha hz hlog htwo hp).2.1

#print axioms covers_of_endpoint_enclosures
#print axioms checked_yBox_d0_contains

end GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage

end


