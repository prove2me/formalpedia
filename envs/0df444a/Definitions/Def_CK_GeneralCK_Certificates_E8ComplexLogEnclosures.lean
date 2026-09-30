-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ComplexLogEnclosures
-- name    : CK_GeneralCK_Certificates_E8ComplexLogEnclosures
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:29:08.566087+00:00
-- url     : https://prove2.me/theorems/33e3f984-0b7f-467a-a3c8-27394e55172c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ComplexLogEnclosures` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ComplexLogEnclosures` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ComplexLogEnclosures` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ComplexLogEnclosures (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ComplexLogEnclosures.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ComplexBallKernel

-- ===== source module GeneralCK.Certificates.E8ComplexLogEnclosures =====
section

/-! Principal-log enclosures on the exact E8 contact disc. -/

namespace GeneralCK.Certificates.E8ComplexLogEnclosures

open E8ComplexBallKernel

noncomputable def contactRadius : ℝ := 1103 / 2500
noncomputable def squareRadius : ℝ := contactRadius ^ 2

theorem log_one_add_contact_taylor12 {c : ℂ} (hc : ‖c‖ ≤ contactRadius) :
    InBall (Complex.log (1 + c)) (Complex.logTaylor 13 c)
      (contactRadius ^ 13 * (1 - contactRadius)⁻¹ / 13) := by
  exact log_one_add_taylor12 hc (by norm_num [contactRadius])

theorem log_one_sub_contact_taylor12 {c : ℂ} (hc : ‖c‖ ≤ contactRadius) :
    InBall (Complex.log (1 - c)) (Complex.logTaylor 13 (-c))
      (contactRadius ^ 13 * (1 - contactRadius)⁻¹ / 13) := by
  apply log_one_add_taylor12 (z := -c)
  · simpa [contactRadius] using hc
  · norm_num [contactRadius]

theorem log_one_sub_square_taylor12 {c : ℂ} (hc : ‖c‖ ≤ contactRadius) :
    InBall (Complex.log (1 - c ^ 2)) (Complex.logTaylor 13 (-(c ^ 2)))
      (squareRadius ^ 13 * (1 - squareRadius)⁻¹ / 13) := by
  apply log_one_add_taylor12 (z := -(c ^ 2))
  · rw [norm_neg, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg c) hc 2
  · norm_num [squareRadius, contactRadius]

/-- The three principal logarithms needed by `thetaParam` are therefore
reduced to degree-12 complex polynomial evaluation plus explicit rational
ball radii. -/
theorem e8_three_logs_enclosed {c : ℂ} (hc : ‖c‖ ≤ contactRadius) :
    InBall (Complex.log (1 + c)) (Complex.logTaylor 13 c)
        (contactRadius ^ 13 * (1 - contactRadius)⁻¹ / 13) ∧
    InBall (Complex.log (1 - c)) (Complex.logTaylor 13 (-c))
        (contactRadius ^ 13 * (1 - contactRadius)⁻¹ / 13) ∧
    InBall (Complex.log (1 - c ^ 2)) (Complex.logTaylor 13 (-(c ^ 2)))
        (squareRadius ^ 13 * (1 - squareRadius)⁻¹ / 13) :=
  ⟨log_one_add_contact_taylor12 hc, log_one_sub_contact_taylor12 hc,
    log_one_sub_square_taylor12 hc⟩

end GeneralCK.Certificates.E8ComplexLogEnclosures

end


