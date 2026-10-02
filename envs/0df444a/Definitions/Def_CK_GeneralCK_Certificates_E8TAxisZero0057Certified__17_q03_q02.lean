-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q03_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q03_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T22:25:41.580985+00:00
-- url     : https://prove2.me/theorems/cd4b2970-682b-4ff6-b6ef-c7d2fd7f0bda
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 4 of 17) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 4 of 17) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 4 of 17) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057Certified (+16 modules: GeneralCK/Certificates/E8TAxisZero0058Certified, GeneralCK/Certificates/E8TAxisZero0059Certified, GeneralCK/Certificates/E8TAxisZero0060Certified, GeneralCK/Certificates/E8TAxisZero0061Certified, GeneralCK/Certificates/E8TAxisZero0062Certified, GeneralCK/Certificates/E8TAxisZero0063Certified, GeneralCK/Certificates/E8TAxisZero0064Certified, GeneralCK/Certificates/E8TAxisZero0065Certified, GeneralCK/Certificates/E8TAxisZero0066Certified, GeneralCK/Certificates/E8TAxisZero0067Certified, GeneralCK/Certificates/E8TAxisZero0068Certified, GeneralCK/Certificates/E8TAxisZero0069Certified, GeneralCK/Certificates/E8TAxisZero0070Certified, GeneralCK/Certificates/E8TAxisZero0071Certified, GeneralCK/Certificates/E8TAxisZero0072Certified, GeneralCK/Certificates/E8TAxisZero0073Certified) (piece 4 of 17) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q03_q01

namespace GeneralCK.Certificates.E8TAxisZero0060Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0060Geometry E8TAxisZero0060CertifiedArithmetic
theorem inputs_range {s t : ℝ} (h : rectangle.Covers s t) : InputsInRange s t :=
  E8TAxisRegularCellCertificateSchema.inputsInRange_of_rectangle
    (by norm_num [rectangle, sLower]) (by norm_num [rectangle, tLower]) upperSlope_mem h

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  apply E8TAxisRegularCellCertificateSchema.Certificate.positiveAt certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    exact inputs_range h
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive
  · exact h

end GeneralCK.Certificates.E8TAxisZero0060Certified


