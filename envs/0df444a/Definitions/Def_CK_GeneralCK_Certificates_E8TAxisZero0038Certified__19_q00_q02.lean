-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0038Certified__19_q00_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0038Certified__19_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:53:02.960484+00:00
-- url     : https://prove2.me/theorems/ddb887ae-f270-4765-9187-da039b82aa22
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified, GeneralCK.Certificates.E8TAxisZero0041Certified, GeneralCK.Certificates.E8TAxisZero0042Certified, GeneralCK.Certificates.E8TAxisZero0043Certified, GeneralCK.Certificates.E8TAxisZero0044Certified, GeneralCK.Certificates.E8TAxisZero0045Certified, GeneralCK.Certificates.E8TAxisZero0046Certified, GeneralCK.Certificates.E8TAxisZero0047Certified, GeneralCK.Certificates.E8TAxisZero0048Certified, GeneralCK.Certificates.E8TAxisZero0049Certified, GeneralCK.Certificates.E8TAxisZero0050Certified, GeneralCK.Certificates.E8TAxisZero0051Certified, GeneralCK.Certificates.E8TAxisZero0052Certified, GeneralCK.Certificates.E8TAxisZero0053Certified, GeneralCK.Certificates.E8TAxisZero0054Certified, GeneralCK.Certificates.E8TAxisZero0055Certified, GeneralCK.Certificates.E8TAxisZero0056Certified) (piece 1 of 19) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified, GeneralCK.Certificates.E8TAxisZero0041Certified, GeneralCK.Certificates.E8TAxisZero0042Certified, GeneralCK.Certificates.E8TAxisZero0043Certified, GeneralCK.Certificates.E8TAxisZero0044Certified, GeneralCK.Certificates.E8TAxisZero0045Certified, GeneralCK.Certificates.E8TAxisZero0046Certified, GeneralCK.Certificates.E8TAxisZero0047Certified, GeneralCK.Certificates.E8TAxisZero0048Certified, GeneralCK.Certificates.E8TAxisZero0049Certified, GeneralCK.Certificates.E8TAxisZero0050Certified, GeneralCK.Certificates.E8TAxisZero0051Certified, GeneralCK.Certificates.E8TAxisZero0052Certified, GeneralCK.Certificates.E8TAxisZero0053Certified, GeneralCK.Certificates.E8TAxisZero0054Certified, GeneralCK.Certificates.E8TAxisZero0055Certified, GeneralCK.Certificates.E8TAxisZero0056Certified) (piece 1 of 19) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified, GeneralCK.Certificates.E8TAxisZero0041Certified, GeneralCK.Certificates.E8TAxisZero0042Certified, GeneralCK.Certificates.E8TAxisZero0043Certified, GeneralCK.Certificates.E8TAxisZero0044Certified, GeneralCK.Certificates.E8TAxisZero0045Certified, GeneralCK.Certificates.E8TAxisZero0046Certified, GeneralCK.Certificates.E8TAxisZero0047Certified, GeneralCK.Certificates.E8TAxisZero0048Certified, GeneralCK.Certificates.E8TAxisZero0049Certified, GeneralCK.Certificates.E8TAxisZero0050Certified, GeneralCK.Certificates.E8TAxisZero0051Certified, GeneralCK.Certificates.E8TAxisZero0052Certified, GeneralCK.Certificates.E8TAxisZero0053Certified, GeneralCK.Certificates.E8TAxisZero0054Certified, GeneralCK.Certificates.E8TAxisZero0055Certified, GeneralCK.Certificates.E8TAxisZero0056Certified) (piece 1 of 19) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0038Certified (+18 modules: GeneralCK/Certificates/E8TAxisZero0039Certified, GeneralCK/Certificates/E8TAxisZero0040Certified, GeneralCK/Certificates/E8TAxisZero0041Certified, GeneralCK/Certificates/E8TAxisZero0042Certified, GeneralCK/Certificates/E8TAxisZero0043Certified, GeneralCK/Certificates/E8TAxisZero0044Certified, GeneralCK/Certificates/E8TAxisZero0045Certified, GeneralCK/Certificates/E8TAxisZero0046Certified, GeneralCK/Certificates/E8TAxisZero0047Certified, GeneralCK/Certificates/E8TAxisZero0048Certified, GeneralCK/Certificates/E8TAxisZero0049Certified, GeneralCK/Certificates/E8TAxisZero0050Certified, GeneralCK/Certificates/E8TAxisZero0051Certified, GeneralCK/Certificates/E8TAxisZero0052Certified, GeneralCK/Certificates/E8TAxisZero0053Certified, GeneralCK/Certificates/E8TAxisZero0054Certified, GeneralCK/Certificates/E8TAxisZero0055Certified, GeneralCK/Certificates/E8TAxisZero0056Certified) (piece 1 of 19) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0038Certified__19_q00_q02_q00

namespace GeneralCK.Certificates.E8TAxisZero0038Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0038Geometry E8TAxisZero0038CertifiedArithmetic
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

end GeneralCK.Certificates.E8TAxisZero0038Certified


