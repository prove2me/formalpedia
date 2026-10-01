-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0038Certified__19_q00_q02_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0038Certified__19_q00_q02_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:49:16.782676+00:00
-- url     : https://prove2.me/theorems/6e8225c1-35e0-4777-b6fe-c0fd53bcf845
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified, GeneralCK.Certificates.E8TAxisZero0041Certified, GeneralCK.Certificates.E8TAxisZero0042Certified, GeneralCK.Certificates.E8TAxisZero0043Certified, GeneralCK.Certificates.E8TAxisZero0044Certified, GeneralCK.Certificates.E8TAxisZero0045Certified, GeneralCK.Certificates.E8TAxisZero0046Certified, GeneralCK.Certificates.E8TAxisZero0047Certified, GeneralCK.Certificates.E8TAxisZero0048Certified, GeneralCK.Certificates.E8TAxisZero0049Certified, GeneralCK.Certificates.E8TAxisZero0050Certified, GeneralCK.Certificates.E8TAxisZero0051Certified, GeneralCK.Certificates.E8TAxisZero0052Certified, GeneralCK.Certificates.E8TAxisZero0053Certified, GeneralCK.Certificates.E8TAxisZero0054Certified, GeneralCK.Certificates.E8TAxisZero0055Certified, GeneralCK.Certificates.E8TAxisZero0056Certified) (piece 1 of 19) (piece 3 of 4) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified, GeneralCK.Certificates.E8TAxisZero0041Certified, GeneralCK.Certificates.E8TAxisZero0042Certified, GeneralCK.Certificates.E8TAxisZero0043Certified, GeneralCK.Certificates.E8TAxisZero0044Certified, GeneralCK.Certificates.E8TAxisZero0045Certified, GeneralCK.Certificates.E8TAxisZero0046Certified, GeneralCK.Certificates.E8TAxisZero0047Certified, GeneralCK.Certificates.E8TAxisZero0048Certified, GeneralCK.Certificates.E8TAxisZero0049Certified, GeneralCK.Certificates.E8TAxisZero0050Certified, GeneralCK.Certificates.E8TAxisZero0051Certified, GeneralCK.Certificates.E8TAxisZero0052Certified, GeneralCK.Certificates.E8TAxisZero0053Certified, GeneralCK.Certificates.E8TAxisZero0054Certified, GeneralCK.Certificates.E8TAxisZero0055Certified, GeneralCK.Certificates.E8TAxisZero0056Certified) (piece 1 of 19) (piece 3 of 4) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0038Certified (+18 modules: GeneralCK.Certificates.E8TAxisZero0039Certified, GeneralCK.Certificates.E8TAxisZero0040Certified, GeneralCK.Certificates.E8TAxisZero0041Certified, GeneralCK.Certificates.E8TAxisZero0042Certified, GeneralCK.Certificates.E8TAxisZero0043Certified, GeneralCK.Certificates.E8TAxisZero0044Certified, GeneralCK.Certificates.E8TAxisZero0045Certified, GeneralCK.Certificates.E8TAxisZero0046Certified, GeneralCK.Certificates.E8TAxisZero0047Certified, GeneralCK.Certificates.E8TAxisZero0048Certified, GeneralCK.Certificates.E8TAxisZero0049Certified, GeneralCK.Certificates.E8TAxisZero0050Certified, GeneralCK.Certificates.E8TAxisZero0051Certified, GeneralCK.Certificates.E8TAxisZero0052Certified, GeneralCK.Certificates.E8TAxisZero0053Certified, GeneralCK.Certificates.E8TAxisZero0054Certified, GeneralCK.Certificates.E8TAxisZero0055Certified, GeneralCK.Certificates.E8TAxisZero0056Certified) (piece 1 of 19) (piece 3 of 4) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0038Certified (+18 modules: GeneralCK/Certificates/E8TAxisZero0039Certified, GeneralCK/Certificates/E8TAxisZero0040Certified, GeneralCK/Certificates/E8TAxisZero0041Certified, GeneralCK/Certificates/E8TAxisZero0042Certified, GeneralCK/Certificates/E8TAxisZero0043Certified, GeneralCK/Certificates/E8TAxisZero0044Certified, GeneralCK/Certificates/E8TAxisZero0045Certified, GeneralCK/Certificates/E8TAxisZero0046Certified, GeneralCK/Certificates/E8TAxisZero0047Certified, GeneralCK/Certificates/E8TAxisZero0048Certified, GeneralCK/Certificates/E8TAxisZero0049Certified, GeneralCK/Certificates/E8TAxisZero0050Certified, GeneralCK/Certificates/E8TAxisZero0051Certified, GeneralCK/Certificates/E8TAxisZero0052Certified, GeneralCK/Certificates/E8TAxisZero0053Certified, GeneralCK/Certificates/E8TAxisZero0054Certified, GeneralCK/Certificates/E8TAxisZero0055Certified, GeneralCK/Certificates/E8TAxisZero0056Certified) (piece 1 of 19) (piece 3 of 4) (piece 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0038Certified__19_q00_q01


namespace GeneralCK.Certificates.E8TAxisZero0038Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0038Geometry E8TAxisZero0038CertifiedArithmetic
theorem inputs_range {s t : ℝ} (h : rectangle.Covers s t) : InputsInRange s t :=
  E8TAxisRegularCellCertificateSchema.inputsInRange_of_rectangle
    (by norm_num [rectangle, sLower]) (by norm_num [rectangle, tLower]) upperSlope_mem h

end GeneralCK.Certificates.E8TAxisZero0038Certified


