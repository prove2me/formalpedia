-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q05_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q05_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T08:43:59.791985+00:00
-- url     : https://prove2.me/theorems/5f04da75-4e34-4d53-9217-80299d0ff363
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 6 of 17) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 6 of 17) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057Certified (+16 modules: GeneralCK.Certificates.E8TAxisZero0058Certified, GeneralCK.Certificates.E8TAxisZero0059Certified, GeneralCK.Certificates.E8TAxisZero0060Certified, GeneralCK.Certificates.E8TAxisZero0061Certified, GeneralCK.Certificates.E8TAxisZero0062Certified, GeneralCK.Certificates.E8TAxisZero0063Certified, GeneralCK.Certificates.E8TAxisZero0064Certified, GeneralCK.Certificates.E8TAxisZero0065Certified, GeneralCK.Certificates.E8TAxisZero0066Certified, GeneralCK.Certificates.E8TAxisZero0067Certified, GeneralCK.Certificates.E8TAxisZero0068Certified, GeneralCK.Certificates.E8TAxisZero0069Certified, GeneralCK.Certificates.E8TAxisZero0070Certified, GeneralCK.Certificates.E8TAxisZero0071Certified, GeneralCK.Certificates.E8TAxisZero0072Certified, GeneralCK.Certificates.E8TAxisZero0073Certified) (piece 6 of 17) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057Certified (+16 modules: GeneralCK/Certificates/E8TAxisZero0058Certified, GeneralCK/Certificates/E8TAxisZero0059Certified, GeneralCK/Certificates/E8TAxisZero0060Certified, GeneralCK/Certificates/E8TAxisZero0061Certified, GeneralCK/Certificates/E8TAxisZero0062Certified, GeneralCK/Certificates/E8TAxisZero0063Certified, GeneralCK/Certificates/E8TAxisZero0064Certified, GeneralCK/Certificates/E8TAxisZero0065Certified, GeneralCK/Certificates/E8TAxisZero0066Certified, GeneralCK/Certificates/E8TAxisZero0067Certified, GeneralCK/Certificates/E8TAxisZero0068Certified, GeneralCK/Certificates/E8TAxisZero0069Certified, GeneralCK/Certificates/E8TAxisZero0070Certified, GeneralCK/Certificates/E8TAxisZero0071Certified, GeneralCK/Certificates/E8TAxisZero0072Certified, GeneralCK/Certificates/E8TAxisZero0073Certified) (piece 6 of 17) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Certified__17_q05_q00

namespace GeneralCK.Certificates.E8TAxisZero0062Certified
open GeneralCK Set DyadicInterval E8TAxisMixedCoefficients E8TAxisPartitionKernel
open E8TAxisRegularGermJet E8TAxisRegularDirectionalJet
open E8TAxisZero0062Geometry E8TAxisZero0062CertifiedArithmetic
theorem upperSlope_mem : 2 * sUpper + tUpper ∈ e8SlopeRange := by
  obtain ⟨a, _, ha, hy⟩ := E8TAxisZero0062EndpointWitnesses.wholeB_covers_slope
    (s := 2*sUpper+tUpper) ⟨by
      norm_num [sLower, sUpper, tLower, tUpper], le_rfl⟩
  rw [← hy]
  exact ⟨E8TAxisStableScalar.X a, E8TAxisStableScalar.X_pos ha,
    E8TAxisStableScalar.e8Theta_X ha⟩

noncomputable def certificate : E8TAxisRegularCellCertificateSchema.Certificate precision :=
  ⟨rectangle, centerS, centerT, data⟩

end GeneralCK.Certificates.E8TAxisZero0062Certified


