-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0579Certified__25_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0579Certified__25_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:17:51.409579+00:00
-- url     : https://prove2.me/theorems/a58ce6f8-336c-4be1-abf9-e63d0c706bb4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0579Certified (+24 modules: GeneralCK.Certificates.E8TAxisProd0580Certified, GeneralCK.Certificates.E8TAxisProd0581Certified…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0579Certified (+24 modules: GeneralCK.Certificates.E8TAxisProd0580Certified, GeneralCK.Certificates.E8TAxisProd0581Certified, GeneralCK.Certificates.E8TAxisProd0582Certified, GeneralCK.Certificates.E8TAxisProd0583Certified, GeneralCK.Certificates.E8TAxisProd0584Certified, GeneralCK.Certificates.E8TAxisProd0585Certified, GeneralCK.Certificates.E8TAxisProd0586Certified, GeneralCK.Certificates.E8TAxisProd0587Certified, GeneralCK.Certificates.E8TAxisProd0588Certified, GeneralCK.Certificates.E8TAxisProd0589Certified, GeneralCK.Certificates.E8TAxisProd0590Certified, GeneralCK.Certificates.E8TAxisProd0591Certified, GeneralCK.Certificates.E8TAxisProd0592Certified, GeneralCK.Certificates.E8TAxisProd0593Certified, GeneralCK.Certificates.E8TAxisProd0594Certified, GeneralCK.Certificates.E8TAxisProd0595Certified, GeneralCK.Certificates.E8TAxisProd0596Certified, GeneralCK.Certificates.E8TAxisProd0597Certified, GeneralCK.Certificates.E8TAxisProd0598Certified, GeneralCK.Certificates.E8TAxisProd0599Certified, GeneralCK.Certificates.E8TAxisProd0600Certified, GeneralCK.Certificates.E8TAxisProd0601Certified, GeneralCK.Certificates.E8TAxisProd0602Certified, GeneralCK.Certificates.E8TAxisProd0603Certified) (piece 1 of 25) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0579Certified (+24 modules: GeneralCK.Certificates.E8TAxisProd0580Certified, GeneralCK.Certificates.E8TAxisProd0581Certified, GeneralCK.Certificates.E8TAxisProd0582Certified, GeneralCK.Certificates.E8TAxisProd0583Certified, GeneralCK.Certificates.E8TAxisProd0584Certified, GeneralCK.Certificates.E8TAxisProd0585Certified, GeneralCK.Certificates.E8TAxisProd0586Certified, GeneralCK.Certificates.E8TAxisProd0587Certified, GeneralCK.Certificates.E8TAxisProd0588Certified, GeneralCK.Certificates.E8TAxisProd0589Certified, GeneralCK.Certificates.E8TAxisProd0590Certified, GeneralCK.Certificates.E8TAxisProd0591Certified, GeneralCK.Certificates.E8TAxisProd0592Certified, GeneralCK.Certificates.E8TAxisProd0593Certified, GeneralCK.Certificates.E8TAxisProd0594Certified, GeneralCK.Certificates.E8TAxisProd0595Certified, GeneralCK.Certificates.E8TAxisProd0596Certified, GeneralCK.Certificates.E8TAxisProd0597Certified, GeneralCK.Certificates.E8TAxisProd0598Certified, GeneralCK.Certificates.E8TAxisProd0599Certified, GeneralCK.Certificates.E8TAxisProd0600Certified, GeneralCK.Certificates.E8TAxisProd0601Certified, GeneralCK.Certificates.E8TAxisProd0602Certified, GeneralCK.Certificates.E8TAxisProd0603Certified) (piece 1 of 25) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0579Certified (+24 modules: GeneralCK.Certificates.E8TAxisProd0580Certified, GeneralCK.Certificates.E8TAxisProd0581Certified, GeneralCK.Certificates.E8TAxisProd0582Certified, GeneralCK.Certificates.E8TAxisProd0583Certified, GeneralCK.Certificates.E8TAxisProd0584Certified, GeneralCK.Certificates.E8TAxisProd0585Certified, GeneralCK.Certificates.E8TAxisProd0586Certified, GeneralCK.Certificates.E8TAxisProd0587Certified, GeneralCK.Certificates.E8TAxisProd0588Certified, GeneralCK.Certificates.E8TAxisProd0589Certified, GeneralCK.Certificates.E8TAxisProd0590Certified, GeneralCK.Certificates.E8TAxisProd0591Certified, GeneralCK.Certificates.E8TAxisProd0592Certified, GeneralCK.Certificates.E8TAxisProd0593Certified, GeneralCK.Certificates.E8TAxisProd0594Certified, GeneralCK.Certificates.E8TAxisProd0595Certified, GeneralCK.Certificates.E8TAxisProd0596Certified, GeneralCK.Certificates.E8TAxisProd0597Certified, GeneralCK.Certificates.E8TAxisProd0598Certified, GeneralCK.Certificates.E8TAxisProd0599Certified, GeneralCK.Certificates.E8TAxisProd0600Certified, GeneralCK.Certificates.E8TAxisProd0601Certified, GeneralCK.Certificates.E8TAxisProd0602Certified, GeneralCK.Certificates.E8TAxisProd0603Certified) (piece 1 of 25) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0579Certified (+24 modules: GeneralCK/Certificates/E8TAxisProd0580Certified, GeneralCK/Certificates/E8TAxisProd0581Certified, GeneralCK/Certificates/E8TAxisProd0582Certified, GeneralCK/Certificates/E8TAxisProd0583Certified, GeneralCK/Certificates/E8TAxisProd0584Certified, GeneralCK/Certificates/E8TAxisProd0585Certified, GeneralCK/Certificates/E8TAxisProd0586Certified, GeneralCK/Certificates/E8TAxisProd0587Certified, GeneralCK/Certificates/E8TAxisProd0588Certified, GeneralCK/Certificates/E8TAxisProd0589Certified, GeneralCK/Certificates/E8TAxisProd0590Certified, GeneralCK/Certificates/E8TAxisProd0591Certified, GeneralCK/Certificates/E8TAxisProd0592Certified, GeneralCK/Certificates/E8TAxisProd0593Certified, GeneralCK/Certificates/E8TAxisProd0594Certified, GeneralCK/Certificates/E8TAxisProd0595Certified, GeneralCK/Certificates/E8TAxisProd0596Certified, GeneralCK/Certificates/E8TAxisProd0597Certified, GeneralCK/Certificates/E8TAxisProd0598Certified, GeneralCK/Certificates/E8TAxisProd0599Certified, GeneralCK/Certificates/E8TAxisProd0600Certified, GeneralCK/Certificates/E8TAxisProd0601Certified, GeneralCK/Certificates/E8TAxisProd0602Certified, GeneralCK/Certificates/E8TAxisProd0603Certified) (piece 1 of 25) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0579Certified__25_q00_q00

namespace GeneralCK.Certificates.E8TAxisProd0579Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0579Geometry E8TAxisProd0579CertifiedArithmetic
theorem wholeBoxes_contains {s t : ℝ} (h : InCell s t) : wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0579EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    have hh := E8TAxisProd0579GraphWholeA.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0579EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0579GraphWholeB.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0579EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    have hh := E8TAxisProd0579GraphWholeC.qJetBox_contains ha hpos
    rwa [hy] at hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0579EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    have hh := E8TAxisProd0579GraphWholeD.qJetBox_contains ha hpos
    rwa [hy] at hh

end GeneralCK.Certificates.E8TAxisProd0579Certified


