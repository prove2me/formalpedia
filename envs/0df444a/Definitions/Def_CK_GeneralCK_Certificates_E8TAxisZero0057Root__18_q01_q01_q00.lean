-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Root__18_q01_q01_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057Root__18_q01_q01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T17:56:17.462651+00:00
-- url     : https://prove2.me/theorems/2dcce599-1f55-43a8-b0bb-7f98f5b21d23
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057Root (+17 modules: GeneralCK.Certificates.E8TAxisZero0058Root, GeneralCK.Certificates.E8TAxisZero0059Root, GeneralCK.Cer…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057Root (+17 modules: GeneralCK.Certificates.E8TAxisZero0058Root, GeneralCK.Certificates.E8TAxisZero0059Root, GeneralCK.Certificates.E8TAxisZero0060Root, GeneralCK.Certificates.E8TAxisZero0061Root, GeneralCK.Certificates.E8TAxisZero0062Root, GeneralCK.Certificates.E8TAxisZero0063Root, GeneralCK.Certificates.E8TAxisZero0064Root, GeneralCK.Certificates.E8TAxisZero0065Root, GeneralCK.Certificates.E8TAxisZero0066Root, GeneralCK.Certificates.E8TAxisZero0067Root, GeneralCK.Certificates.E8TAxisZero0068Root, GeneralCK.Certificates.E8TAxisZero0069Root, GeneralCK.Certificates.E8TAxisZero0070Root, GeneralCK.Certificates.E8TAxisZero0071Root, GeneralCK.Certificates.E8TAxisZero0072Root, GeneralCK.Certificates.E8TAxisZero0073Root, GeneralCK.Certificates.E8TAxisZero0074Root) (piece 2 of 18) (piece 2 of 3) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057Root (+17 modules: GeneralCK.Certificates.E8TAxisZero0058Root, GeneralCK.Certificates.E8TAxisZero0059Root, GeneralCK.Certificates.E8TAxisZero0060Root, GeneralCK.Certificates.E8TAxisZero0061Root, GeneralCK.Certificates.E8TAxisZero0062Root, GeneralCK.Certificates.E8TAxisZero0063Root, GeneralCK.Certificates.E8TAxisZero0064Root, GeneralCK.Certificates.E8TAxisZero0065Root, GeneralCK.Certificates.E8TAxisZero0066Root, GeneralCK.Certificates.E8TAxisZero0067Root, GeneralCK.Certificates.E8TAxisZero0068Root, GeneralCK.Certificates.E8TAxisZero0069Root, GeneralCK.Certificates.E8TAxisZero0070Root, GeneralCK.Certificates.E8TAxisZero0071Root, GeneralCK.Certificates.E8TAxisZero0072Root, GeneralCK.Certificates.E8TAxisZero0073Root, GeneralCK.Certificates.E8TAxisZero0074Root) (piece 2 of 18) (piece 2 of 3) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057Root (+17 modules: GeneralCK.Certificates.E8TAxisZero0058Root, GeneralCK.Certificates.E8TAxisZero0059Root, GeneralCK.Certificates.E8TAxisZero0060Root, GeneralCK.Certificates.E8TAxisZero0061Root, GeneralCK.Certificates.E8TAxisZero0062Root, GeneralCK.Certificates.E8TAxisZero0063Root, GeneralCK.Certificates.E8TAxisZero0064Root, GeneralCK.Certificates.E8TAxisZero0065Root, GeneralCK.Certificates.E8TAxisZero0066Root, GeneralCK.Certificates.E8TAxisZero0067Root, GeneralCK.Certificates.E8TAxisZero0068Root, GeneralCK.Certificates.E8TAxisZero0069Root, GeneralCK.Certificates.E8TAxisZero0070Root, GeneralCK.Certificates.E8TAxisZero0071Root, GeneralCK.Certificates.E8TAxisZero0072Root, GeneralCK.Certificates.E8TAxisZero0073Root, GeneralCK.Certificates.E8TAxisZero0074Root) (piece 2 of 18) (piece 2 of 3) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057Root (+17 modules: GeneralCK/Certificates/E8TAxisZero0058Root, GeneralCK/Certificates/E8TAxisZero0059Root, GeneralCK/Certificates/E8TAxisZero0060Root, GeneralCK/Certificates/E8TAxisZero0061Root, GeneralCK/Certificates/E8TAxisZero0062Root, GeneralCK/Certificates/E8TAxisZero0063Root, GeneralCK/Certificates/E8TAxisZero0064Root, GeneralCK/Certificates/E8TAxisZero0065Root, GeneralCK/Certificates/E8TAxisZero0066Root, GeneralCK/Certificates/E8TAxisZero0067Root, GeneralCK/Certificates/E8TAxisZero0068Root, GeneralCK/Certificates/E8TAxisZero0069Root, GeneralCK/Certificates/E8TAxisZero0070Root, GeneralCK/Certificates/E8TAxisZero0071Root, GeneralCK/Certificates/E8TAxisZero0072Root, GeneralCK/Certificates/E8TAxisZero0073Root, GeneralCK/Certificates/E8TAxisZero0074Root) (piece 2 of 18) (piece 2 of 3) (piece 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Root__18_q01_q00


namespace GeneralCK.Certificates.E8TAxisZero0058Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

end GeneralCK.Certificates.E8TAxisZero0058Root


