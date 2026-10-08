-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Final
-- name    : CK_CKLaneA1_R5Final
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T13:26:10.058649+00:00
-- url     : https://prove2.me/theorems/eae6fe53-9e6b-41e3-9f4a-3d48a85c1d80
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Final` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Final` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Final` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Final (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Final.lean)

import Definitions.Def_CK_CKLaneA1_R5Final_q03

set_option autoImplicit false
namespace CKLaneA1.R5
open GeneralCK CKLaneP CKLaneN1.CEStat CKLaneA1.R5Data
/-- Binding to Lane N1's Prop (verbatim). -/
theorem highTCExclusion_binding : CKLaneN1.CEStat.HighTCExclusion := highTCExclusion

#print axioms highTCExclusion
#print axioms allStrips_ok
#print axioms allStrips_chain

end CKLaneA1.R5


