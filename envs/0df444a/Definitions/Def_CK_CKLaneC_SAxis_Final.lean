-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Final
-- name    : CK_CKLaneC_SAxis_Final
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T14:58:40.133675+00:00
-- url     : https://prove2.me/theorems/8c6514a5-5927-4216-b0e4-ad5bbb711139
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Final` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Final` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Final` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Final (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Final.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Final_q01

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell CKLaneC.SAxis.Data
namespace CKLaneC.SAxis.Final
/-- The s-axis derivative remainder below the `t = 16` tail (unconditional). -/
theorem e8SAxisDerivativeRemainderSixteen : GeneralCK.E8SAxisDerivativeRemainderSixteen := by
  intro s t hadm hs ht0 ht1 hsum
  have hs0 := hadm.1
  have ht0' := hadm.2.1
  exact Tree.check_sound T_valid cells_valid tree 0 (1 / 50) (3 / 50) 16 tree_ok s t
    (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) hs0 ht0' hsum

/-- The `sAxis` field of `GeneralCK.E8CertificateOwners`. -/
theorem sAxis : GeneralCK.E8PositiveOn fun s t => s ≤ 1 / 50 ∧ (3 / 50 : ℝ) ≤ t ∧ t ≤ 20 :=
  GeneralCK.e8_sAxis_of_sixteen_remainder e8SAxisDerivativeRemainderSixteen

end CKLaneC.SAxis.Final


