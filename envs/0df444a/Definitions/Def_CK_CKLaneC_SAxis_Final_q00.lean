-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Final_q00
-- name    : CK_CKLaneC_SAxis_Final_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T23:48:37.534404+00:00
-- url     : https://prove2.me/theorems/9b01cf1b-b74f-40a1-8ed1-321b3b040dff
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Final (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Final (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Final (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Final (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Final (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneC_SAxis_Final_q00_q00

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell CKLaneC.SAxis.Data
namespace CKLaneC.SAxis.Final
theorem cells_valid : ∀ w ∈ cells, w.check T = true :=
  (forall_mem_append_of cells00_valid (forall_mem_append_of cells01_valid (forall_mem_append_of cells02_valid (forall_mem_append_of cells03_valid (forall_mem_append_of cells04_valid (forall_mem_append_of cells05_valid (forall_mem_append_of cells06_valid (forall_mem_append_of cells07_valid (forall_mem_append_of cells08_valid (forall_mem_append_of cells09_valid (forall_mem_append_of cells10_valid (forall_mem_append_of cells11_valid (forall_mem_append_of cells12_valid (forall_mem_append_of cells13_valid (forall_mem_append_of cells14_valid (forall_mem_append_of cells15_valid (forall_mem_append_of cells16_valid (forall_mem_append_of cells17_valid (forall_mem_append_of cells18_valid (forall_mem_append_of cells19_valid (forall_mem_append_of cells20_valid (forall_mem_append_of cells21_valid (forall_mem_append_of cells22_valid (forall_mem_append_of cells23_valid (forall_mem_append_of cells24_valid (forall_mem_append_of cells25_valid (forall_mem_append_of cells26_valid (forall_mem_append_of cells27_valid forall_mem_nil_of))))))))))))))))))))))))))))

end CKLaneC.SAxis.Final


