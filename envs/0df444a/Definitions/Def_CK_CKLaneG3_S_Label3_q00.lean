-- Prove2me | Definitions.Def_CK_CKLaneG3_S_Label3_q00
-- name    : CK_CKLaneG3_S_Label3_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T23:15:59.485357+00:00
-- url     : https://prove2.me/theorems/d4a0773d-41c8-4368-8b2f-5fea7aaff0e1
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.Label3 (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.Label3 (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.Label3 (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.Label3 (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/Label3 (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneG3_S_Label3_q00_q01

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.Label3
open CKLaneD CKLaneG3 CKLaneG3.S
def runs0 : List (ℕ × ℕ × ℕ) := [(122, 39, 11), (123, 0, 50), (124, 0, 4), (124, 27, 23), (125, 0, 13), (127, 25, 25), (128, 0, 8), (128, 34, 16), (129, 0, 50), (130, 0, 8), (130, 36, 1), (130, 34, 2), (130, 37, 13), (131, 0, 1), (132, 21, 29), (133, 0, 9), (133, 26, 24), (134, 0, 50), (135, 0, 28), (139, 16, 34), (140, 0, 35), (140, 48, 2), (141, 0, 50), (142, 0, 15), (143, 6, 44), (144, 0, 16), (145, 14, 22), (146, 5, 16), (126, 14, 36), (127, 0, 25), (131, 1, 48), (133, 9, 10), (137, 46, 4), (150, 2, 9), (4, 15, 35), (5, 0, 50), (6, 0, 8), (6, 13, 5), (6, 46, 4), (7, 0, 42), (11, 36, 10), (87, 1, 13), (88, 16, 22), (113, 38, 12), (114, 0, 37), (115, 22, 25), (116, 11, 18), (119, 26, 24), (120, 0, 28), (125, 46, 4), (126, 0, 14), (128, 8, 26), (117, 13, 37), (118, 0, 50), (119, 0, 4), (120, 28, 22), (122, 19, 4), (130, 8, 26), (142, 15, 35), (143, 0, 6), (144, 16, 34), (145, 0, 14), (145, 36, 5), (149, 7, 43), (150, 0, 2), (145, 41, 9), (146, 0, 5), (150, 11, 39), (151, 0, 4), (152, 36, 14), (153, 0, 7), (146, 21, 29), (147, 0, 50), (148, 0, 10), (148, 39, 11), (149, 0, 7), (148, 10, 29), (151, 4, 46), (152, 0, 36), (121, 0, 50), (122, 0, 19), (122, 23, 16), (125, 13, 33), (124, 4, 23), (131, 49, 1), (132, 0, 21), (133, 19, 7), (136, 28, 22), (137, 0, 46), (138, 0, 50), (139, 0, 16), (140, 35, 13), (135, 28, 22), (136, 0, 28), (119, 4, 22), (7, 42, 8), (8, 0, 50), (9, 0, 32), (10, 0, 10), (10, 22, 8)]
end CKLaneG3.S.Label3


