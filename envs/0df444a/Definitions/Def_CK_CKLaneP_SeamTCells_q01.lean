-- Prove2me | Definitions.Def_CK_CKLaneP_SeamTCells_q01
-- name    : CK_CKLaneP_SeamTCells_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T14:05:38.732726+00:00
-- url     : https://prove2.me/theorems/53c3eaea-7fea-4a07-856d-2b32d5b64b7c
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamTCells (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamTCells (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamTCells (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamTCells (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamTCells (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneP_SeamTCells_q00

set_option autoImplicit false
namespace CKLaneP
open GeneralCK
def tcells : List (ℕ × TCell) :=
  [(2, ⟨(1 / 200000 : ℚ), 5764607523035, (0 : ℚ), (895 / 131072 : ℚ), 5765792771168, (107246001038549449703425 / 1208925819614629174706176 : ℚ), 476416425947612672, 476416425747523072, (992562804856665 / 2251799813685248 : ℚ), 219535701024078560, 219535701463149952⟩),
   (0, ⟨(1 / 200000 : ℚ), 5764607523035, (895 / 131072 : ℚ), (462857 / 16777216 : ℚ), 5765792771168, (608801331727944736833537 / 1208925819614629174706176 : ℚ), 195347413612535104, 195347413221839360, (1 : ℚ), 1, 1⟩),
   (0, ⟨(1 / 200000 : ℚ), 5764607523035, (462857 / 16777216 : ℚ), (279917 / 2097152 : ℚ), 5765792771168, (355122805407836106915841 / 1208925819614629174706176 : ℚ), 297480535351408896, 297480534793447552, (1 : ℚ), 1, 1⟩),
   (0, ⟨(1 / 200000 : ℚ), 5764607523035, (279917 / 2097152 : ℚ), (1431241 / 4194304 : ℚ), 5765792771168, (173389647691816475033601 / 1208925819614629174706176 : ℚ), 420001491743742592, 420001491430823168, (1 : ℚ), 1, 1⟩),
   (0, ⟨(1 / 200000 : ℚ), 5764607523035, (1431241 / 4194304 : ℚ), (8876863 / 16777216 : ℚ), 5765792771168, (88760424406127130705921 / 1208925819614629174706176 : ℚ), 493093768599918912, 493093768433184064, (1 : ℚ), 1, 1⟩),
   (0, ⟨(1 / 200000 : ℚ), 5764607523035, (8876863 / 16777216 : ℚ), (10912117 / 16777216 : ℚ), 5765792771168, (52002140253158260080641 / 1208925819614629174706176 : ℚ), 527129944275628992, 527129944176966464, (1 : ℚ), 1, 1⟩),
   (0, ⟨(1 / 200000 : ℚ), 5764607523035, (10912117 / 16777216 : ℚ), (735917 / 1048576 : ℚ), 5765792771168, (35035670483721982574593 / 1208925819614629174706176 : ℚ), 543128760214614720, 543128760147949760, (1 : ℚ), 1, 1⟩),
   (1, ⟨(1 / 200000 : ℚ), 5764607523035, (735917 / 1048576 : ℚ), (1 : ℚ), 5765792771168, (34602686945157477040129 / 1208925819614629174706176 : ℚ), 543538741163992704, 543538741098147712, (1 : ℚ), 1, 1⟩)]

end CKLaneP


