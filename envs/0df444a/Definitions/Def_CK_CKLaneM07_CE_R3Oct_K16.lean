-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Oct_K16
-- name    : CK_CKLaneM07_CE_R3Oct_K16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T20:59:26.570769+00:00
-- url     : https://prove2.me/theorems/9d766733-f1fc-44ab-8bc5-2bda66fde7a4
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Oct.K16` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Oct.K16` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Oct.K16` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Oct.K16 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Oct/K16.lean)

import Definitions.Def_CK_CKLaneM07_CE_R3Roots
import Definitions.Def_CK_CKLaneM07_CE_R3Glue
import Definitions.Def_CK_CKLaneM07_CE_R3Cells_K16_S0000__3
import Definitions.Def_CK_CKLaneM07_CE_R3Cells_K16_S0003__4
import Definitions.Def_CK_CKLaneM07_CE_R3Cells_K16_S0007__3
import Definitions.Def_CK_CKLaneM07_CE_R3Cells_K16_S0010__3
import Definitions.Def_CK_CKLaneM07_CE_R3Cells_K16_S0013__3
import Definitions.Def_CK_CKLaneM07_CE_R3Cells_K16_S0016__3
import Definitions.Def_CK_CKLaneM07_CE_R3Cells_K16_S0019__2
import Definitions.Def_CK_CKLaneM07_CE_R3Cells_K16_S0021__3

-- ===== source module CKLaneM07.CE.R3Oct.K16 =====
section

/-! Lane M07 row-3 octave k=16: 24 shards glued along the generated skeleton (R3Glue). -/

namespace CKLaneM07.CE.R3Oct.K16

open CKLaneN1 CKLaneM07.CE.R3Roots CKLaneM07.CE.R3Glue

set_option maxRecDepth 100000 in
theorem sem : CKLaneN1.R3.Sem root16 :=
  sem_node 2
    (sem_node 1
      (sem_node 2
        (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0000.sem)
        (sem_node 1
          (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0001.sem)
          (sem_node 1
            (sem_node 0
              (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0002.sem)
              (sem_node 2
                (sem_node 1
                  (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0003.sem)
                  (sem_node 0
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0004.sem)
                    (sem_node 2
                      (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0005.sem)
                      (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0006.sem))))
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0007.sem)))
            (sem_node 2
              (sem_node 0
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0008.sem)
                (sem_node 1
                  (sem_node 2
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0009.sem)
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0010.sem))
                  (sem_node 2
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0011.sem)
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0012.sem))))
              (sem_node 1
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0013.sem)
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0014.sem))))))
      (sem_node 2
        (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0015.sem)
        (sem_node 1
          (sem_node 1
            (sem_node 2
              (sem_node 0
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0016.sem)
                (sem_node 1
                  (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0017.sem)
                  (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0018.sem)))
              (sem_node 1
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0019.sem)
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0020.sem)))
            (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0021.sem))
          (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0022.sem))))
    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0023.sem)

end CKLaneM07.CE.R3Oct.K16

end


