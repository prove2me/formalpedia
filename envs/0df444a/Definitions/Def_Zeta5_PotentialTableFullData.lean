-- Prove2me | Definitions.Def_Zeta5_PotentialTableFullData
-- name    : Zeta5_PotentialTableFullData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-13T15:15:31.551442+00:00
-- url     : https://prove2.me/theorems/072ad8ba-9646-40ec-9464-cb7313fec07a
-- title:
--   Complete rational potential certificate on the short segment
-- statement:
--   A balanced assembly of eleven rational certificate chunks for all 684 intervals of the short-segment potential table. Its outer endpoints are
--
--   $$L=0,\qquad R=2.$$
--
--   The definition contains data only. The eleven chunk validity theorems and the rational overlap checks certify the assembled tree; the generic soundness theorem then gives the potential inequality for every $0<t\le2$.
-- source:
--   Derived rational-certificate encoding of mo271/Zeta5 at commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Table2/All.lean, potential_ineq_le_two (lines 4116–4120), and the U*.lean/I*.lean certificate files; https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Table2/All.lean#L4116-L4120. The certificate datatype and its generic soundness adapter are new formalization infrastructure.

import Definitions.Def_Zeta5_PotentialTableBlock0_63Data
import Definitions.Def_Zeta5_PotentialTableBlock64_127Data
import Definitions.Def_Zeta5_PotentialTableBlock128_191Data
import Definitions.Def_Zeta5_PotentialTableBlock192_255Data
import Definitions.Def_Zeta5_PotentialTableBlock256_319Data
import Definitions.Def_Zeta5_PotentialTableBlock320_383Data
import Definitions.Def_Zeta5_PotentialTableBlock384_447Data
import Definitions.Def_Zeta5_PotentialTableBlock448_511Data
import Definitions.Def_Zeta5_PotentialTableBlock512_575Data
import Definitions.Def_Zeta5_PotentialTableBlock576_639Data
import Definitions.Def_Zeta5_PotentialTableBlock640_683Data

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Apery.PotentialCertificate.FullTable

def certificate : TableCertificate :=
  (.join (.join (.join TableBlock0_63.certificate TableBlock64_127.certificate) (.join TableBlock128_191.certificate (.join TableBlock192_255.certificate TableBlock256_319.certificate))) (.join (.join TableBlock320_383.certificate (.join TableBlock384_447.certificate TableBlock448_511.certificate)) (.join TableBlock512_575.certificate (.join TableBlock576_639.certificate TableBlock640_683.certificate))))

end Apery.PotentialCertificate.FullTable


