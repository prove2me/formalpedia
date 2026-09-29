-- Prove2me | Definitions.Def_Freiman_lowerHistoryShared
-- name    : Freiman_lowerHistoryShared
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:00:42.957894+00:00
-- url     : https://prove2.me/theorems/da35317d-2870-4028-923a-cb8aae3d870e
-- title:
--   Freiman.lowerHistoryShared
-- statement:
--   Index-preserving shared bounds, premise dictionaries and rational rectangles used by all five catalogs. Source: Freiman's Hall ray: Proof report and corrected English text (8 September 2026); history_certificates.tex app:all-suffix-histories, global_selection.tex lem:global-suffix-targets; initial_bridges.tex lem:H-entry-bridges; certificates/target_selection/all_suffix_histories_printed.json.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Appendix app:all-suffix-histories and its exact arithmetic/certificate guide.

import Definitions.Def_Freiman_lowerHistoryBounds01
import Definitions.Def_Freiman_lowerHistoryBounds02
import Definitions.Def_Freiman_lowerHistoryBounds03
import Definitions.Def_Freiman_lowerHistoryBounds04
import Definitions.Def_Freiman_lowerHistoryBounds05
import Definitions.Def_Freiman_lowerHistoryBounds06
import Definitions.Def_Freiman_lowerHistoryPremises01
import Definitions.Def_Freiman_lowerHistoryPremises02
import Definitions.Def_Freiman_lowerHistoryPremises03
import Definitions.Def_Freiman_lowerHistoryPremises04
import Definitions.Def_Freiman_lowerHistoryPremises05
import Definitions.Def_Freiman_lowerHistoryPremises06

namespace Freiman
def lowerHistoryBounds : Array CertBound := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05 ++ lowerHistoryBounds06
def lowerHistoryBound (id : ℕ) : CertBound := lowerHistoryBounds[id-1]?.getD ⟨true,false,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

def lowerHistoryRectangles : Array CertRectangle := #[⟨(1/4),(1/3),(5/19),(4/15)⟩,⟨(1/4),(1/3),(3/4),(4/5)⟩,⟨(5/19),(4/15),(3/4),(4/5)⟩,⟨(1/3),(9/25),(5/19),(4/15)⟩,⟨(1/3),(1/2),(3/4),(4/5)⟩,⟨(1/2),(4/5),(3/4),(4/5)⟩,⟨(3/4),(4/5),(3/4),(4/5)⟩,⟨(15/19),(19/24),(3/4),(4/5)⟩]

def lowerHistoryPremises : Array (List ℕ) := lowerHistoryPremises01 ++ lowerHistoryPremises02 ++ lowerHistoryPremises03 ++ lowerHistoryPremises04 ++ lowerHistoryPremises05 ++ lowerHistoryPremises06
def lowerHistoryPremise (id : ℕ) : List CertBound := ((lowerHistoryPremises[id-1]?).getD []).map lowerHistoryBound

end Freiman


