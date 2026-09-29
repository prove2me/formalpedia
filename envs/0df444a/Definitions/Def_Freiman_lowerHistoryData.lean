-- Prove2me | Definitions.Def_Freiman_lowerHistoryData
-- name    : Freiman_lowerHistoryData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:04:18.638906+00:00
-- url     : https://prove2.me/theorems/1056f327-287f-413a-b30f-f3ea8b74f956
-- title:
--   Freiman.lowerHistoryData
-- statement:
--   Aggregator for the five catalogs, shared dictionaries and bounded witness modules; preserves the published packet IDs. Source: Freiman's Hall ray: Proof report and corrected English text (8 September 2026); history_certificates.tex app:all-suffix-histories, global_selection.tex lem:global-suffix-targets; initial_bridges.tex lem:H-entry-bridges; certificates/target_selection/all_suffix_histories_printed.json.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Appendix app:all-suffix-histories and its exact arithmetic/certificate guide.

import Definitions.Def_Freiman_lowerHistoryShared
import Definitions.Def_Freiman_lowerHistoryWitnesses01
import Definitions.Def_Freiman_lowerHistoryWitnesses02
import Definitions.Def_Freiman_lowerHistoryWitnesses03
import Definitions.Def_Freiman_lowerHistoryWitnesses04
import Definitions.Def_Freiman_lowerHistoryWitnesses05
import Definitions.Def_Freiman_lowerHistoryWitnesses06
import Definitions.Def_Freiman_lowerHistoryCatalogL
import Definitions.Def_Freiman_lowerHistoryCatalogR
import Definitions.Def_Freiman_lowerHistoryCatalogM
import Definitions.Def_Freiman_lowerHistoryCatalogX
import Definitions.Def_Freiman_lowerHistoryCatalogH

namespace Freiman
def lowerHistoryWitnesses : Array CertWitness := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05 ++ lowerHistoryWitnesses06
def lowerHistoryWitness (id : ℕ) : CertWitness := (lowerHistoryWitnesses[id-1]?).getD
  ⟨lowerHistoryBound 0,lowerHistoryBound 0,⟨0,1,0,1⟩,fun _ _ => ⟨0,0,0,0⟩,fun _ _ => 0⟩

def lowerHistoryWitnessIds : Array (ℕ × ℕ) := lowerHistoryWitnessIds01 ++ lowerHistoryWitnessIds02 ++ lowerHistoryWitnessIds03 ++ lowerHistoryWitnessIds04 ++ lowerHistoryWitnessIds05 ++ lowerHistoryWitnessIds06
def lowerHistoryPaths : Array LowerHistoryPath := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX ++ lowerHistoryPathsH
def lowerHistoryRecords : Array LowerHistoryRecord := lowerHistoryRecordsL ++ lowerHistoryRecordsR ++ lowerHistoryRecordsM ++ lowerHistoryRecordsX ++ lowerHistoryRecordsH
end Freiman


