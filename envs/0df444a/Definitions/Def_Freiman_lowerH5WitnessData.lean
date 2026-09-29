-- Prove2me | Definitions.Def_Freiman_lowerH5WitnessData
-- name    : Freiman_lowerH5WitnessData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:39:02.730525+00:00
-- url     : https://prove2.me/theorems/f525f35d-cbbb-486f-93c4-36fc854faf43
-- title:
--   Freiman p97 predecessor certificates: lowerH5WitnessData lowerH5WitnessData
-- statement:
--   Actual source predecessor cases, exact Q(sqrt3,sqrt7) bound-pair witnesses, reconstructed endpoint residuals and earlier-depth priority events.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5WitnessChunk1
import Definitions.Def_Freiman_lowerH5WitnessChunk2
import Definitions.Def_Freiman_lowerH5WitnessChunk3
import Definitions.Def_Freiman_lowerH5WitnessChunk4
namespace Freiman
def lowerH5Witnesses : List CertWitness := lowerH5WitnessChunk1 ++ lowerH5WitnessChunk2 ++ lowerH5WitnessChunk3 ++ lowerH5WitnessChunk4
def lowerH5Witness (i : ℕ) : CertWitness := (lowerH5Witnesses[i-1]?).getD
  ⟨lowerHistoryZero,lowerHistoryHN,⟨0,1,0,1⟩,(fun _ _ => lowerHistoryRat 0),(fun _ _ => 0)⟩
end Freiman


