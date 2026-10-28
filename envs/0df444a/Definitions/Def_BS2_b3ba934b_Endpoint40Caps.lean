-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40Caps
-- name    : BS2_b3ba934b_Endpoint40Caps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:23:11.409739+00:00
-- url     : https://prove2.me/theorems/535d6ead-85ed-4ead-a6a6-9414b2e909b5
-- title:
--   Sensitivity separation: Endpoint40Caps (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40Caps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40Caps.lean; original SHA-256 6ed7a5790f81dcdaca0ca854932102aacbbc71dd12089b8d83f24c9e446ea3e4; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The selected Paley labeling satisfies precisely the numerical caps used
   by the first-endpoint q2 transfer. -/
import Definitions.Def_BS2_b3ba934b_ActualCapPrefix
import Definitions.Def_BS2_b3ba934b_SelectedBoolCaps
import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundEndpoint40Caps
open Sensitivity10007Labeling ThreeBoundNumeric

theorem caps_sound : ThreeBoundActualCaps.CapsSound
    Labeling10007.Adj Sensitivity10007BoolCaps.label Endpoint40.caps where
  ordinary q hq := by
    interval_cases q
    · exact Sensitivity10007BoolCaps.selected_ordinary 0
    · exact Sensitivity10007BoolCaps.selected_ordinary 1
    · exact Sensitivity10007BoolCaps.selected_ordinary 2
  source := by
    intro A M color hdis hM hdom hmis
    apply Sensitivity10007BoolCaps.selected_source A M color hdis hM hdom
    intro v hv
    exact hmis v (by simpa only [Finset.mem_union] using hv)
  double := by
    intro A M color hdis hM hdom hmis
    apply Sensitivity10007BoolCaps.selected_double A M color hdis hM hdom
    intro v hv
    exact hmis v (by simpa only [Finset.mem_union] using hv)
  markedOne q hqlo hqhi := by
    interval_cases q
    · exact Sensitivity10007BoolCaps.selected_marked 0
    · exact Sensitivity10007BoolCaps.selected_marked 1
  markedTwo q hqlo hqhi := by
    interval_cases q
    · exact Sensitivity10007BoolCaps.selected_marked 4
    · exact Sensitivity10007BoolCaps.selected_marked 5
  zeroThree := Sensitivity10007BoolCaps.selected_marked 6
  zeroFour := Sensitivity10007BoolCaps.selected_marked 7
  zeroThree_pos := by decide
  zeroFour_pos := by decide

theorem stage_caps_sound {I : Type} (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool) :
    ThreeBoundActualCaps.CapsSound
      ((Sensitivity10007Endpoint40.recipe p).stage F).Adj
      ((Sensitivity10007Endpoint40.recipe p).stage F).label Endpoint40.caps :=
  caps_sound

end ThreeBoundEndpoint40Caps

#print axioms ThreeBoundEndpoint40Caps.caps_sound
#print axioms ThreeBoundEndpoint40Caps.stage_caps_sound


