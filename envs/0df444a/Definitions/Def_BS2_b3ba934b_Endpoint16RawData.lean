-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawData
-- name    : BS2_b3ba934b_Endpoint16RawData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:27:47.089083+00:00
-- url     : https://prove2.me/theorems/fa03f203-4b2c-4454-a1c5-59866210d502
-- title:
--   Sensitivity separation: Endpoint16RawData (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawData` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawData.lean; original SHA-256 d911862e0c354cab4acf03445394cd6214176df215d4ba5f6064ff3429582ceb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_MinmaxAExpressions

set_option autoImplicit false

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

abbrev caps : Caps := ThreeBoundNumeric.Endpoint40.caps
abbrev records : List (List ℕ) := ThreeBoundNumeric.Endpoint40.records

def raw (p : Fin 4) (v : Profile 16) : Profile 16 :=
  rawTransfer 16 5003 caps.pcross (ThreeBoundMinmaxA.rawAExpr 16 caps records) (recipe p) v

theorem raw_homogeneous (p : Fin 4) (v : Profile 16) (c : ℕ) :
    raw p (fun coord=>c*v coord)=fun coord=>c*raw p v coord :=
  rawTransfer_homogeneous 16 5003 caps.pcross
    (ThreeBoundMinmaxA.rawAExpr 16 caps records) (recipe p) v c

end ThreeBoundMinmaxNumeric.Endpoint16


