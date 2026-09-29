-- Prove2me | Definitions.Def_Freiman_section14WitnessDataPart3
-- name    : Freiman_section14WitnessDataPart3
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:41:34.299704+00:00
-- url     : https://prove2.me/theorems/8af76a8b-afb5-413b-a191-8c4fc84f8094
-- title:
--   Freiman §14: section14WitnessDataPart3
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Model

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataProofsPart3 : List Section14Proof :=
  [⟨⟨true,true,339⟩,⟨false,false,34⟩⟩,
   ⟨⟨true,true,339⟩,⟨false,false,50⟩⟩,
   ⟨⟨true,false,117⟩,⟨false,true,698⟩⟩,
   ⟨⟨true,false,728⟩,⟨false,false,3⟩⟩,
   ⟨⟨true,false,729⟩,⟨false,false,3⟩⟩,
   ⟨⟨true,false,730⟩,⟨false,false,3⟩⟩,
   ⟨⟨true,true,10⟩,⟨false,true,2⟩⟩,
   ⟨⟨true,false,67⟩,⟨false,false,4⟩⟩,
   ⟨⟨true,false,728⟩,⟨false,false,22⟩⟩,
   ⟨⟨true,false,729⟩,⟨false,false,22⟩⟩,
   ⟨⟨true,false,730⟩,⟨false,false,22⟩⟩]

end Freiman


