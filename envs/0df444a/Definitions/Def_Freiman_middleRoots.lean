-- Prove2me | Definitions.Def_Freiman_middleRoots
-- name    : Freiman_middleRoots
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:38:31.111883+00:00
-- url     : https://prove2.me/theorems/b7deac31-0c5b-48dc-a195-c7895d706ba3
-- title:
--   The fifteen exact middle-interval roots
-- statement:
--   The fifteen physical source p.51 cores converted to outward left/right words, and the exact rational inner endpoints from the report initial table.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex

import Definitions.Def_Freiman_middleCover

namespace Freiman

def middleRootList : List MiddleCore :=
  [⟨[1,2], [2]⟩, ⟨[1,1], [2]⟩, ⟨[1,1], [3]⟩, ⟨[2], [2]⟩,
   ⟨[2], [3]⟩, ⟨[2,1,1,3], [4,3]⟩, ⟨[2,1,1,2], [4,3]⟩,
   ⟨[2,1,1,3,1,1], [4,2,1,1,1]⟩, ⟨[2,1,1,3,1,1], [4,2,1,1,2]⟩,
   ⟨[2,1,1,3,2], [4,2,1,1,1]⟩, ⟨[2,1,1,3,2], [4,2,1,1,2]⟩,
   ⟨[2,1,1,1], [4,3]⟩, ⟨[3,3], [3,3]⟩,
   ⟨[2,1,2], [4,3]⟩, ⟨[3], [3]⟩]
def middleRoot (i : Fin 15) : MiddleCore := middleRootList.getD i.val ⟨[],[]⟩
noncomputable def middleInnerLeft (i : Fin 15) : ℝ :=
  (([5059463058,4916850791,4822202079,4724058589,4622202079,
     4621871403,4618712495,4618521582,4618264666,4618053907,
     4617778623,4610772007,4605715026,4598168284,4531593457] : List ℕ).getD i.val 0 : ℝ) / 1000000000
noncomputable def middleInnerRight (i : Fin 15) : ℝ :=
  (([5177797921,5083149209,4940536942,4864968876,4747744739,
     4625420264,4622535073,4618955900,4618565660,4618443970,
     4618098712,4617797239,4612408183,4605774287,4603775776] : List ℕ).getD i.val 0 : ℝ) / 1000000000
noncomputable def middleRootCertificate (i : Fin 15) : Prop :=
  middleRegular (middleRoot i) ∧ middleRatio (middleRoot i) < (19 / 5 : ℝ) ∧
  (middleBounds (middleRoot i)).1 < middleInnerLeft i ∧
  middleInnerRight i < (middleBounds (middleRoot i)).2

end Freiman


