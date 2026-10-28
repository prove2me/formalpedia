-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawProof0_Numeric000
-- name    : BS2_b3ba934b_Endpoint40RawProof0_Numeric000
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:32:13.145169+00:00
-- url     : https://prove2.me/theorems/d7a4ed62-8884-4c77-a593-1e3967a16a91
-- title:
--   Sensitivity separation: Endpoint40RawProof0 numeric batch 1
-- statement:
--   Unchanged original numeric declarations from Endpoint40RawProof0, compiled in small batches. Original proof bodies and definitions are preserved; helper proofs are namespace-visible for import by the next batch.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof0.lean; original SHA-256 7a31c8e6adad0d094c67f9734e9b91bcdce1bd75ee2ff74105e322d178af9e1a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_0
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_1
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_2
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_3
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_4
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

def representativePairs0 : Array (Fin 40 × Fin 40) := #[(0,1),(1,1),(0,2),(1,2),(2,2)]
def representativeBoundTable0 : NatTable :=
(.branch 2
(.branch 1
(.leaf 77806142500417596074000000000000000000000000000000000000000000000000)
(.leaf 1865036319175702176328000000000000000000000000000000000000000000000000))
(.branch 3
(.leaf 59055514859764786074000000000000000000000000000000000000000000000000)
(.branch 4
(.leaf 59055514859764786074000000000000000000000000000000000000000000000000)
(.leaf 809387291765886661574000000000000000000000000000000000000000000000000))))
def representative0 (k : Fin 5) : Fin 40 × Fin 40 := representativePairs0.getD k.val (0,0)
def representativeBound0 (k : Fin 5) : ℕ := representativeBoundTable0.get k.val

theorem representative_checked0 (k : Fin 5) :
    (rawAExpr 40 caps records (recipe 0 (representative0 k).1)
      (recipe 0 (representative0 k).2)).eval profile0≤representativeBound0 k := by
  fin_cases k
  · exact RawPair0_0.raw_bound
  · exact RawPair0_1.raw_bound
  · exact RawPair0_2.raw_bound
  · exact RawPair0_3.raw_bound
  · exact RawPair0_4.raw_bound

end ThreeBoundNumeric.Endpoint40


