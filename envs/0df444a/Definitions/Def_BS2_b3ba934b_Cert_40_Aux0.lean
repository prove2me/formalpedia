-- Prove2me | Definitions.Def_BS2_b3ba934b_Cert_40_Aux0
-- name    : BS2_b3ba934b_Cert_40_Aux0
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:29:38.023023+00:00
-- url     : https://prove2.me/theorems/1caa81ce-ee34-4d3e-a39d-75809f6ea377
-- title:
--   Sensitivity separation: endpoint 40 profile 0 pure case data
-- statement:
--   Exact copies of the representative and case-index data from Endpoint40RawProof0 in a fresh namespace. No numerical certificate proof or old RawProof helper module is imported.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof0.lean; original SHA-256 7a31c8e6adad0d094c67f9734e9b91bcdce1bd75ee2ff74105e322d178af9e1a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

namespace BS2_b3ba934b_Cert_40_Aux0
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

def caseTable0 : NatTable :=
(.branch 800
(.branch 400
(.branch 200
(.branch 100
(.branch 50
(.branch 25
(.branch 12
(.branch 6
(.branch 3
(.branch 1
(.leaf 0)
(.branch 2
(.leaf 0)
(.leaf 2)))
(.leaf 0))
(.leaf 0))
(.leaf 0))
(.branch 37
(.leaf 0)
(.branch 43
(.branch 40
(.leaf 0)
(.branch 41
(.leaf 0)
(.branch 42
(.leaf 1)
(.leaf 3))))
(.leaf 0))))
(.branch 75
(.leaf 0)
(.branch 87
(.branch 81
(.leaf 0)
(.branch 84
(.branch 82
(.leaf 0)
(.branch 83
(.leaf 4)
(.leaf 0)))
(.leaf 0)))
(.leaf 0))))
(.leaf 0))
(.leaf 0))
(.leaf 0))
(.leaf 0))
def caseIndex0 (i j : Fin 40) : Fin 5 :=
  ⟨caseTable0.get (40*i.val+j.val)%5,Nat.mod_lt _ (by decide)⟩

end BS2_b3ba934b_Cert_40_Aux0


