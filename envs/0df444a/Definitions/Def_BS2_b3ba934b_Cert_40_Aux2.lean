-- Prove2me | Definitions.Def_BS2_b3ba934b_Cert_40_Aux2
-- name    : BS2_b3ba934b_Cert_40_Aux2
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T05:06:31.370063+00:00
-- url     : https://prove2.me/theorems/ce03c26c-6805-433e-a64d-7b04c605bb54
-- title:
--   Sensitivity separation: endpoint 40 profile 2 pure case data
-- statement:
--   Exact copies of the representative and case-index data from Endpoint40RawProof2 in a fresh namespace. No numerical certificate proof or old RawProof helper module is imported.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof2.lean; original SHA-256 5c3795e111da5588d9d11d9eefb7938f801835b24c79c5f7b8e2fc1a7db5327d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

namespace BS2_b3ba934b_Cert_40_Aux2
def representativePairs2 : Array (Fin 40 × Fin 40) := #[(0,2),(1,2),(2,2),(0,3),(1,3),(2,3),(3,3)]
def representativeBoundTable2 : NatTable :=
(.branch 3
(.branch 1
(.leaf 439022647791663747058857540000000000000000000000000000000000000000000000)
(.branch 2
(.leaf 439022647791663747058857540000000000000000000000000000000000000000000000)
(.leaf 10509878689536842271677007430000000000000000000000000000000000000000000000)))
(.branch 5
(.leaf 333228916662993117187787030000000000000000000000000000000000000000000000)
(.branch 6
(.leaf 333228916662993117187787030000000000000000000000000000000000000000000000)
(.leaf 4560729516651630895596915310000000000000000000000000000000000000000000000))))
def representative2 (k : Fin 7) : Fin 40 × Fin 40 := representativePairs2.getD k.val (0,0)
def representativeBound2 (k : Fin 7) : ℕ := representativeBoundTable2.get k.val

def caseTable2 : NatTable :=
(.branch 800
(.branch 400
(.branch 200
(.branch 100
(.branch 50
(.branch 25
(.branch 12
(.branch 6
(.branch 3
(.leaf 0)
(.branch 4
(.leaf 3)
(.leaf 0)))
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
(.leaf 0)
(.leaf 1))))
(.branch 46
(.branch 44
(.leaf 4)
(.leaf 0))
(.leaf 0)))))
(.branch 75
(.leaf 0)
(.branch 87
(.branch 81
(.leaf 0)
(.branch 84
(.branch 82
(.leaf 0)
(.branch 83
(.leaf 2)
(.leaf 5)))
(.leaf 0)))
(.leaf 0))))
(.branch 150
(.branch 125
(.branch 112
(.leaf 0)
(.branch 118
(.leaf 0)
(.branch 121
(.leaf 0)
(.branch 123
(.leaf 0)
(.branch 124
(.leaf 6)
(.leaf 0))))))
(.leaf 0))
(.leaf 0)))
(.leaf 0))
(.leaf 0))
(.leaf 0))
def caseIndex2 (i j : Fin 40) : Fin 7 :=
  ⟨caseTable2.get (40*i.val+j.val)%7,Nat.mod_lt _ (by decide)⟩

end BS2_b3ba934b_Cert_40_Aux2


