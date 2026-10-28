-- Prove2me | Definitions.Def_BS2_b3ba934b_Cert_40_Aux3
-- name    : BS2_b3ba934b_Cert_40_Aux3
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:33:49.8371+00:00
-- url     : https://prove2.me/theorems/ab61c89b-7fa7-4a99-96cc-aea5d404fcb6
-- title:
--   Sensitivity separation: endpoint 40 profile 3 pure case data
-- statement:
--   Exact copies of the representative and case-index data from Endpoint40RawProof3 in a fresh namespace. No numerical certificate proof or old RawProof helper module is imported.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof3.lean; original SHA-256 52106b0976aad197869ce9c3632aa349f775d54c498fea7ebf8933a746553dfe; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

namespace BS2_b3ba934b_Cert_40_Aux3
def representativePairs3 : Array (Fin 40 × Fin 40) := #[(0,3),(1,3),(2,3),(3,3),(0,4),(1,4),(2,4),(3,4),(4,4)]
def representativeBoundTable3 : NatTable :=
(.branch 4
(.branch 2
(.leaf 32945822928780164219782456170000000000000000000000000000000000000000000000)
(.branch 3
(.leaf 32945822928780164219782456170000000000000000000000000000000000000000000000)
(.leaf 788367171188124766890095226590000000000000000000000000000000000000000000000)))
(.branch 6
(.leaf 25006000113424645102729645880000000000000000000000000000000000000000000000)
(.branch 7
(.leaf 25006000113424645102729645880000000000000000000000000000000000000000000000)
(.branch 8
(.leaf 25006000113424645102729645880000000000000000000000000000000000000000000000)
(.leaf 342172149755249424156185556300000000000000000000000000000000000000000000000)))))
def representative3 (k : Fin 9) : Fin 40 × Fin 40 := representativePairs3.getD k.val (0,0)
def representativeBound3 (k : Fin 9) : ℕ := representativeBoundTable3.get k.val

def caseTable3 : NatTable :=
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
(.leaf 0)
(.branch 5
(.leaf 4)
(.leaf 0))))
(.leaf 0))
(.leaf 0))
(.branch 37
(.leaf 0)
(.branch 43
(.leaf 0)
(.branch 46
(.branch 44
(.leaf 1)
(.branch 45
(.leaf 5)
(.leaf 0)))
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
(.leaf 0)
(.leaf 2)))
(.branch 85
(.leaf 6)
(.leaf 0))))
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
(.leaf 3)
(.leaf 7))))))
(.leaf 0))
(.branch 175
(.branch 162
(.leaf 0)
(.branch 168
(.branch 165
(.branch 163
(.leaf 0)
(.branch 164
(.leaf 0)
(.leaf 8)))
(.leaf 0))
(.leaf 0)))
(.leaf 0))))
(.leaf 0))
(.leaf 0))
(.leaf 0))
def caseIndex3 (i j : Fin 40) : Fin 9 :=
  ⟨caseTable3.get (40*i.val+j.val)%9,Nat.mod_lt _ (by decide)⟩

end BS2_b3ba934b_Cert_40_Aux3


