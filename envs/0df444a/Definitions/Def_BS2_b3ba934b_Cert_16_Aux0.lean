-- Prove2me | Definitions.Def_BS2_b3ba934b_Cert_16_Aux0
-- name    : BS2_b3ba934b_Cert_16_Aux0
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:29:02.63772+00:00
-- url     : https://prove2.me/theorems/c50176b2-29fa-487d-ad8b-a4ed297c2b00
-- title:
--   Sensitivity separation: endpoint 16 profile 0 pure case data
-- statement:
--   Exact copies of the representative and case-index data from Endpoint16RawProof0 in a fresh namespace. No numerical certificate proof or old RawProof helper module is imported.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof0.lean; original SHA-256 69fc765c38fd207decac7eddb39f39d683909d7ea74eed806ed2c3aa57dd71d2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

namespace BS2_b3ba934b_Cert_16_Aux0
def representativePairs0 : Array (Fin 16 × Fin 16) := #[(0,1),(1,1),(0,2),(1,2),(2,2)]
def representativeBoundTable0 : NatTable :=
(.branch 2
(.branch 1
(.leaf 156008723698269154745000000000000000000000000000000000000000000000000)
(.leaf 2579858090809581183210000000000000000000000000000000000000000000000000))
(.branch 3
(.leaf 118398645020199144745000000000000000000000000000000000000000000000000)
(.branch 4
(.leaf 118398645020199144745000000000000000000000000000000000000000000000000)
(.leaf 1319591558996649990745000000000000000000000000000000000000000000000000))))
def representative0 (k : Fin 5) : Fin 16 × Fin 16 := representativePairs0.getD k.val (0,0)
def representativeBound0 (k : Fin 5) : ℕ := representativeBoundTable0.get k.val

def caseTable0 : NatTable :=
(.branch 128
(.branch 64
(.branch 32
(.branch 16
(.branch 8
(.branch 4
(.branch 2
(.leaf 0)
(.branch 3
(.leaf 2)
(.leaf 0)))
(.leaf 0))
(.leaf 0))
(.branch 24
(.branch 20
(.branch 18
(.branch 17
(.leaf 0)
(.leaf 1))
(.branch 19
(.leaf 3)
(.leaf 0)))
(.leaf 0))
(.leaf 0)))
(.branch 48
(.branch 40
(.branch 36
(.branch 34
(.leaf 0)
(.branch 35
(.leaf 4)
(.leaf 0)))
(.leaf 0))
(.leaf 0))
(.leaf 0)))
(.leaf 0))
(.leaf 0))
def caseIndex0 (i j : Fin 16) : Fin 5 :=
  ⟨caseTable0.get (16*i.val+j.val)%5,Nat.mod_lt _ (by decide)⟩

end BS2_b3ba934b_Cert_16_Aux0


