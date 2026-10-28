-- Prove2me | Definitions.Def_BS2_b3ba934b_Cert_16_Aux2
-- name    : BS2_b3ba934b_Cert_16_Aux2
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:30:13.861025+00:00
-- url     : https://prove2.me/theorems/4af93896-c619-4f73-95d8-775c82de4431
-- title:
--   Sensitivity separation: endpoint 16 profile 2 pure case data
-- statement:
--   Exact copies of the representative and case-index data from Endpoint16RawProof2 in a fresh namespace. No numerical certificate proof or old RawProof helper module is imported.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof2.lean; original SHA-256 ec2d4c7f9e58f3aecbe5b2d18087140b7a8b5ae560a22e93d0a48061fde4862c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

namespace BS2_b3ba934b_Cert_16_Aux2
def representativePairs2 : Array (Fin 16 × Fin 16) := #[(0,2),(1,2),(2,2),(0,3),(1,3),(2,3),(3,3)]
def representativeBoundTable2 : NatTable :=
(.branch 3
(.branch 1
(.leaf 871561019159694584044656120000000000000000000000000000000000000000000000)
(.branch 2
(.leaf 871561019159694584044656120000000000000000000000000000000000000000000000)
(.leaf 14410105262606791464357289260000000000000000000000000000000000000000000000)))
(.branch 5
(.leaf 661465889144801567244956340000000000000000000000000000000000000000000000)
(.branch 6
(.leaf 661465889144801567244956340000000000000000000000000000000000000000000000)
(.leaf 7370794181513951641388310720000000000000000000000000000000000000000000000))))
def representative2 (k : Fin 7) : Fin 16 × Fin 16 := representativePairs2.getD k.val (0,0)
def representativeBound2 (k : Fin 7) : ℕ := representativeBoundTable2.get k.val

def caseTable2 : NatTable :=
(.branch 128
(.branch 64
(.branch 32
(.branch 16
(.branch 8
(.branch 4
(.branch 2
(.leaf 0)
(.branch 3
(.leaf 0)
(.leaf 3)))
(.leaf 0))
(.leaf 0))
(.branch 24
(.branch 20
(.branch 18
(.leaf 0)
(.branch 19
(.leaf 1)
(.leaf 4)))
(.leaf 0))
(.leaf 0)))
(.branch 48
(.branch 40
(.branch 36
(.branch 34
(.leaf 0)
(.branch 35
(.leaf 2)
(.leaf 5)))
(.leaf 0))
(.leaf 0))
(.branch 56
(.branch 52
(.branch 50
(.leaf 0)
(.branch 51
(.leaf 0)
(.leaf 6)))
(.leaf 0))
(.leaf 0))))
(.leaf 0))
(.leaf 0))
def caseIndex2 (i j : Fin 16) : Fin 7 :=
  ⟨caseTable2.get (16*i.val+j.val)%7,Nat.mod_lt _ (by decide)⟩

end BS2_b3ba934b_Cert_16_Aux2


