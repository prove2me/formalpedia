-- Prove2me | Definitions.Def_BS2_b3ba934b_Cert_16_Aux1
-- name    : BS2_b3ba934b_Cert_16_Aux1
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:29:06.365753+00:00
-- url     : https://prove2.me/theorems/4cd90483-4f9f-474d-a568-92d5e4c5b23a
-- title:
--   Sensitivity separation: endpoint 16 profile 1 pure case data
-- statement:
--   Exact copies of the representative and case-index data from Endpoint16RawProof1 in a fresh namespace. No numerical certificate proof or old RawProof helper module is imported.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof1.lean; original SHA-256 b1d515f7bedd1f571892779beb6a1d5900f6ae7d9d8a93901f49f5e18733d56a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

namespace BS2_b3ba934b_Cert_16_Aux1
def representativePairs1 : Array (Fin 16 × Fin 16) := #[(0,2),(1,2),(2,2),(0,3),(1,3),(2,3),(3,3)]
def representativeBoundTable1 : NatTable :=
(.branch 3
(.branch 1
(.leaf 11659749300103673188588500000000000000000000000000000000000000000000000)
(.branch 2
(.leaf 11659749300103673188588500000000000000000000000000000000000000000000000)
(.leaf 192825632236769287372743000000000000000000000000000000000000000000000000)))
(.branch 5
(.leaf 8848850045846562315998500000000000000000000000000000000000000000000000)
(.branch 6
(.leaf 8848850045846562315998500000000000000000000000000000000000000000000000)
(.leaf 98629719959159679536468500000000000000000000000000000000000000000000000))))
def representative1 (k : Fin 7) : Fin 16 × Fin 16 := representativePairs1.getD k.val (0,0)
def representativeBound1 (k : Fin 7) : ℕ := representativeBoundTable1.get k.val

def caseTable1 : NatTable :=
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
def caseIndex1 (i j : Fin 16) : Fin 7 :=
  ⟨caseTable1.get (16*i.val+j.val)%7,Nat.mod_lt _ (by decide)⟩

end BS2_b3ba934b_Cert_16_Aux1


