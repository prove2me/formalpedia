-- Prove2me | Definitions.Def_BS2_b3ba934b_Cert_16_Aux3
-- name    : BS2_b3ba934b_Cert_16_Aux3
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:29:41.58599+00:00
-- url     : https://prove2.me/theorems/6913fee3-6e7f-4686-9cb2-5400034e364d
-- title:
--   Sensitivity separation: endpoint 16 profile 3 pure case data
-- statement:
--   Exact copies of the representative and case-index data from Endpoint16RawProof3 in a fresh namespace. No numerical certificate proof or old RawProof helper module is imported.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawProof3.lean; original SHA-256 539c53bed447ae5c6ed37397bf1e9675200da15133afd04107cc772283d3f314; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

namespace BS2_b3ba934b_Cert_16_Aux3
def representativePairs3 : Array (Fin 16 × Fin 16) := #[(0,3),(1,3),(2,3),(3,3),(0,4),(1,4),(2,4),(3,4),(4,4)]
def representativeBoundTable3 : NatTable :=
(.branch 4
(.branch 2
(.leaf 65136953840227306262442285060000000000000000000000000000000000000000000000)
(.branch 3
(.leaf 65136953840227306262442285060000000000000000000000000000000000000000000000)
(.leaf 1076339290179921391893340797180000000000000000000000000000000000000000000000)))
(.branch 6
(.leaf 49435378198966834859642266240000000000000000000000000000000000000000000000)
(.branch 7
(.leaf 49435378198966834859642266240000000000000000000000000000000000000000000000)
(.branch 8
(.leaf 49435378198966834859642266240000000000000000000000000000000000000000000000)
(.leaf 550556636831362288633025143960000000000000000000000000000000000000000000000)))))
def representative3 (k : Fin 9) : Fin 16 × Fin 16 := representativePairs3.getD k.val (0,0)
def representativeBound3 (k : Fin 9) : ℕ := representativeBoundTable3.get k.val

def caseTable3 : NatTable :=
(.branch 128
(.branch 64
(.branch 32
(.branch 16
(.branch 8
(.branch 4
(.leaf 0)
(.branch 6
(.branch 5
(.leaf 4)
(.leaf 0))
(.leaf 0)))
(.leaf 0))
(.branch 24
(.branch 20
(.branch 18
(.leaf 0)
(.branch 19
(.leaf 0)
(.leaf 1)))
(.branch 22
(.branch 21
(.leaf 5)
(.leaf 0))
(.leaf 0)))
(.leaf 0)))
(.branch 48
(.branch 40
(.branch 36
(.branch 34
(.leaf 0)
(.branch 35
(.leaf 0)
(.leaf 2)))
(.branch 38
(.branch 37
(.leaf 6)
(.leaf 0))
(.leaf 0)))
(.leaf 0))
(.branch 56
(.branch 52
(.branch 50
(.leaf 0)
(.branch 51
(.leaf 0)
(.leaf 3)))
(.branch 54
(.branch 53
(.leaf 7)
(.leaf 0))
(.leaf 0)))
(.leaf 0))))
(.branch 96
(.branch 80
(.branch 72
(.branch 68
(.leaf 0)
(.branch 70
(.branch 69
(.leaf 8)
(.leaf 0))
(.leaf 0)))
(.leaf 0))
(.leaf 0))
(.leaf 0)))
(.leaf 0))
def caseIndex3 (i j : Fin 16) : Fin 9 :=
  ⟨caseTable3.get (16*i.val+j.val)%9,Nat.mod_lt _ (by decide)⟩

end BS2_b3ba934b_Cert_16_Aux3


