-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawProof0_Numeric001
-- name    : BS2_b3ba934b_Endpoint40RawProof0_Numeric001
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:34:03.802813+00:00
-- url     : https://prove2.me/theorems/6d88abf5-ab7f-4f2a-8105-4a40959fc5a0
-- title:
--   Sensitivity separation: Endpoint40RawProof0 numeric batch 2
-- statement:
--   Unchanged original numeric declarations from Endpoint40RawProof0, compiled in small batches. Original proof bodies and definitions are preserved; helper proofs are namespace-visible for import by the next batch.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawProof0.lean; original SHA-256 7a31c8e6adad0d094c67f9734e9b91bcdce1bd75ee2ff74105e322d178af9e1a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RawProof0_Numeric000
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

theorem case_chunk_0_0 : ∀ j : Fin 40, (0 : Fin 40)≤j →
    0<(recipe 0 j).tolerance → (recipe 0 j).tolerance≤2 →
    recipe 0 0=recipe 0 (representative0 (caseIndex0 0 j)).1 ∧
    recipe 0 j=recipe 0 (representative0 (caseIndex0 0 j)).2 ∧
    representativeBound0 (caseIndex0 0 j)≤rawProfile0 (.a 0 j) := by decide +kernel

theorem case_chunk_0_1 : ∀ j : Fin 40, (1 : Fin 40)≤j →
    0<(recipe 0 j).tolerance → (recipe 0 j).tolerance≤2 →
    recipe 0 1=recipe 0 (representative0 (caseIndex0 1 j)).1 ∧
    recipe 0 j=recipe 0 (representative0 (caseIndex0 1 j)).2 ∧
    representativeBound0 (caseIndex0 1 j)≤rawProfile0 (.a 1 j) := by decide +kernel

theorem case_chunk_0_2 : ∀ j : Fin 40, (2 : Fin 40)≤j →
    0<(recipe 0 j).tolerance → (recipe 0 j).tolerance≤2 →
    recipe 0 2=recipe 0 (representative0 (caseIndex0 2 j)).1 ∧
    recipe 0 j=recipe 0 (representative0 (caseIndex0 2 j)).2 ∧
    representativeBound0 (caseIndex0 2 j)≤rawProfile0 (.a 2 j) := by decide +kernel

theorem case_chunk_0_3 : ∀ j : Fin 40, (3 : Fin 40)≤j →
    0<(recipe 0 j).tolerance → (recipe 0 j).tolerance≤2 →
    recipe 0 3=recipe 0 (representative0 (caseIndex0 3 j)).1 ∧
    recipe 0 j=recipe 0 (representative0 (caseIndex0 3 j)).2 ∧
    representativeBound0 (caseIndex0 3 j)≤rawProfile0 (.a 3 j) := by decide +kernel

end ThreeBoundNumeric.Endpoint40


