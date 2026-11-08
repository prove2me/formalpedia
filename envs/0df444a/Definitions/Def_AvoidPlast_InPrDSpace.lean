-- Prove2me | Definitions.Def_AvoidPlast_InPrDSpace
-- name    : AvoidPlast_InPrDSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:31.271729+00:00
-- url     : https://prove2.me/theorems/8a188710-6c09-4e1e-a034-4898a1c9961d
-- title:
--   The class prDSPACE$[O(s(n))]$
-- statement:
--   A promise problem is in **prDSPACE$[O(s(n))]$** if a deterministic machine halting on every input, with work space at most $C(s(|x|)+1)$, accepts every yes-instance and rejects every no-instance.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.8, p.25

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Halts
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_workSpace

namespace AvoidPlast

/-- The class prDSPACE[O(s(n))] (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.8, p.25): promise problems decided by a
deterministic machine of work space `O(s(n))`, halting on every input. -/
def InPrDSpace (s : ℕ → ℝ) (P : KarpLiptonOM.PromiseProblem) : Prop :=
  ∃ (M : Machine 1) (C : ℝ),
    (∀ x : List Bool, Halts M ![x] ∧ (workSpace M ![x] : ℝ) ≤ C * (s x.length + 1)) ∧
    (∀ x ∈ P.yes, Accepts M ![x]) ∧ (∀ x ∈ P.no, ¬ Accepts M ![x])

end AvoidPlast


