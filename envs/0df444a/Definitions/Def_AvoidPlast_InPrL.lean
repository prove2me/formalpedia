-- Prove2me | Definitions.Def_AvoidPlast_InPrL
-- name    : AvoidPlast_InPrL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:24.65159+00:00
-- url     : https://prove2.me/theorems/571b63fb-d365-4c4c-93c7-aa8f22df2254
-- title:
--   The class prL
-- statement:
--   A promise problem is in **prL** if a deterministic machine of work space $O(\log n)$, halting on every input, accepts every yes-instance and rejects every no-instance.
--
--   **Formalization Note** The space and halting bound hold on every input, also outside the promise; a logspace machine can clock itself, so this loses nothing.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 1.2, p.3

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Halts
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_lg

namespace AvoidPlast

/-- The class prL (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §1.2, p.3): promise problems decided by a deterministic machine of work
space `O(log n)`, halting on every input.

**Formalization Note** The machine must halt and respect the space bound on every input, also
outside the promise. For logspace this loses nothing, since a machine can clock itself. -/
def InPrL (P : KarpLiptonOM.PromiseProblem) : Prop :=
  ∃ (M : Machine 1) (C : ℝ),
    (∀ x : List Bool, Halts M ![x] ∧ (workSpace M ![x] : ℝ) ≤ C * (lg x.length + 1)) ∧
    (∀ x ∈ P.yes, Accepts M ![x]) ∧ (∀ x ∈ P.no, ¬ Accepts M ![x])

end AvoidPlast


