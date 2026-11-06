-- Prove2me | Definitions.Def_BorelRobustMDP_RobustModel
-- name    : BorelRobustMDP_RobustModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:54.819343+00:00
-- url     : https://prove2.me/theorems/00ac6fb2-69d1-4edf-9340-7467e6958012
-- title:
--   The distributionally robust Markov decision model
-- statement:
--   The decision model together with the reference laws and ambiguity sets of its disturbances.
--
--   This is the object about which every theorem of the mission speaks.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, §2, pp.3–4

import Mathlib
import Definitions.Def_BorelRobustMDP_DecisionModel
import Definitions.Def_BorelRobustMDP_AmbiguityFamily

namespace BorelRobustMDP

universe u v

/-- The distributionally robust model of Bäuerle & Glauner, arXiv:2007.13103v1, §2, pp.3–4: a decision
model together with reference laws and ambiguity sets for its disturbances. -/
structure RobustModel (E A : Type u) (Z : Type v) [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] (N : ℕ) extends DecisionModel E A Z N, AmbiguityFamily Z N

end BorelRobustMDP


