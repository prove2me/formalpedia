-- Prove2me | Definitions.Def_TargetedSamplers_InPrDTIME
-- name    : TargetedSamplers_InPrDTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:55.515695+00:00
-- url     : https://prove2.me/theorems/e5827bbe-7cb7-41ef-aeea-17189440665f
-- title:
--   The class $\mathrm{prDTIME}[t]$
-- statement:
--   A promise problem $\Pi$ is in $\mathrm{prDTIME}[t]$ if one deterministic program halts on every input $x$ within time $t(|x|)$, outputs one bit, and outputs $1$ on every yes-instance and $0$ on every no-instance.
--
--   **Formalization Note** Time is $\mathrm{budget}$ (constant and polylogarithmic factors), as for every class of the mission.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.29, p.41 (pdf p.43); Theorem 4.30, p.42 (pdf p.44)

import Mathlib
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_KarpLiptonOM_PromiseProblem

namespace TargetedSamplers

/-- The class `prDTIME[t]` (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission,
manuscript sha256 599d0a59…, Theorem 4.29, p.41, Theorem 4.30, p.42): one deterministic program
halts on every input `x` within time `t(|x|)` and outputs one bit, `1` on every yes-instance and
`0` on every no-instance.

**Formalization Note** Time is `budget` (constant and polylogarithmic factors), as for every class
of this development; the program has no coins, no witness and no oracle. -/
def InPrDTIME (t : ℕ → ℕ) (L : KarpLiptonOM.PromiseProblem) : Prop :=
  ∃ (A : Program) (K k : ℕ), ∀ x : List Bool, ∃ b : Bool,
    A.RunsIn (Tapes.ofInput x) (budget K k (t x.length) x.length) (some [b]) ∧
    (x ∈ L.yes → b = true) ∧ (x ∈ L.no → b = false)

end TargetedSamplers


