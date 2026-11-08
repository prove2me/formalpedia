-- Prove2me | Definitions.Def_AvoidPlast_PolyTime
-- name    : AvoidPlast_PolyTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:45:08.39747+00:00
-- url     : https://prove2.me/theorems/5beb96b8-e0bf-45ab-8435-6a852ee6201f
-- title:
--   Polynomial-time machines
-- statement:
--   A machine $M$ with one read-only tape is **polynomial-time** if there is $C$ such that on every input $x$ it halts within $C(|x|^C+1)$ steps.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 1.2, p.3; Theorem 5.14, p.29

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin

namespace AvoidPlast

/-- A deterministic polynomial-time machine (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §1.2, p.3 and Theorem 5.14, p.29): it halts on
every input `x` within `C · (|x|^C + 1)` steps. -/
def PolyTime (M : Machine 1) : Prop :=
  ∃ C : ℕ, ∀ x : List Bool, HaltsWithin M ![x] (C * (x.length ^ C + 1))

end AvoidPlast


