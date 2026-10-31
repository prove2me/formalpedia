-- Prove2me | Definitions.Def_CombOpt_Circulation_IsAugmentingPath
-- name    : CombOpt_Circulation_IsAugmentingPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:36.169691+00:00
-- url     : https://prove2.me/theorems/0e53e7a9-d5f1-4424-81b4-ec2b4f02b3b2
-- title:
--   $x$-augmenting paths
-- statement:
--   An **$x$-augmenting path** is an $(r,s)$-path, that is a path from $r$ to $s$, that is $x$-incrementing.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, p. 41 (PDF p. 50)

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_IsPath
import Definitions.Def_CombOpt_Circulation_IsIncrementing

open scoped ENNReal

namespace CombOpt.Circulation

variable {V E : Type*}

/-- An `x`-augmenting path, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, p. 41 (PDF p. 50): "an `(r, s)`-path that is
`x`-incrementing". -/
def IsAugmentingPath (G : MultiDigraph V E) (u : E → ℝ≥0∞) (x : E → ℝ) (r s : V)
    (p : List (E × Bool)) : Prop :=
  IsPath G r p s ∧ IsIncrementing u x p

end CombOpt.Circulation


