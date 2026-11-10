-- Prove2me | Definitions.Def_VAS5Reach_VASS_DeletesCycles
-- name    : VAS5Reach_VASS_DeletesCycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:28:26.092738+00:00
-- url     : https://prove2.me/theorems/3feb4bc8-471e-4914-95f7-0e5fc0723949
-- title:
--   Obtaining a path by deleting cycles
-- statement:
--   A path $\rho$ is obtained from a path $\pi$ of a VASS $V$ by **deleting one cycle** if $\pi = \alpha\theta\gamma$ where $\theta$ is a cycle of $V$ (a nonempty path from a state back to itself) and $\rho = \alpha\gamma$ (`DeleteCycleStep`). It is **obtained by deleting cycles** if it results from finitely many successive such deletions, possibly none (`DeletesCycles`). Lemma 3.2 uses this relation.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 3.2, p.16 (PDF p.18); cycles p.13 (PDF p.15)

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun

namespace VAS5Reach

namespace VASS

variable {S ι : Type}

/-- One cycle deletion: `ρ` is obtained from the path `π` by deleting one cycle, i.e.
`π = α θ γ` where `θ` is a cycle of `V` (a nonempty path of `V` from a state back to itself) and
`ρ = α γ`. -/
def DeleteCycleStep (V : VASS S ι) (π ρ : List (S × (ι → ℤ) × S)) : Prop :=
  ∃ α θ γ, π = α ++ θ ++ γ ∧ ρ = α ++ γ ∧ θ ≠ [] ∧ ∃ r, IsPath V r θ r

/-- `DeletesCycles V π ρ`: `ρ` is obtained from `π` by deleting cycles (finitely many successive
cycle deletions, possibly none).

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 3.2, printed p. 16
(PDF p. 18): "Moreover, ρ is obtained by deleting cycles from π and therefore has the same final
state as π."; p. 13: "It is a cycle if it is nonempty and qk = p1". -/
def DeletesCycles (V : VASS S ι) (π ρ : List (S × (ι → ℤ) × S)) : Prop :=
  Relation.ReflTransGen (DeleteCycleStep V) π ρ

end VASS

end VAS5Reach


