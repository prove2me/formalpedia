-- Prove2me | Definitions.Def_SConvexGS_IsProperGS
-- name    : SConvexGS_IsProperGS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:07.401763+00:00
-- url     : https://prove2.me/theorems/984cd4cf-1796-4747-b80a-6e2027044dac
-- title:
--   Proper GS-function
-- statement:
--   A GS-function $f$ is called **proper** if there exists at least one point $p$ such that $\arg\max f[-p]\ne\emptyset$.
--
--   If this condition fails, GS provides no information on the function.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), p.21

import Mathlib
import Definitions.Def_SConvexGS_IsGS

namespace SConvexGS

/-- Proper GS-functions (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of
2021-10-29), p.21): a GS-function `f` is proper if there exists at least one point `p` such that
`arg max f[−p] ≠ ∅`. -/
def IsProperGS {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsGS f ∧ ∃ p, (argMaxTilt f p).Nonempty

end SConvexGS


