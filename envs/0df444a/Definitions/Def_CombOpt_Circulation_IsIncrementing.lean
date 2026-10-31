-- Prove2me | Definitions.Def_CombOpt_Circulation_IsIncrementing
-- name    : CombOpt_Circulation_IsIncrementing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:23.197396+00:00
-- url     : https://prove2.me/theorems/b66530e6-10fe-42cf-a9c9-ebfb523cbd24
-- title:
--   $x$-incrementing paths
-- statement:
--   A path is **$x$-incrementing** if every forward arc $e$ has $x_e<u_e$ and every reverse arc $e$ has $x_e>0$.
--
--   **Formalization Note** The condition is stated on the list of arc and direction pairs of `IsPath`; $x_e<u_e$ is compared in the extended reals, so it holds whenever $u_e=\infty$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, p. 41 (PDF p. 50)

import Mathlib

open scoped ENNReal

namespace CombOpt.Circulation

variable {E : Type*}

/-- `x`-incrementing, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, p. 41 (PDF p. 50): "every forward arc `e` has `x_e < u_e` and
every reverse arc `e` has `x_e > 0`". The path is recorded as in `IsPath`.

**Formalization Note** `x_e < u_e` is compared in `EReal`, so it holds at every real `x_e` when
`u_e = ∞`. -/
def IsIncrementing (u : E → ℝ≥0∞) (x : E → ℝ) (p : List (E × Bool)) : Prop :=
  ∀ e, ((e, true) ∈ p → (x e : EReal) < (u e : EReal)) ∧ ((e, false) ∈ p → 0 < x e)

end CombOpt.Circulation


