-- Prove2me | Definitions.Def_SConvexGS_IsSConcave
-- name    : SConvexGS_IsSConcave
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:06.594464+00:00
-- url     : https://prove2.me/theorems/d9f1198d-708b-4984-a799-f87caaf72463
-- title:
--   S-concave function
-- statement:
--   A function $f$ is called **S-concave** if $-f$ is S-convex.
--
--   Since $-f$ must not take the value $-\infty$, an S-concave function has values in $[-\infty,\infty)$, and $-f$ takes the value $+\infty$ where $f$ takes the value $-\infty$.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Definition 1, p.10

import Mathlib
import Definitions.Def_SConvexGS_IsSConvex

namespace SConvexGS

/-- S-concave functions (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of
2021-10-29), Definition 1, p.10): "A function `f` is called S-concave if `−f` is S-convex".

Formalization Note: `−f` is `EReal` negation, which takes `⊤` where `f` takes `⊥`. -/
def IsSConcave {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsSConvex (fun x => - f x)

end SConvexGS


