-- Prove2me | Definitions.Def_AubinLipschitz_effDom
-- name    : AubinLipschitz_effDom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:20.550364+00:00
-- url     : https://prove2.me/theorems/6cf23f03-e8ee-425f-9e46-421cae16a013
-- title:
--   Effective domain of an extended-valued function
-- statement:
--   For $f:E\to\mathbb R\cup\{\pm\infty\}$, the **effective domain** is
--
--   $$
--   \operatorname{Dom} f=\{x\in E\mid f(x)<+\infty\}.
--   $$
--
--   It appears in the constraint qualification (2) of §5.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (2), p.31

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (2), p.31: the effective domain `Dom f = {x | f(x) < +∞}` of an extended-valued
function. -/
def effDom {E : Type*} (f : E → EReal) : Set E :=
  {x | f x ≠ ⊤}

end AubinLipschitz


