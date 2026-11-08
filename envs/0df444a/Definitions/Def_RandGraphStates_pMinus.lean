-- Prove2me | Definitions.Def_RandGraphStates_pMinus
-- name    : RandGraphStates_pMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:37.299439+00:00
-- url     : https://prove2.me/theorems/dbd3794c-ab44-44c8-a7eb-85c715520988
-- title:
--   The parameters $p_-$, $p_+$ and $q$
-- statement:
--   For $0<p<1$, the paper sets
--   $$
--   p_-:=\min\{p,1-p\},\qquad p_+:=\max\{p,1-p\},\qquad q:=1-2p .
--   $$
--   Every hypothesis on the edge density is stated through $p_-$, so the results treat $p$ and $1-p$ alike.
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), §4, p.17

import Mathlib

set_option autoImplicit false

namespace RandGraphStates

/-- `p₋ := min{p, 1 - p}`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), Theorem 2.4, p.6, and §4, p.17. -/
noncomputable def pMinus (p : ℝ) : ℝ := min p (1 - p)

/-- `p₊ := max{p, 1 - p}`. Source: ibid., §4, p.17. -/
noncomputable def pPlus (p : ℝ) : ℝ := max p (1 - p)

/-- `q := 1 - 2p`. Source: ibid., §4, p.17. -/
def qOf (p : ℝ) : ℝ := 1 - 2 * p

end RandGraphStates


