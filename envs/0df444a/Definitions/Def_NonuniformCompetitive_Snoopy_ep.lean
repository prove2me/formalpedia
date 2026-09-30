-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_ep
-- name    : NonuniformCompetitive_Snoopy_ep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:46:38.634723+00:00
-- url     : https://prove2.me/theorems/fbcebc24-71c4-44d7-8dba-67a5f979af84
-- title:
--   The constant $e_p = (1 + 1/p)^p$
-- statement:
--   For a positive integer $p$ (in the snoopy-caching model, the number of bus cycles needed to transfer a block of $p-1$ variables), define
--
--   $$e_p = \left(1 + \frac{1}{p}\right)^p .$$
--
--   As $p \to \infty$, $e_p$ increases to $e$. The ratio $e_p/(e_p - 1)$ is the optimal competitive factor of randomized block snoopy caching against an oblivious adversary; it equals $2$ at $p = 1$, $9/5$ at $p = 2$, and decreases to $e/(e-1) \approx 1.582$.
--
--   **Formalization Note** The constant is a real number indexed by a natural number $p$. Every statement of the mission that uses it assumes $p \ge 1$; the value at $p = 0$ (where Lean's convention $1/0 = 0$ gives $e_0 = 1$) is never used.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 551, §3.2 display defining e_p

import Mathlib

namespace NonuniformCompetitive.Snoopy

/-- The constant `e_p = (1 + 1/p)^p` of Karlin–Manasse–McGeoch–Owicki (Algorithmica 11 (1994),
§3.2, p. 551), for a block-transfer cost `p`. In the snoopy-caching model `p` is a positive
integer (a block of `p − 1` variables costs `p` bus cycles to transfer); every statement of this
mission that uses `ep p` assumes `1 ≤ p`. (At `p = 0` Lean's `1 / 0 = 0` gives `ep 0 = 1`; that
value is never used.) -/
noncomputable def ep (p : ℕ) : ℝ := (1 + 1 / (p : ℝ)) ^ p

end NonuniformCompetitive.Snoopy


