-- Prove2me | Definitions.Def_FMMM_TSM_adsWith
-- name    : FMMM_TSM_adsWith
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:19:13.930144+00:00
-- url     : https://prove2.me/theorems/bc44a36e-6255-49c1-893b-4ef58c671482
-- title:
--   The ad classes $A_{BR}, A_{BB}, A_B, A_R$
-- statement:
--   Given the blue edges $B$ and the red edges $F \setminus B$ of a TSM colouring, the set of ads incident to exactly $b$ blue and exactly $r$ red edges is denoted here $A(b, r)$. The paper's four classes are
--
--   $$A_{BR} = A(1,1), \qquad A_{BB} = A(2,0), \qquad A_B = A(1,0), \qquad A_R = A(0,1):$$
--
--   the ads incident to a blue and a red edge, to two blue edges, to only a blue edge, and to only a red edge. The analysis bounds both $\mathrm{ALG}$ and $\mathrm{OPT}$ in terms of the sizes of these classes.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.2, p. 7 (A_BR, A_B, A_BB, A_R)

import Mathlib

namespace FMMM.TSM

/-- **The ad classes `A_BR`, `A_BB`, `A_B`, `A_R`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.2, p. 7: "let A_BR be the ads that are incident to a blue and a red edge,
and A_B be the ads that are incident to only a blue edge. Similarly define A_BB and A_R."

`adsWith F blue b r` is the set of ads incident to exactly `b` blue edges and exactly `r` red edges
(red = `F \ blue`). Then `A_BR = adsWith F blue 1 1`, `A_BB = adsWith F blue 2 0`,
`A_B = adsWith F blue 1 0`, `A_R = adsWith F blue 0 1`. -/
def adsWith {A J : Type} [Fintype A] [DecidableEq A] [DecidableEq J]
    (F blue : Finset (A × J)) (b r : ℕ) : Finset A :=
  Finset.univ.filter (fun a => (blue.filter (fun e => e.1 = a)).card = b ∧
    ((F \ blue).filter (fun e => e.1 = a)).card = r)

end FMMM.TSM


