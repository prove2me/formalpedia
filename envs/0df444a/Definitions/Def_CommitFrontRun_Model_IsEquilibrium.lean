-- Prove2me | Definitions.Def_CommitFrontRun_Model_IsEquilibrium
-- name    : CommitFrontRun_Model_IsEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:50.252586+00:00
-- url     : https://prove2.me/theorems/2cdac620-534c-405c-9633-edfba8b1688a
-- title:
--   Equilibrium of the commit-reveal game (Nash, behavior strategies)
-- statement:
--   A profile $(A,B)$ is an **equilibrium** when neither player gains by a unilateral change of strategy:
--   $$
--   u_A(A',B)\le u_A(A,B)\quad\text{for every strategy }A'\text{ of }A,\qquad u_B(A,B')\le u_B(A,B)\quad\text{for every strategy }B'\text{ of }B.
--   $$
--   This is a Nash equilibrium in behavior strategies with ex-ante payoffs, the notion footnote 16 of the paper refers to ("as noted already in Nash (1950)").
--
--   **Formalization Note** No sequential rationality and no belief system are imposed; an ex-ante Nash equilibrium leaves a player's choices at information sets of probability zero unconstrained.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, pp.14–16; footnote 16, p.15

import Mathlib
import Definitions.Def_CommitFrontRun_Model_payoffA
import Definitions.Def_CommitFrontRun_Model_payoffB

namespace CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

/-- **Equilibrium of the commit-reveal game**: a Nash equilibrium in behavior strategies with
ex-ante payoffs. Neither player gains by a unilateral change of his or her own strategy.
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, pp.14–16, footnote 16, p.15 ("as noted already in Nash (1950)").

**Formalization Note** The paper does not name its solution concept beyond footnote 16's
appeal to Nash (1950); Nash equilibrium is the weakest standard reading, with no sequential
rationality or belief system added. -/
def Model.IsEquilibrium (M : Model S Msg) (A : StratA S) (B : StratB Msg) : Prop :=
  (∀ A' : StratA S, M.payoffA A' B ≤ M.payoffA A B) ∧
    (∀ B' : StratB Msg, M.payoffB A B' ≤ M.payoffB A B)

end CommitFrontRun


