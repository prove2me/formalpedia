-- Prove2me | Definitions.Def_SmoothedNash_PayoffsIn01
-- name    : SmoothedNash_PayoffsIn01
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:28.645698+00:00
-- url     : https://prove2.me/theorems/9c39c1d8-2882-4123-9c9e-42f52ebae417
-- title:
--   Payoffs in $[0,1]$
-- statement:
--   A game $u$ has **payoffs in $[0, 1]$** if
--   $$
--   0 \le u_i(a) \le 1 \qquad \text{for every player } i \text{ and every action profile } a \in [n]^m .
--   $$
--   This is the paper's game model (payoff functions $u_i : [n]^m \to [0, 1]$); it makes every deviation payoff lie in $[0, 1]$ and gives the Lipschitz bound of Lemma 2.3.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §1.1.2, p.6

import Mathlib
import Definitions.Def_SmoothedNash_Game

namespace SmoothedNash

/-- The payoffs of the game lie in `[0, 1]`: `u_i : [n]^m → [0, 1]` for every player `i`
(Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §1.1.2, p.6). -/
def PayoffsIn01 {m n : ℕ} (u : Game m n) : Prop :=
  ∀ i s, 0 ≤ u i s ∧ u i s ≤ 1

end SmoothedNash


