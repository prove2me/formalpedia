-- Prove2me | Definitions.Def_GarberOLO_Alg3_alg2Terminates
-- name    : GarberOLO_Alg3_alg2Terminates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:54:51.830136+00:00
-- url     : https://prove2.me/theorems/da44e6c2-a327-403b-98d1-9b098fff685e
-- title:
--   Termination of Algorithm 2
-- statement:
--   Algorithm 2 on input $(y, \varepsilon)$ **terminates** if at some pass the Separation-or-Decomposition procedure returns decomposition data instead of a separating vector, so that the loop returns.
--
--   Lemma 7 proves termination; Theorem 1 presupposes it for every round of Algorithm 3.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Algorithm 2, p. 12; Lemma 7, p. 12

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_sepOrDec
import Definitions.Def_GarberOLO_Alg3_Nprescribed
import Definitions.Def_GarberOLO_Alg3_alg2Iter

namespace GarberOLO.Alg3

/-- **Termination of Algorithm 2.**
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 7, p. 12: "Algorithm 2 terminates after at most ⌈α²R²/ε²⌉ iterations"; Algorithm 2,
p. 12 (the loop "for t = 1 . . . do" returns when the procedure outputs a decomposition).

`alg2Terminates S OK c ε y` says that for some pass `i` the procedure `sepOrDec`, run at
`alg2Iter S OK c ε y i` with `N = Nprescribed`, returns a decomposition (`isSep = false`), i.e.
that the loop of Algorithm 2 returns. -/
def alg2Terminates {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (c ε : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ i : ℕ, (sepOrDec S OK (alg2Iter S OK c ε y i) ε
    (Nprescribed S c ε (alg2Iter S OK c ε y i))).isSep = false

end GarberOLO.Alg3


