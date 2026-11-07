-- Prove2me | Definitions.Def_StochAutoreg_root
-- name    : StochAutoreg_root
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:33.558835+00:00
-- url     : https://prove2.me/theorems/cfa1b48a-28d4-4495-9dd3-3a355c5dfd36
-- title:
--   Root $r_j=b_j1$
-- statement:
--   The root $r_j=b_j1$ built from a string $b_j$, as in the proof of Lemma 6.1.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Lemma 6.1 (proof), p.12

import Mathlib

namespace StochAutoreg

/-- The root `r_j = b_j 1` of Lemma 6.1's proof. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Lemma 6.1 (proof), p.12. -/
def root {ι : Type} (b : ι → List Bool) (j : ι) : List Bool := b j ++ [true]

end StochAutoreg


