-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_Stage
-- name    : KawasakiSOS_Threshold_Stage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:38.684455+00:00
-- url     : https://prove2.me/theorems/122fd106-98eb-4770-9275-35e10a98047c
-- title:
--   Pairs of window centers
-- statement:
--   A pair $S=(c_A,c_B)$ of sites of $\mathbb Z_k$, the centers of the two windows of a stage.
--
--   **Formalization Note** The disjointness required of a stage in Definition 4.5 is the separate predicate `IsStage`, so that the formula (6) can be written as a total function.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12)

import Mathlib

namespace KawasakiSOS.Threshold

/-- A pair `(c_A, c_B)` of sites, the data of a stage. The disjointness condition is the predicate `IsStage`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Definition 4.5, p. 11 (PDF p. 12). -/
@[ext] structure Stage (k : ℕ) where
  cA : ZMod k
  cB : ZMod k
  deriving DecidableEq

end KawasakiSOS.Threshold


