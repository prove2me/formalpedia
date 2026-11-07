-- Prove2me | Definitions.Def_PrivLittlestone_Alg1Coins
-- name    : PrivLittlestone_Alg1Coins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:44.03505+00:00
-- url     : https://prove2.me/theorems/2215e9a1-d284-4fc7-8a43-4afc26bdefee
-- title:
--   Coin space of Algorithm 1
-- statement:
--   The **coins of Algorithm 1** are: for each phase $j \le K$, $m$ uniform variables that draw $h_1, \dots, h_m$ (line 6) and the threshold noise $\xi_j$ (line 8); and for each round $t \le T$ the query noise $\nu_t$ (line 15). Every draw uses fresh randomness.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Algorithm 1, p.7

import Mathlib
import Definitions.Def_PrivLittlestone_Alg1Spec

namespace PrivLittlestone

/-- The **coin space of Algorithm 1** (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Algorithm 1, p.7): for
each phase `j < K` the `m` uniform variables that draw `h_1, …, h_m` (line 6) and the threshold
noise `ξ_j` (line 8), and for each round `t < T` the query noise `ν_t` (line 15).

**Formalization Note** "Fresh randomness" is one independent coordinate per phase and per round;
unused coordinates (phases never started) do not affect the transcript. -/
abbrev Alg1Coins {X Z U : Type*} {D : ℕ} {B : ℝ} (P : Alg1Spec X Z U D B) : Type :=
  (Fin P.K → Fin P.m → ℝ) × (Fin P.K → ℝ) × (Fin P.T → ℝ)

end PrivLittlestone


