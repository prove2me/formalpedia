-- Prove2me | Definitions.Def_PrivLittlestone_sampleAgg
-- name    : PrivLittlestone_sampleAgg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:37:10.770275+00:00
-- url     : https://prove2.me/theorems/60c96d56-7956-453e-b35b-b0f2a70e11d3
-- title:
--   Phase aggregate $g = \mathrm{Agg}(h_1,\dots,h_m)$
-- statement:
--   At the start of phase $j$ with retained sequence $S$, the **phase aggregate** is $g = \mathrm{Agg}(h_1, \dots, h_m)$, where $h_1, \dots, h_m$ are drawn independently from $Q_S$ by the phase's uniform coins.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Algorithm 1, lines 6–7, p.7

import Mathlib
import Definitions.Def_PrivLittlestone_Alg1Coins
import Definitions.Def_PrivLittlestone_pick

namespace PrivLittlestone

/-- The **phase aggregate** `g = Agg(h_1, …, h_m)` of phase `j`, with `h_1, …, h_m` drawn from
`Q_S` by the phase's uniform coins (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Algorithm 1, lines 6–7,
p.7). Phases `j ≥ K` never occur; they read the coin `0`. -/
noncomputable def sampleAgg {X Z U : Type*} {D : ℕ} {B : ℝ} (P : Alg1Spec X Z U D B)
    (ω : Alg1Coins P) (j : ℕ) (S : List Z) : X → Bool :=
  P.agg (fun i => pick P.sys P.η P.a S (if h : j < P.K then ω.1 ⟨j, h⟩ i else 0))

end PrivLittlestone


