-- Prove2me | Definitions.Def_PrivLittlestone_algState__7d3f58
-- name    : PrivLittlestone_algState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:40:45.001784+00:00
-- url     : https://prove2.me/theorems/7d3f580d-923f-46d7-a43c-f9b8e2152b97
-- title:
--   State of Algorithm 1 after the first $t$ records
-- statement:
--   The **state of Algorithm 1 after $t$ records** is obtained by replaying the algorithm deterministically from the records and the coins: initially phase $1$, $S = ()$, $c = 0$ and the aggregate of the first phase sampled from $Q_{()}$; then one round per record.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Algorithm 1, p.7

import Mathlib
import Definitions.Def_PrivLittlestone_algStep

namespace PrivLittlestone

/-- The **state of Algorithm 1 after the first `t` records** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Algorithm 1, p.7), replayed deterministically from the records and the coins: initially phase
`0`, `S = ()`, `c = 0`, and the aggregate of phase `0` sampled from `Q_∅` (lines 1, 6–8); then one
`algStep` per record. -/
noncomputable def algState {X Z U : Type*} {D : ℕ} {B : ℝ} (P : Alg1Spec X Z U D B)
    (ω : Alg1Coins P) : (t : ℕ) → (Fin t → X × Bool) → AlgState X Z
  | 0, _ =>
    { phase := 0, start := 0, retained := [], counter := 0,
      current := sampleAgg P ω 0 [], fallback := false }
  | t + 1, hist => algStep P ω t (hist (Fin.last t)) (algState P ω t (Fin.init hist))

end PrivLittlestone


