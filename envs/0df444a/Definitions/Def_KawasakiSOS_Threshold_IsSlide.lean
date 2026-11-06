-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsSlide
-- name    : KawasakiSOS_Threshold_IsSlide
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:20.93174+00:00
-- url     : https://prove2.me/theorems/cccb8484-b43e-4d70-87bd-ac7293add599
-- title:
--   Slides between stages
-- statement:
--   The stage $S'$ is obtained from $S$ by a slide if one of the following holds:
--
--   1. an A-slide: $c_A$ changes by $\pm1$ and $c_B$ is fixed;
--   2. a B-slide: $c_B$ changes by $\pm1$ and $c_A$ is fixed;
--   3. a block slide: both centers change by the same $\pm1$, and $U=\emptyset$ in both $S$ and $S'$, or $T=\emptyset$ in both.
--
--   In each case exactly one site $u\notin W$ enters $W'=W_A'\cup W_B'$ and exactly one site $v\in W$ leaves it.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.8, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_windows
import Definitions.Def_KawasakiSOS_Threshold_arcU
import Definitions.Def_KawasakiSOS_Threshold_arcT

namespace KawasakiSOS.Threshold

/-- `S′` is obtained from `S` by a slide: (a) an A-slide, (b) a B-slide, or (c) a block slide, and exactly one site `u ∉ W` enters `W′` and exactly one site `v ∈ W` leaves it.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.8, p. 12 (PDF p. 13). -/
def IsSlide {k : ℕ} [NeZero k] (S S' : Stage k) : Prop :=
  (((S'.cA = S.cA + 1 ∨ S'.cA = S.cA - 1) ∧ S'.cB = S.cB) ∨
    (S'.cA = S.cA ∧ (S'.cB = S.cB + 1 ∨ S'.cB = S.cB - 1)) ∨
    (((S'.cA = S.cA + 1 ∧ S'.cB = S.cB + 1) ∨ (S'.cA = S.cA - 1 ∧ S'.cB = S.cB - 1)) ∧
      ((arcU S = ∅ ∧ arcU S' = ∅) ∨ (arcT S = ∅ ∧ arcT S' = ∅)))) ∧
  ∃ u v, windows S' \ windows S = {u} ∧ windows S \ windows S' = {v}

end KawasakiSOS.Threshold


