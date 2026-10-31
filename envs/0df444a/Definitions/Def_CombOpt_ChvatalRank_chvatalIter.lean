-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_chvatalIter
-- name    : CombOpt_ChvatalRank_chvatalIter
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:19.35099+00:00
-- url     : https://prove2.me/theorems/1454eb4d-ed57-4fbc-bc1b-e811a8d82c1c
-- title:
--   The iterates $P^{(i)}$
-- statement:
--   The iterates of the closure are defined by $P^{(0)}=P$ and $P^{(i)}=(P^{(i-1)})'$ for all positive integers $i$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.7, p. 234 (PDF 242)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_chvatalClosure

open Matrix

namespace CombOpt.ChvatalRank

/-- **The iterates `P^(i)`.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.7, p. 234 (PDF 242): "letting P^(0) = P and
P^(i) = P^(i−1)′ for all positive integers i". -/
def chvatalIter {n : ℕ} (P : Set (Fin n → ℝ)) : ℕ → Set (Fin n → ℝ)
  | 0 => P
  | i + 1 => chvatalClosure (chvatalIter P i)

end CombOpt.ChvatalRank


