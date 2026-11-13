-- Prove2me | Definitions.Def_RvsCert_raceOf
-- name    : RvsCert_raceOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:39:40.201484+00:00
-- url     : https://prove2.me/theorems/bb65a682-e4f5-454a-9fa7-bebbcad3f64a
-- title:
--   The $j$-th race of a country
-- statement:
--   For a country $c$ and $j\in\{0,\dots,2n-2\}$, the $j$-th race of $c$ is the race $\{c,d\}$ against its $j$-th opponent $d$.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, pp.1–2

import Mathlib
import Definitions.Def_RvsCert_Race
import Definitions.Def_RvsCert_opponent

namespace RvsCert

/-- **The `j`-th race of country `c`**: the race `{c, opponent c j}`, as the ordered pair
(smaller, larger) (Section 2, pp.1–2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1). -/
def raceOf {n : ℕ} (c : Fin (2 * n)) (j : Fin (2 * n - 1)) : Race n :=
  if h : (j : ℕ) < c then
    ⟨(opponent c j, c), by rw [Fin.lt_def]; simp only [opponent, if_pos h]; exact h⟩
  else
    ⟨(c, opponent c j), by rw [Fin.lt_def]; simp only [opponent, if_neg h]; omega⟩

end RvsCert


