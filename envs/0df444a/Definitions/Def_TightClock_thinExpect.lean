-- Prove2me | Definitions.Def_TightClock_thinExpect
-- name    : TightClock_thinExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:48:37.575215+00:00
-- url     : https://prove2.me/theorems/933a956c-6ec8-4847-9b7c-c306488a235d
-- title:
--   Expectation over a random child of a set
-- statement:
--   Let $D$ be a random child of $S$: a subset containing each member of $S$ independently with probability $a$. Then
--
--   $$\mathbb E_D[g(D)]=\sum_{D\subseteq S}a^{|D|}(1-a)^{|S\setminus D|}g(D).$$
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Lemma 6.7, §6.4, p.42 (PDF p.45)

import Mathlib
import Definitions.Def_TightClock_a

set_option autoImplicit false

namespace TightClock

/-- The expectation over a random child `D` of a set `S`: `D` contains each member of `S` independently with
probability `a`. Afshinmehr et al., manuscript (STOC 2027 submission), Lemma 6.7, §6.4, p.42 (PDF 45). -/
noncomputable def thinExpect {n : ℕ} (q : ℕ) (S : Finset (Fin n)) (g : Finset (Fin n) → ℝ) : ℝ :=
  ∑ D ∈ S.powerset, (a q) ^ D.card * (1 - a q) ^ (S \ D).card * g D

end TightClock


