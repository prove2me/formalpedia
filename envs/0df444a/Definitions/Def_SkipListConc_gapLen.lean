-- Prove2me | Definitions.Def_SkipListConc_gapLen
-- name    : SkipListConc_gapLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:59.159428+00:00
-- url     : https://prove2.me/theorems/cd1c35cb-bd93-4bb6-ae0a-4cfd361c8766
-- title:
--   Gap $A_i$ of the weighted Bernoulli gap model
-- statement:
--   In the **weighted Bernoulli gap model** (Definition 4.8), positions $1,\dots,N$ are marked or not and a sentinel position $0$ is always marked. For $i\ge 1$,
--   $$
--   A_i=\min\{a\ge 0:\ i-a\text{ is marked}\}
--   $$
--   is the number of unmarked positions passed moving left from $i$ before reaching a mark, so $A_i=0$ if $i$ is marked and $A_i\le i$.
--
--   **Formalization Note** A marking is a Boolean function of the position; the sentinel is the case $a=i$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 4.8, p.26

import Mathlib

namespace SkipListConc

/-- The gap `A_i = min {a ≥ 0 : i − a is marked}` of the weighted Bernoulli gap model
(Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Definition 4.8, p.26): the number of unmarked
positions passed moving left from `i` before reaching a mark, where the sentinel position `0` is
always marked. So `A_i = 0` if `i` is marked and `A_i ≤ i`.

**Formalization Note** `mark j ω` says whether position `j ≥ 1` is marked; the sentinel is the
case `a = i`, whatever `mark 0` says. -/
noncomputable def gapLen {Ω : Type*} (mark : ℕ → Ω → Bool) (i : ℕ) (ω : Ω) : ℕ :=
  Nat.find (⟨i, Or.inl rfl⟩ : ∃ a, a = i ∨ mark (i - a) ω = true)

end SkipListConc


