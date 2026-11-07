-- Prove2me | Definitions.Def_QBFBackdoor_roundMap
-- name    : QBFBackdoor_roundMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:31.893867+00:00
-- url     : https://prove2.me/theorems/7a0ea8d1-3e22-47be-bb26-aa904f1ade80
-- title:
--   Disjunct counts of the balanced squishing rounds
-- statement:
--   In a **balanced round** the current $d$ disjuncts are split into batches of six, the fewer than six remaining disjuncts are carried, and every full batch is squished to four disjuncts. When exactly five disjuncts remain, one is duplicated and the resulting batch of six is squished. So the count after a round is
--
--   $$
--   g(d)=\begin{cases}4, & d=5,\\ 4\lfloor d/6\rfloor + (d \bmod 6), & \text{otherwise.}\end{cases}
--   $$
--
--   The number of rounds $\mathrm{rounds}(d)$ is $0$ when $d\le 4$, and $1+\mathrm{rounds}(g(d))$ otherwise.
--
--   These quantities measure how many quantifier blocks the reduction to four disjuncts adds.
--
--   **Formalization Note** The definitions are `roundMap` and `rounds`; `rounds` terminates because $g(d)<d$ for $d\ge5$.
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), §5.2, pp.25–26

import Mathlib

namespace QBFBackdoor

/-- **The number of disjuncts after one balanced round.** Eriksson, Lagerkvist, Ordyniak, Osipov,
Panolan, Rychlicki, *Backdoors for Quantified Boolean Formulas*, arXiv:2604.15927 (held version,
sha256 3ea1662e…), §5.2, p.25: "In a round, partition the current disjuncts into batches of six and
carry the remaining fewer than six disjuncts unchanged. Squish every full batch … When the total
number of remaining disjuncts is five, duplicate one and squish the resulting batch of six." Each
full batch of six becomes four (Lemma 5.7 with k = 4, p = 1), so `d = 6b + r` with `0 ≤ r < 6`
becomes `4b + r`, and `5` becomes `4`.

**Formalization Note** The map is only applied while `d ≥ 5` (`rounds`). -/
def roundMap (d : ℕ) : ℕ :=
  if d = 5 then 4 else 4 * (d / 6) + d % 6

/-- **The number of balanced rounds** that bring `d` disjuncts down to at most four (§5.2,
pp.25–26): no round once `d ≤ 4`, otherwise one round and then the rounds of `roundMap d`. -/
def rounds (d : ℕ) : ℕ :=
  if h : d ≤ 4 then 0 else rounds (roundMap d) + 1
termination_by d
decreasing_by
  unfold roundMap
  split <;> omega

end QBFBackdoor


