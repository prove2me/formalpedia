-- Prove2me | Definitions.Def_ManipPotential_IsKASPAt
-- name    : ManipPotential_IsKASPAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:43.46021+00:00
-- url     : https://prove2.me/theorems/1278fc2a-428a-447e-bd9f-2ed810823ba5
-- title:
--   $k$-augmentation strategyproofness at electorate size $n$ (Definition 1)
-- statement:
--   A **social choice function** (SCF) is a map $f : \mathcal L(C)^* \to C$ assigning a winner to every preference profile of any number of voters. For a profile $\succ_N = (\succ_1, \dots, \succ_n)$, a voter $i$, an alternative order $\succ_i'$ and an integer $k \ge 0$, write $(\succ_i', \succ_{-i})$ for the profile in which voter $i$'s ballot is replaced by $\succ_i'$, and $\succ_N + k(\succ_i)$ for the profile with $k$ additional copies of $\succ_i$ appended.
--
--   The SCF $f$ is **$k$-augmentation strategyproof ($k$-ASP) at electorate size $n$** if for every profile $\succ_N$ of $n$ voters, every voter $i$ and every $\succ_i' \in \mathcal L(C)$,
--   $$
--   f(\succ_N + k(\succ_i)) \ \succeq_i\ f(\succ_i', \succ_{-i}).
--   $$
--
--   In words: no voter is ever strictly better off misreporting than having $k$ additional truthful copies of her ballot join the original profile. $0$-ASP is ordinary strategyproofness.
--
--   **Formalization Note** A profile is a list of rankings and voter $i$ a list index; an SCF is a total function on lists. The $k$ copies are appended at the end, the manipulation replaces entry $i$, and both outcomes are compared in voter $i$'s truthful ranking.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 1, p.8

import Mathlib
import Definitions.Def_ManipPotential_Ranking_WeaklyPrefers

namespace ManipPotential

/-- `k`-augmentation strategyproofness at electorate size `n` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 1, p.8): for
every profile `≻_N` of `n` voters, every voter `i` and every alternative order `≻'_i`,
`f(≻_N + k(≻_i)) ⪰_i f(≻'_i, ≻_{−i})`.

**Formalization Note** A profile is a `List (Ranking m)`, voter `i` a list index; an SCF is a total
map `List (Ranking m) → Fin m` (`f : L(C)* → C`). The `k` copies of voter `i`'s truthful ballot are
appended at the end, as printed; the manipulated profile is `P.set i s`; both outcomes are compared
in voter `i`'s truthful ranking. -/
def IsKASPAt {m : ℕ} (f : List (Ranking m) → Fin m) (n k : ℕ) : Prop :=
  ∀ P : List (Ranking m), P.length = n → ∀ (i : Fin P.length) (s : Ranking m),
    Ranking.WeaklyPrefers (P.get i) (f (P ++ List.replicate k (P.get i))) (f (P.set i s))

end ManipPotential


