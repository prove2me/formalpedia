-- Prove2me | Definitions.Def_ManipPotential_Supplement_IsKASPAtSCC
-- name    : ManipPotential_Supplement_IsKASPAtSCC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:55:28.269558+00:00
-- url     : https://prove2.me/theorems/3485d881-16ab-499d-b416-815aa930815b
-- title:
--   $k$-augmentation strategyproofness of an SCC
-- statement:
--   An SCC $F$ is **$k$-augmentation strategyproof** ($k$-ASP) at electorate size $n$ if the tie-broken social choice function $F_T$ is $k$-ASP (Definition 1) for every linear tiebreaker $\succ_T \in \mathcal L(C)$.
--
--   Consequently, "$F$ is not $k$-ASP" means that some tiebreaker $\succ_T$, some profile $\succ_N$ of $n$ voters, some voter $i$ and some manipulation $\succ_i'$ satisfy $F_T(\succ_i', \succ_{-i}) \succ_i F_T(\succ_N + k(\succ_i))$.
--
--   **Formalization Note** Built on the published Definition 1 at electorate size $n$ (`ManipPotential.IsKASPAt`).
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s", p.10

import Mathlib
import Definitions.Def_ManipPotential_IsKASPAt
import Definitions.Def_ManipPotential_Supplement_tieBreak

namespace ManipPotential.Supplement

/-- `k`-augmentation strategyproofness of an SCC at electorate size `n` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3,
"Tie(breaker)s", p.10): `F` is `k`-ASP if `F_T` is `k`-ASP (Definition 1) for every linear
tiebreaker `≻_T ∈ L(C)`.

**Formalization Note** Uses the published `IsKASPAt` (Definition 1 at electorate size `n`). So
"`F` is not `k`-ASP" means: some tiebreaker `T` has `¬ IsKASPAt (tieBreak F T) n k`. -/
def IsKASPAtSCC {m : ℕ} [NeZero m] (F : SCC m) (n k : ℕ) : Prop :=
  ∀ T : Ranking m, IsKASPAt (tieBreak F T) n k

end ManipPotential.Supplement


