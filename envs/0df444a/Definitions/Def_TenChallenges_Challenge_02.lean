-- Prove2me | Definitions.Def_TenChallenges_Challenge_02
-- name    : TenChallenges_Challenge_02
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:54:46.419193+00:00
-- url     : https://prove2.me/theorems/486b015d-fb1d-4b76-8809-00a84aced941
-- title:
--   Challenge 2: the scaled excluded-minor statement $S(r,B)$
-- statement:
--   The scaled form of Challenge 2. For natural numbers $r$ and $B$, the statement $S(r,B)$ says:
--
--   $$\text{for every prime } p \text{ and every } m\ge 1 \text{ with } p^m\le r,\ \text{the class of } \mathrm{GF}(p^m)\text{-representable matroids has at most } B \text{ excluded minors up to isomorphism.}$$
--
--   "At most $B$ excluded minors up to isomorphism" is the predicate $\mathrm{ExcludedMinorsAtMost}(p,m,B)$ of the companion definition. The statement is monotone: $S(r,B)$ implies $S(r',B')$ for $r'\le r$ and $B'\ge B$, and it is vacuous for $r\le 1$. Known rungs are $S(2,1)$ (Tutte), $S(3,4)$ (Bixby, Seymour) and $S(4,7)$ (Geelen, Gerards, Kapoor).
--
--   **Formalization Note.** The primality of $p$ enters as the instance argument `[Fact p.Prime]`, as required by `GaloisField p m`.
-- source:
--   Ten Challenges repository, file Challenges/challenge_02.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Challenges/challenge_02.lean; V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 2.

import Definitions.Def_TenChallenges_MatroidRepresentability

namespace TenChallenges

/-- For every prime power `pᵐ ≤ r`, the excluded minors for
`GF(pᵐ)`-representability number at most `B` up to isomorphism. -/
def statement_02 (r B : ℕ) : Prop :=
  ∀ (p m : ℕ) [Fact p.Prime], 0 < m → p ^ m ≤ r → ExcludedMinorsAtMost p m B

end TenChallenges


