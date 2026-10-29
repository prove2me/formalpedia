-- Prove2me | Definitions.Def_ElectManip_Scoring_Protocol
-- name    : ElectManip_Scoring_Protocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:51.767787+00:00
-- url     : https://prove2.me/theorems/077c1312-32d1-4c78-9bc3-e92def7114b1
-- title:
--   Weighted positional scoring protocols and unique winners
-- statement:
--   Let $n$ be a natural number and label the candidates by $0,\ldots,n-1$. A complete ballot is a permutation $b$ sending each candidate to its rank, with rank zero best. A positional scoring protocol is a nonincreasing integer vector $\alpha$ on those ranks. A weighted profile $V$ is a finite list of pairs $(w,b)$, where $w$ is a natural number and $b$ a ballot. Define
--
--   $$s_\alpha(V,c)=\sum_{(w,b)\in V}w\alpha_{b(c)}.$$
--
--   A candidate $p$ is a unique winner precisely when $s_\alpha(V,q)<s_\alpha(V,p)$ for every $q\ne p$. This reusable scoring model is independent of the manipulation question. Negative and constant score vectors, zero weights, repeated ballots, and empty profiles are allowed. An empty profile gives every candidate score zero. For $n=0$ there is no candidate to query; for $n=1$ the sole candidate satisfies the winner condition vacuously. The mission's goal specializes to exactly three candidates.
--
--   **Formalization Note** Candidate and rank indices use `Fin n`; integer sums are not truncated natural arithmetic. Lists distinguish voters even when their weights and ballots agree.
-- source:
--   Conitzer, Sandholm and Lang, When Are Elections with Few Candidates Hard to Manipulate?, Journal of the ACM (2007), DOI 10.1145/1236457.1236461, pp. 5–6, Section 2; p. 8, tie convention after Definition 2 (PDF pp. 5–6, 8).

import Mathlib

namespace ElectManip.Scoring

/-- A complete strict ranking, sending each candidate to its zero-based rank. -/
abbrev Ballot (n : ℕ) := Equiv.Perm (Fin n)

/-- A positional scoring protocol has arbitrary nonincreasing integer scores. -/
structure Protocol (n : ℕ) where
  points : Fin n → ℤ
  nonincreasing : Antitone points

/-- Finite lists retain separate voters, including repeated ballots and zero weights. -/
abbrev Profile (n : ℕ) := List (ℕ × Ballot n)

/-- The integer total of weight times the score at the candidate's rank. -/
def score {n : ℕ} (α : Protocol n) (votes : Profile n) (c : Fin n) : ℤ :=
  (votes.map fun v => (v.1 : ℤ) * α.points (v.2 c)).sum

/-- A tie for the greatest score does not count as a win. -/
def UniqueWinner {n : ℕ} (α : Protocol n) (votes : Profile n) (p : Fin n) : Prop :=
  ∀ q : Fin n, q ≠ p → score α votes q < score α votes p

end ElectManip.Scoring


