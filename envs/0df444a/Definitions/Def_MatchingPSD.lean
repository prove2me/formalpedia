-- Prove2me | Definitions.Def_MatchingPSD
-- name    : MatchingPSD
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.516549+00:00
-- url     : https://prove2.me/theorems/480c8d87-e86e-46ba-8658-65653d6ac483
-- statement:
--   Vertices are Fin n, and an Edge is an ordered pair (a,b) with a<b, so edges are the unordered pairs of distinct vertices. A set M of edges is a perfect matching if every vertex lies in exactly one edge of M. An OddCut is a vertex subset U of odd cardinality, and a Row is either an edge or an odd cut. An edge crosses U if exactly one of its endpoints lies in U, and crossingCount(U,M) is the number of edges of a perfect matching M that cross U. The slack of a row at a perfect matching M is the indicator that e belongs to M when the row is an edge e, and is crossingCount(U,M) minus 1 when the row is an odd cut U. HasFactorization(n,r) says there are real r×r positive semidefinite matrices A_i, one for each row i, and B_M, one for each perfect matching M, such that slack(i,M) = trace(A_i B_M) for all rows i and matchings M, with no equivariance or rank-one restriction. psdRank(n) is the least positive r for which this holds, taken as an infimum over naturals. MainClaim is a defined proposition, not an established theorem: for every real C>0 there is n₀≥4 such that for all even n≥n₀, n^C (real power) is strictly less than psdRank(n), meaning the PSD rank of the perfect matching slack matrix grows faster than any polynomial in n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatchingPSD.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingPSD.lean; bytes 16..1759
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PerfectMatchingPSD

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def IsPerfectMatching {n : ℕ} (M : Finset (Edge n)) : Prop :=
  ∀ v : Fin n, (M.filter fun e => e.1.1 = v ∨ e.1.2 = v).card = 1

abbrev PerfectMatching (n : ℕ) :=
  {M : Finset (Edge n) // IsPerfectMatching M}

abbrev OddCut (n : ℕ) := {U : Finset (Fin n) // Odd U.card}

abbrev Row (n : ℕ) := Edge n ⊕ OddCut n

def Crosses {n : ℕ} (U : Finset (Fin n)) (e : Edge n) : Prop :=
  (e.1.1 ∈ U ∧ e.1.2 ∉ U) ∨ (e.1.1 ∉ U ∧ e.1.2 ∈ U)

noncomputable def crossingCount {n : ℕ} (U : Finset (Fin n))
    (M : PerfectMatching n) : ℕ := by
  classical
  exact (M.1.filter (Crosses U)).card

noncomputable def slack {n : ℕ} (i : Row n) (M : PerfectMatching n) : ℝ := by
  classical
  exact match i with
  | Sum.inl e => if e ∈ M.1 then 1 else 0
  | Sum.inr U => (crossingCount U.1 M : ℝ) - 1

/-- Real PSD factors of order `r`, without equivariance or rank-one restrictions. -/
def HasFactorization (n r : ℕ) : Prop :=
  ∃ (A : Row n → Matrix (Fin r) (Fin r) ℝ)
    (B : PerfectMatching n → Matrix (Fin r) (Fin r) ℝ),
    (∀ i, (A i).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
    ∀ i M, slack i M = Matrix.trace (A i * B M)

/-- The least positive order of a real PSD factorization. -/
noncomputable def psdRank (n : ℕ) : ℕ :=
  sInf {r : ℕ | 0 < r ∧ HasFactorization n r}

/-- Every positive real power is eventually smaller than the PSD rank,
uniformly over all even vertex counts. The exponentiation is real `rpow`. -/
def MainClaim : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → Even n → (n : ℝ) ^ C < (psdRank n : ℝ)



end PerfectMatchingPSD
end OAI


