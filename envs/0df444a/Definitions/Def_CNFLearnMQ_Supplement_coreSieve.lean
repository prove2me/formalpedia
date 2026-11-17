-- Prove2me | Definitions.Def_CNFLearnMQ_Supplement_coreSieve
-- name    : CNFLearnMQ_Supplement_coreSieve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:02:48.563875+00:00
-- url     : https://prove2.me/theorems/3335e432-598a-4972-a39a-5a89795a030b
-- title:
--   CoreSieve$(\delta)$ (Algorithm 5)
-- statement:
--   CoreSieve$(\delta)$ is the exact learner of §6. It is given $n,k,\alpha$ and $\delta\in(0,1)$, sample access to $\mu_\Phi$ and membership-query access to $\Phi$. With
--   $$N=\Bigl\lceil 4^k\, n^{\eta_k}\ln\frac{2\alpha n}{\delta}\Bigr\rceil,\qquad d_n=\lceil 10\log n\rceil,$$
--   it repeats $N$ times: draw a fresh solution $X_i\sim\mu_\Phi$, run LearnCore$(X_i,\delta/(2N))$ with degree parameter $d_n$, and insert the induced subclause $c(X_i,R)=(R,\neg (X_i)_R)$ into the candidate set $\widehat{\mathcal C}$ for every returned core $R$, discarding duplicates. It then removes every candidate strictly contained in another candidate and returns $\widehat\Phi=(V,\widehat{\mathcal C})$.
--
--   The algorithm uses the published LearnCore of the mission; Theorem 6.1 states its guarantee on random formulas.
--
--   **Formalization Note** The program is an `OProg`: it never receives $\Phi$ and reaches it only through sample and query answers. Time is charged explicitly: $1$ per round and for computing $N$; $(|R|+1)(\lfloor\log_2(|\widehat{\mathcal C}|+1)\rfloor+2)$ per insertion (writing the clause and inserting it in a balanced search tree); and $\sum_{s,c\in\widehat{\mathcal C}}(|s|+|c|+1)$ for the pairwise containment pass with literals in variable order (p.40). Returned cores are enumerated in a fixed order; the output set does not depend on it.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Algorithm 5, p.39, and the parameters N, d_n of §6.2, p.38; charges from the proof of Theorem 6.1, p.40

import Mathlib
import Definitions.Def_CNFLearnMQ_learnCore
import Definitions.Def_CNFLearnMQ_Supplement_randomCNF

set_option autoImplicit false

namespace CNFLearnMQ.Supplement

open CNFLearning873.Valiant CNFLearnMQ CNFLearnMQ.OProg

variable {n : ℕ}

/-- The number of sampled solutions `N = ⌈4^k · n^{η_k} · ln(2αn/δ)⌉` (Feng, Yu, Zhang, STOC 2027
submission (manuscript sha256 519ee6d4…), §6.2, p.38). -/
noncomputable def sieveRounds (n k : ℕ) (α δ : ℝ) : ℕ :=
  ⌈(4 : ℝ) ^ k * (n : ℝ) ^ etaK k * Real.log (2 * α * n / δ)⌉₊

/-- The degree parameter `d_n = ⌈10 log n⌉` (base-2 logarithm) passed to LearnCore (p.38). -/
noncomputable def degreeParam (n : ℕ) : ℕ := ⌈10 * log₂ n⌉₊

/-- Line 5 of Algorithm 5: insert `c(X, R)` into the candidate set `Ĉ` for every returned `R`,
discarding duplicates. Charge per insertion: `(|R| + 1)·(⌊log₂(|Ĉ| + 1)⌋ + 2)`, which covers
writing `c(X, R)` with literals in variable order and inserting it into a balanced search tree of
the candidates (`⌊log₂(|Ĉ| + 1)⌋ + 1` comparisons of `O(|R| + 1)` literal steps each). -/
def insertAll (X : Assignment n) : List (Finset (Fin n)) → CNF n → OProg n (CNF n)
  | [], C => OProg.pure C
  | R :: Rs, C => do
    charge ((R.card + 1) * (Nat.log 2 (C.card + 1) + 2))
    insertAll X Rs (insert (inducedClause X R) C)

/-- Lines 2–5 of Algorithm 5: `i` remaining rounds, each drawing a fresh solution `X`, running
LearnCore(`X`, `ζ`) with degree parameter `d_n` and inserting the induced subclauses of the returned
cores. Charge `1` per round for the loop counter. The returned family is enumerated in the fixed
order `Finset.toList` (the output set does not depend on it). -/
noncomputable def sieveLoop (n k : ℕ) (ζ : ℝ) : ℕ → CNF n → OProg n (CNF n)
  | 0, C => OProg.pure C
  | i + 1, C => do
    charge 1
    let X ← draw
    let Rs ← learnCore n k (degreeParam n) X ζ
    let C' ← insertAll X Rs.toList C
    sieveLoop n k ζ i C'

/-- Line 6 of Algorithm 5: the candidates not strictly contained (as literal sets) in another
candidate. -/
noncomputable def maximalOnly (C : CNF n) : CNF n := by
  classical
  exact C.filter fun s => ¬ ∃ c ∈ C, Subclause s c ∧ s ≠ c

/-- CoreSieve(δ) (Algorithm 5, p.39), with the parameters `n, k, α`, sample access to `µ_Φ` and
membership-query access to `Φ`: draw `N` solutions, recover their cores with LearnCore(`X_i`,
`δ/(2N)`) and degree parameter `d_n`, collect the induced subclauses `c(X_i, R)`, and return those not
strictly contained in another collected clause.

Charges: `1` for computing `N` (unit-cost real arithmetic); the loop and insertions as in
`sieveLoop` and `insertAll`; for line 6, `Σ_{s, c ∈ Ĉ} (|s| + |c| + 1)`, one merge-style containment
test per ordered pair with literals listed in variable order (p.40).

**Formalization Note** The program never receives `Φ`; it reaches it only through `run`'s sample
and membership-query answers. The paper fixes no order for the containment pass; the output set
does not depend on any order. -/
noncomputable def coreSieve (n k : ℕ) (α δ : ℝ) : OProg n (CNF n) := do
  charge 1
  let N := sieveRounds n k α δ
  let C ← sieveLoop n k (δ / (2 * (N : ℝ))) N ∅
  charge (∑ s ∈ C, ∑ c ∈ C, (width s + width c + 1))
  return maximalOnly C

end CNFLearnMQ.Supplement


