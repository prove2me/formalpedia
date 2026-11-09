-- Prove2me | Definitions.Def_L22EigEst_QueryPlan
-- name    : L22EigEst_QueryPlan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:12:01.72072+00:00
-- url     : https://prove2.me/theorems/1ce17af0-48b8-41a3-8f8d-285c511b95c9
-- title:
--   Randomized non-adaptive query algorithms in the $\ell_2^2$-sampling model
-- statement:
--   A **query plan** for an $n\times n$ matrix consists of
--
--   1. a finite set $Q\subseteq[n]\times[n]$ of positions to read, and
--   2. an output map that turns the values $(A_{ij})_{(i,j)\in Q}$ into $n$ reals $\hat\lambda_1,\dots,\hat\lambda_n$.
--
--   The output depends on $A$ only through the entries at $Q$. A **randomized query algorithm in the $\ell_2^2$-sampling model** is, for each dimension $n$, accuracy $\varepsilon$ and list $r=(\|A_1\|_2^2,\dots,\|A_n\|_2^2)$ of squared row norms, a probability distribution over query plans. Its **query complexity** on a run is $|Q|$, the number of entries read, and its **sample complexity** is the size of the smallest $T\subseteq[n]$ with $Q\subseteq T\times T$, the dimension of the smallest principal submatrix containing all queries.
--
--   Because the plan is drawn before any entry is read, the algorithm is non-adaptive, as the paper's algorithm is ("the algorithm's queries can all be specified before the algorithm reads any entry of $A$").
--
--   **Formalization Note** Positions are ordered pairs with 0-based indices; a plan may read only one of $(i,j)$, $(j,i)$. The distribution is a `PMF` (countably supported). No running-time or computability condition is imposed on the output map, since the paper claims none.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), §1, p.3 (Query and Sample Complexity), §1.1, p.4 (non-adaptivity)

import Mathlib

namespace L22EigEst

/-- **A non-adaptive query plan** on an `n × n` matrix: a finite set `Q` of positions to read and
an output map that produces `n` reals from the values read at `Q` only.
Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…), §1, p.3 ("Query Complexity:
The number of entries of A which the algorithm reads"; "Sample Complexity: … the dimension of the
smallest principal submatrix which contains all queries") and §1.1, p.4 ("the algorithm's queries
can all be specified before the algorithm reads any entry of A").

**Formalization Note.** The output map has type `(↥Q → ℝ) → Fin n → ℝ`: it sees the matrix only
through the values at the positions in `Q`. Positions are ordered pairs `(i, j)` with 0-based
indices; a plan may read only one of `(i, j)`, `(j, i)`. No computability or running-time condition
is imposed (the paper claims none). -/
structure QueryPlan (n : ℕ) where
  /-- the positions read -/
  Q : Finset (Fin n × Fin n)
  /-- the output, as a function of the values read -/
  out : (↥Q → ℝ) → Fin n → ℝ

/-- The answers to the queries of a plan `P` on the matrix `A`: the entries of `A` at the
positions of `P.Q`, and nothing else. -/
def respond {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P : QueryPlan n) : ↥P.Q → ℝ :=
  fun x => A x.1.1 x.1.2

/-- **A randomized non-adaptive query algorithm in the ℓ₂²-sampling model**: for each dimension
`n`, accuracy `ε` and list `r` of squared row norms, a probability distribution over query plans.
Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…), §1, p.3 ("the algorithm is
given query access to A together with the list of squared row norms").

**Formalization Note.** The distribution is a `PMF` (countably supported randomness); it depends on
`n`, `ε` and `r` only, never on the matrix. The probability of a set `E` of plans is
`(alg n ε r).toOuterMeasure E`. -/
abbrev QueryAlg : Type :=
  (n : ℕ) → ℝ → (Fin n → ℝ) → PMF (QueryPlan n)

end L22EigEst


