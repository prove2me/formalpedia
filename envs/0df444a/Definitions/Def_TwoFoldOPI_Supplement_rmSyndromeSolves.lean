-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_rmSyndromeSolves
-- name    : TwoFoldOPI_Supplement_rmSyndromeSolves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:54:50.839209+00:00
-- url     : https://prove2.me/theorems/7e5d29d4-5d16-4307-868d-d337c043233e
-- title:
--   Solutions of $\mathrm{RMSyndrome}$: $y$ with no zero entry and $By=0$
-- statement:
--   Let $S=\{p_1,\dots,p_m\}\subseteq\mathbb F_q^v$ and $r=\lfloor\rho v\rfloor$. The matrix $B$ has one row for each monomial $X^\alpha$ with $\alpha\in\{0,\dots,q-1\}^v$ and $\alpha_1+\dots+\alpha_v\le r$, one column for each point $p_j$, and entries $p_j^\alpha$. A vector $y\in\mathbb F_q^m$ **solves** $\mathrm{RMSyndrome}$ if every $y_j\ne0$ and
--   $$\sum_{j=1}^m p_j^{\alpha}\,y_j=0\quad\text{for every row }\alpha .$$
--
--   **Formalization Note** $By=0$ is stated row by row, so the row order is immaterial; the column order is the listing of the points.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §6, Definition 6.2, p. 36

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **Solutions of the dual formulation `RMSyndrome`: `y` with no zero entry and `By = 0`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §6, Definition 6.2, p.36: "Let B ∈ F_q^{n×m} have rows indexed by monomials in
F_q[X_1, …, X_v] of individual degree ≤ q − 1 and total degree ≤ ⌊ρv⌋, and columns indexed by the
points of S. Each entry of B is the row's monomial evaluated at the column's point. Then the
algorithm's task is to find a vector y ∈ F_q^m such that none of its entries are 0, and By = 0."

For points `pts j ∈ K^v` (`j < m`, the columns) and `r = ⌊ρv⌋`, `rmSyndromeSolves r pts y` says
that every `y_j ≠ 0` and, for every exponent vector `α ∈ {0, …, q−1}^v` with
`α_1 + ⋯ + α_v ≤ r` (a row of `B`), `Σ_j (∏_i (pts j)_i^{α_i}) · y_j = 0`.

**Formalization Note.** `By = 0` is written row by row, so the order of the rows of `B` does not
matter; the column order is the order of `pts`. `q = |K|`. -/
def rmSyndromeSolves {K : Type*} [Field K] [Fintype K] {v m : ℕ} (r : ℕ)
    (pts : Fin m → Fin v → K) (y : Fin m → K) : Prop :=
  (∀ j, y j ≠ 0) ∧
    ∀ α : Fin v → Fin (Fintype.card K), ∑ i, (α i : ℕ) ≤ r →
      ∑ j, (∏ i, pts j i ^ (α i : ℕ)) * y j = 0

end Supplement

end TwoFoldOPI


