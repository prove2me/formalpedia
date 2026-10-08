-- Prove2me | Definitions.Def_RegevLWE_SmoothingLB_Lattice
-- name    : RegevLWE_SmoothingLB_Lattice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:15.741049+00:00
-- url     : https://prove2.me/theorems/c1600274-0c67-4999-a4c6-5383632cd4f5
-- title:
--   p. 34:18 — the successive minima λ₁(L) and λ_n(L) of a ℤ-submodule of ℝⁿ
-- statement:
--   Work in $\mathbb{R}^n$ with its Euclidean norm $\|\cdot\|$. A **lattice** $L \subset \mathbb{R}^n$ is the set of all integer combinations of $n$ linearly independent vectors.
--
--   **Successive minima** (p. 34:18). $\lambda_1(L)$ is the length of a shortest nonzero vector of $L$, and $\lambda_n(L)$ is the minimum length of a set of $n$ linearly independent vectors of $L$, the length of a set being the length of its longest vector:
--   $$\lambda_1(L) := \inf\{\|v\| : v \in L,\ v \neq 0\},\qquad \lambda_n(L) := \inf\{r : L \text{ contains } n \text{ linearly independent vectors of norm} \le r\}.$$
--
--   These are, together with the Gaussian $\rho_s$, the dual lattice $L^*$, the mass $\rho_s(L^*\setminus\{0\})$ and the smoothing parameter $\eta_\epsilon(L)$ of Definition 2.10 (defined in the shared module `RegevLWE.GaussConv`), the objects of Claim 2.13 and of Banaszczyk's transference theorem (Lemma 2.3).
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`; $L$ is any `Submodule ℤ` of it, so both minima apply to the dual $L^*$ directly; the theorems of the mission add Mathlib's lattice instances `DiscreteTopology L`, `IsZLattice ℝ L`. "Shortest" and "minimum" are written as infima (`sInf`); for a lattice (or its dual) in dimension $n \ge 1$ the sets are nonempty, bounded below by $0$, and the infima are attained. On degenerate input `sInf` returns $0$ (the zero submodule, or $\lambda_n$ at $n = 0$, where the empty family qualifies for every $r$), which is why the theorems assume $n \ge 1$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:18 (λ₁, λ_n)

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice

namespace RegevLWE.SmoothingLB

/-- The first successive minimum `λ₁(L)`, the length of a shortest nonzero vector of `L`
(p. 34:18), written as the infimum of the norms of the nonzero vectors of `L`. Defined for any
`ℤ`-submodule of `ℝⁿ`, so it applies to the dual lattice `L*` (`RegevLWE.GaussConv.dual L`) as well. -/
noncomputable def lambda1 {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf {r : ℝ | ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ = r}

/-- The `n`-th successive minimum `λ_n(L)` (p. 34:18): the minimum, over all sets of `n` linearly
independent vectors of `L`, of the length of the longest vector in the set; written as the
infimum of the `r` such that `L` contains `n` linearly independent vectors of norm at most `r`. -/
noncomputable def lambdaN {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin n → EuclideanSpace ℝ (Fin n),
    LinearIndependent ℝ v ∧ ∀ i, v i ∈ L ∧ ‖v i‖ ≤ r}

end RegevLWE.SmoothingLB


