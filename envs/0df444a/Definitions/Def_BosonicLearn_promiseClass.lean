-- Prove2me | Definitions.Def_BosonicLearn_promiseClass
-- name    : BosonicLearn_promiseClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:20:46.885207+00:00
-- url     : https://prove2.me/theorems/0cbadfc4-5dcc-4d4e-904d-2a8882b4cb0e
-- title:
--   The promise class $K(n,\nu)=\{\rho(\mu,\Sigma):\Sigma\succeq(\tfrac12+\nu)I\}$
-- statement:
--   For $n\in\mathbb N$ and $\nu\in\mathbb R$, $K(n,\nu)$ is the set of $n$-mode density operators that are Gaussian states $\rho(\mu,\Sigma)$ with an arbitrary mean $\mu\in\mathbb R^{2n}$ and a covariance satisfying
--
--   $$\Sigma\succeq\Big(\tfrac12+\nu\Big)I$$
--
--   in the Loewner order on real symmetric $2n\times 2n$ matrices. This is the family of states that the learner must handle in Theorems 3 and 8 and Corollary 19.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 3, pp. 6–7; Eq. (205), p. 61

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicLearn

/-- **The promise class `K(n, ν)`: Gaussian states with `Σ ⪰ (½ + ν) I`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 3, pp. 6–7: "Under the promise that an n-mode Gaussian state ρ(µ, Σ) satisfies
Σ ≥ (1/2 + ν)I for some ν > 0"; also Eq. (205), p. 61.

`promiseClass n ν` is the set of density operators on the `n`-mode Fock space that are Gaussian states
`ρ(µ, Σ)` for some mean `µ ∈ ℝ²ⁿ` (arbitrary) and some covariance `Σ` with `Σ − (½+ν) I` positive
semidefinite (Loewner order on real symmetric `2n × 2n` matrices).

**Formalization Note.** The covariance is the paper's (vacuum `½ I`), see `IsGaussianState`. The mean is
unrestricted. -/
def promiseClass (n : ℕ) (ν : ℝ) : Set (State (Occupation (Fin n))) :=
  {ρ | ∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    IsGaussianState ρ μ S ∧
      (S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef}

end BosonicLearn


