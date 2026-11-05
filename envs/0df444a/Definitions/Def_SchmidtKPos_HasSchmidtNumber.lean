-- Prove2me | Definitions.Def_SchmidtKPos_HasSchmidtNumber
-- name    : SchmidtKPos_HasSchmidtNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:49.924612+00:00
-- url     : https://prove2.me/theorems/550b4bef-e17f-4e37-af5b-27452d33c6dd
-- title:
--   Schmidt number of a bipartite density matrix (Definition 1)
-- statement:
--   A bipartite operator $\rho$ on $\mathcal H_n\otimes\mathcal H_n$ **has Schmidt number** $k$ if
--
--   1. for every decomposition $\{p_i\ge 0,|\psi_i\rangle\}$ of $\rho$, at least one of the vectors $|\psi_i\rangle$ has Schmidt rank at least $k$, and
--   2. there exists a decomposition of $\rho$ all of whose vectors have Schmidt rank at most $k$.
--
--   The Schmidt rank of a pure state $|\psi\rangle=\sum_{i=1}^k\sqrt{\lambda_i}\,|a_i\rangle\otimes|b_i\rangle$ (Eq. (1)) is the number $k$ of terms of its Schmidt decomposition, equivalently the rank of the reduced density matrix or of the coefficient matrix $(\psi_{ij})$. The Schmidt number is thus the minimum Schmidt rank of the pure states needed to construct $\rho$; separable states have Schmidt number $1$.
--
--   **Formalization Note** The Schmidt rank is the published coefficient-matrix rank `Dependency50.P50.schmidtNumber`. Definition 1 is kept as a relation, so that no default value appears for an undefined quantity.
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, Definition 1, p. 1; Eq. (1), p. 1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
import Definitions.Def_SchmidtKPos_IsPureDecomposition
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

open QAlgorithms.Papers.Independent.Dependency50.P50 (schmidtNumber)

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, Definition 1, p.1: `ρ` has Schmidt number `k` if (i) for any
decomposition `{p_i ≥ 0, |ψ_i⟩}` of `ρ`, at least one of the vectors has at least Schmidt rank
`k`, and (ii) there exists a decomposition of `ρ` with all vectors of Schmidt rank at most `k`.

**Formalization Note.** The Schmidt rank of Eq. (1) is the published coefficient-matrix rank
`Dependency50.P50.schmidtNumber` (the rank of `Tr_B |ψ⟩⟨ψ|`; that development calls it the
Schmidt number of a vector). Definition 1 is a relation, not a function, so no junk value
arises: "Schmidt number at least `k + 1`" is `∃ j, k + 1 ≤ j ∧ HasSchmidtNumber ρ j`. Decompositions
are as in `IsPureDecomposition`. Clause (i) excludes `ρ = 0` through the empty decomposition, which
is harmless: `0` is not a density matrix. -/
def HasSchmidtNumber {n : ℕ} (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (k : ℕ) : Prop :=
  (∀ (r : ℕ) (p : Fin r → ℝ) (ψ : Fin r → EuclideanSpace ℂ (Fin n × Fin n)),
      IsPureDecomposition ρ p ψ → ∃ i, k ≤ schmidtNumber (ψ i)) ∧
  (∃ (r : ℕ) (p : Fin r → ℝ) (ψ : Fin r → EuclideanSpace ℂ (Fin n × Fin n)),
      IsPureDecomposition ρ p ψ ∧ ∀ i, schmidtNumber (ψ i) ≤ k)

end SchmidtKPos


