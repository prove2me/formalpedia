-- Prove2me | Definitions.Def_FermiHubbardMix_Supplement_productStates
-- name    : FermiHubbardMix_Supplement_productStates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:04:31.42593+00:00
-- url     : https://prove2.me/theorems/0a4d2836-8001-44a3-ae04-c8f70f1abf45
-- title:
--   $n$-qubit product states $\rho_1\otimes\cdots\otimes\rho_n$
-- statement:
--   An $n$-qubit **product state** is an operator
--   $$
--   \rho=\rho_1\otimes\rho_2\otimes\cdots\otimes\rho_n,
--   $$
--   where each $\rho_k$ is a single-qubit density matrix: a $2\times2$ positive semidefinite matrix of trace one (mixed factors allowed). A state is a **convex combination of product states** if it lies in the convex hull of this set.
--
--   This is the notion of separability in Theorem 9.1.
--
--   **Formalization Note** The tensor product is the published `FermiCap.Gaussian.pauliString`, factor $k$ acting on qubit $k$.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Theorem 9.1, p.41

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana
import Definitions.Def_FermiHubbardMix_parityOp
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

/-- The set of `n`-qubit **product states** `ρ_1 ⊗ ⋯ ⊗ ρ_n`, each `ρ_k` a single-qubit density matrix
(a `2 × 2` positive semidefinite matrix of trace one) (Bakshi, Moitra, Tan, *Algorithmic Aspects of the
Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), Theorem 9.1, p.41).

**Formalization Note** The tensor product is the published `FermiCap.Gaussian.pauliString`
(factor `k` on qubit `k`). The factors may be mixed. "A convex combination of product states" is
membership in `convexHull ℝ (productStates n)`. -/
def productStates (n : ℕ) : Set (Op n) :=
  {ρ | ∃ ρs : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
    (∀ k, (ρs k).PosSemidef ∧ (ρs k).trace = 1) ∧ ρ = FermiCap.Gaussian.pauliString ρs}

end FermiHubbardMix.Supplement


