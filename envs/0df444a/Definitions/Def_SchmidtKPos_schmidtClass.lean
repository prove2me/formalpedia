-- Prove2me | Definitions.Def_SchmidtKPos_schmidtClass
-- name    : SchmidtKPos_schmidtClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:49:36.467738+00:00
-- url     : https://prove2.me/theorems/c4cf5800-a388-45e9-8de7-9e87c43d4f38
-- title:
--   $S_k$: density matrices of Schmidt number at most $k$
-- statement:
--   For natural numbers $n$ and $k$, the set $S_k$ consists of the density matrices on $\mathcal H_n\otimes\mathcal H_n$ (positive semidefinite, of trace one) that have Schmidt number $k$ or less:
--
--   $$
--   S_k=\{\rho\ \text{density matrix on}\ \mathcal H_n\otimes\mathcal H_n:\ \rho\ \text{has Schmidt number}\ j\ \text{for some}\ j\le k\}.
--   $$
--
--   The set $S_1$ is the set of separable density matrices. The sets $S_k$ form the hierarchy that $k$-positive maps detect.
--
--   **Formalization Note** The space $\mathcal H_n$ is $\mathbb C^n$ with basis `Fin n`. Since a unit vector has Schmidt rank at least one, $S_0=\emptyset$.
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, p. 1, "Let us denote the set of density matrices on Hn ⊗ Hn that have Schmidt number k or less by Sk"

import Mathlib
import Definitions.Def_SchmidtKPos_HasSchmidtNumber
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, p.1: `S_k`, "the set of density matrices on `H_n ⊗ H_n` that have
Schmidt number `k` or less".

**Formalization Note.** `H_n` is `ℂ^n` with basis `Fin n`, so `H_n ⊗ H_n` has basis
`Fin n × Fin n`. Since a unit vector has Schmidt rank at least `1`, `S_0 = ∅`. -/
def schmidtClass (n k : ℕ) : Set (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :=
  {ρ | QAlgorithms.IsDensityMatrix ρ ∧ ∃ j ≤ k, HasSchmidtNumber ρ j}

end SchmidtKPos


