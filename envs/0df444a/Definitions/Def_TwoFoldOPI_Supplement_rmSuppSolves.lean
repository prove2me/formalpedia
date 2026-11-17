-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_rmSuppSolves
-- name    : TwoFoldOPI_Supplement_rmSuppSolves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:55:12.762616+00:00
-- url     : https://prove2.me/theorems/a794c3a5-ac5f-4634-b5a3-6105a5427e8c
-- title:
--   Solutions of $\mathrm{RMSupp}$: a polynomial of low degree nonzero exactly on $S$
-- statement:
--   A polynomial $f\in\mathbb F_q[X_1,\dots,X_v]$ **solves** $\mathrm{RMSupp}$ for $S\subseteq\mathbb F_q^v$ and $r=\lfloor\rho v\rfloor$ if its total degree is at most $v(q-1)-r-1$, $f(x)\ne0$ for $x\in S$ and $f(x)=0$ for $x\notin S$.
--
--   The polynomial is given by its coefficient vector over the reduced monomials $X^\alpha$, $\alpha\in\{0,\dots,q-1\}^v$.
--
--   **Formalization Note** Any solution can be reduced ($X_i^q\mapsto X_i$ preserves values on $\mathbb F_q^v$ and does not raise the total degree), so this output format loses no solution. The degree bound is compared in $\mathbb Z$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §6, Definition 6.1, p. 36

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **Solutions of the primal formulation `RMSupp`: a low-degree polynomial nonzero exactly on
`S`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §6, Definition 6.1, p.36: "The algorithm's task is to find a polynomial
f ∈ F_q[X_1, …, X_v] of total degree at most v(q − 1) − ⌊ρv⌋ − 1 such that for all x ∈ S we have
f(x) ≠ 0, and for all x ∉ S we have f(x) = 0."

The polynomial is given by its coefficients `coeff α` on the reduced monomials
`X^α = X_1^{α_1} ⋯ X_v^{α_v}`, `α ∈ {0, …, q−1}^v`. `rmSuppSolves v r S coeff` says:
1. every `α` with `coeff α ≠ 0` has `α_1 + ⋯ + α_v ≤ v(q − 1) − r − 1` (total degree);
2. `f(x) = Σ_α coeff α · x^α` is nonzero exactly at the points of `S`.

**Formalization Note.** The output format is the coefficient vector over reduced monomials
(individual degrees `≤ q − 1`). Any solution can be reduced (`X_i^q ↦ X_i` does not raise the
total degree and does not change values on `K^v`), so this format loses no solution. The degree
bound is compared in `ℤ`, so `v(q−1) − r − 1 < 0` allows only the zero polynomial. -/
def rmSuppSolves {K : Type*} [Field K] [Fintype K] (v r : ℕ) (S : Set (Fin v → K))
    (coeff : (Fin v → Fin (Fintype.card K)) → K) : Prop :=
  (∀ α, coeff α ≠ 0 →
      ((∑ i, (α i : ℕ) : ℕ) : ℤ) ≤ ((v * (Fintype.card K - 1) : ℕ) : ℤ) - r - 1) ∧
    ∀ x : Fin v → K, (∑ α, coeff α * ∏ i, x i ^ (α i : ℕ)) ≠ 0 ↔ x ∈ S

end Supplement

end TwoFoldOPI


