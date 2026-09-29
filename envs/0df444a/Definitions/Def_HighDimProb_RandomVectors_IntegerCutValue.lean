-- Prove2me | Definitions.Def_HighDimProb_RandomVectors_IntegerCutValue
-- name    : HighDimProb_RandomVectors_IntegerCutValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T06:40:27.842122+00:00
-- url     : https://prove2.me/theorems/dcc49a4c-bfb2-4027-8e50-4d20a87d700a
-- title:
--   INT(A) — the integer optimization problem (3.20)
-- statement:
--   This definition is $\mathrm{INT}(A)$, the maximum value of the integer optimization problem
--   (3.20) that Theorem 3.5.6 compares to its semidefinite relaxation.
--
--   For an $n \times n$ real matrix $A = (A_{ij})$,
--
--   $$
--   \mathrm{INT}(A) \;:=\; \max\Bigl\{ \sum_{i,j=1}^n A_{ij}\, x_i x_j \;:\; x_i \in \{-1,1\}
--   \text{ for } i = 1,\dots,n \Bigr\}.
--   $$
--
--   The feasible set $\{-1,1\}^n$ has $2^n$ elements, so this maximum is always attained; it is
--   the value of the intractable (NP-hard, in general) combinatorial problem that the
--   semidefinite program (3.21)/(3.22) is designed to approximate.
--
--   **Formalization Note** The sign vector $x \in \{-1,1\}^n$ is represented as a function
--   `Fin n → Bool` (via $b \mapsto 1$ if `b = true`, $-1$ if `b = false`), a nonempty finite
--   type for every `n`, including `n = 0` (the single empty sign assignment, giving
--   $\mathrm{INT}(A) = 0$ for the unique $0 \times 0$ matrix). The value is a genuine supremum
--   over a finite, nonempty set, hence an honest maximum, never a vacuous or unbounded `sSup`.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Eq. (3.20), p. 64 (PDF p. 72)

import Mathlib

namespace HighDimProb.RandomVectors

/-- `INT(A)`, the maximum of the integer optimization problem (3.20). Vershynin,
*High-Dimensional Probability* (2018), p. 64, Eq. (3.20):

`maximize ∑ᵢⱼ Aᵢⱼ xᵢ xⱼ : xᵢ = ±1 for i = 1, …, n`.

The feasible set `{−1, 1}ⁿ` is represented as `Fin n → Bool`, a nonempty finite type (via the
sign map `b ↦ if b then 1 else -1`), so the supremum below is an honest maximum attained on a
finite, nonempty set — never a vacuous or unbounded `sSup`. -/
noncomputable def integerCutValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ x : Fin n → Bool,
    ∑ i, ∑ j, A i j * (if x i then (1 : ℝ) else -1) * (if x j then (1 : ℝ) else -1)

end HighDimProb.RandomVectors


