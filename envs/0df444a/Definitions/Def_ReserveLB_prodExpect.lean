-- Prove2me | Definitions.Def_ReserveLB_prodExpect
-- name    : ReserveLB_prodExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:51.436605+00:00
-- url     : https://prove2.me/theorems/694f76d9-7c96-4fdc-a1aa-321102815e95
-- title:
--   Expectation over independent jobs with listed laws
-- statement:
--   Let $X_1, \dots, X_n$ be independent random sizes, $X_j$ with the listed law $((a_{j\ell}, p_{j\ell}))_\ell$. For a function $F$ of the size vector,
--   $$
--   \mathbb E\,F(X) = \sum_{c} \Bigl(\prod_{j=1}^{n} p_{j c_j}\Bigr)\, F\bigl(a_{1 c_1}, \dots, a_{n c_n}\bigr),
--   $$
--   the sum over all choices $c = (c_1, \dots, c_n)$ of one listed atom per job.
--
--   This is the expectation in $\mathrm{OPT}_k = \min_\sigma \mathbb E\,T_\sigma(X)$ and in Lemma 3.1: an exact finite sum over the product law, with no measure theory.
--
--   **Formalization Note** Jobs are indexed by `Fin n`; values and probabilities are cast from $\mathbb Q$ to $\mathbb R$.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2 (independent sizes, $\mathbb E\,T_\sigma(X)$)

import Mathlib

namespace ReserveLB

/-- **Expectation over independent jobs with listed finite laws.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "n independent mandatory original sizes Xj ≥ 0 … Finite marginal laws
are explicitly listed"; the expectation `E T_σ(X)` in the definition of `OPT_k`.

`prodExpect law F = Σ_c (Π_j p_(j, c_j)) · F(a_(1, c_1), …, a_(n, c_n))`, the sum over all choices
`c` of one listed atom per job: the expectation of `F(X)` when `X_1, …, X_n` are independent and
`X_j` has the listed law `law j`.

**Formalization Note.** This is the exact expectation over the product law, written as a finite
sum (no measure theory). Jobs are `Fin n`. -/
noncomputable def prodExpect {n : ℕ} (law : Fin n → List (ℚ × ℚ)) (F : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ c : (j : Fin n) → Fin (law j).length,
    (∏ j, ((((law j).get (c j)).2 : ℚ) : ℝ)) * F (fun j => ((((law j).get (c j)).1 : ℚ) : ℝ))

end ReserveLB


