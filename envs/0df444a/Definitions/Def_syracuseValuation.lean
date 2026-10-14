-- Prove2me | Definitions.Def_syracuseValuation
-- name    : syracuseValuation
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-13T07:59:38.523541+00:00
-- url     : https://prove2.me/theorems/736124a2-f5a7-426b-98d6-c77f15925032
-- title:
--   Syracuse valuation vector and its sum
-- statement:
--   For a natural number $n$, let $\nu_2$ denote the 2-adic valuation. The Syracuse valuation at $n$ is $\nu_2(3n+1)$, the exponent of $2$ removed in one accelerated Collatz step. For $n_0 \ge 0$, the valuation vector of length $n_0$ at $n$ records these valuations along the first $n_0$ Syracuse iterates:
--
--   $$\vec{a}^{(n_0)}(n) = \bigl(\nu_2(3\,\mathrm{Syr}^j(n)+1)\bigr)_{j<n_0},$$
--
--   and the valuation sum is the sum of its coordinates.
--
--   These are the basic random variables in Tao's analysis of Syracuse orbits (the heuristic is that they behave like independent geometric random variables of mean $2$), so they are shared infrastructure for any formalization of Proposition 1.9 and its consequences.
--
--   **Formalization Note** `syrVal` is `Nat.factorization (3 * n + 1) 2`, `valVec` is the vector above as a function on `Fin n_0`, and `valSum` is its coordinate sum. The Syracuse map itself is `syracuseStep`.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 1.2 and equations (1.4), (1.8). Helpers originally by junyihjy in theorem preambles; moved here so statements can import them. https://arxiv.org/html/1909.03562v7

import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_syracuseStep

/-- The 2-adic valuation of `3n+1` (Tao 2022, section 1.2). -/
def syrVal (n : ℕ) : ℕ := Nat.factorization (3 * n + 1) 2

/-- The Syracuse valuation vector of length `n₀` (Tao 2022, (1.8)). -/
def valVec (n₀ : ℕ) (n : ℕ) : Fin n₀ → ℕ := fun j => syrVal (syracuseStep^[j.val] n)

/-- The valuation-vector sum (Tao 2022, (1.4)). -/
def valSum (n₀ n : ℕ) : ℕ := Finset.sum Finset.univ (fun j => valVec n₀ n j)


