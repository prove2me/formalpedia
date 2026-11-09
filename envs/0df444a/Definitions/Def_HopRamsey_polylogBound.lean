-- Prove2me | Definitions.Def_HopRamsey_polylogBound
-- name    : HopRamsey_polylogBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:50.023554+00:00
-- url     : https://prove2.me/theorems/434dade4-cf72-42cb-b5eb-10a48622cde3
-- title:
--   The polylogarithmic bound $\Lambda_K(n)=\log_2(n+1)\,(1+\log_2(1+\log_2(n+1)))^K$
-- statement:
--   For integers $K,n\ge 0$ let
--
--   $$
--   \Lambda_K(n)=\log_2(n+1)\cdot\bigl(1+\log_2(1+\log_2(n+1))\bigr)^K .
--   $$
--
--   A quantity is $\tilde O(\log n)$ when it is at most $C\cdot\Lambda_K(n)$ for constants $C>0$ and $K$ that do not depend on $n$ or on any other parameter of the instance; this is the paper's convention $\tilde O(g)=O(g)\cdot\mathrm{polylog}(g)$ for $g=\log n$.
--
--   **Formalization Note** For $n\ge 4$, $\Lambda_K(n)$ is within constant factors of $\log n\cdot(\log\log n)^K$; the shifts by $1$ only keep $\Lambda_K(n)\ge 1$ at $n=1,2$, where $\log\log n\le 0$.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §3, p.12 (PDF p.14), definition of Õ

import Mathlib

namespace HopRamsey

/-- The polylogarithmic bound `Λ_K(n) = log₂(n+1) · (1 + log₂(1 + log₂(n+1)))^K`, the reading of
`Õ(log n)` used in Theorem 1.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), §3, p.12
(PDF p.14): "Õ notation hides polylogarithmic factors, that is Õ(g) = O(g) · polylog(g)."

**Formalization Note.** A bound is `Õ(log n)` when it is at most `C · Λ_K(n)` for constants
`C > 0` and `K ∈ ℕ` independent of every other quantity. For `n ≥ 4`, `Λ_K(n)` is within constant
factors of `log n · (log log n)^K`; the shifts by `1` only keep `Λ_K(n) ≥ 1` for `n = 1, 2`, where
`log log n ≤ 0`. -/
noncomputable def polylogBound (K n : ℕ) : ℝ :=
  Real.logb 2 ((n : ℝ) + 1) * (1 + Real.logb 2 (1 + Real.logb 2 ((n : ℝ) + 1))) ^ K

end HopRamsey


