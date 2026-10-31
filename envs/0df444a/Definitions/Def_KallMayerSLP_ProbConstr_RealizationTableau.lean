-- Prove2me | Definitions.Def_KallMayerSLP_ProbConstr_RealizationTableau
-- name    : KallMayerSLP_ProbConstr_RealizationTableau
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:24.617716+00:00
-- url     : https://prove2.me/theorems/d23eefb6-2ca8-4f61-8970-0de47c41eb17
-- title:
--   Realization tableau of a finite discrete distribution
-- statement:
--   A finite discrete distribution of $\xi\in\mathbb R^r$ is given by a realization tableau
--   $$
--   \begin{pmatrix} p_1 & \cdots & p_N\\ \hat\xi^1 & \cdots & \hat\xi^N\end{pmatrix}
--   $$
--   with probabilities $p_i>0$ for all $i$ and $\sum_{i=1}^N p_i=1$, and realizations $\hat\xi^i\in\mathbb R^r$: the random vector takes the value $\hat\xi^i$ with probability $p_i$.
--
--   **Formalization Note** Indices are `Fin N` ($0,\dots,N-1$ for the book's $1,\dots,N$). The realizations need not be distinct.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.2, (2.15), p.98 (PDF 108)

import Mathlib

namespace KallMayerSLP.ProbConstr

/-- A finite discrete distribution of `ξ ∈ ℝ^r`, given by the realization tableau (2.15)
`(p_1 … p_N ; ξ̂^1 … ξ̂^N)` with `p_i > 0` for all `i` and `Σ_{i=1}^N p_i = 1`.

Kall & Mayer 2005, Chapter 2, §2.2, (2.15), p.98 (PDF 108).

**Formalization Note.** Indices are `Fin N` (the book's indices `1, …, N` shifted down by one). The atoms
`ξ̂^i` need not be distinct; the induced distribution (`RealizationTableau.measure`) puts mass
`Σ_{i : ξ̂^i = ξ} p_i` on each point `ξ`, which is the law the tableau describes. -/
structure RealizationTableau (N r : ℕ) where
  /-- The probabilities `p_i`. -/
  p : Fin N → ℝ
  /-- The realizations `ξ̂^i ∈ ℝ^r`. -/
  xi : Fin N → Fin r → ℝ
  /-- `p_i > 0` for every `i`. -/
  p_pos : ∀ i, 0 < p i
  /-- `Σ_i p_i = 1`. -/
  p_sum : ∑ i, p i = 1

end KallMayerSLP.ProbConstr


