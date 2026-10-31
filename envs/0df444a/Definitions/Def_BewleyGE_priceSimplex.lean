-- Prove2me | Definitions.Def_BewleyGE_priceSimplex
-- name    : BewleyGE_priceSimplex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:32.695668+00:00
-- url     : https://prove2.me/theorems/ca9de2d9-a0eb-44ca-87c2-0c8e0bdfd603
-- title:
--   Normalized prices $\Lambda$
-- statement:
--   The set of **normalized price–interest vectors** is
--   $$
--   \Lambda=\Big\{(p,r)\in\mathbb R^n_+\times\mathbb R_+ : \sum_{i=1}^np_i+r=1\Big\}.
--   $$
--
--   **Formalization Note** $(p,r)$ is a vector $\pi\in\mathbb R^{n+1}$ with $p_i=\pi_i$ for $i\le n$ and $r=\pi_{n+1}$, the paper's convention $p_{n+1}:=r$.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §3.1, p.11 (restated p.20)

import Mathlib

namespace BewleyGE

/-- **Normalized prices** `Λ = {(p, r) ∈ ℝⁿ₊ × ℝ₊ : ∑ᵢ pᵢ + r = 1}`.
Light, arXiv:1906.06810v2, §3.1, p.11 (restated p.20).

**Formalization Note.** A price-interest vector `(p, r)` is `π : Fin (n + 1) → ℝ` with
`pᵢ = π i.castSucc` and `r = π (Fin.last n)`, the paper's own convention `p_{n+1} := r` (p.29). -/
def priceSimplex (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {π | (∀ k, 0 ≤ π k) ∧ ∑ k, π k = 1}

end BewleyGE


