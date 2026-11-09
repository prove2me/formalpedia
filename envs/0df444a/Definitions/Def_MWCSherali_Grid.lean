-- Prove2me | Definitions.Def_MWCSherali_Grid
-- name    : MWCSherali_Grid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:06.729079+00:00
-- url     : https://prove2.me/theorems/d8e49baa-7d2f-4c3a-bb0b-7a3349ffcc7c
-- title:
--   The discrete simplex $\Delta_{k,n}$
-- statement:
--   For positive integers $k,n$, the **discrete simplex** is
--
--   $$\Delta_{k,n}=\Big\{x\in\big(\tfrac1n\mathbb Z_{\ge0}\big)^k \;\Big|\; \sum_{i=1}^k x_i=1\Big\},$$
--
--   the points of the unit simplex $\Delta_k$ whose coordinates are multiples of $1/n$. It is the vertex set of the non-opposite cut instances of the paper.
--
--   **Formalization Note** A point $x$ is stored through its integer coordinates $y=nx\in\mathbb Z_{\ge0}^k$ with $\sum_i y_i=n$. Coordinates are 0-based: the paper's coordinate $i\in[k]$ is index $i-1$. The type is finite.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §1.1, p.4; §2.1, p.14

import Mathlib

namespace MWCSherali

/-- **The discrete simplex `Δ_{k,n}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511
(version of Nov. 3, 2026), §1.1, p.4, and §2.1, p.14:
`Δ_{k,n} = {x ∈ ((1/n)ℤ_{≥0})^k | ∑_{i=1}^k x_i = 1}`.

**Formalization Note.** A point `x ∈ Δ_{k,n}` is stored through its integer coordinates
`y = n·x : Fin k → ℕ`, with `∑ᵢ yᵢ = n`; so `Grid k n` is `Δ_{k,n}` for `n ≥ 1` (the paper takes
`n` a positive integer). Coordinates are 0-based: the paper's coordinate `i ∈ [k]` is index
`i - 1`. The `Fintype` instance enumerates `Finset.Nat.antidiagonalTuple k n`. -/
def Grid (k n : ℕ) : Type := {y : Fin k → ℕ // ∑ i, y i = n}

instance (k n : ℕ) : Fintype (Grid k n) :=
  Fintype.subtype (Finset.Nat.antidiagonalTuple k n) (by simp [Finset.Nat.mem_antidiagonalTuple])

instance (k n : ℕ) : DecidableEq (Grid k n) :=
  inferInstanceAs (DecidableEq {y : Fin k → ℕ // ∑ i, y i = n})

end MWCSherali


