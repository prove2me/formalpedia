-- Prove2me | Definitions.Def_ResultantVNP_CoeffVar
-- name    : ResultantVNP_CoeffVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:15.99682+00:00
-- url     : https://prove2.me/theorems/a43a9291-0e41-493b-9198-07de54ba25d5
-- title:
--   Coefficient variables $u_{i,e}$ of a system of homogeneous forms
-- statement:
--   Let $d_1,\dots,d_n$ be natural numbers. The **universal coefficient variables** of a system of $n$ homogeneous forms of degrees $d_1,\dots,d_n$ in $n$ variables $x=(x_1,\dots,x_n)$ are the symbols $u_{i,e}$, one for each pair $(i,e)$ with $i\in[n]$ and $e\in\mathbb Z_{\ge0}^n$ an exponent vector of total degree $|e|=e_1+\dots+e_n=d_i$.
--
--   The multivariate resultant $\mathrm{Res}_{d_1,\dots,d_n}$ is a polynomial in these variables.
--
--   **Formalization Note** Indices are $0$-based (`Fin n`); an exponent vector is a finitely supported function `Fin n →₀ ℕ` with coordinate sum $d_i$. The type is finite (a `Fintype` instance for each block is provided).
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Definition 2.1, p.11

import Mathlib

namespace ResultantVNP

/-- **Universal coefficient variables** `u_{i,e}` of a system of `n` homogeneous forms of degrees
`d₁, …, dₙ` in `n` variables: one variable for each pair `(i, e)` with `i ∈ [n]` and `e` an
exponent vector of total degree `|e| = d_i`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Definition 2.1, p.11: "Introduce the universal coefficient variables 𝒖 = (u_{i,𝒆}), one for
each possible pair (i, 𝒆)."

**Formalization Note** Indices are 0-based (`Fin n` for the paper's `[n]`); an exponent vector is a
finitely supported `e : Fin n →₀ ℕ` with `∑ j, e j = d i`. The type is finite; the instances below
make sums over it available. -/
abbrev CoeffVar {n : ℕ} (d : Fin n → ℕ) : Type :=
  Σ i : Fin n, {e : Fin n →₀ ℕ // ∑ j, e j = d i}

instance instFintypeCoeffBlock {n : ℕ} (k : ℕ) :
    Fintype {e : Fin n →₀ ℕ // ∑ j, e j = k} :=
  Fintype.subtype (Finset.finsuppAntidiag Finset.univ k) (fun e => by simp)

end ResultantVNP


