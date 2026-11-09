-- Prove2me | Definitions.Def_ResultantVNP_ResultantSystem
-- name    : ResultantVNP_ResultantSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:33:45.381424+00:00
-- url     : https://prove2.me/theorems/296e8f32-f272-48ac-8a0e-43d293ed1cd4
-- title:
--   Resultant system: a choice of $\mathrm{Res}_{d_1,\dots,d_n}$ for every degree vector
-- statement:
--   A **resultant system** assigns to every $n$ and every degree vector $d=(d_1,\dots,d_n)$ an integral polynomial $\mathrm{res}_d\in\mathbb Z[u]$ such that, whenever $n\ge1$ and all $d_i\ge1$, $\mathrm{res}_d$ has the three properties of Definition 2.1. By the uniqueness asserted in Definition 2.1, $\mathrm{res}_d$ is then the multivariate resultant $\mathrm{Res}_{d_1,\dots,d_n}$.
--
--   Every statement of this mission is made for an arbitrary resultant system, so it is a statement about the multivariate resultant itself.
--
--   **Formalization Note** The paper cites the existence and uniqueness of the resultant [GKZ94, Chapter 13] rather than proving it. Instead of choosing a polynomial by `Classical.choose`, the statements quantify over all resultant systems. Values for $n=0$ or a zero degree are unconstrained and never used: for $n=0$ no polynomial has the three properties (property 2 forces $R=1$, which is not irreducible).
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Definition 2.1, p.11

import Mathlib
import Definitions.Def_ResultantVNP_IsMultivariateResultant

namespace ResultantVNP

/-- A **resultant system**: for every number of variables `n` and degree vector `d`, an integral
polynomial `res d ∈ ℤ[u]`, which satisfies the three properties of Definition 2.1 whenever `n ≥ 1`
and all degrees are positive. By the uniqueness in Definition 2.1, `res d` is then the multivariate
resultant `Res_{d₁,…,dₙ}`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Definition 2.1, p.11 ("The multivariate resultant Res ∈ ℤ[𝒖] is the unique integral polynomial
that satisfies the following properties"; existence and uniqueness are cited from [GKZ94, Chapter 13]).

**Formalization Note** The paper does not prove that the resultant exists; it cites it. Rather than
choosing a polynomial with `Classical.choose`, every statement of this mission quantifies over all
resultant systems; by uniqueness each one agrees with the resultant on every admissible degree vector,
so the statements say exactly the paper's. The value of `res d` for `n = 0` or a zero degree is
unconstrained: the paper's resultant needs positive degrees, and for `n = 0` no polynomial satisfies
the three properties (property 2 forces `R = 1`, which is not irreducible). -/
structure ResultantSystem where
  /-- The candidate resultant `Res_{d₁,…,dₙ}`. -/
  res : ∀ {n : ℕ} (d : Fin n → ℕ), MvPolynomial (CoeffVar d) ℤ
  /-- It satisfies Definition 2.1 for `n ≥ 1` and positive degrees. -/
  spec : ∀ {n : ℕ} (d : Fin n → ℕ), 1 ≤ n → (∀ i, 0 < d i) → IsMultivariateResultant d (res d)

end ResultantVNP


