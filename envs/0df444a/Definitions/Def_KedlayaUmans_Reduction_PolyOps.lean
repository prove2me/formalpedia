-- Prove2me | Definitions.Def_KedlayaUmans_Reduction_PolyOps
-- name    : KedlayaUmans_Reduction_PolyOps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:23.760503+00:00
-- url     : https://prove2.me/theorems/c56520a2-8abd-4916-9f55-7015dd15102d
-- title:
--   Remainder modulo a polynomial with unit leading coefficient, and interpolation over a commutative ring (Problem 2.2, Figure 1)
-- statement:
--   Let $R$ be a commutative ring.
--
--   1. **Remainder.** For $p, h \in R[X]$ with the leading coefficient $\mathrm{lc}(h)$ a unit of $R$, the polynomial $p \bmod h$ is the remainder of $p$ on division by the monic associate $h \cdot \mathrm{lc}(h)^{-1}$:
--   $$
--   p \bmod h \;=\; p \bmod_{\mathrm{monic}} \bigl(h\,\mathrm{lc}(h)^{-1}\bigr).
--   $$
--   Since $h$ and its monic associate generate the same ideal and have the same degree, this is the unique polynomial $r$ with $\deg r < \deg h$ and $h \mid p - r$, which is the operation "mod $h(X)$" of Problem 2.2.
--
--   2. **Interpolation.** For nodes $\beta_0, \dots, \beta_{n-1} \in R$ and values $v_0, \dots, v_{n-1} \in R$, the interpolating polynomial is given by the Lagrange formula
--   $$
--   \mathrm{interp}(\beta, v) \;=\; \sum_{k=0}^{n-1} v_k \prod_{j \ne k} (X - \beta_j)\,(\beta_k - \beta_j)^{-1}.
--   $$
--   Figure 1 of the paper requires the differences $\beta_k - \beta_j$ ($j \ne k$) to be units, so that the inverses exist.
--
--   These are the two univariate operations the reduction of Theorem 3.1 uses in Steps 2, 5 and 6.
--
--   **Formalization Note** Both inverses are `Ring.inverse`, which returns $0$ on a non-unit; so the definitions carry no hypotheses, and every statement that uses them assumes that $\mathrm{lc}(h)$ and the node differences are units. Mathlib's `Lagrange` interpolation is stated over fields only, which is why the formula is written out over a commutative ring.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 7, Problem 2.2 ("mod h(X)"), and p. 8, Figure 1 (remainder and interpolation rows, with the caption's unit hypothesis)

import Mathlib

namespace KedlayaUmans.Reduction

open Polynomial

/-- Remainder of `p` modulo a univariate polynomial `h` whose leading coefficient is a unit
(the operation "`p mod h`" of Problem 2.2 and Figure 1). It is the remainder of `p` on division
by the monic associate `h · lc(h)⁻¹`, which generates the same ideal as `h`; so it is the unique
polynomial `r` with `deg r < deg h` and `h ∣ p - r`. (If the leading coefficient of `h` is not a
unit the value is meaningless; every statement assumes it is.) -/
noncomputable def modLc {R : Type*} [CommRing R] (p h : R[X]) : R[X] :=
  p %ₘ (h * C (Ring.inverse h.leadingCoeff))

/-- Lagrange interpolation over a commutative ring (Figure 1, last row): from nodes
`β_0, …, β_{n-1}` and values `v_0, …, v_{n-1}`,
`∑_k v_k ∏_{j ≠ k} (X - β_j) (β_k - β_j)⁻¹`. The inverses exist when the differences
`β_k - β_j`, `j ≠ k`, are units, which is the hypothesis of Figure 1; otherwise `Ring.inverse`
returns `0`. -/
noncomputable def interpolate {R : Type*} [CommRing R] {n : ℕ} (β v : Fin n → R) : R[X] :=
  ∑ k, C (v k) * ∏ j ∈ Finset.univ.erase k, ((X - C (β j)) * C (Ring.inverse (β k - β j)))

end KedlayaUmans.Reduction


