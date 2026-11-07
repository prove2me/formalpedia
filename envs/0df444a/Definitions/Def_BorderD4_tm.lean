-- Prove2me | Definitions.Def_BorderD4_tm
-- name    : BorderD4_tm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:18.188767+00:00
-- url     : https://prove2.me/theorems/17a893bb-206f-4cd6-8a42-c5d9001b0dbd
-- title:
--   The trailing monomial $\mathrm{tm}(G)$
-- statement:
--   For a fixed monomial order and $G\ne 0$, $\mathrm{tm}(G)$ is the smallest monomial occurring in $G$, with its coefficient omitted. It is multiplicative, $\mathrm{tm}(fg)=\mathrm{tm}(f)\mathrm{tm}(g)$.
--
--   **Formalization Note** The value is the exponent. It is the minimum under the order, the opposite of Mathlib's `MonomialOrder.degree`.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2.1 "Monomial Orders", p.28

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The exponent of the trailing monomial `tm(G)`: the smallest monomial occurring in `G` under the monomial
order `ω`, with its coefficient omitted.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2.1 "Monomial Orders", p.28.

**Formalization Note** Mathlib's `MonomialOrder.degree` is the largest exponent, not this one. At `G = 0`, which
the page excludes, the value is `0`. -/
noncomputable def tm {L τ : Type*} [Field L] (ω : MonomialOrder τ) (G : MvPolynomial τ L) : τ →₀ ℕ :=
  open Classical in
  if h : (G.support.image ω.toSyn).Nonempty then
    ω.toSyn.symm ((G.support.image ω.toSyn).min' h)
  else 0

end BorderD4


