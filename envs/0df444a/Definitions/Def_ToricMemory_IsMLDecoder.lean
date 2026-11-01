-- Prove2me | Definitions.Def_ToricMemory_IsMLDecoder
-- name    : ToricMemory_IsMLDecoder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:33.762533+00:00
-- url     : https://prove2.me/theorems/8ca89c8b-99e5-4c29-b2bd-255da23fd2fb
-- title:
--   Maximum-likelihood (minimal-weight) decoder
-- statement:
--   Given the observed boundary $\partial S=\partial E$ of the unknown error history $E$, the recovery procedure of Sec. V A selects, among all chains with that boundary, a chain $E_{\min}$ of highest probability (equivalently, of minimal weight (46) when $0<p,q<1$). If several chains attain the maximum, one of them is chosen.
--
--   A map $D$ from sets of sites to chains is a **maximum-likelihood decoder** for $(p,q)$ if, for every chain $X$,
--
--   1. $\partial D(\partial X)=\partial X$, and
--   2. $\mu_{p,q}(Y)\le\mu_{p,q}(D(\partial X))$ for every chain $Y$ with $\partial Y=\partial X$.
--
--   Every deterministic tie-breaking rule gives such a map, and a random tie-break that does not look at $E$ is a mixture of them; the theorems of the mission hold for every such $D$.
--
--   **Formalization Note** The decoder maximizes $\mu_{p,q}$ directly rather than minimizing the logarithmic weights (46), which are undefined at $p,q\in\{0,1\}$.
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V A, eqs. (44)–(46), p. 18

import Mathlib
import Definitions.Def_ToricMemory_Lattice

namespace ToricMemory

/-- A **maximum-likelihood (minimal-weight) decoder**, arXiv:quant-ph/0110143v1, Sec. V A,
eqs. (44)–(46), p. 18: given the observed boundary `∂S = ∂E` of the error history, `D` returns a
chain `E_min = D(∂E)` with the same boundary and the highest probability among all chains with
that boundary. Ties may be broken in any way ("one of the minimal chains is selected
randomly"); a random tie-break independent of `E` is a mixture of such maps.

**Formalization Note** The decoder maximizes the probability `chainProb p q` rather than
minimizing the weight (46); for `0 < p, q < 1` the two coincide, and the product form is
defined at `p, q ∈ {0, 1}` as well. Only achievable boundaries `∂X` constrain `D`. -/
def IsMLDecoder {L T : ℕ} [NeZero L] [NeZero T] (p q : ℝ)
    (D : Finset (Site L T) → Finset (Link L T)) : Prop :=
  ∀ X : Finset (Link L T), boundary (D (boundary X)) = boundary X ∧
    ∀ Y : Finset (Link L T), boundary Y = boundary X →
      chainProb p q Y ≤ chainProb p q (D (boundary X))

end ToricMemory


