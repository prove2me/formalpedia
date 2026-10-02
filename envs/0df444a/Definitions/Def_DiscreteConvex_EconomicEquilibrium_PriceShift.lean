-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_PriceShift
-- name    : DiscreteConvex_EconomicEquilibrium_PriceShift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:49:23.522109+00:00
-- url     : https://prove2.me/theorems/63f591fc-bf48-4e41-8faa-e8b3a57f9564
-- title:
--   Price-shifted utility $U[-p]$
-- statement:
--   The price-shifted utility $U[-p](x) = U(x) - \langle p,x\rangle$ (Eq. (11.8)) for a utility-type function $U : \mathbb Z^K \to \mathbb R \cup \{-\infty\}$ and a price vector $p \in \mathbb R^K$. This is the book's own notation, used throughout section 11.3 (e.g. p.330) and in the demand set (Eq. (11.8)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325, Eq. (11.8) (the notation `U[−p]` used
throughout section 11.3, e.g. p.330): the price-shifted utility, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The price-shifted utility `U[−p](x) = U(x) − ⟨p,x⟩` for a utility-type function
`U : Zᴷ → R ∪ {−∞}` and a price vector `p ∈ Rᴷ`. -/
def PriceShift {K : Type*} [Fintype K] (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) (x : K → ℤ) :
    WithBot ℝ :=
  U x + ((-(∑ k, p k * (x k : ℝ)) : ℝ) : WithBot ℝ)

end DiscreteConvex.EconomicEquilibrium


