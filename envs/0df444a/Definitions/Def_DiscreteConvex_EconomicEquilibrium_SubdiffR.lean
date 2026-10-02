-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_SubdiffR
-- name    : DiscreteConvex_EconomicEquilibrium_SubdiffR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:49:49.768984+00:00
-- url     : https://prove2.me/theorems/2a6abda6-db00-46d4-90a9-619749eb7e24
-- title:
--   Subdifferential of a cost-type function (Eq. 6.86)
-- statement:
--   The subdifferential (Eq. (6.86), cf. Eq. (3.23)) $\partial_{\mathbb R} f(x) = \{p \in \mathbb R^K \mid f(y) - f(x) \ge \langle p, y-x\rangle\ \forall y \in \mathbb Z^K\}$ of a cost-type function $f : \mathbb Z^K \to \mathbb R \cup \{+\infty\}$ at $x$, restated without subtraction as $f(y) \ge f(x) + \langle p,y-x\rangle$. Applied in chapter 11 to the aggregate cost function $\Psi$ (Proposition 11.10, p.335, and Proposition 11.12, p.337).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.176, Eq. (6.86).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.176, Eq. (6.86)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.176, Eq. (6.86) (cf. Eq. (3.23)), applied in
chapter 11 to the aggregate cost function `Ψ` (e.g. Proposition 11.10, p.335): the subdifferential
of a cost-type function, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The subdifferential (Eq. (6.86)) `∂R f(x) = {p ∈ Rᴷ | f(y) − f(x) ≥ ⟨p, y-x⟩ ∀y ∈ Zᴷ}` of a
cost-type function `f : Zᴷ → R ∪ {+∞}` at `x`, restated without subtraction as
`f(y) ≥ f(x) + ⟨p, y-x⟩`. -/
def SubdiffR {K : Type*} [Fintype K] (f : (K → ℤ) → WithTop ℝ) (x : K → ℤ) : Set (K → ℝ) :=
  {p | ∀ y : K → ℤ, f y ≥ f x + ((∑ k, p k * ((y k - x k : ℤ) : ℝ) : ℝ) : WithTop ℝ)}

end DiscreteConvex.EconomicEquilibrium


