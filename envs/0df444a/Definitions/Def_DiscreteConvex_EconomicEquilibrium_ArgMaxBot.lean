-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_ArgMaxBot
-- name    : DiscreteConvex_EconomicEquilibrium_ArgMaxBot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:49:32.382441+00:00
-- url     : https://prove2.me/theorems/64a22510-870e-4e25-8cad-0a699a50848b
-- title:
--   Maximizer set of a WithBot-valued function
-- statement:
--   The maximizer set $\arg\max g = \{x \in \mathbb Z^K : g(x) \ge g(y)\ \forall y \in \mathbb Z^K\}$ of $g : \mathbb Z^K \to \mathbb R \cup \{-\infty\}$. Used to form the demand set $D_h(p) = \arg\max_x (U_h(x) - \langle p,x\rangle)$ (Eq. (11.8)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325, Eq. (11.8) (the demand set `Dh(p) = arg
max_x (Uh(x) − ⟨p,x⟩)`): the maximizer set of a `WithBot ℝ`-valued function, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The maximizer set `arg max g = {x ∈ Zᴷ : g(x) ≥ g(y) ∀y ∈ Zᴷ}` of `g : Zᴷ → R ∪ {−∞}`. -/
def ArgMaxBot {K : Type*} (g : (K → ℤ) → WithBot ℝ) : Set (K → ℤ) :=
  {x | ∀ y, g y ≤ g x}

end DiscreteConvex.EconomicEquilibrium


