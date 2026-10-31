-- Prove2me | Definitions.Def_NashStackelberg_IsPNE
-- name    : NashStackelberg_IsPNE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:12.466152+00:00
-- url     : https://prove2.me/theorems/fbaf93e8-2482-45d8-ab40-4d69365283ca
-- title:
--   Pure Nash equilibrium of a simultaneous game
-- statement:
--   A **simultaneous game** among $n$ players is a tuple of optimization problems: player $i$ chooses a vector $x^i$ from its feasible set $\mathcal F^i$ and **minimizes** an objective $f^i(x^i,x^{-i})$ that depends on its own choice and on the choices $x^{-i}$ of the other players.
--
--   A profile $x=(x^1,\dots,x^n)$ is a **pure Nash equilibrium (PNE)** if every $x^i$ is feasible and no player can lower its objective by a unilateral feasible deviation:
--   $$
--   x^i\in\mathcal F^i\quad\text{and}\quad f^i(x^i,x^{-i})\le f^i(\tilde x^i,x^{-i})\qquad\text{for every player } i \text{ and every } \tilde x^i\in\mathcal F^i .
--   $$
--
--   This is the equilibrium notion of the followers' games, of the convexified game $\widetilde N$ and of the facile games whose equilibria are computed by an LCP.
--
--   **Formalization Note** Players are indexed by `Fin n`; player $i$'s vector is a function $V_i\to\mathbb R$ for an arbitrary index type $V_i$. Definition 2 calls an MNE with singleton supports a PNE; for Dirac strategies both sides of its inequality are pure costs, so the PNE is stated directly in pure form (the two forms are shown to agree in a proved sanity check).
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Definition 1 and Definition 2, pp.6–7

import Mathlib

namespace NashStackelberg

/-- **Pure Nash equilibrium of a simultaneous game** (Carvalho, Dragotto, Feijoo, Lodi &
Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, Definition 1 and
Definition 2, pp.6–7).

A simultaneous game among `n` players is given by the feasible set `F i` of each player `i`
(a set of vectors `x i : V i → ℝ`) and its objective `f i`, which depends on the whole profile
`x = (x¹, …, xⁿ)` and is **minimized**. A profile `x` is a PNE if every `x i` is feasible and no
player can lower its objective by a unilateral feasible deviation:
`f i x ≤ f i (x with xⁱ replaced by x')` for every `x' ∈ F i`.

**Formalization Note.** Players are `Fin n`; player `i`'s variables are indexed by an arbitrary
type `V i` (so `ℝ^{nᵢ}` is `V i → ℝ`). Definition 2 calls an MNE whose mixed strategies have
singleton support a PNE; for a Dirac profile both sides of Definition 2's inequality are the pure
costs, so the PNE is stated here directly in its pure form (the Dirac form is related to it in the
verification file). -/
def IsPNE {n : ℕ} {V : Fin n → Type*} (F : (i : Fin n) → Set (V i → ℝ))
    (f : Fin n → ((j : Fin n) → V j → ℝ) → ℝ) (x : (j : Fin n) → V j → ℝ) : Prop :=
  ∀ i, x i ∈ F i ∧ ∀ x' ∈ F i, f i x ≤ f i (Function.update x i x')

end NashStackelberg


