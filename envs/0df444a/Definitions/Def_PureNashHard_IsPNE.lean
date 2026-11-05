-- Prove2me | Definitions.Def_PureNashHard_IsPNE
-- name    : PureNashHard_IsPNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:58.244525+00:00
-- url     : https://prove2.me/theorems/0a4363a0-81a1-4a8d-80df-e6422d4fd90b
-- title:
--   Pure Nash equilibrium (Definition 2.2)
-- statement:
--   Let $G$ be a game. A global strategy $x$ is a **pure Nash equilibrium** of $G$ if for every player $p$ there is no action $a\in\mathrm{Act}(p)$ such that
--   $$
--   u_p(x) < u_p\bigl(x_{-p}[p_a]\bigr),
--   $$
--   where $x_{-p}[p_a]$ is the global strategy in which $p$ plays $a$ and every other player keeps her action in $x$. The set of pure Nash equilibria is $NE(G)$.
--
--   This is the solution concept whose existence problem the mission studies.
--
--   **Formalization Note** $x_{-p}[p_a]$ is `Function.update x p a`; the improvement is strict, as in the paper.
-- source:
--   Gottlob, Greco, Scarcello, Pure Nash Equilibria: Hard and Easy Games, JAIR 24 (2005), doi:10.1613/jair.1683, Definition 2.2, pp.366–367 (PDF pp.10–11)

import Definitions.Def_PureNashHard_Game

set_option autoImplicit false

namespace PureNashHard

/-- **Pure Nash equilibrium** (Gottlob, Greco, Scarcello, JAIR 24 (2005), Definition 2.2,
pp.366–367): "a global strategy x is a pure Nash Equilibrium for G if, for every player
p ∈ P, ∄ p_a ∈ St(p) such that u_p(x) < u_p(x_{−p}[p_a])".

**Formalization Note** `x_{−p}[p_a]` is `Function.update x p a`: player `p`'s action is
replaced by `a` and every other player keeps hers. The improvement is strict (`<`), as on the
page. -/
def IsPNE {R : Type} [LT R] (G : Game R) (x : G.Profile) : Prop :=
  ∀ (p : Fin G.N) (a : Fin (G.act p)), ¬ G.utility p x < G.utility p (Function.update x p a)

end PureNashHard


