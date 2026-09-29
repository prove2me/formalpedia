-- Prove2me | Definitions.Def_NonmonotoneSubmod_Nonadaptive_omega
-- name    : NonmonotoneSubmod_Nonadaptive_omega
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T06:14:13.992816+00:00
-- url     : https://prove2.me/theorems/2f542ebe-c679-4b91-85fe-afdf0da10cbf
-- title:
--   Definition 2.4 — the averaged marginal value $\omega(x)$
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ on a finite ground set $X$, and let $R = X(1/2)$ be a uniformly random subset of $X$. For each element $x \in X$ define
--
--   $$
--   \omega(x) = \mathbf{E}\big[f(R \cup \{x\}) - f(R \setminus \{x\})\big].
--   $$
--
--   Thus $\omega(x)$ is the average, over all subsets of the rest of the ground set, of the change in $f$ caused by adding $x$. A positive value indicates that including $x$ helps on average. Algorithm NA of the paper keeps exactly those elements whose (estimated) $\omega$ is positive.
--
--   **Formalization Note** $\omega(x)$ is the uniform average $2^{-|X|}\sum_{S \subseteq X}\big(f(S \cup \{x\}) - f(S \setminus \{x\})\big)$, written with the random-set expectation $F$ of this mission at $x_i = 1/2$ for all $i$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1138, Definition 2.4

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace NonmonotoneSubmod.Nonadaptive

/-- Definition 2.4 (Feige–Mirrokni–Vondrák 2011, p. 1138): with `R = X(1/2)` a uniformly random
subset of `X`, `ω(x) = E[f(R ∪ {x}) − f(R \ {x})]`. The expectation is the uniform average
`F (fun S => f (S ∪ {x}) - f (S \ {x})) (fun _ => 1/2)` over all subsets `S ⊆ X`. -/
noncomputable def omega {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (x : X) : ℝ :=
  NonmonotoneSubmod.Shared.F (fun S => f (insert x S) - f (S.erase x)) (fun _ => 1 / 2)

end NonmonotoneSubmod.Nonadaptive


