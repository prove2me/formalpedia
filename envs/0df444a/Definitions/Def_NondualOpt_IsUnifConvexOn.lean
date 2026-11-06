-- Prove2me | Definitions.Def_NondualOpt_IsUnifConvexOn
-- name    : NondualOpt_IsUnifConvexOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:44.292207+00:00
-- url     : https://prove2.me/theorems/01a794d3-2fbb-4079-837e-f9e93cf1863a
-- title:
--   $(c,\kappa)$-uniform convexity on a set
-- statement:
--   Let $(E,\|\cdot\|)$ be a normed space, $K\subseteq E$ convex, $c>0$ and $\kappa\ge2$. A function $\Phi$ is **$(c,\kappa)$-uniformly convex on $K$** if
--   $$
--   \frac{\Phi(u)+\Phi(v)}2\ge\Phi\Big(\frac{u+v}2\Big)+c\|u-v\|^\kappa,\qquad u,v\in K .
--   $$
--   Lemma 26 bounds sequential fat-shattering through such potentials.
--
--   **Formalization Note** $\Phi$ is a function on $E$; only its values on $K$ enter. The conditions $c>0$, $\kappa\ge2$ and convexity of $K$ are hypotheses where the notion is used.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Definition 25, p.37

import Mathlib

namespace NondualOpt

/-- `Φ` is `(c, κ)`-uniformly convex on `K` with respect to `‖·‖`:
`(Φ(u) + Φ(v))/2 ≥ Φ((u + v)/2) + c‖u − v‖^κ` for all `u, v ∈ K`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Definition 25, p.37.

**Formalization Note.** `Φ` is a function on `E`; only its values on `K` enter. The conditions
`c > 0`, `κ ≥ 2` and convexity of `K` are hypotheses where the notion is used. -/
def IsUnifConvexOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E)
    (Φ : E → ℝ) (c κ : ℝ) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, Φ ((1 / 2 : ℝ) • (u + v)) + c * ‖u - v‖ ^ κ ≤ (Φ u + Φ v) / 2

end NondualOpt


