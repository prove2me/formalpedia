-- Prove2me | Definitions.Def_ApproxVI_Ttilde
-- name    : ApproxVI_Ttilde
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:00.451423+00:00
-- url     : https://prove2.me/theorems/91f60256-48d9-41e0-b2fe-f0768b90dbf7
-- title:
--   The perturbed Bellman operator $\tilde T x = Tx + B^\epsilon$
-- statement:
--   Given a map $T:\mathbb R^d\to\mathbb R^d$, weights $\nu$ and $\epsilon$, the **perturbed Bellman operator** is the set-valued map
--
--   $$
--   \tilde T x = Tx + B^\epsilon=\{y\in\mathbb R^d:\ \|y-Tx\|_\nu\le\epsilon\}.
--   $$
--
--   Approximate value iteration with errors bounded by $\epsilon$ is a stochastic approximation of the differential inclusion $\dot J\in\tilde TJ-J$; its equilibria are the fixed points $J\in\tilde TJ$.
--
--   **Formalization Note** The Minkowski sum $Tx+B^\epsilon$ is written as $\{y : y-Tx\in B^\epsilon\}$, the same set. $T$ is an arbitrary map here; the statements using $\tilde T$ add the contraction property (AV1) when they need it.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Lemma 2, p.14

import Mathlib
import Definitions.Def_ApproxVI_ballNu

namespace ApproxVI

/-- The perturbed Bellman operator of Ramaswamy & Bhatnagar, *Analyzing Approximate Value
Iteration Algorithms*, arXiv:1709.04673v5, Lemma 2, p.14: the set-valued map
`T̃x = Tx + B^ε`, with `B^ε = {y | ‖y‖_ν ≤ ε}` (Lemma 1, p.14).

**Formalization Note** The Minkowski sum `Tx + B^ε` is written as `{y | y − Tx ∈ B^ε}`, the
same set. `T` is any map `ℝ^d → ℝ^d`; the statements that use `T̃` add the hypotheses on `T`
they need. -/
def Ttilde {d : ℕ} (ν : Fin d → ℝ) (T : (Fin d → ℝ) → (Fin d → ℝ)) (ε : ℝ)
    (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {y | y - T x ∈ ballNu ν ε}

end ApproxVI


