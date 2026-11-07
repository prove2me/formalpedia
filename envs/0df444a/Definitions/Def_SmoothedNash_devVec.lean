-- Prove2me | Definitions.Def_SmoothedNash_devVec
-- name    : SmoothedNash_devVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:21.890784+00:00
-- url     : https://prove2.me/theorems/d06aa5b6-48f1-45fc-9c4c-9f9ae4e2b9ef
-- title:
--   Deviation payoff vector $U(x) \in \mathbb R^{mn}$
-- statement:
--   For a game $u$ and a mixed profile $x$, the **single-action deviation payoff vector** is
--   $$
--   U(x) := \bigl(U_{i,a}(x)\bigr)_{i \in [m],\, a \in [n]} \in \mathbb R^{mn}.
--   $$
--   Assumption 1.18 is a condition on the law of this vector when the game is random, and line 10 of Algorithm 2 computes it at each tested center.
--
--   **Formalization Note** $\mathbb R^{mn}$ is the space of functions on `Fin m × Fin n`, which carries Lebesgue measure.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Assumption 1.18, p.7

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_devPayoff

namespace SmoothedNash

/-- The **single-action deviation payoff vector** `U(x) := (U_{i,a}(x))_{i ∈ [m], a ∈ [n]}`
(Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Assumption 1.18, p.7), a point of `ℝ^{mn}`.

**Formalization Note** `ℝ^{mn}` is the function type `Fin m × Fin n → ℝ`, which carries Lebesgue
measure `volume`. -/
noncomputable def devVec {m n : ℕ} (u : Game m n) (x : Fin m → Fin n → ℝ) :
    Fin m × Fin n → ℝ :=
  fun p => devPayoff u x p.1 p.2

end SmoothedNash


