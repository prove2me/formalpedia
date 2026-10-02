-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_IsSteepestDescentRunTieBreak
-- name    : DiscreteConvex_Algorithms_IsSteepestDescentRunTieBreak
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:35:36.274018+00:00
-- url     : https://prove2.me/theorems/8ab0ab91-b849-4994-bd7a-9bc6668c7a2b
-- title:
--   A run of the steepest descent algorithm with tie-breaking (Eq. 10.2)
-- statement:
--   A run of the steepest descent algorithm with the tie-breaking rule (10.2) from $x^0$ terminating after exactly $N$ iterations.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2)

import Mathlib
import Definitions.Def_DiscreteConvex_Algorithms_SteepestDescentStepTieBreak
import Definitions.Def_DiscreteConvex_Algorithms_IsSteepestDescentTerminal

namespace DiscreteConvex.Algorithms

/-- A run of the steepest descent algorithm with tie-breaking rule (10.2) from `x0` that
terminates after exactly `N` iterations. -/
def IsSteepestDescentRunTieBreak {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (φ : V → ℕ) (x0 : V → ℤ) (x : ℕ → V → ℤ) (N : ℕ) : Prop :=
  x 0 = x0 ∧ (∀ i < N, SteepestDescentStepTieBreak f φ (x i) (x (i + 1))) ∧
    (∀ i < N, ¬ IsSteepestDescentTerminal f (x i)) ∧ IsSteepestDescentTerminal f (x N)

end DiscreteConvex.Algorithms


