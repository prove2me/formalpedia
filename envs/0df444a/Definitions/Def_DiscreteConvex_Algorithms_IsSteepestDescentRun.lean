-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_IsSteepestDescentRun
-- name    : DiscreteConvex_Algorithms_IsSteepestDescentRun
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:32:30.008957+00:00
-- url     : https://prove2.me/theorems/743dfef3-465e-4222-8b03-1a3356cdc522
-- title:
--   A run of the steepest descent algorithm (p.282)
-- statement:
--   A function $x : \mathbb N \to \mathbb Z^V$ is a **run** of the steepest descent algorithm from $x^0$ terminating after exactly $N$ iterations: it starts at $x^0$, takes $N$ genuine (non-terminal) steps, and $x_N$ is terminal — the Lean representation of "the number of iterations in the steepest descent algorithm" that Propositions 10.1 and 10.2 bound, following the mission's own decision to represent the algorithm as an abstract sequence of iterates satisfying its step-transition relations rather than an executable recursive program; see `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282

import Mathlib
import Definitions.Def_DiscreteConvex_Algorithms_SteepestDescentStep
import Definitions.Def_DiscreteConvex_Algorithms_IsSteepestDescentTerminal

namespace DiscreteConvex.Algorithms

/-- `x : ℕ → Zⱽ` is a run of the steepest descent algorithm (p.282) from `x0` that terminates
after exactly `N` iterations: it starts at `x0`, takes `N` genuine (non-terminal) steps, and
`x N` is terminal. -/
def IsSteepestDescentRun {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (x0 : V → ℤ) (x : ℕ → V → ℤ) (N : ℕ) : Prop :=
  x 0 = x0 ∧ (∀ i < N, SteepestDescentStep f (x i) (x (i + 1))) ∧
    (∀ i < N, ¬ IsSteepestDescentTerminal f (x i)) ∧ IsSteepestDescentTerminal f (x N)

end DiscreteConvex.Algorithms


