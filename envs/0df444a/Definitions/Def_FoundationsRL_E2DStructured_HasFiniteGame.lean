-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_HasFiniteGame
-- name    : FoundationsRL_E2DStructured_HasFiniteGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:45.741038+00:00
-- url     : https://prove2.me/theorems/735df536-7067-4abe-b161-aef06d0dfcac
-- title:
--   The condition: $\Pi$ finite, or $\mathcal F$ a finite class of bounded functions
-- statement:
--   A class $\mathcal F\subseteq\{f:\Pi\to\mathbb R\}$ **has a finite game** when $\Pi$ is finite, or $\mathcal F$ is finite and each of its members is a bounded function.
--
--   Under this condition one player of the DEC game has a compact strategy set, $\Delta(\Pi)$ or $\Delta(\mathcal F)$, and the DEC over the convex hull $\mathrm{co}(\mathcal F)$ agrees with the DEC over all reference models. Without it the agreement fails.
--
--   **Formalization Note** Boundedness in the second branch makes every expectation of the game finite for every $p\in\Delta(\Pi)$, so that the game is the real bilinear game of the minimax theorem.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 41; Proposition 24, p. 80 (corrected)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The condition under which the convex-hull form of the DEC is valid: `Π` is finite, or `F` is a
finite class of bounded functions. This is the correction of Proposition 24 and of the last step of
Proposition 13 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, pp. 65, 80): Lemma 41 needs a compact player, which `Δ(Π)` is for finite `Π` and
`Δ(F)` is for finite `F`.

**Formalization Note.** Boundedness in the second branch makes every expectation of the game finite
for every `p ∈ Δ(Π)`, so the game is the real bilinear game Lemma 41 is about; for a finite `Π` it is
automatic. -/
def HasFiniteGame {D : Type*} (F : Set (D → ℝ)) : Prop :=
  Finite D ∨ (F.Finite ∧ ∀ f ∈ F, ∃ C : ℝ, ∀ π, |f π| ≤ C)

end FoundationsRL.E2DStructured


