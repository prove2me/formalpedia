-- Prove2me | Definitions.Def_MondererShapley_Improvement_ImprovesTo
-- name    : MondererShapley_Improvement_ImprovesTo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:33.657463+00:00
-- url     : https://prove2.me/theorems/f38781df-7fab-441a-96a7-28e11ab3cb0e
-- title:
--   Improvement reachability relation
-- statement:
--   For strategy profiles $x,y\in Y$, the relation $x>y$ holds exactly when $x\ne y$ and there is a finite improvement path starting at $y$ and ending at $x$:
--
--   $$
--   x>y\quad\Longleftrightarrow\quad x\ne y\ \text{ and a finite improvement path leads from }y\text{ to }x.
--   $$
--
--   The relation is the one represented by a strictly increasing real function in the proof of Lemma 2.5.
--
--   **Formalization Note** The Lean name `ImprovesTo u x y` follows the paper's destination-first orientation.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 129 (PDF p. 6), Lemma 2.5 proof, relation “>”

import Mathlib
import Definitions.Def_MondererShapley_Improvement_IsImprovement

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- `ImprovesTo u x y` is the paper's relation `x > y` (p. 129). -/
def ImprovesTo (u : ι → (∀ i, Y i) → ℝ) (x y : ∀ i, Y i) : Prop :=
  x ≠ y ∧
    ∃ γ : FinPath Y,
      γ.IsImprovement u ∧ γ.pt 0 = y ∧ γ.pt (Fin.last γ.len) = x

end MondererShapley.Improvement


