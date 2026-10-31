-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P40
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P40
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:29:30.339591+00:00
-- url     : https://prove2.me/theorems/bf36961a-8918-4b19-ab46-e42814ca04b9
-- title:
--   Definitions for Derived Algebraic Geometry II: Noncommutative Algebra
-- statement:
--   The objects the formalized statements of *Derived Algebraic Geometry II: Noncommutative Algebra* (arXiv:math/0702299) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `leftCoherent`: Definition 4.7.15, PDF p. 164: every finitely generated left ideal of the associative unital ring R is finitely presented as a left R-module. A left ideal is a submodule of the left regular module; commutativity is not required.
-- source:
--   Derived Algebraic Geometry II: Noncommutative Algebra, arXiv:math/0702299v5, https://arxiv.org/abs/math/0702299v5

import Mathlib

/-!
Statements from Lurie, Derived Algebraic Geometry II: Noncommutative Algebra,
arXiv:math/0702299v5. This partial draft retains the classical Lemma 4.7.17.
The remaining planned results have explicit deferrals in this unit's GAPS.json.
-/

universe u v w

namespace QAlgorithms.Papers.Independent.Intakenext100.P40

/-- Definition 4.7.15, PDF p. 164: every finitely generated left ideal of the
associative unital ring R is finitely presented as a left R-module. A left ideal
is a submodule of the left regular module; commutativity is not required. -/
def leftCoherent (R : Type u) [Ring R] : Prop :=
  ∀ I : Submodule R R, I.FG → Module.FinitePresentation R I

/-- The zero ideal is included in the coherence condition (PDF p. 164). -/
example (R : Type u) [Ring R] (hR : leftCoherent R) :
    (⊥ : Submodule R R).FG ∧
      Module.FinitePresentation R (⊥ : Submodule R R) :=
  ⟨Submodule.fg_bot, hR _ Submodule.fg_bot⟩

/-- The empty finite free module is finitely presented; rank zero is allowed. -/
example (R : Type u) [Ring R] :
    Module.FinitePresentation R (Fin 0 → R) := by
  infer_instance

end QAlgorithms.Papers.Independent.Intakenext100.P40


