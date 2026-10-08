-- Prove2me | Definitions.Def_ChapterA3w
-- name    : ChapterA3w
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T15:00:36.748074+00:00
-- url     : https://prove2.me/theorems/03e7fe58-7bc2-4ca7-b84d-88d9403f7012
-- title:
--   Chapter A3w
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3w.lean`): generated def bundle for ChapterA3w. See BookProof/ChapterA3w.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3w.lean

import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3q
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA4
import Mathlib


/-!
# Chapter A3w — the Weyl half of the exhaustiveness bundle (roadmap N11, Lemma 52)

This file assembles the *complete-reducibility / classification* clause of the
book's Lemma 52 (Notes 50–51): the finite-dimensional irreducible representations
of the Lorentz group are the `V_{(m,n)}`, and parity glues `V_{(m,n)}` to
`V_{(n,m)}`, so the parity-invariant real irreps are `V_{(m,n)} ⊕ V_{(n,m)}`.

Following the `IsSchurFull` / `PauliFundamental` design, the one genuinely
external input — **Weyl's theorem** that finite-dimensional `SL(2,ℂ)`-reps are
completely reducible — is introduced as a **named hypothesis with a citation
docstring, never an `axiom`**.  The concrete *parity-gluing mechanism* is then
fully proved from the on-disk chirality/parity cores of `ChapterA3j`/`ChapterA3k`,
and the general-`N` complete-reducibility projector system is `ChapterA3q`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); the Weyl input is a hypothesis, not an axiom.
-/

open Matrix

namespace BookProof.ChapterA3w

open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3q

/-! ## External input: Weyl complete reducibility -/

/-- **Weyl's theorem** (H. Weyl, *Math. Z.* 24 (1926) 328–395), taken as an
`EXTERNAL` named hypothesis (not available in Mathlib for `SL(2,ℂ)`; never an
`axiom`).  Every finite-dimensional representation of `SL(2,ℂ)` is completely
reducible: every invariant subspace has an invariant complement (equivalently,
the representation is a direct sum of the irreducibles `V_{(m,n)}`). -/
def WeylCompleteReducibility : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)
    (W : Submodule ℂ V), (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x ∈ W, ρ g x ∈ W) →
      ∃ W' : Submodule ℂ V,
        (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x ∈ W', ρ g x ∈ W') ∧ IsCompl W W'



/-! ## Concrete parity-gluing mechanism (fully proved from the cores) -/



end BookProof.ChapterA3w


