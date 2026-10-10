-- Prove2me | Definitions.Def_ChapterA2
-- name    : ChapterA2
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T06:33:57.125225+00:00
-- url     : https://prove2.me/theorems/11c70686-8e0c-43ad-bdab-329e73090853
-- title:
--   Chapter A2
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA2.lean`): generated def bundle for ChapterA2. See BookProof/ChapterA2.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA2.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA1c
import Mathlib


/-!
# Chapter A, §A.2 — Schur systems and uniqueness of the antiisometry (work-package N2)

This file begins work-package **N2** of `FORMALIZATION_ROADMAP.md` (§A.2, the
commutant classification).  It formalizes the self-contained algebraic layer:
the **Schur property for unitaries** as a named predicate (the roadmap flags the
unitary-representation Schur lemma as an `EXTERNAL` input, so it is introduced as
a hypothesis, never an `axiom`) and **Lemma 14** — the uniqueness of the
antiisometry up to a unit phase.

* `CommutesUnitary` / `IsSchurUnitary` — a `ℂ`-linear isometric equivalence
  commuting with `M`, and the Schur property that every such is a scalar of
  modulus one.
* `antiisometry_unique_up_to_phase` (**Lemma 14**) — in a Schur system, any two
  anti-unitaries commuting with `M` differ by a unit complex phase.
* `commuting_antiUnitary_scalar_multiple` — the immediate corollary that once
  one commuting anti-unitary exists, every commuting anti-unitary is a unit
  scalar multiple of it (uniqueness of the C-conjugation up to phase).

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ## The Schur property for unitaries -/

/-- A `ℂ`-linear isometric equivalence `g` **commutes with** the system `M` iff
it commutes with every `m ∈ M`. -/
def CommutesUnitary (M : System ℂ V) (g : V ≃ₗᵢ[ℂ] V) : Prop :=
  ∀ m ∈ M.ops, ∀ x, g (m x) = m (g x)

/-- **Def 13 (Schur, unitary form).**  `M` is *Schur for unitaries* iff every
`ℂ`-linear isometric equivalence commuting with `M` is a scalar of modulus one.
The roadmap flags the unitary-representation Schur lemma as an `EXTERNAL`
theorem (not available in Mathlib); it is used here only as a named hypothesis,
never an `axiom`. -/
def IsSchurUnitary (M : System ℂ V) : Prop :=
  ∀ g : V ≃ₗᵢ[ℂ] V, CommutesUnitary M g → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, g x = c • x

/-! ## Lemma 14 — uniqueness of the antiisometry up to phase -/





end BookProof.ChapterA


