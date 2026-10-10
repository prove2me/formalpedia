-- Prove2me | Definitions.Def_ChapterA1f
-- name    : ChapterA1f
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T07:01:53.336406+00:00
-- url     : https://prove2.me/theorems/1c50a393-8665-4246-8935-c628e00cc918
-- title:
--   Chapter A1f
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA1f.lean`): generated def bundle for ChapterA1f. See BookProof/ChapterA1f.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA1f.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA1b
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA1d
import Definitions.Def_ChapterA1e
import Definitions.Def_Complexification
import Mathlib


/-!
# Chapter A, §A.1 — realification of a C-real system reduces (work-package N1)

This file continues work-package **N1** of `FORMALIZATION_ROADMAP.md` (§A.1,
Props 11/12).  Building on the realification correspondence of
`BookProof/ChapterA1d.lean` (the canonical R-imaginary operator `Jmap : u ↦ i·u`,
the criterion `complex_irreducible_iff_no_Jinvariant_subsystem`) and the
`V ⊕ V̄` dichotomy of `BookProof/ChapterA1e.lean` (`realification_splits`), we
formalize the concrete direction of Prop 12 that requires no external input:

> **`realification_reducible_of_conjugation`.**  If a complex system `(M, V)`
> admits a **C-conjugation** `θ` (an anti-unitary involution commuting with `M`,
> i.e. `M` is *C-real*), then its realification `(M, V^r)` is **reducible**: the
> real fixed space `conjFixed θ = {v : θ v = v}` is a proper non-trivial real
> subsystem (the real form `V = W ⊕ i·W` picture of Def 10 / Prop 11).

This is exactly the R-real half of the Def 10 dichotomy from the realification
side: a complex irreducible system is C-real precisely when its realification
splits along a real form.  The converse direction (a reducible realification of a
complex-irreducible system produces a C-conjugation — the R-pseudoreal/R-complex
sorting) is recorded as the remaining N1 obstruction in `BookProof/STATUS.md`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace BookProof.ChapterA

attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **The real fixed space `conjFixed θ = {v : θ v = v}`** of an anti-unitary
operator `θ`, as a real subspace of the realification `V^r`.  When `θ` is a
C-conjugation this is the real form `W` with `V = W ⊕ i·W`. -/
noncomputable def conjFixed (θ : AntiUnitary V) : Submodule ℝ V where
  carrier := {v | θ v = v}
  add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [map_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro r v hv; simp only [Set.mem_setOf_eq] at *
    have : (r : ℝ) • v = ((r : ℝ) : ℂ) • v := by simp [Complex.coe_smul]
    rw [this, θ.map_smulₛₗ, hv]; simp

omit [CompleteSpace V] in
@[simp] lemma mem_conjFixed {θ : AntiUnitary V} {v : V} : v ∈ conjFixed θ ↔ θ v = v := Iff.rfl











/-! ## Headline: a C-real realification is reducible -/







end BookProof.ChapterA


