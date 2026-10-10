-- Prove2me | Definitions.Def_ChapterA1c
-- name    : ChapterA1c
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-09T16:55:19.88236+00:00
-- url     : https://prove2.me/theorems/82d7a799-f328-4d61-85bd-c040cbcf8fcf
-- title:
--   Chapter A1c
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA1c.lean`): generated def bundle for ChapterA1c. See BookProof/ChapterA1c.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA1c.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
import Mathlib


/-!
# Chapter A, §A.1 — the C-type and R-type classification (work-package N1)

This file continues work-package **N1** of `FORMALIZATION_ROADMAP.md` (§A.1,
Defs 9/10 and Props 11/12).  The previous passes built

* the complex inner-product structure on the complexification `Cx W` and the
  canonical conjugation `Cx.cxConj` (`BookProof/Complexification.lean`), together
  with the fact that the complexification of a real system is **C-real**
  (`cxConj_isConjugation`); and
* the order-preserving bijection between real subsystems and
  conjugation-invariant complex subsystems, giving the reduction of real
  irreducibility to the conjugation-stable complex lattice
  (`irreducible_iff_no_conj_subsystem`, `BookProof/ChapterA1b.lean`).

Here we add the *classification predicates* themselves:

* **Def 9** — the three types of an irreducible **complex** system:
  `IsCReal` (a C-conjugation exists), `IsCPseudoreal` (no C-conjugation but a
  commuting anti-unitary exists), `IsCComplex` (no commuting anti-unitary at
  all), together with the trichotomy (exactly one holds) and the fact that the
  complexification of a real system is always C-real.

* **Def 10 / Prop 12 (R-real case)** — the *R-real* real systems, i.e. those
  whose complexification is (C-real and) irreducible, and the converse half of
  the trichotomy: an R-real system is irreducible.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace BookProof.ChapterA

/-! ## Def 9 — the C-type of a complex system -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- An anti-unitary operator **commutes with** the complex system `M` iff it
commutes with every `m ∈ M`. -/
def CommutesAntiUnitary (M : System ℂ V) (θ : AntiUnitary V) : Prop :=
  ∀ m ∈ M.ops, ∀ x, θ (m x) = m (θ x)

/-- The complex system `M` **has a commuting anti-unitary** iff some anti-unitary
operator commutes with `M`. -/
def HasCommutingAntiUnitary (M : System ℂ V) : Prop :=
  ∃ θ : AntiUnitary V, CommutesAntiUnitary M θ

/-- **Def 9.1 (C-real).** A complex system `M` is *C-real* iff it admits a
C-conjugation (an anti-unitary **involution** commuting with `M`). -/
def IsCReal (M : System ℂ V) : Prop :=
  ∃ θ : AntiUnitary V, IsConjugation M θ

/-- **Def 9.2 (C-pseudoreal).** A complex system `M` is *C-pseudoreal* iff it has
no C-conjugation, yet some anti-unitary operator commutes with `M`. -/
def IsCPseudoreal (M : System ℂ V) : Prop :=
  ¬ IsCReal M ∧ HasCommutingAntiUnitary M

/-- **Def 9.3 (C-complex).** A complex system `M` is *C-complex* iff no
anti-unitary operator commutes with `M` at all. -/
def IsCComplex (M : System ℂ V) : Prop :=
  ¬ HasCommutingAntiUnitary M













/-! ## Def 10 / Prop 12 — the R-real case -/

open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]



/-- **Def 10 (R-real).** A real system `M` is *R-real* iff its complexification
`(M, Cx W)` is irreducible (as a complex system).  By `cxSystem_isCReal` the
complexification is automatically C-real, so this matches Def 10's "C-real
irreducible complexification". -/
def IsRReal (M : System ℝ W) : Prop :=
  (cxSystem M).IsIrreducible





end BookProof.ChapterA


