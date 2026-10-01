-- Prove2me | Definitions.Def_ChapterClosureUniqueness
-- name    : ChapterClosureUniqueness
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T00:58:39.296731+00:00
-- url     : https://prove2.me/theorems/3c8f427f-a81a-4a62-85b5-6c97e57dc8ee
-- title:
--   Chapter ClosureUniqueness
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.ClosureUniqueness`, source chapter `BookProof/ChapterClosureUniqueness.lean`): Chapter ClosureUniqueness
--
--   Generated def bundle for ChapterClosureUniqueness. See BookProof/ChapterClosureUniqueness.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterClosureUniqueness.lean

import Definitions.Def_ChapterEsaClosureCore
import Mathlib


/-!
# Uniqueness of the closure, and of the `A* ∘ Ā` factorization

`BookProof.ChapterEsaClosure` builds the closure `clExt T` of a densely defined
symmetric operator `T` as the operator whose graph is the topological closure
`clGraph T` of the graph of `T`, and shows that when `T` is essentially
self-adjoint that closure is the unique self-adjoint extension.  This module
answers the two questions that the *applications* of the Faris–Lavine criterion
(`BookProof.ChapterFarisLavine`) raise about that construction.

## 1.  Is the closure unique?

Yes, and this is a purely geometric fact: the closure is *defined* by
`𝒢(Ā) = closure 𝒢(A)`, and the topological closure of a set is unique.  Here:

* `IsClosedExtension T A` — `A` extends `T` and has a closed graph;
* `IsClosureOf T A` — `A` is a *minimal* closed extension of `T`;
* `clGraph_le_opGraph_of_isClosedExtension` — the closed graph of *any* closed
  extension contains `clGraph T`, so a minimal closed extension is exactly one
  whose graph **is** `clGraph T` (`opGraph_eq_clGraph_of_isClosureOf`);
* `clExt_isClosureOf` — the construction of `ChapterEsaClosure` is one;
* **`closure_unique`** — any two closures of `T` have the same domain and the
  same values.  So `Ā` is strictly unique.

## 2.  Closure versus self-adjoint extension

The closure is unique, but it need not be self-adjoint, and self-adjoint
extensions need not be unique.  The first half of that distinction is proved:

* **`not_isSelfAdjointExtension_clExt_of_deficiency`** — if `T` has a non-zero
  deficiency vector at `i`, its (unique) closure is *not* a self-adjoint
  extension.  So "unique closure" is strictly weaker than "unique self-adjoint
  extension"; the latter is the essential-self-adjointness statement
  `BookProof.EsaClosure.isSelfAdjointExtension_unique_of_esa`.

## 3.  The factorization `(A²)_F = A* Ā = Ā* Ā`

The factors are uniquely determined by `A`, and only through its closure:

* `adjPairs G` — the adjoint of a graph `G`, i.e. the pairs `(w, u)` with
  `⟪y, w⟫ = ⟪x, u⟫` for all `(x, y) ∈ G`; `adjGraph T = adjPairs (opGraph T)` is
  the graph of `T*`;
* **`adjGraph_eq_adjPairs_clGraph`** — `T* = (T̄)*`: the adjoint sees only the
  closure (this is the reason the adjoint of a core is the adjoint of the closed
  operator);
* **`factorGraph_eq_of_clGraph_eq`**, **`compGraph_eq_of_isClosureOf`** — the
  composite `A* ∘ Ā`, rendered as a relation, is the same for every operator
  realizing the closure, and (`factorGraph_eq_of_isCoreOf`) the same for two
  different dense cores `𝒟₁`, `𝒟₂` of one closed operator.  That is items (a)
  and (b) of the factorization question.
* **`exists_linearIsometry_of_inner_eq`** and
  **`eqOn_topologicalClosure_range_of_eqOn_range`** — item (c), the
  polar-decomposition half: two operators `B`, `C` on a common domain with
  `B*B = C*C` (as forms) are intertwined by a *linear isometry* `U` of `ran B`
  onto `ran C` with `C = U B`, and any two continuous intertwiners agree on the
  whole initial space `closure (ran B)`.  So the factorization `S = B*B` is
  unique exactly up to such a partial isometry.
* **`positive_factor_unique`** — and it is strictly unique if the factor is
  required to be positive and self-adjoint: for bounded operators, a positive
  `B` with `B² = S` is `√S`, so there is only one.

The `#print axioms` audit for this module is `Work/ClosureUniquenessAudit.lean`
(`lake build Work.ClosureUniquenessAudit`); it is kept outside the chapter graph
so that auditing does not enlarge anyone else's dependency cone — see
`BUILD_LAYOUT.md`.

## Honest boundary

Item (c) is proved here for the *form* identity `⟪Bx, By⟫ = ⟪Cx, Cy⟫` (which is
what `B*B = C*C` means on the common domain), and the strict uniqueness of the
positive factor is proved for **bounded** operators, where Mathlib's continuous
functional calculus supplies the square root.  The identity
`(A²)_F = A* Ā` itself — that the Friedrichs extension of `A²` *is* the
composite — is not proved here; this module is about the uniqueness of the
objects entering it, and no unproved statement is used as a hypothesis of any
theorem below.
-/

namespace BookProof.ClosureUniqueness

open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

/-! ## Part 1 — the closure is unique -/

/-- `A` on `Dom` **extends** `T` on `D`. -/
def Extends (T : D →ₗ[ℂ] F) (A : Dom →ₗ[ℂ] F) : Prop :=
  ∀ v : D, ∃ h : (v : F) ∈ Dom, A ⟨(v : F), h⟩ = T v



/-- `A` is a **closed extension** of `T`: it extends `T` and its graph is closed. -/
def IsClosedExtension (T : D →ₗ[ℂ] F) (A : Dom →ₗ[ℂ] F) : Prop :=
  Extends T A ∧ IsClosed ((opGraph A : Submodule ℂ (F × F)) : Set (F × F))



/-- `A` is **the closure** of `T`: a minimal closed extension. -/
def IsClosureOf (T : D →ₗ[ℂ] F) (A : Dom →ₗ[ℂ] F) : Prop :=
  IsClosedExtension T A ∧ opGraph A ≤ clGraph T















/-! ## Part 2 — the closure need not be self-adjoint -/





/-! ## Part 3 — the closure does not depend on the core -/

/-- `T₁` is a **core** for `T₂`: `T₂` extends `T₁`, and the graph of `T₂` is
inside the closure of the graph of `T₁`. -/
def IsCoreOf (T₁ : D₁ →ₗ[ℂ] F) (T₂ : D₂ →ₗ[ℂ] F) : Prop :=
  Extends T₁ T₂ ∧ opGraph T₂ ≤ clGraph T₁







/-! ## Part 4 — the adjoint depends only on the closure -/

/-- The **adjoint of a graph**: the pairs `(w, u)` with `⟪y, w⟫ = ⟪x, u⟫` for all
`(x, y) ∈ G`. -/
def adjPairs (G : Submodule ℂ (F × F)) : Submodule ℂ (F × F) where
  carrier := {p : F × F | ∀ q ∈ G, (inner ℂ q.2 p.1 : ℂ) = inner ℂ q.1 p.2}
  add_mem' := by
    intro p p' hp hp' q hq
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
    rw [hp q hq, hp' q hq]
  zero_mem' := by intro q _; simp
  smul_mem' := by
    intro c p hp q hq
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right]
    rw [hp q hq]

/-- The **graph of the adjoint** `T*`. -/
def adjGraph (T : D →ₗ[ℂ] F) : Submodule ℂ (F × F) := adjPairs (opGraph T)









/-! ## Part 5 — the factorization `A* ∘ Ā` is unique -/

/-- The composite `T* ∘ T̄`, as a relation: `(x, z)` with `T̄ x = y` and `T* y = z`. -/
def factorGraph (T : D →ₗ[ℂ] F) : Set (F × F) :=
  {p : F × F | ∃ y, (p.1, y) ∈ clGraph T ∧ (y, p.2) ∈ adjGraph T}

/-- The composite `A* ∘ A` of an operator with the adjoint of its graph. -/
def compGraph (A : Dom →ₗ[ℂ] F) : Set (F × F) :=
  {p : F × F | ∃ y, (p.1, y) ∈ opGraph A ∧ (y, p.2) ∈ adjPairs (opGraph A)}









/-! ### `A* ∘ Ā` is a positive symmetric extension of `A²`

The identity `(A²)_F = A* Ā` is not proved here, but the three facts that make
the right-hand side a candidate for a Friedrichs extension of `A²` are: the
composite extends `A²`, it is symmetric, and its quadratic form `⟪x, A*Āx⟫` is
the non-negative number `‖Āx‖²`. -/

/-- The square `A²` of an operator that leaves its domain invariant. -/
def sqOp (A : D →ₗ[ℂ] F) (hstab : ∀ v : D, (A v : F) ∈ D) : D →ₗ[ℂ] F where
  toFun v := A ⟨A v, hstab v⟩
  map_add' v w := by
    have : (⟨A (v + w), hstab (v + w)⟩ : D) = ⟨A v, hstab v⟩ + ⟨A w, hstab w⟩ := by
      apply Subtype.ext; simp
    rw [this, map_add]
  map_smul' c v := by
    have : (⟨A (c • v), hstab (c • v)⟩ : D) = c • ⟨A v, hstab v⟩ := by
      apply Subtype.ext; simp
    rw [this, map_smul]; rfl











/-! ## Part 6 — (c) uniqueness up to a partial isometry -/





/-! ## Part 7 — (c) the positive self-adjoint factor is strictly unique -/



/-! ## Part 8 — the Faris–Lavine application

The reason the questions above matter here: the Faris–Lavine criterion produces
*essential self-adjointness on a core*, and what the applications use is the
closure.  Combining the criterion with Parts 1 and 3 gives the complete package
for an operator satisfying its hypotheses. -/

section FarisLavineApplication

variable [CompleteSpace F]





end FarisLavineApplication



end BookProof.ClosureUniqueness


