-- Prove2me | Definitions.Def_ChapterFriedrichsSquareFactorization
-- name    : ChapterFriedrichsSquareFactorization
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-09T10:07:39.526198+00:00
-- url     : https://prove2.me/theorems/a3048a35-7b77-4f9c-97fc-43154ff48ae1
-- title:
--   The Lean 4 theorem `flipGraph_isClosed` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFriedrichsSquareFactorization.lean`): generated def bundle for ChapterFriedrichsSquareFactorization. See BookProof/ChapterFriedrichsSquareFactorization.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsSquareFactorization.lean

import Theorems.Thm_BookProof_ClosureUniqueness_mem_adjGraph_iff


import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Mathlib


/-!
# `(A²)_F = A* Ā` — the Friedrichs extension of the square is the factorization

`BookProof.ChapterClosureUniqueness` renders the composite `A* ∘ Ā` of a densely
defined symmetric operator `A` as a relation `factorGraph A ⊆ F × F` and proves
that this relation is uniquely determined by `A` (it does not depend on the
realization of the closure, nor on the core), that it extends `A²`, that it is
symmetric and that its quadratic form is `‖Āx‖² ≥ 0`.  What it left open is the
identity itself:

> the composite `A* Ā` **is** the Friedrichs extension of `A²`.

This module proves it.  `A` is a densely defined symmetric operator whose domain
`D` is invariant (`A D ⊆ D`), so `A²` is a symmetric non-negative operator on the
same domain, and the Friedrichs extension of `A²` is characterized — this is the
Freudenthal/Krein characterization — as the unique **self-adjoint extension of
`A²` whose domain lies in the form domain**.  The form of `A²` is
`⟪x, A²y⟫ = ⟪Ax, Ay⟫`, so the form domain is the domain `clDom A` of the closure
`Ā` (the graph-norm closure of `D` is exactly the closed graph, by definition).

## The statement

`IsFriedrichsSqExtension A hstab R` says that the relation `R ⊆ F × F` is

* an extension of `A²` (`extends_sq`),
* supported in the form domain, `x ∈ clDom A` for every `(x, z) ∈ R`
  (`form_domain`), and
* self-adjoint, `R* = R` (`selfAdjoint`; it is in particular symmetric,
  `IsFriedrichsSqExtension.symmetric`).

**`isFriedrichsSqExtension_iff_eq_factorRel`** — for a Hilbert space `F` and a
symmetric `A` with invariant domain (density of the domain is needed only for the
operator form below, not for the statement about relations), `R` has these three
properties **iff** `R = factorRel A`, the relation `A* Ā`.  In particular the
Friedrichs extension of `A²` exists, is unique, and equals `A* Ā`.

The same statement in operator form is **`eq_frExt_of_isSelfAdjointExtension`**:
the relation `A* Ā` is single-valued (`factorRel_snd_eq_zero_of_fst_eq_zero`),
so it is the graph of an operator `frExt A` on `frDom A ≤ clDom A`, that operator
is a positive self-adjoint extension of `A²` (`isSelfAdjointExtension_frExt`,
`frExt_quadForm_nonneg`), and every self-adjoint extension of `A²` whose domain
lies in the form domain has the domain and the values of `frExt A`.

## The two halves

* **Everything symmetric in the form domain is below `A* Ā`**
  (`le_factorRel_of_symmetric_extension`): if `R` is a symmetric extension of
  `A²` whose domain lies in `clDom A`, then `R ≤ factorRel A`.  This needs no
  self-adjointness and no completeness: for `(x, z) ∈ R` and `v ∈ D`,
  symmetry of `R` gives `⟪z, v⟫ = ⟪x, A²v⟫`, while `(x, Āx) ∈ clGraph A` and the
  symmetry of `A` give `⟪Āx, Av⟫ = ⟪x, A²v⟫`; hence `(Āx, z)` is an adjoint pair.
* **`A* Ā` is self-adjoint** (`adjPairs_factorRel`), which is von Neumann's
  theorem `Ā*Ā = (Ā)*Ā` self-adjoint.  The proof is the standard one: the flip
  `V(x, y) = (−y, x)` is unitary on `F ⊕₂ F`, and
  `adjPairs (clGraph A) = (V (clGraph A))ᗮ`, so the closed graph and its flip
  decompose `F ⊕₂ F` orthogonally; splitting `(0, h)` along that decomposition
  solves `x + A*Āx = h` (`exists_mem_factorRel_add`, surjectivity of `1 + A*Ā`),
  and surjectivity upgrades symmetry to self-adjointness.

Together with `BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair` this
says that the Friedrichs extension of `A²` may be computed from any core of `Ā`.
-/

namespace BookProof.FriedrichsSquare

open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

/-! ## The composite `A* Ā` as a submodule of `F × F` -/

/-- The relation `A* ∘ Ā` of `BookProof.ClosureUniqueness.factorGraph`, packaged
as a submodule of `F × F` (it is a linear relation). -/
def factorRel (A : D →ₗ[ℂ] F) : Submodule ℂ (F × F) where
  carrier := factorGraph A
  add_mem' := by
    rintro p q ⟨y, hy, hy'⟩ ⟨z, hz, hz'⟩
    exact ⟨y + z, (clGraph A).add_mem hy hz, (adjGraph A).add_mem hy' hz'⟩
  zero_mem' := ⟨0, (clGraph A).zero_mem, (adjGraph A).zero_mem⟩
  smul_mem' := by
    rintro c p ⟨y, hy, hy'⟩
    exact ⟨c • y, (clGraph A).smul_mem c hy, (adjGraph A).smul_mem c hy'⟩

@[simp] theorem mem_factorRel_iff {A : D →ₗ[ℂ] F} {p : F × F} :
    p ∈ factorRel A ↔ ∃ y, (p.1, y) ∈ clGraph A ∧ (y, p.2) ∈ adjGraph A := Iff.rfl









/-! ## Surjectivity of `1 + A* Ā` -/

section Complete

variable [CompleteSpace F]

/-- The flip of the closed graph, `V 𝒢(Ā) = {(−Āx, x)}`, inside the Hilbert
direct sum `F ⊕₂ F`. -/
def flipGraph (A : D →ₗ[ℂ] F) : Submodule ℂ (WithLp 2 (F × F)) where
  carrier := {p | ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) ∈ clGraph A}
  add_mem' := by
    intro p q hp hq
    have : ((WithLp.ofLp (p + q)).2, -(WithLp.ofLp (p + q)).1)
        = ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) + ((WithLp.ofLp q).2, -(WithLp.ofLp q).1) := by
      simp [add_comm]
    rw [Set.mem_setOf_eq, this]
    exact (clGraph A).add_mem hp hq
  zero_mem' := by
    have : ((WithLp.ofLp (0 : WithLp 2 (F × F))).2, -(WithLp.ofLp (0 : WithLp 2 (F × F))).1)
        = (0 : F × F) := by simp [Prod.ext_iff]
    rw [Set.mem_setOf_eq, this]
    exact (clGraph A).zero_mem
  smul_mem' := by
    intro c p hp
    have : ((WithLp.ofLp (c • p)).2, -(WithLp.ofLp (c • p)).1)
        = c • ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) := by
      simp [smul_neg]
    rw [Set.mem_setOf_eq, this]
    exact (clGraph A).smul_mem c hp



omit [CompleteSpace F] in
theorem flipGraph_isClosed (A : D →ₗ[ℂ] F) :
    IsClosed ((flipGraph A : Submodule ℂ (WithLp 2 (F × F))) : Set (WithLp 2 (F × F))) := by
  have hcont : Continuous fun p : WithLp 2 (F × F) => ((WithLp.ofLp p).2, -(WithLp.ofLp p).1) := by
    fun_prop
  exact (clGraph_isClosed A).preimage hcont

instance flipGraph_hasOrthogonalProjection (A : D →ₗ[ℂ] F) :
    (flipGraph A).HasOrthogonalProjection := by
  haveI : CompleteSpace (flipGraph A) := by
    haveI := flipGraph_isClosed A
    exact IsClosed.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _





end Complete

/-! ## `A* Ā` is symmetric, and self-adjoint -/





/-! ## The Friedrichs extension of `A²` -/

/-- `R` is **a Friedrichs extension of `A²`**: a self-adjoint extension of `A²`,
as a relation, whose domain lies in the form domain `clDom A = D(Ā)`. -/
structure IsFriedrichsSqExtension (A : D →ₗ[ℂ] F) (hstab : ∀ v : D, (A v : F) ∈ D)
    (R : Submodule ℂ (F × F)) : Prop where
  /-- `R` extends `A²`. -/
  extends_sq : ∀ v : D, ((v : F), sqOp A hstab v) ∈ R
  /-- The domain of `R` lies in the form domain of `A²`. -/
  form_domain : ∀ p ∈ R, p.1 ∈ clDom A
  /-- `R` is self-adjoint. -/
  selfAdjoint : adjPairs R = R













/-! ## The same statement for operators

The relation `factorRel A` is single-valued as soon as `A` is densely defined and
symmetric, so it is the graph of an operator `frExt A` on the domain `frDom A`;
that operator is a positive self-adjoint extension of `A²`, and it is the unique
one whose domain lies in the form domain. -/

/-- **`A* Ā` is single-valued**: a densely defined symmetric operator is
closable, and the adjoint of a densely defined operator is an operator. -/
theorem factorRel_snd_eq_zero_of_fst_eq_zero {A : D →ₗ[ℂ] F} (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) {z : F} (h : ((0 : F), z) ∈ factorRel A) : z = 0 := by
  obtain ⟨y, hy, hz⟩ := h
  have hy0 : y = 0 := clGraph_snd_eq_zero_of_fst_eq_zero hdense hsym hy
  rw [mem_adjGraph_iff] at hz
  refine Dense.eq_zero_of_inner_right (𝕜 := ℂ) (S := D) hdense fun v hv => ?_
  have hv := hz ⟨v, hv⟩
  simp only [hy0, inner_zero_right] at hv
  exact hv.symm

/-- The domain of `A* Ā`. -/
def frDom (A : D →ₗ[ℂ] F) : Submodule ℂ F := (factorRel A).map (LinearMap.fst ℂ F F)

theorem mem_frDom_iff {A : D →ₗ[ℂ] F} {x : F} : x ∈ frDom A ↔ ∃ z, (x, z) ∈ factorRel A := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨z, hz⟩
    exact ⟨(x, z), hz, rfl⟩

/-- The value of `A* Ā` at a point of its domain (chosen; unique by
`frFun_unique`). -/
noncomputable def frFun (A : D →ₗ[ℂ] F) (x : frDom A) : F :=
  Classical.choose (mem_frDom_iff.1 x.2)

theorem frFun_spec (A : D →ₗ[ℂ] F) (x : frDom A) : ((x : F), frFun A x) ∈ factorRel A :=
  Classical.choose_spec (mem_frDom_iff.1 x.2)

theorem frFun_unique {A : D →ₗ[ℂ] F} (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A)
    {x : frDom A} {z : F} (h : ((x : F), z) ∈ factorRel A) : frFun A x = z := by
  have hz : ((0 : F), frFun A x - z) ∈ factorRel A := by
    have := Submodule.sub_mem (factorRel A) (frFun_spec A x) h
    simpa using this
  exact sub_eq_zero.mp (factorRel_snd_eq_zero_of_fst_eq_zero hdense hsym hz)

/-- **The Friedrichs extension of `A²`**, as a linear operator. -/
noncomputable def frExt (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    frDom A →ₗ[ℂ] F where
  toFun := frFun A
  map_add' x y := by
    refine frFun_unique hdense hsym ?_
    have := Submodule.add_mem (factorRel A) (frFun_spec A x) (frFun_spec A y)
    simpa using this
  map_smul' c x := by
    refine frFun_unique hdense hsym ?_
    have := Submodule.smul_mem (factorRel A) c (frFun_spec A x)
    simpa using this

@[simp] theorem frExt_apply (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) (x : frDom A) : frExt A hdense hsym x = frFun A x := rfl











end BookProof.FriedrichsSquare


