-- Prove2me | Definitions.Def_ChapterReducingSubspaceEsa
-- name    : ChapterReducingSubspaceEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T18:43:48.126463+00:00
-- url     : https://prove2.me/theorems/48d24fa7-b091-4052-a47d-5b5f3e2f8d7f
-- title:
--   The Lean 4 theorem `apply_of_mem_range` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterReducingSubspaceEsa.lean`): generated def bundle for ChapterReducingSubspaceEsa. See BookProof/ChapterReducingSubspaceEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterReducingSubspaceEsa.lean

import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib


/-!
# Reduction of an essentially self-adjoint operator to an invariant sector

The second-quantization wave proves essential self-adjointness of the derivation `dΓ(h)` on
the **full** tensor powers `H^{⊗n}`.  The physical Fock spaces are the *symmetric* (bosonic)
and *antisymmetric* (fermionic) subspaces of those powers, i.e. the ranges of the
symmetrizing and antisymmetrizing projections.  This module supplies the general instrument
that carries essential self-adjointness from the ambient space to such a sector:

> **Reduction.**  Let `T : D →ₗ[ℂ] F` be an operator, and let `P : F →ₗ[ℂ] F` be an
> idempotent, symmetric (hence orthogonal) projection which maps `D` into `D` and commutes
> with `T` there.  Then the part of `T` inside the range `K = P F`, on the domain
> `D ∩ K`, is symmetric whenever `T` is, and **every deficiency space of the reduced
> operator vanishes as soon as the corresponding deficiency space of `T` does**.  In
> particular essential self-adjointness descends to the sector.

No completeness and no closedness are used: the argument is the one-line computation
`⟪T v, w⟫ = ⟪T (P v), w⟫` for `w` in the range of `P`, which turns a deficiency vector of
the reduced operator into a deficiency vector of `T` itself.

## Contents

* `IsReducingProjection` — idempotent and symmetric.
* `redDom`, `redIncl`, `redOp` — the sector `D ∩ K` and the part of `T` inside `K`.
* `symmetricOn_redOp`, `deficiencyTrivialAt_red`, **`essentiallySelfAdjointOn_red`** — the
  reduction principle.
* `symProj` / `asymProj` — the two spectral projections `(1 ± U)/2` of a self-inverse
  isometry `U`, shown to be reducing projections, together with
  **`essentiallySelfAdjointOn_symSector`** and **`essentiallySelfAdjointOn_asymSector`**:
  if a self-inverse isometry `U` preserves the domain and commutes with `T`, then `T` is
  essentially self-adjoint on each of the two sectors `U x = x` and `U x = -x` as soon as
  it is essentially self-adjoint on `D`.  For the swap of a two-particle space these are
  exactly the bosonic and the fermionic sectors.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.ReducedEsa

open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## Reducing projections -/

/-- An **orthogonal projection**, in the algebraic form used here: an idempotent and
symmetric linear map.  Its range is the sector onto which operators are reduced. -/
structure IsReducingProjection (P : F →ₗ[ℂ] F) : Prop where
  /-- idempotence -/
  idem : ∀ x, P (P x) = P x
  /-- symmetry -/
  symm : ∀ x y : F, (inner ℂ (P x) y : ℂ) = inner ℂ x (P y)

variable {P : F →ₗ[ℂ] F}

/-- On its range a projection is the identity. -/
theorem IsReducingProjection.apply_of_mem_range (hP : IsReducingProjection P) {w : F}
    (hw : w ∈ LinearMap.range P) : P w = w := by
  obtain ⟨u, rfl⟩ := hw
  exact hP.idem u

/-! ## The reduced operator -/

variable (P) in
/-- The sector: the range of the projection, as a subspace of `F`. -/
def sector : Submodule ℂ F := LinearMap.range P

variable (P) (D : Submodule ℂ F) in
/-- The domain of the reduced operator: the part of `D` inside the sector. -/
def redDom : Submodule ℂ (sector P) := Submodule.comap (sector P).subtype D

variable {D : Submodule ℂ F}



variable (P D) in
/-- The inclusion of the reduced domain into `D`. -/
def redIncl : redDom P D →ₗ[ℂ] D :=
  LinearMap.codRestrict D (((sector P).subtype).comp (redDom P D).subtype) (fun x => x.2)

@[simp] theorem redIncl_coe (x : redDom P D) : ((redIncl P D x : D) : F) = (x : F) := rfl

variable (T : D →ₗ[ℂ] F)

/-- The hypothesis that `P` preserves the domain of `T` and commutes with `T` on it. -/
structure Commutes (hPD : ∀ x ∈ D, P x ∈ D) : Prop where
  /-- `T (P x) = P (T x)` for `x` in the domain -/
  comm : ∀ x : D, T ⟨P (x : F), hPD _ x.2⟩ = P (T x)

variable {T}

/-- The reduced operator takes its values in the sector. -/
theorem map_mem_sector (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) (x : redDom P D) : T (redIncl P D x) ∈ sector P := by
  have hx : P ((x : F)) = (x : F) := hP.apply_of_mem_range (x : sector P).2
  have h1 : (⟨P ((redIncl P D x : D) : F), hPD _ (redIncl P D x).2⟩ : D) = redIncl P D x := by
    apply Subtype.ext
    simpa using hx
  have := hC.comm (redIncl P D x)
  rw [h1] at this
  exact ⟨T (redIncl P D x), this.symm⟩

variable (T) in
/-- The **part of `T` inside the sector**: the operator `T` restricted to `D ∩ K` and
regarded as an operator of the inner product space `K`. -/
def redOp (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D} (hC : Commutes T hPD) :
    redDom P D →ₗ[ℂ] sector P :=
  LinearMap.codRestrict (sector P) (T ∘ₗ redIncl P D) (map_mem_sector hP hC)

@[simp] theorem redOp_coe (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) (x : redDom P D) :
    ((redOp T hP hC x : sector P) : F) = T (redIncl P D x) := rfl

/-! ## Symmetry and the deficiency spaces -/







/-! ## The two sectors of a self-inverse isometry -/

variable (U : F →ₗ[ℂ] F)

/-- The symmetrizing projection `(1 + U)/2` of a self-inverse map `U`. -/
def symProj : F →ₗ[ℂ] F := (2⁻¹ : ℂ) • (LinearMap.id + U)

/-- The antisymmetrizing projection `(1 - U)/2` of a self-inverse map `U`. -/
def asymProj : F →ₗ[ℂ] F := (2⁻¹ : ℂ) • (LinearMap.id - U)

@[simp] theorem symProj_apply (x : F) : symProj U x = (2⁻¹ : ℂ) • (x + U x) := rfl

@[simp] theorem asymProj_apply (x : F) : asymProj U x = (2⁻¹ : ℂ) • (x - U x) := rfl

variable {U}



















/-! ## The sectors are the eigenspaces of `U` -/





end

end BookProof.ReducedEsa


