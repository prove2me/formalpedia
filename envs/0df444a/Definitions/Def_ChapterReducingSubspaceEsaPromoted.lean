-- Prove2me | Definitions.Def_ChapterReducingSubspaceEsaPromoted
-- name    : ChapterReducingSubspaceEsaPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-09T10:26:53.169193+00:00
-- url     : https://prove2.me/theorems/43fb3d45-32ec-4571-aeb2-6e697847ca04
-- title:
--   Reducing projections: redDom, redOp and the reduction lemmas
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterReducingSubspaceEsa.lean`): the platform's served `Def_ChapterReducingSubspaceEsa` copy is a skeleton (no declarations), so consumers that cite `IsReducingProjection`, `redDom`, `redOp` and the reduction lemmas die with `unknown identifier`, and published bundles are immutable, so the fix is a new bundle name that keeps the original namespace (the new-name route, PIPELINE_PLAN §2.13). This bundle re-carries the chapter's full body in `BookProof.ReducedEsa`: the notion of a reducing projection of an inner product space, the reduced domain `redDom` and the reduced operator `redOp` together with the compatibility conditions that make them well defined, and the results showing that symmetry, essential self-adjointness and graph-core density pass to the reduced operator. Consumers add a single `import Definitions.Def_ChapterReducingSubspaceEsaPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterReducingSubspaceEsa.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterReducingSubspaceEsa` copy is a
-- skeleton (no declarations at all), so `open BookProof.ReducedEsa` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterReducingSubspaceEsaPromoted`.
import Definitions.Def_ChapterGraphCoreTransferPromoted
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

theorem mem_redDom_iff {x : sector P} : x ∈ redDom P D ↔ (x : F) ∈ D := Iff.rfl

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

/-- The reduced operator of a symmetric operator is symmetric. -/
theorem symmetricOn_redOp (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) (hT : SymmetricOn D T) :
    SymmetricOn (redDom P D) (redOp T hP hC) := by
  intro x y
  have hx := hT (redIncl P D x) (redIncl P D y)
  simpa [Submodule.coe_inner] using hx

/-- **The deficiency spaces of the reduced operator are contained in those of `T`.**  A
vector `w` of the sector annihilating `T - z̄` on `D ∩ K` annihilates it on all of `D`,
because `⟪T v, w⟫ = ⟪P (T v), w⟫ = ⟪T (P v), w⟫` and `P v` lies in `D ∩ K`. -/
theorem deficiencyTrivialAt_red (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) {z : ℂ} (hz : DeficiencyTrivialAt D T z) :
    DeficiencyTrivialAt (redDom P D) (redOp T hP hC) z := by
  intro w hw
  set W : F := (w : F) with hW
  have hPW : P W = W := hP.apply_of_mem_range (w : sector P).2
  have key : ∀ v : D, (inner ℂ (T v) W : ℂ) = z * inner ℂ (v : F) W := by
    intro v
    -- the projected vector, as an element of the reduced domain
    have hPv : P (v : F) ∈ D := hPD _ v.2
    set v' : redDom P D := ⟨⟨P (v : F), ⟨(v : F), rfl⟩⟩, hPv⟩ with hv'
    have h1 : (inner ℂ (T ⟨P (v : F), hPv⟩) W : ℂ) = z * inner ℂ (P (v : F)) W := by
      have h2 := hw v'
      simp only [hv', redOp_coe, Submodule.coe_inner] at h2
      have hinc : (redIncl P D) ⟨⟨P (v : F), ⟨(v : F), rfl⟩⟩, hPv⟩ = ⟨P (v : F), hPv⟩ := rfl
      rw [hinc] at h2
      rw [hW]
      exact h2
    have h2 : (inner ℂ (T v) W : ℂ) = inner ℂ (P (T v)) W := by
      rw [hP.symm (T v) W, hPW]
    have h3 : (inner ℂ (P (T v)) W : ℂ) = inner ℂ (T ⟨P (v : F), hPv⟩) W := by
      rw [hC.comm v]
    have h4 : (inner ℂ (P (v : F)) W : ℂ) = inner ℂ (v : F) W := by
      rw [hP.symm (v : F) W, hPW]
    rw [h2, h3, h1, h4]
  have hW0 : W = 0 := hz W key
  exact Subtype.ext (by simpa [hW] using hW0)

/-- **Reduction of essential self-adjointness to an invariant sector.** -/
theorem essentiallySelfAdjointOn_red (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) (hesa : EssentiallySelfAdjointOn D T) :
    EssentiallySelfAdjointOn (redDom P D) (redOp T hP hC) :=
  ⟨deficiencyTrivialAt_red hP hC hesa.1, deficiencyTrivialAt_red hP hC hesa.2⟩

/-! ## The two sectors of a self-inverse isometry -/

variable (U : F →ₗ[ℂ] F)

/-- The symmetrizing projection `(1 + U)/2` of a self-inverse map `U`. -/
def symProj : F →ₗ[ℂ] F := (2⁻¹ : ℂ) • (LinearMap.id + U)

/-- The antisymmetrizing projection `(1 - U)/2` of a self-inverse map `U`. -/
def asymProj : F →ₗ[ℂ] F := (2⁻¹ : ℂ) • (LinearMap.id - U)

@[simp] theorem symProj_apply (x : F) : symProj U x = (2⁻¹ : ℂ) • (x + U x) := rfl

@[simp] theorem asymProj_apply (x : F) : asymProj U x = (2⁻¹ : ℂ) • (x - U x) := rfl

variable {U}

/-- A self-inverse isometry is symmetric: `⟪U x, y⟫ = ⟪x, U y⟫`. -/
theorem symmetric_of_involutive_isometry (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) (x y : F) :
    (inner ℂ (U x) y : ℂ) = inner ℂ x (U y) := by
  have := hUi x (U y)
  rw [hU2 y] at this
  exact this

/-- `(1 + U)/2` is a reducing projection. -/
theorem isReducingProjection_symProj (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) :
    IsReducingProjection (symProj U) where
  idem x := by
    simp only [symProj_apply, map_smul, map_add, hU2]
    rw [smul_add, smul_smul]
    module
  symm x y := by
    simp only [symProj_apply, inner_smul_left, inner_smul_right, inner_add_left,
      inner_add_right, symmetric_of_involutive_isometry hU2 hUi x y, map_inv₀, map_ofNat]

/-- `(1 - U)/2` is a reducing projection. -/
theorem isReducingProjection_asymProj (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) :
    IsReducingProjection (asymProj U) where
  idem x := by
    simp only [asymProj_apply, map_smul, map_sub, hU2]
    rw [smul_sub, smul_smul]
    module
  symm x y := by
    simp only [asymProj_apply, inner_smul_left, inner_smul_right, inner_sub_left,
      inner_sub_right, symmetric_of_involutive_isometry hU2 hUi x y, map_inv₀, map_ofNat]

/-- If `U` preserves the domain then so does `(1 + U)/2`. -/
theorem symProj_mem (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, symProj U x ∈ D := by
  intro x hx
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx (hUD x hx))

/-- If `U` preserves the domain then so does `(1 - U)/2`. -/
theorem asymProj_mem (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, asymProj U x ∈ D := by
  intro x hx
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx (hUD x hx))

/-- If `U` commutes with `T` then so does `(1 + U)/2`. -/
theorem commutes_symProj {hUD : ∀ x ∈ D, U x ∈ D}
    (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x)) :
    Commutes T (symProj_mem (D := D) hUD) where
  comm x := by
    have hsplit : (⟨symProj U (x : F), symProj_mem (D := D) hUD _ x.2⟩ : D)
        = (2⁻¹ : ℂ) • ((x : D) + ⟨U (x : F), hUD _ x.2⟩) := by
      apply Subtype.ext
      simp [symProj]
    rw [hsplit, map_smul, map_add, hTU x]
    simp [symProj]

/-- If `U` commutes with `T` then so does `(1 - U)/2`. -/
theorem commutes_asymProj {hUD : ∀ x ∈ D, U x ∈ D}
    (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x)) :
    Commutes T (asymProj_mem (D := D) hUD) where
  comm x := by
    have hsplit : (⟨asymProj U (x : F), asymProj_mem (D := D) hUD _ x.2⟩ : D)
        = (2⁻¹ : ℂ) • ((x : D) - ⟨U (x : F), hUD _ x.2⟩) := by
      apply Subtype.ext
      simp [asymProj]
    rw [hsplit, map_smul, map_sub, hTU x]
    simp [asymProj]

/-- **Essential self-adjointness on the symmetric sector** `U x = x`. -/
theorem essentiallySelfAdjointOn_symSector (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y)
    {hUD : ∀ x ∈ D, U x ∈ D} (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x))
    (hesa : EssentiallySelfAdjointOn D T) :
    EssentiallySelfAdjointOn (redDom (symProj U) D)
      (redOp T (isReducingProjection_symProj hU2 hUi) (commutes_symProj hTU)) :=
  essentiallySelfAdjointOn_red _ _ hesa

/-- **Essential self-adjointness on the antisymmetric sector** `U x = -x`. -/
theorem essentiallySelfAdjointOn_asymSector (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y)
    {hUD : ∀ x ∈ D, U x ∈ D} (hTU : ∀ x : D, T ⟨U (x : F), hUD _ x.2⟩ = U (T x))
    (hesa : EssentiallySelfAdjointOn D T) :
    EssentiallySelfAdjointOn (redDom (asymProj U) D)
      (redOp T (isReducingProjection_asymProj hU2 hUi) (commutes_asymProj hTU)) :=
  essentiallySelfAdjointOn_red _ _ hesa

/-! ## The sectors are the eigenspaces of `U` -/



/-- The range of `(1 - U)/2` is exactly the `-1` eigenspace of `U`. -/
theorem mem_sector_asymProj_iff (hU2 : ∀ x, U (U x) = x) {x : F} :
    x ∈ sector (asymProj U) ↔ U x = -x := by
  constructor
  · rintro ⟨u, rfl⟩
    simp only [asymProj_apply, map_smul, map_sub, hU2]
    rw [smul_sub, smul_sub]
    abel
  · intro hx
    exact ⟨x, by simp [asymProj, hx]; module⟩

end

end BookProof.ReducedEsa


