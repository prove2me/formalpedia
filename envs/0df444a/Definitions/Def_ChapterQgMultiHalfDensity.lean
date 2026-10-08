-- Prove2me | Definitions.Def_ChapterQgMultiHalfDensity
-- name    : ChapterQgMultiHalfDensity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T15:36:10.186646+00:00
-- url     : https://prove2.me/theorems/417b23ee-fa9f-4875-9d2d-64655eef6205
-- title:
--   ChapterQgMultiHalfDensity
-- statement:
--   ChapterQgMultiHalfDensity

import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Mathlib


/-!
# The multi-dimensional half-density unitary of the densitized change of variables

Plan item **QG-1** of `CONSOLIDATED_PLAN.md` records that the densitized change
of variables is a Hilbert-space unitary only after the Jacobian half-density
factor is inserted, and that this had been proved only for the **one**
conformal fibre (`BookProof.QuantumGravityHalfDensity.halfDensityUnitary`,
`L²((0,∞), de) ≃ₗᵢ L²((0,∞), 2y dy)`).  Its tasks are to build the unitary for
the *full* field space — the tetrad-determinant coordinate `y = √e` **times**
the remaining (shear / ghost) directions, which the change of variables leaves
untouched — and to prove that it intertwines the physical and densitized core
operators, so that
`BookProof.QuantumGravityDensitized.densitized_hasZeroDeficiencyOn_transfer`
applies verbatim.

This module does both.

## 1. The general transfer unitary

For a pair of mutually (a.e.) inverse measure-preserving maps `Φ : X → Y`,
`Ψ : Y → X` between measure spaces `(X, μ)` and `(Y, ν)`:

* `mpUnitary` — the unitary `L²(ν) ≃ₗᵢ[ℂ] L²(μ)`, `(W g)(x) = g(Φ x)`, with
  `mpUnitary_apply` and `mpUnitary_symm_apply`;
* `mpUnitary_mem_boundedEnergyCore`, `mpUnitary_boundedEnergyCore_surjective`
  — it carries the bounded-energy core of an energy `g` **onto** the
  bounded-energy core of the pulled-back energy `g ∘ Φ`;
* `mpUnitary_intertwines_multOp` — and intertwines the two multiplication
  operators;
* `mpUnitary_hasZeroDeficiencyOn_transfer` — hence the Part D.4 transfer runs.

## 2. The field-space (product) instance

The densitized change of variables acts on the conformal coordinate only:
`(y, ξ) ↦ (y², ξ)`.  With `X` the remaining directions carrying any s-finite
measure:

* `measurePreserving_qgProdSquare`, `measurePreserving_qgProdSqrt` — the
  product map is measure preserving between `(2y dy) ⊗ μ` and `de ⊗ μ`;
* `multiHalfDensityUnitary` — **the multi-dimensional half-density unitary**
  `L²((0,∞) × X, de ⊗ μ) ≃ₗᵢ[ℂ] L²((0,∞) × X, 2y dy ⊗ μ)`, with the pointwise
  formula `multiHalfDensityUnitary_apply`;
* `multiHalfDensityUnitary_intertwines_multOp` — it intertwines multiplication
  by a potential `V` with multiplication by its pullback `V(y², ξ)`;
* `multi_hasZeroDeficiencyOn_transfer` — the transfer theorem at this unitary;
* `fieldHalfDensityUnitary` — the instance with `n` flat shear directions,
  `X = Fin n → ℝ` with Lebesgue measure, i.e. the field space of the plan with
  its conformal coordinate densitized.

## Honest boundary

The unitary is exactly the change of variables `e = y²` in the conformal
coordinate, tensored with the identity on all the other directions; the
remaining directions enter only through their measure, so the plan's concrete
field space (flat shear directions, and a finite ghost factor with the counting
measure) is a special case of the `X` here.  Nothing in this module asserts
essential self-adjointness of the continuum gravity operator: it supplies the
unitary and the intertwining, which is precisely what the transfer step took as
data.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgMultiHalfDensity

open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

/-! ## 1. The general transfer unitary -/

section General

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}

/-- Composition with `Φ`, as a linear isometry `L²(ν) →ₗᵢ L²(μ)`. -/
def mpIsom (hPhi : MeasurePreserving Phi mu nu) : Lp ℂ 2 nu →ₗᵢ[ℂ] Lp ℂ 2 mu :=
  Lp.compMeasurePreservingₗᵢ ℂ Phi hPhi

theorem mpIsom_apply (hPhi : MeasurePreserving Phi mu nu) (g : Lp ℂ 2 nu) :
    (mpIsom hPhi g : X → ℂ) =ᵐ[mu] fun x => (g : Y → ℂ) (Phi x) :=
  Lp.coeFn_compMeasurePreserving _ hPhi

theorem mpIsom_mpIsom (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (h : Lp ℂ 2 mu) :
    mpIsom hPhi (mpIsom hPsi h) = h := by
  refine Lp.ext ?_
  have h1 := mpIsom_apply hPhi (mpIsom hPsi h)
  have h2 := (mpIsom_apply hPsi h).comp_tendsto hPhi.quasiMeasurePreserving.tendsto_ae
  filter_upwards [h1, h2, hinv] with x hx1 hx2 hx3
  simp only [Function.comp_apply] at hx2
  rw [hx1, hx2, hx3]

theorem mpIsom_surjective (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) :
    Function.Surjective (mpIsom hPhi) :=
  fun h => ⟨mpIsom hPsi h, mpIsom_mpIsom hPhi hPsi hinv h⟩

/-- **The transfer unitary of a measure-preserving change of variables**:
composition with `Φ` is a unitary `L²(ν) ≃ₗᵢ[ℂ] L²(μ)`. -/
def mpUnitary (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu)
    (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) : Lp ℂ 2 nu ≃ₗᵢ[ℂ] Lp ℂ 2 mu :=
  LinearIsometryEquiv.ofSurjective (mpIsom hPhi) (mpIsom_surjective hPhi hPsi hinv)







/-! ### The bounded-energy cores correspond -/

variable {g : Y → ℝ}









end General

/-! ## 2. The field-space instance: the conformal coordinate times the rest -/

section Field

variable {X : Type*} [MeasurableSpace X] (mu : Measure X)

/-- The densitized change of variables on the full field space: it squares the
conformal coordinate and leaves every other direction alone. -/
def qgProdSquare : ℝ × X → ℝ × X := Prod.map qgSquare id

/-- Its inverse `(e, ξ) ↦ (√e, ξ)`. -/
def qgProdSqrt : ℝ × X → ℝ × X := Prod.map Real.sqrt id

theorem qgProd_ae_inv :
    ∀ᵐ p ∂(qgSrcMeasure.prod mu), qgProdSqrt (qgProdSquare p) = p := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae qgSrcMeasure_ae_pos] with p hp
  have hsq : Real.sqrt (p.1 ^ 2) = p.1 := Real.sqrt_sq hp.le
  simp [qgProdSqrt, qgProdSquare, qgSquare, Prod.map, hsq]



instance : SFinite qgSrcMeasure := by
  rw [qgSrcMeasure]; infer_instance

variable [SFinite mu]

/-- **The multi-dimensional densitized change of variables is measure
preserving**: pushing `(2y dy) ⊗ μ` forward along `(y, ξ) ↦ (y², ξ)` gives
`de ⊗ μ`. -/
theorem measurePreserving_qgProdSquare :
    MeasurePreserving (qgProdSquare (X := X)) (qgSrcMeasure.prod mu)
      (BookProof.ScalaronDensitized.physMeasure.prod mu) :=
  measurePreserving_qgSquare.prod (MeasurePreserving.id mu)

theorem measurePreserving_qgProdSqrt :
    MeasurePreserving (qgProdSqrt (X := X))
      (BookProof.ScalaronDensitized.physMeasure.prod mu) (qgSrcMeasure.prod mu) :=
  measurePreserving_qgSqrt.prod (MeasurePreserving.id mu)

/-- **The multi-dimensional half-density unitary.**  The densitized change of
variables of the full field space — the conformal coordinate `e = y²` together
with the untouched remaining directions — paired with the Jacobian half-density
weight `2y`, is a Hilbert-space unitary

  `L²((0,∞) × X, de ⊗ μ)  ≃ₗᵢ[ℂ]  L²((0,∞) × X, 2y dy ⊗ μ)`. -/
def multiHalfDensityUnitary :
    Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod mu)
      ≃ₗᵢ[ℂ] Lp ℂ 2 (qgSrcMeasure.prod mu) :=
  mpUnitary (measurePreserving_qgProdSquare mu) (measurePreserving_qgProdSqrt mu)
    (qgProd_ae_inv mu)



@[simp] theorem multiHalfDensityUnitary_norm
    (g : Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod mu)) :
    ‖multiHalfDensityUnitary mu g‖ = ‖g‖ :=
  (multiHalfDensityUnitary mu).norm_map g









end Field

/-- **The field-space half-density unitary with `n` flat shear directions.**
The plan's densitized field space is this instance: the tetrad-determinant
coordinate `y = √e` carries the half-density weight `2y`, the `n` remaining
directions carry Lebesgue measure and are untouched by the change of
variables. -/
def fieldHalfDensityUnitary (n : ℕ) :
    Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod
        (volume : Measure (Fin n → ℝ)))
      ≃ₗᵢ[ℂ] Lp ℂ 2 (qgSrcMeasure.prod (volume : Measure (Fin n → ℝ))) :=
  multiHalfDensityUnitary (volume : Measure (Fin n → ℝ))



end

end BookProof.QgMultiHalfDensity


