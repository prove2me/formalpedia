-- Prove2me | Definitions.Def_ChapterNsScalarFourier
-- name    : ChapterNsScalarFourier
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T14:46:00.210089+00:00
-- url     : https://prove2.me/theorems/eeae3b6a-9147-4fe8-b6e7-c6f61cfb710b
-- title:
--   Chapter NsScalarFourier
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsScalarFourier.lean`): generated def bundle for ChapterNsScalarFourier. See BookProof/ChapterNsScalarFourier.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsScalarFourier.lean

import Definitions.Def_ChapterNsPartialFourier
import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterA4
import Mathlib


/-!
# The spatial-only Fourier transform on the **scalar** one-particle space

`BookProof.ChapterNsPartialFourier` built the partial (spatial-only) Fourier transform on the
*fibred* model `L²(V; L²(W))` of the Navier–Stokes one-particle space, and
`BookProof.ChapterNsScalarVectorCurry` identified that model with the *scalar* one,
`L²(V × W)`, by the unitary `curryLI`.  This module is what the identification unblocks: the
spatial transform **on the scalar space of two variables**, obtained by conjugation,

* `nsScalarFourier : L²(V × W) ≃ₗᵢ[ℂ] L²(V × W)` — `curryLI ∘ nsPartialFourier ∘ curryLI.symm`,
  with `nsScalarFourier_norm` its Plancherel identity;
* `scalarFibreOp T` — an operator of the fibre variable alone, transported to the scalar space;
  `scalarFibreOp_prodMk` identifies it on the product generators as the expected `1 ⊗ T`,
  `(x, y) ↦ a x * c y ↦ (x, y) ↦ a x * (T c) y`;
* `nsScalarFourier_scalarFibreOp` — the fibre-blindness of the spatial transform, now stated on
  the scalar space: the spatial transform commutes with every operator `1 ⊗ T` of the fibre
  variable;
* `nsScalarFourier_prodMk_eq` — the transform, computed on a product generator, is again the
  scalar picture of the corresponding fibred computation.

Everything here is a conjugation of a proved statement by a proved unitary; no new analysis
enters.
-/

open MeasureTheory

namespace BookProof.NsScalarFourier

open BookProof.NsPartialFourier BookProof.NsScalarVectorCurry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable (V W) in
/-- **The spatial-only Fourier transform of the scalar Navier–Stokes one-particle space**
`L²(ℝ^d_x × ℝ^m_u)`: the fibred transform of `ChapterNsPartialFourier`, conjugated by the
scalar–vector identification `curryLI`. -/
def nsScalarFourier :
    Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W)) :=
  (curryLI.symm.trans (nsPartialFourier V W)).trans curryLI





variable (V) in
/-- An operator **of the fibre variable alone**, on the scalar space of two variables: the
pointwise action of `T` in the fibre, transported by `curryLI`.  On the product generators it is
`1 ⊗ T` (`scalarFibreOp_prodMk`). -/
def scalarFibreOp (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W)) :
    Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure V).prod (volume : Measure W)) :=
  (curryLI.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((fibreOp V T).comp (curryLI.symm.toContinuousLinearEquiv.toContinuousLinearMap))













end

end BookProof.NsScalarFourier


