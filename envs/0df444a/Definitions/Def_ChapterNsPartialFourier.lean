-- Prove2me | Definitions.Def_ChapterNsPartialFourier
-- name    : ChapterNsPartialFourier
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:32:26.248964+00:00
-- url     : https://prove2.me/theorems/85d2e11a-3d29-4183-9816-f43cc560785e
-- title:
--   Chapter NsPartialFourier
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsPartialFourier.lean`): generated def bundle for ChapterNsPartialFourier. See BookProof/ChapterNsPartialFourier.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsPartialFourier.lean

import Mathlib


/-!
# The partial (spatial-only) Fourier transform on the fibred one-particle space

This module continues item 1 of the Navier–Stokes plan items of `CONSOLIDATED_PLAN.md`, *the
spatial Fourier unitary and the diagonal derivative*.  The module
`BookProof.ChapterNsSpatialMomentumMultiplier` did the multiplier half on `L²(V)`; the part left
open there was the **partial** transform — the one that transforms the spatial variable and leaves
the fibre variable alone.

The fibred model used here is the vector-valued one: the one-particle space is
`L²(V; F) = Lp F 2 (volume : Measure V)`, functions of the spatial variable `x ∈ V` with values in
the fibre Hilbert space `F`; for the Navier–Stokes route `F` is itself an `L²` space of the fibre
variable, `F = L²(W)` (§4 below).  On this space:

* `partialFourier` — the Plancherel identification `L²(V; F) ≃ₗᵢ[ℂ] L²(V; F)` in the *spatial*
  variable only, with `partialFourier_norm` and `partialFourier_inner` its unitarity;
* `partialFourier_fibreOp` — **the transform leaves the fibre alone**: it commutes with the
  pointwise action of *every* bounded operator of the fibre, `𝓕 ∘ (T ·) = (T ·) ∘ 𝓕`.  This is the
  precise content of "partial": nothing at all happens in the fibre variable.  Proved by density
  of the Schwartz functions from the Schwartz-level identity `fourier_postcompCLM`;
* `fourier_vecMomentumOp_apply` — **the diagonal spatial derivative**: for a fibre-valued Schwartz
  function the transform carries `π_m = −i ∂_m` to multiplication by the real symbol
  `2π ⟪ξ, m⟫`, exactly the scalar symbol of `BookProof.FourierMultiplierEsa`, in particular one
  that does not involve the fibre;
* `postcompCLM_vecMomentumOp` — the spatial derivative itself commutes with every fibre operator;
* §4 — the concrete Navier–Stokes instance `F = L²(W)`: `nsPartialFourier` is the spatial-only
  transform of `L²(V; L²(W))`, `nsPartialFourier_fibreOp` says it commutes with every operator of
  the fibre variable, and `nsPartialFourier_fibreFourier` that it commutes in particular with the
  Fourier transform *of the fibre variable*, whose composite with it is the full transform in both
  variables (`nsPartialFourier_comp_fibreFourier_eq`).

Auxiliary and of independent use: `postcompCLM`, the postcomposition of a Schwartz function with a
continuous linear map of the target, which Mathlib does not provide, together with its Fourier
(`fourier_postcompCLM`), `L²` (`toLp_postcompCLM`) and derivative (`postcompCLM_lineDerivOp`)
compatibilities.

**The model.**  The model used here is the vector-valued one, `L²(V; L²(W))`.  Its
measure-theoretic identification with the scalar `L²(V × W)` — which Mathlib does not have — is
now formalized in `BookProof.ChapterNsScalarVectorCurry` (`curryLI`, pinned down on the
generators by `curryLI_fibMk` and `curryLI_indicator_prod`), and
`BookProof.ChapterNsScalarFourier` transports the transform of this module to the scalar space
by it (`nsScalarFourier`, with `nsScalarFourier_scalarFibreOp` for the fibre-blindness).

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsPartialFourier

open MeasureTheory SchwartzMap FourierTransform LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ## 1. Postcomposition of a Schwartz function with an operator of the target -/

section Postcomp

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- **Postcomposition with a continuous linear map of the target**, as a continuous linear map of
Schwartz spaces: `f ↦ T ∘ f`.  (Mathlib has precomposition, `SchwartzMap.compCLM`, but not this.) -/
def postcompCLM (T : F →L[ℂ] G) : 𝓢(V, F) →L[ℂ] 𝓢(V, G) :=
  SchwartzMap.bilinLeftCLM (((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] G →L[ℂ] G).flip).comp T)
    (g := fun _ : V => (1 : ℂ)) (Function.HasTemperateGrowth.const _)











end Postcomp

/-! ## 2. The partial transform and its fibre-blindness -/

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (V F) in
/-- **The partial (spatial-only) Fourier transform** of the fibred one-particle space
`L²(V; F)`: Plancherel in the spatial variable `x ∈ V`, with the fibre `F` untouched. -/
def partialFourier : (Lp F 2 (volume : Measure V)) ≃ₗᵢ[ℂ] (Lp F 2 (volume : Measure V)) :=
  MeasureTheory.Lp.fourierTransformₗᵢ V F







variable (V) in
/-- An operator **of the fibre alone**, acting pointwise in the spatial variable. -/
def fibreOp (T : F →L[ℂ] G) :
    Lp F 2 (volume : Measure V) →L[ℂ] Lp G 2 (volume : Measure V) :=
  T.compLpL 2 (volume : Measure V)





/-! ## 3. The diagonal spatial derivative in the fibred space -/

/-- The spatial momentum operator `π_m = −i ∂_m` on fibre-valued Schwartz functions. -/
def vecMomentumOp (m : V) : 𝓢(V, F) →L[ℂ] 𝓢(V, F) :=
  (-Complex.I) • lineDerivOpCLM ℂ 𝓢(V, F) m







/-! ## 4. The Navier–Stokes instance: the fibre is an `L²` space -/

section Concrete

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable (V W) in
/-- **The spatial-only Fourier transform of the fibred Navier–Stokes one-particle space.**  The
space is `L²(V; L²(W))` — square-integrable functions of the spatial variable `x ∈ V` with values
in the fibre space `L²(W)` of the fibre variable `u ∈ W` — and the transform acts in `x` only. -/
def nsPartialFourier :
    (Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) ≃ₗᵢ[ℂ]
      (Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) :=
  partialFourier V (Lp ℂ 2 (volume : Measure W))





variable (W) in
/-- The Fourier transform **of the fibre variable**, as an operator of the fibre. -/
def fibreFourierCLM : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W) :=
  (MeasureTheory.Lp.fourierTransformₗᵢ W ℂ).toLinearIsometry.toContinuousLinearMap





end Concrete

end

end BookProof.NsPartialFourier


