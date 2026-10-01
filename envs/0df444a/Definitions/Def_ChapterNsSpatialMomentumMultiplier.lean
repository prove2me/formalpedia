-- Prove2me | Definitions.Def_ChapterNsSpatialMomentumMultiplier
-- name    : ChapterNsSpatialMomentumMultiplier
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:43:12.605382+00:00
-- url     : https://prove2.me/theorems/f6c5e814-a6b1-4817-a43d-5af052cab683
-- title:
--   Chapter NsSpatialMomentumMultiplier
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsSpatialMomentumMultiplier.lean`): generated def bundle for ChapterNsSpatialMomentumMultiplier. See BookProof/ChapterNsSpatialMomentumMultiplier.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsSpatialMomentumMultiplier.lean

import Definitions.Def_ChapterFourierMultiplierEsa
import Mathlib


/-!
# The Plancherel identification and the diagonal spatial derivative

Part of item 1 of the Navier–Stokes plan items of `CONSOLIDATED_PLAN.md`: *the spatial Fourier
unitary and the diagonal derivative*.  The item asks for the Plancherel identification of the
one-particle space and for the statement that on it the spatial derivative `−i ∂_{x_j}` is the
Fourier multiplier of the real symbol `p_j`.

What is proved here, for an arbitrary finite-dimensional real inner-product space `V` carrying the
volume measure:

* `l2Fourier` — the Plancherel identification of `L²(V)` with itself in the momentum variable, as a
  linear isometry equivalence (Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ`), with
  `l2Fourier_norm` and `l2Fourier_inner` the unitarity statements;
* `fourier_opL2_eq_mulSymbol` — **the multiplier statement at the `L²` level**: if the Fourier
  transform turns a Schwartz operator `P` into multiplication by the real symbol `σ`, then on the
  Schwartz core the Plancherel identification carries the `L²` realization of `P` to multiplication
  by `σ`.  This upgrades the pointwise Schwartz-space identity of
  `BookProof.FourierMultiplierEsa` to the Hilbert space where the operator lives;
* `fourier_opL2_firstOrderOp` and `fourier_opL2_momentumOp` — the specialization to the momentum
  operators: `∑_j c_j (−i ∂_{w_j})` becomes multiplication by `∑_j 2π c_j ⟪ξ, w_j⟫`, and `−i ∂_m`
  becomes multiplication by `2π ⟪ξ, m⟫` — the real symbol `p_j` of the plan item;
* `foSymbolFn_add_fibre` and `foSymbolFn_congr_of_inner_eq` — **the derivative is diagonal in the
  spatial momentum and blind to the fibre**: the symbol of a family of *spatial* directions is
  unchanged when the frequency is moved by any vector orthogonal to all of them, so it depends on
  the spatial frequency only;
* `spatialMomentum_esa` — essential self-adjointness of the spatial momentum family on the
  Schwartz core (`BookProof.FourierMultiplierEsa.firstOrderOp_essentiallySelfAdjoint`), so the
  derivative side of the construction is a proved instrument.

**Honest boundary.**  The identification used is the *full* Plancherel transform of `L²(V)`; the
partial ("spatial-only") transform `L²(ℝ_x^d × ℝ_u^m) ≅ L²(ℝ_p^d × ℝ_u^m)`, which transforms the
spatial variable and leaves the fibre variable alone, is **not** constructed here.  What is proved
instead is that the symbol of a spatial derivative does not see the fibre frequency
(`foSymbolFn_add_fibre`), which is the content the route uses: the spatial derivative is diagonal
in the spatial momentum and acts as the identity on the fibre.  The remaining part of plan item 1
is therefore the construction of the partial transform itself.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsSpatialMultiplier

open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

/-! ## 1. The Plancherel identification -/

variable (V) in
/-- **The Plancherel identification** of `L²(V)` with the momentum-side `L²(V)`: the Fourier
transform as a linear isometry equivalence. -/
def l2Fourier : (Lp ℂ 2 (volume : Measure V)) ≃ₗᵢ[ℂ] (Lp ℂ 2 (volume : Measure V)) :=
  MeasureTheory.Lp.fourierTransformₗᵢ V ℂ







/-! ## 2. Multiplication by a real symbol, and the multiplier statement on `L²` -/

/-- Multiplication by a real symbol, on Schwartz space. -/
def mulSymbolOp (σ : V → ℝ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  smulLeftCLM ℂ (fun x => ((σ x : ℝ) : ℂ))





/-! ## 3. The symbol of the momentum operators, as a continuous linear functional -/

/-- The symbol `ξ ↦ ∑_j 2π c_j ⟪ξ, w_j⟫` of `∑_j c_j (−i ∂_{w_j})`, as a continuous linear
functional — which is what makes it a function of temperate growth. -/
def foSymbolCLM (c : ι → ℝ) (w : ι → V) : V →L[ℝ] ℝ :=
  ∑ i, (2 * Real.pi * c i) • ((innerSL ℝ).flip (w i))





/-! ## 4. The momentum operator is multiplication by the momentum -/





/-! ## 5. The spatial symbol is blind to the fibre -/





/-! ## 6. The concrete picture `ℝ_x^d × ℝ_u^m` -/



/-! ## 7. Essential self-adjointness of the spatial momentum family -/



end

end BookProof.NsSpatialMultiplier


