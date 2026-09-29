-- Prove2me | Definitions.Def_ChapterStrichartzWave
-- name    : ChapterStrichartzWave
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:46:24.858289+00:00
-- url     : https://prove2.me/theorems/56083068-b85c-4fd5-896c-eb23a2bf2873
-- title:
--   This module proves that the d'Alembertian
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.StrichartzWave`, source chapter `BookProof/ChapterStrichartzWave.lean`).
--
--   This module proves that the d'Alembertian
--
--   $$\Box = -\partial_t^2 + \Delta_x$$
--
--   on spacetime `ℝ^{1+n}`, together with a real constant potential, is **essentially self-adjoint** on `L²(ℝ^{1+n})` when taken on the Schwartz core. This is the Strichartz-type statement for hyperbolic wave operators: the (formally symmetric) operator has vanishing deficiency indices, so it possesses exactly one self-adjoint extension.
--
--   The proof follows the Fourier-multiplier route, which for a *constant-coefficient* operator replaces the light-cone cut-off/energy estimates of the variable-coefficient theory:
--
--   * Under the Fourier transform (a unitary of `L²` by Plancherel, available in Mathlib as `MeasureTheory.Lp.fourierTransformₗᵢ`) the operator `∑ i, c i • ∂_{w i}² + κ` becomes multiplication by the **real** symbol `symbolFn c w κ ξ = ∑ i, c i * (-4π²) * ⟪ξ, w i⟫² + κ`. * Symmetry is then immediate from realness of the symbol. * For the deficiency spaces: if `u ∈ L²` satisfies `⟪P v, u⟫ = z ⟪v, u⟫` for all `v` in the core and `Im z ≠ 0`, put `g = 𝓕 u`. Given any smooth compactly supported real `χ`, the function `ψ = χ / (symbol - conj z)` is again smooth with compact support (the denominator never vanishes because the symbol is real), hence Schwartz, and testing against `v = 𝓕⁻¹ ψ` gives `∫ χ • g = 0`. As `χ` is arbitrary, `g = 0`, so `u = 0`.
--
--   Everything is proved in the general setting of a finite-dimensional real inner product space `V` and an arbitrary finite family of directions `w : ι → V` with real coefficients `c : ι → ℝ`; the Minkowski signature `c = (-1, 1, …, 1)` gives the wave operator, and `c = (1, …, 1)` gives the Laplacian.
--
--   Essential self-adjointness is expressed with the deficiency-space predicates of `BookProof.ChapterFarisLavine` (`BookProof.FarisLavine.EssentiallySelfAdjointOn`), which are used throughout this project.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFreeFieldConstraint
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterU

import Mathlib

import Mathlib

/-!
# Essential self-adjointness of the wave operator on the Schwartz core

This module proves that the d'Alembertian

$$\Box = -\partial_t^2 + \Delta_x$$

on spacetime `ℝ^{1+n}`, together with a real constant potential, is **essentially
self-adjoint** on `L²(ℝ^{1+n})` when taken on the Schwartz core.  This is the
Strichartz-type statement for hyperbolic wave operators: the (formally symmetric)
operator has vanishing deficiency indices, so it possesses exactly one self-adjoint
extension.

The proof follows the Fourier-multiplier route, which for a *constant-coefficient*
operator replaces the light-cone cut-off/energy estimates of the variable-coefficient
theory:

* Under the Fourier transform (a unitary of `L²` by Plancherel, available in Mathlib as
  `MeasureTheory.Lp.fourierTransformₗᵢ`) the operator `∑ i, c i • ∂_{w i}² + κ` becomes
  multiplication by the **real** symbol
  `symbolFn c w κ ξ = ∑ i, c i * (-4π²) * ⟪ξ, w i⟫² + κ`.
* Symmetry is then immediate from realness of the symbol.
* For the deficiency spaces: if `u ∈ L²` satisfies `⟪P v, u⟫ = z ⟪v, u⟫` for all `v` in
  the core and `Im z ≠ 0`, put `g = 𝓕 u`.  Given any smooth compactly supported real
  `χ`, the function `ψ = χ / (symbol - conj z)` is again smooth with compact support
  (the denominator never vanishes because the symbol is real), hence Schwartz, and
  testing against `v = 𝓕⁻¹ ψ` gives `∫ χ • g = 0`.  As `χ` is arbitrary, `g = 0`, so
  `u = 0`.

Everything is proved in the general setting of a finite-dimensional real inner product
space `V` and an arbitrary finite family of directions `w : ι → V` with real
coefficients `c : ι → ℝ`; the Minkowski signature `c = (-1, 1, …, 1)` gives the wave
operator, and `c = (1, …, 1)` gives the Laplacian.

Essential self-adjointness is expressed with the deficiency-space predicates of
`BookProof.ChapterFarisLavine` (`BookProof.FarisLavine.EssentiallySelfAdjointOn`), which
are used throughout this project.
-/

namespace BookProof.StrichartzWave

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

/-! ## The operator and its symbol -/

/-- The second directional derivative `∂_m ∂_m` as a continuous linear map on Schwartz
space. -/
noncomputable def secondDeriv (m : V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  lineDerivOpCLM ℂ 𝓢(V, ℂ) m ∘L lineDerivOpCLM ℂ 𝓢(V, ℂ) m

/-- The constant-coefficient operator `∑ i, c i • ∂_{w i}² + κ` on Schwartz space.  For the
Minkowski signature `c = (-1, 1, …, 1)` and the standard coordinate directions this is the
d'Alembertian `□ = -∂_t² + Δ_x` plus the constant potential `κ`. -/
noncomputable def constCoeffOp (c : ι → ℝ) (w : ι → V) (κ : ℝ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  (∑ i, (c i : ℂ) • secondDeriv (w i)) + (κ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(V, ℂ)

/-- The (real!) symbol of `constCoeffOp c w κ`: with Mathlib's Fourier convention
`𝓕 f ξ = ∫ e^{-2πi⟪x,ξ⟫} f x`, the operator `∂_m²` becomes multiplication by
`-4π²⟪ξ, m⟫²`. -/
noncomputable def symbolFn (c : ι → ℝ) (w : ι → V) (κ : ℝ) (x : V) : ℝ :=
  (∑ i, c i * (-4 * Real.pi ^ 2) * (inner ℝ x (w i)) ^ 2) + κ







/-! ## The operator on `L²` -/

/-- The Schwartz core, as a submodule of `L²`. -/
noncomputable def schwartzDomain (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] :
    Submodule ℂ (Lp ℂ 2 (volume : Measure V)) :=
  LinearMap.range (toLpCLM ℂ ℂ 2 (volume : Measure V)).toLinearMap

/-- Schwartz functions are in bijection with the Schwartz core of `L²`. -/
noncomputable def schwartzEquiv (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] :
    𝓢(V, ℂ) ≃ₗ[ℂ] schwartzDomain V :=
  LinearEquiv.ofInjective (toLpCLM ℂ ℂ 2 (volume : Measure V)).toLinearMap
    (SchwartzMap.injective_toLp 2 (volume : Measure V))

/-- An operator on Schwartz space, viewed as an unbounded operator on `L²` with the Schwartz
core as its domain. -/
noncomputable def opL2 (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) :
    schwartzDomain V →ₗ[ℂ] Lp ℂ 2 (volume : Measure V) :=
  (toLpCLM ℂ ℂ 2 (volume : Measure V)).toLinearMap ∘ₗ T.toLinearMap ∘ₗ
    (schwartzEquiv V).symm.toLinearMap





/-! ## Elementary `L²` identities -/









/-! ## Symmetry -/



/-! ## Vanishing deficiency spaces -/







/-! ## Smooth cut-off functions

The Fourier-multiplier proof above needs no cut-offs, but the cut-off functions of the
variable-coefficient (energy-estimate) theory are recorded here: for every radius `R`
there is a smooth compactly supported `χ` with values in `[0,1]` which equals `1` on the
ball of radius `R` and has a bounded gradient. -/



/-! ## The wave operator on spacetime -/

/-- Spacetime `ℝ^{1+n}`: one time coordinate (index `0`) and `n` space coordinates. -/
abbrev SpaceTime (n : ℕ) := EuclideanSpace ℝ (Fin (1 + n))

/-- The Minkowski signature `(-1, +1, …, +1)`. -/
def minkowskiSign (n : ℕ) : Fin (1 + n) → ℝ := fun i => if i = 0 then -1 else 1

/-- The coordinate directions of spacetime. -/
noncomputable def coordDir (n : ℕ) : Fin (1 + n) → SpaceTime n := fun i =>
  EuclideanSpace.single i 1

/-- The d'Alembertian `□ = -∂_t² + Δ_x` with a real constant potential `κ`, as an operator on
the Schwartz space of spacetime. -/
noncomputable def waveOp (n : ℕ) (κ : ℝ) : 𝓢(SpaceTime n, ℂ) →L[ℂ] 𝓢(SpaceTime n, ℂ) :=
  constCoeffOp (minkowskiSign n) (coordDir n) κ





end BookProof.StrichartzWave


