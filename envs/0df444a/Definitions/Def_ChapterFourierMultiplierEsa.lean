-- Prove2me | Definitions.Def_ChapterFourierMultiplierEsa
-- name    : ChapterFourierMultiplierEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:56:11.505712+00:00
-- url     : https://prove2.me/theorems/5009da8a-9fcf-4340-a72f-c17f36e6bfd0
-- title:
--   Chapter FourierMultiplierEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFourierMultiplierEsa.lean`): generated def bundle for ChapterFourierMultiplierEsa. See BookProof/ChapterFourierMultiplierEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFourierMultiplierEsa.lean

import Definitions.Def_ChapterStrichartzWave
import Mathlib


/-!
# Essential self-adjointness of Fourier multipliers with a real symbol

`BookProof.ChapterStrichartzWave` proves that the *second-order* constant-coefficient
operator `∑ᵢ cᵢ ∂_{wᵢ}² + κ` is essentially self-adjoint on the Schwartz core of `L²(V)`,
by the Fourier-multiplier route: under Plancherel the operator becomes multiplication by
its real symbol, symmetry is immediate, and the deficiency equation is killed by dividing
a test function by `symbol − z̄`.

That argument never uses the *shape* of the operator: it uses only that the operator is a
Fourier multiplier with a **real, smooth** symbol.  This module extracts it as a reusable
instrument and applies it to the operators the second-order family could not reach — the
*first-order* ones.

## What is proved

* `symmetricOn_of_real_symbol`, `deficiencyTrivialAt_of_real_symbol`,
  `essentiallySelfAdjointOn_of_real_symbol` — **the instrument**: any continuous linear
  operator `P` on Schwartz space which the Fourier transform turns into multiplication by
  a real, smooth function `σ` is symmetric and essentially self-adjoint on the Schwartz
  core of `L²(V)`;
* `foSymbolFn`, `fourier_firstOrderOp_apply` — the first-order operator
  `∑ᵢ cᵢ πᵢ`, `πᵢ = −i ∂_{wᵢ}`, is the Fourier multiplier with the real symbol
  `∑ᵢ 2π cᵢ ⟪ξ, wᵢ⟫`;
* `firstOrderOp_essentiallySelfAdjoint` — **the momentum operator is essentially
  self-adjoint** on the Schwartz core, for an arbitrary finite family of directions and
  arbitrary real coefficients; `momentumOp_essentiallySelfAdjoint` is the one-direction
  case `−i ∂_m`;
* `mixedOp_essentiallySelfAdjoint` — the full real-symbol constant-coefficient operator
  `∑ᵢ cᵢ ∂_{wᵢ}² + ∑ᵢ aᵢ (−i ∂_{wᵢ}) + κ`, second order plus first order plus a constant,
  is essentially self-adjoint on the same core.

The last statement covers the *kernel directions* of the quadratic family of
`BookProof.ChapterShiftedQuadraticDegenerate`, in the case where only the momentum
coefficient survives: there `H` degenerates to `∑ᵢ b'ᵢ πᵢ`, which has no `L²` eigenvector,
so the Hermite-eigenbasis argument used for the quadratic family cannot see it, while the
Fourier multiplier argument here handles it directly.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.FourierMultiplierEsa

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

/-! ## 1. The instrument: a real symbol gives essential self-adjointness -/









/-! ## 2. The first-order (momentum) operator -/

/-- The momentum operator `π_m = −i ∂_m` on Schwartz space. -/
noncomputable def momentumOp (m : V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  (-Complex.I) • lineDerivOpCLM ℂ 𝓢(V, ℂ) m

/-- The general first-order operator `∑ᵢ cᵢ π_{wᵢ}` with real coefficients. -/
noncomputable def firstOrderOp (c : ι → ℝ) (w : ι → V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  ∑ i, (c i : ℂ) • momentumOp (w i)

/-- The (real!) symbol of `firstOrderOp c w`: `∑ᵢ 2π cᵢ ⟪ξ, wᵢ⟫`. -/
noncomputable def foSymbolFn (c : ι → ℝ) (w : ι → V) (x : V) : ℝ :=
  ∑ i, 2 * Real.pi * c i * (inner ℝ x (w i))













/-! ## 3. Second order plus first order plus a constant -/

/-- The full constant-coefficient operator `∑ᵢ cᵢ ∂_{wᵢ}² + ∑ᵢ aᵢ (−i ∂_{wᵢ}) + κ`. -/
noncomputable def mixedOp (a c : ι → ℝ) (w : ι → V) (κ : ℝ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  constCoeffOp c w κ + firstOrderOp a w

/-- Its (real) symbol. -/
noncomputable def mixedSymbolFn (a c : ι → ℝ) (w : ι → V) (κ : ℝ) (x : V) : ℝ :=
  symbolFn c w κ x + foSymbolFn a w x









end BookProof.FourierMultiplierEsa


