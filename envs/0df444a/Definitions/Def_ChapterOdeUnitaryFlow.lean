-- Prove2me | Definitions.Def_ChapterOdeUnitaryFlow
-- name    : ChapterOdeUnitaryFlow
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:35:24.063641+00:00
-- url     : https://prove2.me/theorems/d83b4d72-feb1-4ecc-9769-cc7a2c01e624
-- title:
--   Chapter OdeUnitaryFlow
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterOdeUnitaryFlow.lean`): generated def bundle for ChapterOdeUnitaryFlow. See BookProof/ChapterOdeUnitaryFlow.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterOdeUnitaryFlow.lean

import Mathlib


/-!
# The unitary time-evolution of the blow-up ODE `ẋ = x²`

Source: `book.tex`, chapter *"Resolution of the singularity of the ODE x'=x^2 when the
initial x has uncertainties"*, §*State-of-the-art* (Equation 1) and §*Resolution of the
singularity using the uncertainties in x* (Equations 2–4).

The chapter's computation is the following.  The classical initial-value problem

```
ẋ = x²,   x(0) = x₀
```

has the solution `x(t) = x₀ / (1 - t x₀)` (Equation 1), which **blows up** at the finite
time `t = 1/x₀` when `x₀ > 0`: there is no global deterministic solution.  The book then
quantizes the vector field, `H = x² p - i x`, diagonalizes `H` by the kernel
`U(x,p) = e^{-i p / x} / (√(2π) x)` and evaluates the resulting time-evolution kernel,
obtaining (Equation 3)

```
(e^{-i H t} ψ)(x) = 1/(x t + 1) · ψ( x / (x t + 1) )
```

and, for a multiplication operator `ρ` (a probability density in the `x`-basis),
(Equation 4)

```
(e^{-i H t} ρ e^{+i H t} ψ)(x) = ρ( x / (x t + 1) ) · ψ(x) .
```

This file formalizes that computation *as an independent mathematical statement*: we
**define** the operator family of Equation 3 and prove that it is what the book claims it
is — a one-parameter group of **probability-preserving** operators on `L²(ℝ)` whose
generator is exactly `-i H`, and which conjugates a multiplication operator as in
Equation 4.  Nothing here presupposes the (merely formal) manipulations with the
δ-function kernel of the source text; the point of the formalization is that the *result*
of those manipulations is correct, and that it does resolve the singularity at the level
of probability measures: **for every real time `t`, including times beyond the classical
blow-up, total probability is exactly conserved** (`odeKoop_lintegral_normSq`).

The mechanism is visible in the formulas.  The flow map

```
mob t x = x / (1 + t x)
```

is a Möbius map which is *not* defined at the single point `x = -1/t`, and which maps
`ℝ \ {-1/t}` bijectively onto `ℝ \ {1/t}`.  A single point is a Lebesgue-null set, so as a
transformation of the *probability space* the flow is a bijection up to null sets: what
"escapes to `+∞`" re-enters at `-∞`.  The pointwise trajectory of a single initial
condition still blows up (`classicalSol_tendsto_atTop`), but the evolution of the
uncertainty — the wave-function — is global and norm-preserving.

## Main results

* `classicalSol_hasDerivAt`, `classicalSol_zero` — Equation 1 solves `ẋ = x²`.
* `classicalSol_tendsto_atTop` — and blows up at `t = 1/x₀` for `x₀ > 0`.
* `mob_mob`, `mob_zero`, `mob_neg_mob` — the Möbius flow is a group action off the pole.
* `odeKoop_add`, `odeKoop_zero` — Equation 3 defines a one-parameter group.
* `odeKoop_lintegral_normSq` — **probability conservation for every `t`** (the `L²`
  isometry; the headline).
* `odeKoop_conj_mul` — Equation 4: conjugation of a multiplication operator.
* `hasDerivAt_odeKoop_zero`, `odeKoop_generator` — the generator of the group is `-i H`
  with `H = x² p - i x`, `p = -i ∂ₓ`: Equation 3 solves the Schrödinger equation of the
  quantized vector field.
-/

namespace BookProof.OdeUnitaryFlow

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-! ## The classical solution and its blow-up -/

/-- Equation 1 of the chapter: the solution of `ẋ = x²` with `x(0) = x₀`. -/
noncomputable def classicalSol (x₀ t : ℝ) : ℝ := x₀ / (1 - t * x₀)









/-! ## The Möbius flow -/

/-- The Möbius flow map `x ↦ x/(1 + t x)` appearing in Equation 3.  It is the classical
flow of `ẋ = x²` run *backwards*: `mob (-t) x₀ = classicalSol x₀ t`. -/
noncomputable def mob (t x : ℝ) : ℝ := x / (1 + t * x)





/-- The set of points at which the flow map at time `t` is defined. -/
def flowDom (t : ℝ) : Set ℝ := {x : ℝ | 1 + t * x ≠ 0}

















/-! ## Equation 3: the evolution operator -/

/-- **Equation 3**: the time-evolution operator `e^{-iHt}` of the quantized vector
field, `(e^{-iHt}ψ)(x) = ψ(x/(1+tx))/(1+tx)`. -/
noncomputable def odeKoop (t : ℝ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((1 + t * x : ℝ) : ℂ)⁻¹ * ψ (mob t x)







/-! ## Probability conservation -/











/-! ## Equation 4: conjugation of a multiplication operator -/



/-! ## The generator: the quantized vector field -/

/-- The value at `x` of the quantized Hamiltonian `H = x² p - i x` (with `p = -i ∂ₓ`)
applied to a function with value `v` and derivative `d` at `x`. -/
noncomputable def hamValue (x : ℝ) (d v : ℂ) : ℂ :=
  (x : ℂ) ^ 2 * (-Complex.I * d) - Complex.I * (x : ℂ) * v





/-! ## The change of variables `w = -1/x`: the evolution *is* a translation

The chapter observes that *"the Hamiltonian differs from the translation in space by a
change of variables `y → 1/x`"*.  We prove exactly that: the unitary change of variables
`W` induced by `x ↦ -1/x` intertwines the evolution of Equation 3 with the translation
group, `e^{-iHt} ∘ W = W ∘ T_t`.  This is the structural reason for the group law and for
the conservation of probability: on the `w`-chart the singular flow is just `w ↦ w - t`.
-/

/-- The change of variables `x ↦ -1/x` of the chapter (an involution of `ℝ \ {0}`). -/
noncomputable def invMap (x : ℝ) : ℝ := -1 / x





/-- The unitary implementing the change of variables on wave-functions:
`(Wψ)(x) = ψ(-1/x)/x`. -/
noncomputable def chartW (ψ : ℝ → ℂ) (x : ℝ) : ℂ := ((x : ℝ) : ℂ)⁻¹ * ψ (invMap x)

/-- Translation of a wave-function by the time `t`. -/
def transl (t : ℝ) (ψ : ℝ → ℂ) (w : ℝ) : ℂ := ψ (w - t)





/-! ### The chart is norm-preserving -/











end BookProof.OdeUnitaryFlow


