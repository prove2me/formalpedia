-- Prove2me | Definitions.Def_ChapterHowlandAutonomization
-- name    : ChapterHowlandAutonomization
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:11:44.269512+00:00
-- url     : https://prove2.me/theorems/36065923-0b48-4b2c-b950-98fb879a148f
-- title:
--   Chapter HowlandAutonomization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHowlandAutonomization.lean`): generated def bundle for ChapterHowlandAutonomization. See BookProof/ChapterHowlandAutonomization.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHowlandAutonomization.lean

import Mathlib


/-!
# A time-dependent evolution becomes time-independent in a larger space

Source: `book.tex`, chapter *"Resolution of the singularity of the ODE x'=x^2 when the
initial x has uncertainties"*, §*General picture* (`book.tex` line ~1000):

> *"any solution in a standard probability space is given by a time-dependent self-adjoint
> Hamiltonian in a larger probability space, then the singularities in a standard
> probability space are consequence of a time-dependent Hamiltonian which is non-integrable.
> But since any time-dependent Hamiltonian can be converted into a time-independent
> Hamiltonian in an even larger sample space, then we can always resolve the singularities
> in a larger sample space which better defines the dynamical system."*

Two levels of that statement are formalized here.

## The classical level: a non-autonomous vector field is autonomous on `ℝ × E`

`autonomize f (s, x) = (1, f s x)` is the extended vector field, and
`hasDerivAt_autonomize` says that the graph `t ↦ (t, x t)` of a solution of the
non-autonomous equation `ẋ = f(t, x)` is a solution of the autonomous equation `ż = F z`;
`hasDerivAt_of_autonomize` is the converse, so nothing is lost by enlarging the space.

## The quantum level: the Howland evolution group

For a time-dependent Hamiltonian the natural object is the family of propagators
`U(t,s)`, which is *not* a one-parameter group.  On the enlarged space of
time-dependent states `ψ : ℝ → H` — the "even larger sample space" of the quotation — the
translated evolution

```
(𝒰(σ)ψ)(t) = U(t, t − σ) ψ(t − σ)
```

**is** a one-parameter group (`howland_add`, `howland_zero`, `howland_neg`) of
probability-preserving maps (`howland_lintegral_normSq`), i.e. an autonomous evolution; by
Stone's theorem (formalized in this project in `BookProof.ChapterStoneTheorem` and
`BookProof.ChapterStoneConverse`) its generator is a *time-independent* self-adjoint
Hamiltonian on the larger space.  Only the three defining properties of a unitary
propagator are used: `U t t = id`, the cocycle law, and pointwise isometry.
-/

namespace BookProof.Howland

open MeasureTheory

/-! ## The classical level -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The autonomous vector field on `ℝ × E` attached to a non-autonomous field `f`. -/
def autonomize (f : ℝ → E → E) : ℝ × E → ℝ × E := fun z => (1, f z.1 z.2)





/-! ## The quantum level: the Howland group of a time-dependent propagator -/

variable {H : Type*} [NormedAddCommGroup H]

/-- The defining properties of the propagator family of a time-dependent Hamiltonian:
`U t s` evolves a state from time `s` to time `t`. -/
structure IsPropagator (U : ℝ → ℝ → H → H) : Prop where
  refl : ∀ t x, U t t x = x
  cocycle : ∀ t s r x, U t s (U s r x) = U t r x
  isometry : ∀ t s x, ‖U t s x‖ = ‖x‖





variable {U : ℝ → ℝ → H → H}

/-- The Howland evolution on time-dependent states: `(𝒰(σ)ψ)(t) = U(t, t−σ) ψ(t−σ)`. -/
def howland (U : ℝ → ℝ → H → H) (σ : ℝ) (ψ : ℝ → H) : ℝ → H :=
  fun t => U t (t - σ) (ψ (t - σ))









end BookProof.Howland


