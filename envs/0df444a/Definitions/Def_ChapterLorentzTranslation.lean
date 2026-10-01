-- Prove2me | Definitions.Def_ChapterLorentzTranslation
-- name    : ChapterLorentzTranslation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:20:53.810578+00:00
-- url     : https://prove2.me/theorems/ced57235-cc18-44d2-a20a-7de6f7d9214f
-- title:
--   Chapter LorentzTranslation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLorentzTranslation.lean`): generated def bundle for ChapterLorentzTranslation. See BookProof/ChapterLorentzTranslation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLorentzTranslation.lean

import Mathlib


/-!
# Chapter — Yang–Mills / Classical Statistical Field Theory: the space-time
translation representation in the momentum-diagonal basis

Source: `book.tex`, chapter *"Quantization due to time-evolution: Yang-Mills and
Classical Statistical Field Theory"*, §*"Lorentz covariance"* (line ~6506).

Working in a basis where the 3-momentum operator is diagonal, the author writes
the space-time translations of a free system of invariant mass `M` as

  `T(x) Ψ(γv) = e^{i M τ(γv, x)} Ψ(γv)`,   `τ(γv, x) = γ x₀ − (γv)·x`,

where the four-velocity is `(γ, γv)` with `γ = √(1 + (γv)²)` a function of the
spatial momentum `γv`.  The book observes that in this basis the space-time
translations "have the same structure as the time-evolution in non-relativistic
space-time, with `M` playing the role of the Hamiltonian and `τ` playing the role
of (proper) time".

This file makes that self-contained content precise.  We model the spatial
momentum `γv` by `w : Fin 3 → ℝ`, define `gamma w = √(1 + ∑ (w i)²)`, the
proper-time functional `properTime w x₀ xs = γ x₀ − ∑ wᵢ xsᵢ`, and the phase
`transPhase M w x₀ xs = e^{i M τ}`.  We prove:

* `gamma_sq` / `mass_shell` — the four-velocity is on the unit mass shell,
  `γ² − (γv)² = 1`;
* `gamma_zero` — the rest-frame value `γ = 1` at `γv = 0`;
* `properTime_add`, `properTime_zero` — `τ` is additive in the space-time
  translation `x` (a homomorphism `(ℝ⁴, +) → (ℝ, +)`);
* `properTime_rest` — in the rest frame `τ = x₀` (proper time = coordinate time);
* `transPhase_add` — **headline**: the phases compose,
  `T(x + y) = T(x) · T(y)`, so `x ↦ transPhase M w x` is a one-dimensional
  unitary representation of the space-time translation group;
* `transPhase_zero` — `T(0) = 1`;
* `transPhase_norm` — each `T(x)` is unitary (`‖·‖ = 1`, for real `M`);
* `transPhase_rest` — in the rest frame `T(x) = e^{i M x₀}`, exactly the
  non-relativistic time-evolution phase.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterLorentzTranslation

open scoped BigOperators

/-- The Lorentz factor `γ = √(1 + (γv)²)` as a function of the spatial momentum
`γv = w`; the temporal component of the (dimensionless) four-velocity `(γ, γv)`. -/
noncomputable def gamma (w : Fin 3 → ℝ) : ℝ := Real.sqrt (1 + ∑ i, (w i) ^ 2)









/-- The proper-time functional `τ(γv, x) = γ x₀ − (γv)·x` appearing in the phase
`e^{i M τ}` of the space-time translation `T(x)`. -/
noncomputable def properTime (w : Fin 3 → ℝ) (x0 : ℝ) (xs : Fin 3 → ℝ) : ℝ :=
  gamma w * x0 - ∑ i, w i * xs i







/-- The space-time translation phase `T(x) = e^{i M τ(γv, x)}` in the
momentum-diagonal basis, acting (by multiplication) on the eigenfunction of
spatial momentum `w = γv`. -/
noncomputable def transPhase (M : ℝ) (w : Fin 3 → ℝ) (x0 : ℝ) (xs : Fin 3 → ℝ) : ℂ :=
  Complex.exp (Complex.I * (M : ℂ) * (properTime w x0 xs : ℂ))









end BookProof.ChapterLorentzTranslation


