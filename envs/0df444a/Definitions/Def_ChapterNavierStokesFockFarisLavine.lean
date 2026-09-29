-- Prove2me | Definitions.Def_ChapterNavierStokesFockFarisLavine
-- name    : ChapterNavierStokesFockFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T13:05:27.648405+00:00
-- url     : https://prove2.me/theorems/ff050031-16fe-413a-bea5-be0222c21d58
-- title:
--   This module puts the two previous ones together. `ChapterNavierStokesSecondQuant` lifts essential self-adjointness from ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesFockFarisLavine`, source chapter `BookProof/ChapterNavierStokesFockFarisLavine.lean`).
--
--   This module puts the two previous ones together. `ChapterNavierStokesSecondQuant` lifts essential self-adjointness from the sectors of the Fock space `⨁ₘ Sₘ` to the finite-particle domain, and `ChapterNavierStokesFarisLavineLift` analyses what happens to the two Faris–Lavine inequalities when the one-particle operators are summed over the particles of a sector. Here the inequalities are transported to the Fock space itself:
--
--   * `fockOp_isSymmetricDom` — a sector-wise symmetric operator is symmetric on the finite-particle domain; * `fockOp_norm_le_of_sectors` — the relative bound `‖Ĥψ‖ ≤ c₁‖N̂ψ‖` holds on the Fock space as soon as it holds in every sector with the same constant; * `fockOp_norm_inner_le_of_sectors` — likewise for the form bound `|⟪ψ, Âψ⟫| ≤ c₂ Re⟪ψ, N̂ψ⟫`, which applied to `Â = [Ĥ, N̂]` is the Faris–Lavine commutator bound; * `fockOp_commDom` — the commutator of two second quantizations is the second quantization of the sector-wise commutators, so the previous item does apply to it; * `fockOp_hasZeroDeficiencyOn_of_farisLavine` — the assembled statement: given the Faris–Lavine criterion (as a named hypothesis, exactly as elsewhere in this project — it is never an `axiom`), sector-wise symmetry, and the two sector-wise inequalities, the second-quantized Hamiltonian has vanishing adjoint deficiency on the finite-particle domain of the Fock space.
--
--   `fockComparison_hasZeroDeficiencyOn` records the unconditional half in a concrete case: the second quantization of the one-particle comparison operator `n = ∑πᵢ² + ∑Vᵢ² + I` of the fiber momentum representation is essentially self-adjoint on the finite-particle domain of the corresponding Fock space, and that domain is a proper subspace.
--
--   Essential self-adjointness of the continuum Navier–Stokes Hamiltonian is **not** claimed. The Faris–Lavine criterion is an input here, and its two inequalities are proved here only to *lift*: whether they hold for the one-particle Navier–Stokes operator is not settled in this project.
--
--   **Update.** The named hypothesis `farisLavine` of `fockOp_hasZeroDeficiencyOn_of_farisLavine` is stated in the *unrestricted* form (relative bound plus commutator bound, with no positivity of `N` and no surjectivity of `N + 1`), and that form of the criterion is refutable — `BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound`. The hypothesis-free replacement is in `BookProof.ChapterNavierStokesIkebeKato` and `BookProof.ChapterNavierStokesMomentumEsa`: there the comparison operator is taken on its maximal domain, where positivity, surjectivity of `N + 1` and the core property of the finite-mode states are all *proved*, and the criterion itself is the theorem `BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockFarisLavine.lean

import Definitions.Def_ChapterNavierStokesSecondQuant
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Mathlib

import Mathlib

/-!
# The Faris–Lavine data on the Fock space

This module puts the two previous ones together.  `ChapterNavierStokesSecondQuant`
lifts essential self-adjointness from the sectors of the Fock space
`⨁ₘ Sₘ` to the finite-particle domain, and `ChapterNavierStokesFarisLavineLift`
analyses what happens to the two Faris–Lavine inequalities when the
one-particle operators are summed over the particles of a sector.  Here the
inequalities are transported to the Fock space itself:

* `fockOp_isSymmetricDom` — a sector-wise symmetric operator is symmetric on the
  finite-particle domain;
* `fockOp_norm_le_of_sectors` — the relative bound `‖Ĥψ‖ ≤ c₁‖N̂ψ‖` holds on the
  Fock space as soon as it holds in every sector with the same constant;
* `fockOp_norm_inner_le_of_sectors` — likewise for the form bound
  `|⟪ψ, Âψ⟫| ≤ c₂ Re⟪ψ, N̂ψ⟫`, which applied to `Â = [Ĥ, N̂]` is the
  Faris–Lavine commutator bound;
* `fockOp_commDom` — the commutator of two second quantizations is the second
  quantization of the sector-wise commutators, so the previous item does apply
  to it;
* `fockOp_hasZeroDeficiencyOn_of_farisLavine` — the assembled statement: given
  the Faris–Lavine criterion (as a named hypothesis, exactly as elsewhere in this
  project — it is never an `axiom`), sector-wise symmetry, and the two
  sector-wise inequalities, the second-quantized Hamiltonian has vanishing
  adjoint deficiency on the finite-particle domain of the Fock space.

`fockComparison_hasZeroDeficiencyOn` records the unconditional half in a
concrete case: the second quantization of the one-particle comparison operator
`n = ∑πᵢ² + ∑Vᵢ² + I` of the fiber momentum representation is essentially
self-adjoint on the finite-particle domain of the corresponding Fock space, and
that domain is a proper subspace.

## Scope

Essential self-adjointness of the continuum Navier–Stokes Hamiltonian is **not**
claimed.  The Faris–Lavine criterion is an input here, and its two inequalities
are proved here only to *lift*: whether they hold for the one-particle
Navier–Stokes operator is not settled in this project.

**Update.**  The named hypothesis `farisLavine` of
`fockOp_hasZeroDeficiencyOn_of_farisLavine` is stated in the *unrestricted* form
(relative bound plus commutator bound, with no positivity of `N` and no
surjectivity of `N + 1`), and that form of the criterion is refutable —
`BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound`.  The
hypothesis-free replacement is in
`BookProof.ChapterNavierStokesIkebeKato` and
`BookProof.ChapterNavierStokesMomentumEsa`: there the comparison operator is
taken on its maximal domain, where positivity, surjectivity of `N + 1` and the
core property of the finite-mode states are all *proved*, and the criterion
itself is the theorem
`BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace SecondQuant

open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}

/-! ## Algebra of second quantizations -/







/-! ## Symmetry -/



/-! ## The relative bound -/





/-! ## The form bound -/





/-! ## The assembled Faris–Lavine statement on the Fock space -/



/-! ## A concrete Fock space over the fiber momentum representation -/

section ConcreteFock

open FarisLavineLift LpNat DiagonalEsa

/-- The sector spaces of the concrete example: every sector is a copy of the
fiber space `ℓ²(ℕ)` of the momentum representation. -/
abbrev fiberSector : ℕ → Type := fun _ => L2N

/-- The sector domains: the finite-mode core of each fiber, the analogue of
`C_c^∞`. -/
noncomputable def fiberCore : ∀ m : ℕ, Submodule ℂ (fiberSector m) := fun _ => lpFiniteModes ℕ

/-- **The second quantization `N̂ = dΓ(n) + I` of the one-particle comparison
operator** `n = ∑πᵢ² + ∑Vᵢ² + I`, in the fiber momentum representation. -/
noncomputable def fockComparison (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    fockCore fiberCore →ₗ[ℂ] fockCore fiberCore :=
  fockOp (fun _ => (diagComparisonData d p q).comparison)









end ConcreteFock

end SecondQuant

end BookProof.NavierStokesFlow


