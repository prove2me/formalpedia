-- Prove2me | Definitions.Def_ChapterUnitaryTransport
-- name    : ChapterUnitaryTransport
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:14:49.822993+00:00
-- url     : https://prove2.me/theorems/4e42444a-8474-4c10-9abf-442dfbd3fb4a
-- title:
--   `BookProof.ChapterUnboundedPosition` proves the whole unbounded package — dense natural domain, symmetry, self-adjointne ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.UnitaryTransport`, source chapter `BookProof/ChapterUnitaryTransport.lean`).
--
--   `BookProof.ChapterUnboundedPosition` proves the whole unbounded package — dense natural domain, symmetry, self-adjointness, and a strongly continuous unitary group of which the operator is the generator — for *multiplication* operators on `ℓ²(ℤ)`. That is the concrete half of the spectral picture. This module supplies the abstract half: **all of it is invariant under a unitary change of Hilbert space.**
--
--   For a unitary `W : H ≃ₗᵢ[ℂ] K` and a densely defined operator `A` on a domain `D ⊆ H`, the transported operator is `W A W⁻¹` on `W(D)` (`transportDomain`, `transportOp`), and each structural property moves across:
--
--   * `transportDomain_dense` — the transported domain is dense; * `transportOp_symmetric` — symmetry; * `transport_adjointDomain` / `transport_isSelfAdjointOn` — the adjoint domain is the image of the adjoint domain, so **self-adjointness** transports; * `tendsto_transportUnitary` — strong continuity of the transported group; * `tendsto_slope_transportUnitary` — **Stone's relation** `dV/dt|₀ = i(WAW⁻¹)`.
--
--   Combining the two halves, `IsSelfAdjointOn` and the full Stone package hold for *every* operator unitarily equivalent to a lattice multiplication operator, on any complex Hilbert space: `transported_position_isSelfAdjointOn`, `transported_position_group`, `tendsto_transported_position_unitary`, `tendsto_slope_transported_position`.
--
--   This is exactly the reduction the spectral theorem is used for: an unbounded self-adjoint operator with a diagonalizing unitary inherits its group. What is still missing for a general Stone theorem is the *existence* of the diagonalizing unitary, i.e. the spectral theorem for unbounded self-adjoint operators.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnitaryTransport.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterUnboundedPosition

import Mathlib

import Mathlib
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterContinuityUnitaryInfinite

/-!
# Unitary transport of the unbounded layer

`BookProof.ChapterUnboundedPosition` proves the whole unbounded package — dense
natural domain, symmetry, self-adjointness, and a strongly continuous unitary
group of which the operator is the generator — for *multiplication* operators on
`ℓ²(ℤ)`.  That is the concrete half of the spectral picture.  This module supplies
the abstract half: **all of it is invariant under a unitary change of Hilbert
space.**

For a unitary `W : H ≃ₗᵢ[ℂ] K` and a densely defined operator `A` on a domain
`D ⊆ H`, the transported operator is `W A W⁻¹` on `W(D)` (`transportDomain`,
`transportOp`), and each structural property moves across:

* `transportDomain_dense` — the transported domain is dense;
* `transportOp_symmetric` — symmetry;
* `transport_adjointDomain` / `transport_isSelfAdjointOn` — the adjoint domain is
  the image of the adjoint domain, so **self-adjointness** transports;
* `tendsto_transportUnitary` — strong continuity of the transported group;
* `tendsto_slope_transportUnitary` — **Stone's relation** `dV/dt|₀ = i(WAW⁻¹)`.

Combining the two halves, `IsSelfAdjointOn` and the full Stone package hold for
*every* operator unitarily equivalent to a lattice multiplication operator, on any
complex Hilbert space:
`transported_position_isSelfAdjointOn`, `transported_position_group`,
`tendsto_transported_position_unitary`, `tendsto_slope_transported_position`.

This is exactly the reduction the spectral theorem is used for: an unbounded
self-adjoint operator with a diagonalizing unitary inherits its group.  What is
still missing for a general Stone theorem is the *existence* of the diagonalizing
unitary, i.e. the spectral theorem for unbounded self-adjoint operators.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped InnerProductSpace

namespace BookProof.ChapterUnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! ## Abstract vocabulary for a densely defined operator -/

/-- The **domain of the adjoint** of an operator `A` defined on the domain `D`:
the vectors `φ` for which `ψ ↦ ⟪Aψ, φ⟫` is represented by an inner product. -/
def adjointDomain (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) : Set H :=
  {phi | ∃ eta : H, ∀ psi : D, ⟪A psi, phi⟫_ℂ = ⟪(psi : H), eta⟫_ℂ}

/-- `A` is **symmetric** on its domain. -/
def IsSymmetricOn (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) : Prop :=
  ∀ psi phi : D, ⟪A psi, (phi : H)⟫_ℂ = ⟪(psi : H), A phi⟫_ℂ

/-- `A` is **self-adjoint** on its domain: the adjoint domain is not merely
contained in but *equal* to `D`. -/
def IsSelfAdjointOn (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) : Prop :=
  adjointDomain D A = (D : Set H)





/-! ## Transporting the domain and the operator -/

/-- The transported domain `W(D) ⊆ K`. -/
def transportDomain (W : H ≃ₗᵢ[ℂ] K) (D : Submodule ℂ H) : Submodule ℂ K :=
  D.map (W.toLinearEquiv : H →ₗ[ℂ] K)



/-- `W` restricts to a linear equivalence `D ≃ W(D)`. -/
noncomputable def transportEquiv (W : H ≃ₗᵢ[ℂ] K) (D : Submodule ℂ H) :
    D ≃ₗ[ℂ] transportDomain W D :=
  W.toLinearEquiv.submoduleMap D



/-- The **transported operator** `W A W⁻¹`, defined on `W(D)`. -/
noncomputable def transportOp (W : H ≃ₗᵢ[ℂ] K) (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) :
    transportDomain W D →ₗ[ℂ] K :=
  (W.toLinearEquiv : H →ₗ[ℂ] K) ∘ₗ A ∘ₗ ((transportEquiv W D).symm : transportDomain W D →ₗ[ℂ] D)



/-! ## The structural properties transport -/









/-! ## The unitary group transports -/

/-- The transported unitary `W U W⁻¹`. -/
noncomputable def transportUnitary (W : H ≃ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) : K ≃ₗᵢ[ℂ] K :=
  (W.symm.trans U).trans W











/-! ## Consequence: everything unitarily equivalent to lattice multiplication -/
















end BookProof.ChapterUnitaryTransport


