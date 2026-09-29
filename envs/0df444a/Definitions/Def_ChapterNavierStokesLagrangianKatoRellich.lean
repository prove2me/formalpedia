-- Prove2me | Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
-- name    : ChapterNavierStokesLagrangianKatoRellich
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T02:51:51.750827+00:00
-- url     : https://prove2.me/theorems/583fd807-e3b9-4858-a384-5c7689c09064
-- title:
--   This module closes the analytic step that the Lagrangian (parcel) route of the Navier–Stokes thread was missing. After t ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesLagrangianKatoRellich`, source chapter `BookProof/ChapterNavierStokesLagrangianKatoRellich.lean`).
--
--   This module closes the analytic step that the Lagrangian (parcel) route of the Navier–Stokes thread was missing. After the change of variables of `BookProof.ChapterNavierStokesFlow` the Navier–Stokes Hamiltonian is
--
--   `ĥ_full = ½∑ᵢ Pᵢ² + ν ∑ᵢ Qᵢ² + ∑ᵢ fᵢ Dᵢ + C`,
--
--   a **positive** second-order part (advection plus viscosity — this is the whole point of passing to the trajectory picture), a first-order drift, and a zeroth-order constraint. `BookProof.ChapterNavierStokesLagrangianEsa` builds this operator without any truncation and proves it symmetric with positive second-order part, but its essential self-adjointness was obtained there only from *external* criteria (a complete flow, a bounded realization, or a total family of common eigenvectors), and `exists_lagrangianFullData_not_hasZeroDeficiencyOn` shows an unbounded drift can destroy the property outright.
--
--   Here the drift is controlled by the positive second-order part itself, and essential self-adjointness of the full operator follows from essential self-adjointness of that second-order part alone.
--
--   The positivity gain of the Lagrangian variables *is* the relative bound. For each `i`,
--
--   `‖Pᵢ v‖² = ⟪v, Pᵢ² v⟫ ≤ 2⟪v, (½∑ⱼPⱼ² + ν∑ⱼQⱼ²) v⟫ ≤ 2‖v‖ ‖T v‖`,
--
--   because every other term of `T = ½∑Pⱼ² + ν∑Qⱼ²` has a **nonnegative** quadratic form. With the elementary inequality `√(2AB) ≤ εB + A/(2ε)` this gives, for every `ε > 0`,
--
--   `‖Pᵢ v‖ ≤ ε ‖T v‖ + (2ε)⁻¹ ‖v‖` (`norm_P_le`),
--
--   i.e. any first-order term dominated by the parcel momenta is `T`-bounded **with arbitrarily small relative bound** — the Kato–Rellich/Ikebe–Kato interpolation of a first-order operator against a second-order one, in the exact form the Lagrangian route asks for. Adding a bounded constraint term and taking `ε` small enough, the whole low-order part is `T`-bounded with relative bound `< 1`, and `BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded` applies.
--
--   * `secondOrder` / `lowOrder` and `hFull_eq_add` — the split of the transformed Hamiltonian into its positive second-order part and its low-order remainder; * `norm_P_sq_le`, `norm_P_le`, `norm_sum_P_le` — the interpolation inequality: the parcel momenta are dominated by the positive second-order part with arbitrarily small relative bound; * `lowOrder_relBound` — a drift dominated by the parcel momenta, together with a bounded constraint, is `T`-bounded with *any* prescribed relative bound `a > 0`; * `hFull_essentiallySelfAdjointOn` and `hFull_hasZeroDeficiencyOn` — **the headline**: if the positive second-order part is essentially self-adjoint on the domain, so is the full transformed Navier–Stokes Hamiltonian. The drift may be unbounded; no common eigenvectors, no flow, no boundedness is assumed; * `drift_dominated_of_drive_eq_P` and `hFull_hasZeroDeficiencyOn_of_drive_eq_P` — the physical case in which the drift generators *are* the parcel momenta (`Dᵢ = Pᵢ`, the term `f·∇_X`), where the domination hypothesis is automatic; * `hasZeroDeficiencyOn_of_lagrangian_katoRellich` — transported back through the unitary change of variables to the Eulerian operator; * `lagrangianCore`, `lagrangian_selfAdjoint_extension`, `lagrangian_selfAdjoint_extension_unique`, `lagrangian_hashimoto_selects` and `lagrangian_shiftInvert_selects` — the Hashimoto/SIRK shift-invert selection theorem **on the Lagrangian side**, obtained from the Kato–Rellich essential self-adjointness rather than from the Eulerian chain: the shift-invert resolvents of the transformed generator exist, are bounded, satisfy the resolvent identity and the SIRK relation, have strongly convergent Galerkin truncations, and each of them determines the unique self-adjoint transformed generator; * `diagKR`, `diagKR_hFull_essentiallySelfAdjointOn`, `diagKR_drift_not_bounded` and `diagKR_hashimoto_selects` — a genuinely infin
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

import Definitions.Def_ChapterKatoRellichRelative
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterEsaClosureCore
import Mathlib

import Mathlib

/-!
# The Lagrangian route: Kato–Rellich control of the drift, and the Hashimoto
selection

This module closes the analytic step that the Lagrangian (parcel) route of the
Navier–Stokes thread was missing.  After the change of variables of
`BookProof.ChapterNavierStokesFlow` the Navier–Stokes Hamiltonian is

`ĥ_full = ½∑ᵢ Pᵢ² + ν ∑ᵢ Qᵢ² + ∑ᵢ fᵢ Dᵢ + C`,

a **positive** second-order part (advection plus viscosity — this is the whole
point of passing to the trajectory picture), a first-order drift, and a
zeroth-order constraint.  `BookProof.ChapterNavierStokesLagrangianEsa` builds
this operator without any truncation and proves it symmetric with positive
second-order part, but its essential self-adjointness was obtained there only
from *external* criteria (a complete flow, a bounded realization, or a total
family of common eigenvectors), and
`exists_lagrangianFullData_not_hasZeroDeficiencyOn` shows an unbounded drift can
destroy the property outright.

Here the drift is controlled by the positive second-order part itself, and
essential self-adjointness of the full operator follows from essential
self-adjointness of that second-order part alone.

## The mechanism

The positivity gain of the Lagrangian variables *is* the relative bound.  For
each `i`,

`‖Pᵢ v‖² = ⟪v, Pᵢ² v⟫ ≤ 2⟪v, (½∑ⱼPⱼ² + ν∑ⱼQⱼ²) v⟫ ≤ 2‖v‖ ‖T v‖`,

because every other term of `T = ½∑Pⱼ² + ν∑Qⱼ²` has a **nonnegative** quadratic
form.  With the elementary inequality `√(2AB) ≤ εB + A/(2ε)` this gives, for
every `ε > 0`,

`‖Pᵢ v‖ ≤ ε ‖T v‖ + (2ε)⁻¹ ‖v‖`  (`norm_P_le`),

i.e. any first-order term dominated by the parcel momenta is `T`-bounded **with
arbitrarily small relative bound** — the Kato–Rellich/Ikebe–Kato interpolation
of a first-order operator against a second-order one, in the exact form the
Lagrangian route asks for.  Adding a bounded constraint term and taking `ε`
small enough, the whole low-order part is `T`-bounded with relative bound `< 1`,
and `BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded` applies.

## What is proved

* `secondOrder` / `lowOrder` and `hFull_eq_add` — the split of the transformed
  Hamiltonian into its positive second-order part and its low-order remainder;
* `norm_P_sq_le`, `norm_P_le`, `norm_sum_P_le` — the interpolation inequality:
  the parcel momenta are dominated by the positive second-order part with
  arbitrarily small relative bound;
* `lowOrder_relBound` — a drift dominated by the parcel momenta, together with a
  bounded constraint, is `T`-bounded with *any* prescribed relative bound
  `a > 0`;
* `hFull_essentiallySelfAdjointOn` and `hFull_hasZeroDeficiencyOn` — **the
  headline**: if the positive second-order part is essentially self-adjoint on
  the domain, so is the full transformed Navier–Stokes Hamiltonian.  The drift
  may be unbounded; no common eigenvectors, no flow, no boundedness is assumed;
* `drift_dominated_of_drive_eq_P` and
  `hFull_hasZeroDeficiencyOn_of_drive_eq_P` — the physical case in which the
  drift generators *are* the parcel momenta (`Dᵢ = Pᵢ`, the term `f·∇_X`), where
  the domination hypothesis is automatic;
* `hasZeroDeficiencyOn_of_lagrangian_katoRellich` — transported back through the
  unitary change of variables to the Eulerian operator;
* `lagrangianCore`, `lagrangian_selfAdjoint_extension`,
  `lagrangian_selfAdjoint_extension_unique`, `lagrangian_hashimoto_selects` and
  `lagrangian_shiftInvert_selects` — the Hashimoto/SIRK shift-invert selection
  theorem **on the Lagrangian side**, obtained from the Kato–Rellich essential
  self-adjointness rather than from the Eulerian chain: the shift-invert
  resolvents of the transformed generator exist, are bounded, satisfy the
  resolvent identity and the SIRK relation, have strongly convergent Galerkin
  truncations, and each of them determines the unique self-adjoint transformed
  generator;
* `diagKR`, `diagKR_hFull_essentiallySelfAdjointOn`, `diagKR_drift_not_bounded`
  and `diagKR_hashimoto_selects` — a genuinely infinite-dimensional, genuinely
  **unbounded** instance on `ℓ²(ℕ)` whose drift is not a bounded perturbation,
  so the bounded Kato–Rellich theorem does not apply to it and the relative one
  does;
* `jacobiLag_secondOrder_eq_zero` and
  `jacobiLag_drift_not_relativelyBounded` — the sharpness record of
  `ChapterNavierStokesLagrangianEsa` seen from here: in the counterexample the
  second-order part is `0`, so its drift is dominated by nothing, which is
  precisely the hypothesis of this module that fails.

## Honest boundary

Unchanged (Contention D5): nothing here claims global regularity of the
*classical* Navier–Stokes PDE.  Essential self-adjointness of the positive
second-order part `T` is a hypothesis of the abstract theorem — it is the
statement that the Lagrangian "Laplacian" `−½Δ_X − νΔ_{ξ,X}` is essentially
self-adjoint on the chosen core — and it is verified here only for the concrete
realization on `ℓ²(ℕ)`.  What the module supplies is the step the Lagrangian
route named as missing: the first-order drift is controlled by that second-order
part, so no separate hypothesis about the drift is needed.
-/

open Filter Topology

namespace BookProof.NavierStokesFlow

namespace LagrangianKatoRellich

open FullEsa LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure

/-! ## The split into second-order and low-order parts -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

/-- The **positive second-order part** `T = ½∑Pᵢ² + ν∑Qᵢ²` of the transformed
Hamiltonian: advection plus viscosity. -/
noncomputable def secondOrder : L.D →ₗ[ℂ] L.D := L.kinetic + L.viscous

/-- The low-order remainder `∑fᵢDᵢ + C`: the first-order drift plus the
zeroth-order volume-preservation constraint. -/
noncomputable def lowOrder : L.D →ₗ[ℂ] L.D := L.drift + L.constraintOp

/-- The transformed (Lagrangian) Navier–Stokes Hamiltonian, viewed as an
operator into the ambient space — the form the closure and shift-invert
machinery works with. -/
noncomputable def lagrangianCore : L.D →ₗ[ℂ] F := L.D.subtype.comp L.hFull











/-! ### The interpolation inequality -/







/-! ### The relative bound for the low-order part -/



/-! ### The Kato–Rellich theorem for the transformed Hamiltonian -/





/-! ### The physical case: the drift generators are the parcel momenta -/









end Abstract

/-! ## The Hashimoto/SIRK selection on the Lagrangian side -/

section Selection

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (L : LagrangianFullData F)









end Selection

/-! ## A genuinely unbounded instance on `ℓ²(ℕ)` -/

section Instance

open LpNat DiagonalEsa



/-- Transformed Navier–Stokes data on `ℓ²(ℕ)` whose parcel momenta are the
**unbounded** diagonal operators `Pᵢ = diag(n)`, whose drift generators are those
same momenta (as the Lagrangian picture demands, `Dᵢ = Pᵢ`), with unit force in
each direction, no viscosity and no constraint.  The second-order part is
`diag(3n²/2)` and the drift is `diag(3n)`: an unbounded first-order perturbation
of an unbounded second-order operator. -/
noncomputable def diagKR : LagrangianFullData L2N :=
  diagLagData (fun _ n => (n : ℝ)) (fun _ _ => 0) (fun _ n => (n : ℝ)) (fun _ => 0)
    (fun _ => 1) (le_refl (0 : ℝ))



















/-- `ℓ²(ℕ)` carries an `ℕ`-indexed Hilbert basis, so the selection theorem below
is not vacuous. -/
noncomputable def l2NatBasis : HilbertBasis ℕ ℂ L2N :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ L2N)



end Instance

/-! ## The sharpness record, seen from here -/

section Sharpness

open LpNat JacobiDeficiency

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]







end Sharpness

end LagrangianKatoRellich

end BookProof.NavierStokesFlow


