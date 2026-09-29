-- Prove2me | Definitions.Def_ChapterNavierStokesLagrangianEsa
-- name    : ChapterNavierStokesLagrangianEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:30:30.203291+00:00
-- url     : https://prove2.me/theorems/0bab03c5-714c-4178-888d-8d8023a88de2
-- title:
--   `BookProof.ChapterNavierStokesFlow` records the Lagrangian (parcel) change of variables of `PLAN_LEAN_SPECIALIST_NS_FLOW ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesLagrangianEsa`, source chapter `BookProof/ChapterNavierStokesLagrangianEsa.lean`).
--
--   `BookProof.ChapterNavierStokesFlow` records the Lagrangian (parcel) change of variables of `PLAN_LEAN_SPECIALIST_NS_FLOW.md` Part B for a **finite truncation**: with the Eulerian velocity replaced by the parcel trajectory `X(ξ)` and its canonical momentum `P(ξ) = Ẋ(ξ) = u(X(ξ))`, the Navier–Stokes operator becomes the four-term expression
--
--   `ĥ_full = −½Δ_X − ν Δ_{ξ,X} − i f(X)·∇_X + Ĥ_constraint` ` = ½ ∑ᵢ Pᵢ² + ν ∑ᵢ Qᵢ² + ∑ᵢ fᵢ Dᵢ + C`,
--
--   whose first two terms are *positive* second-order operators, the third a first-order drift and the fourth the zeroth-order volume-preservation constraint. `BookProof.ChapterNavierStokesFullEsa` removes the truncation from the *Eulerian* operator. This module removes the truncation from the *transformed* one and proves its essential self-adjointness.
--
--   * `LagrangianFullData` — the untruncated transformed data: a dense domain `D` of an arbitrary complex inner-product space, three symmetric parcel momenta `Pᵢ`, three symmetric viscous gradients `Qᵢ`, three symmetric drift generators `Dᵢ` with a real external force, a symmetric constraint operator and a viscosity `ν ≥ 0`. Nothing is finite-dimensional and nothing is bounded. * `LagrangianFullData.hFull_isSymmetricDom` — the transformed Hamiltonian is symmetric on its domain, unconditionally. * `LagrangianFullData.kinetic_inner`, `kinetic_nonneg`, `viscous_nonneg` — the quadratic forms of the two second-order terms are `½∑‖Pᵢv‖²` and `ν∑‖Qᵢv‖²`: after the change of variables the advection term is **positive**, which is the structural gain the change of variables is made for. * `LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors` — **the headline criterion**: if the constituents of the transformed operator have a total family of common eigenvectors with real eigenvalues in the domain — the Lagrangian *momentum representation* — then the full transformed Hamiltonian is essentially self-adjoint, with the explicit eigenvalue `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`. Also the flow criterion (`hasZeroDeficiencyOn_of_completeUnitaryFlow`) and the bounded-realization criterion. * `hasZeroDeficiencyOn_of_linearIsometryEquiv` and `NSFullData.hasZeroDeficiencyOn_of_lagrangian` — **the change of variables transfers essential self-adjointness**: vanishing adjoint deficiency is invariant under a unitary change of variables, so proving essential self-adjointness *after* passing to the Lagrangian variables proves it for the Eulerian operator it came from. * **Two genuinely infinite-dimensional, untruncated instances.** On `ℓ²(ℤ)` the parcel momenta and viscous gradients are the lattice (symmetric-difference) momentum — so the kinetic term `½∑Pᵢ²` really is a discrete Laplacian — the drift generators and the constraint are multiplication by bounded real fields, and the transformed Hamiltonian is essentially self-adjoint on the **proper** dense domain of finitely supported modes (`latticeLag_hasZeroDeficiencyOn`), and is not the zero operator (`latticeLag_hFull_ne_zero`). On `ℓ²(ℕ)` all the constituents are diagonal with arbitrary — in particular unbounded — real symbols, and the transformed Hamiltonian is again essentially self-adjoint (`diagLag_hasZeroDeficiencyOn`), for a suitable choice genuinely unbounded (`diagLag_not_bounded`). * **Sharpness.** `exists_lagrangianFullData_not_hasZeroDeficiencyOn`: the algebraic shape of the transformed operator is by itself not enough — an unbounded first-order *drift* term can already destroy essential self-adjointness. So the criteria above are necessary, not decorative; this is the formal counterpart of the `ẋ = x²` warning of the ODE chapter.
--
--   Essential self-adjointness of the *continuum* transformed Navier–Stokes generator — and with it global existence for Navier–Stokes — is **not** claimed. What is proved is: the transformed operator is symmetric and has
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianEsa.lean

import Definitions.Def_ChapterNavierStokesFullEsa
import Mathlib

import Mathlib

/-!
# Essential self-adjointness of the **full** Navier–Stokes Hamiltonian *after the
Lagrangian change of variables*

`BookProof.ChapterNavierStokesFlow` records the Lagrangian (parcel) change of
variables of `PLAN_LEAN_SPECIALIST_NS_FLOW.md` Part B for a **finite
truncation**: with the Eulerian velocity replaced by the parcel trajectory
`X(ξ)` and its canonical momentum `P(ξ) = Ẋ(ξ) = u(X(ξ))`, the Navier–Stokes
operator becomes the four-term expression

`ĥ_full = −½Δ_X − ν Δ_{ξ,X} − i f(X)·∇_X + Ĥ_constraint`
       ` = ½ ∑ᵢ Pᵢ² + ν ∑ᵢ Qᵢ² + ∑ᵢ fᵢ Dᵢ + C`,

whose first two terms are *positive* second-order operators, the third a
first-order drift and the fourth the zeroth-order volume-preservation
constraint.  `BookProof.ChapterNavierStokesFullEsa` removes the truncation from
the *Eulerian* operator.  This module removes the truncation from the
*transformed* one and proves its essential self-adjointness.

## What is proved here

* `LagrangianFullData` — the untruncated transformed data: a dense domain `D` of
  an arbitrary complex inner-product space, three symmetric parcel momenta `Pᵢ`,
  three symmetric viscous gradients `Qᵢ`, three symmetric drift generators `Dᵢ`
  with a real external force, a symmetric constraint operator and a viscosity
  `ν ≥ 0`.  Nothing is finite-dimensional and nothing is bounded.
* `LagrangianFullData.hFull_isSymmetricDom` — the transformed Hamiltonian is
  symmetric on its domain, unconditionally.
* `LagrangianFullData.kinetic_inner`, `kinetic_nonneg`, `viscous_nonneg` — the
  quadratic forms of the two second-order terms are `½∑‖Pᵢv‖²` and `ν∑‖Qᵢv‖²`:
  after the change of variables the advection term is **positive**, which is the
  structural gain the change of variables is made for.
* `LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors` — **the
  headline criterion**: if the constituents of the transformed operator have a
  total family of common eigenvectors with real eigenvalues in the domain — the
  Lagrangian *momentum representation* — then the full transformed Hamiltonian
  is essentially self-adjoint, with the explicit eigenvalue
  `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`.  Also the flow criterion
  (`hasZeroDeficiencyOn_of_completeUnitaryFlow`) and the bounded-realization
  criterion.
* `hasZeroDeficiencyOn_of_linearIsometryEquiv` and
  `NSFullData.hasZeroDeficiencyOn_of_lagrangian` — **the change of variables
  transfers essential self-adjointness**: vanishing adjoint deficiency is
  invariant under a unitary change of variables, so proving essential
  self-adjointness *after* passing to the Lagrangian variables proves it for the
  Eulerian operator it came from.
* **Two genuinely infinite-dimensional, untruncated instances.**  On `ℓ²(ℤ)`
  the parcel momenta and viscous gradients are the lattice
  (symmetric-difference) momentum — so the kinetic term `½∑Pᵢ²` really is a
  discrete Laplacian — the drift generators and the constraint are
  multiplication by bounded real fields, and the transformed Hamiltonian is
  essentially self-adjoint on the **proper** dense domain of finitely supported
  modes (`latticeLag_hasZeroDeficiencyOn`), and is not the zero operator
  (`latticeLag_hFull_ne_zero`).  On `ℓ²(ℕ)` all the constituents are diagonal
  with arbitrary — in particular unbounded — real symbols, and the transformed
  Hamiltonian is again essentially self-adjoint
  (`diagLag_hasZeroDeficiencyOn`), for a suitable choice genuinely unbounded
  (`diagLag_not_bounded`).
* **Sharpness.**  `exists_lagrangianFullData_not_hasZeroDeficiencyOn`: the
  algebraic shape of the transformed operator is by itself not enough — an
  unbounded first-order *drift* term can already destroy essential
  self-adjointness.  So the criteria above are necessary, not decorative; this
  is the formal counterpart of the `ẋ = x²` warning of the ODE chapter.

## Scope

Essential self-adjointness of the *continuum* transformed Navier–Stokes
generator — and with it global existence for Navier–Stokes — is **not** claimed.
What is proved is: the transformed operator is symmetric and has positive
second-order part in complete generality; it is essentially self-adjoint,
unconditionally, for the two untruncated infinite-dimensional realizations
above; it is essentially self-adjoint under each of three general criteria; and
essential self-adjointness passes back and forth along the change of variables.
By `exists_lagrangianFullData_not_hasZeroDeficiencyOn` no statement about the
abstract transformed data can do better than a criterion of this kind.
-/

namespace BookProof.NavierStokesFlow

namespace LagrangianEsa

open FullEsa

/-! ## The untruncated transformed (Lagrangian) data -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The untruncated Lagrangian Navier–Stokes data.**  The parcel momenta `Pᵢ`
(= the Eulerian velocities evaluated along the trajectory, `uᵢ(X(ξ)) = Pᵢ(ξ)`),
the viscous gradients `Qᵢ = ∇_ξPᵢ`, the drift generators `Dᵢ` of the external
force, the zeroth-order volume-preservation constraint `C` and the viscosity
`ν ≥ 0` — now as operators on a *dense domain* `D` of an arbitrary complex
inner-product space. -/
structure LagrangianFullData (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] where
  /-- The dense domain. -/
  D : Submodule ℂ F
  /-- The parcel momenta: the advection term is `½∑Pᵢ²`. -/
  P : Fin 3 → (D →ₗ[ℂ] D)
  /-- The viscous gradients: the viscosity term is `ν∑Qᵢ²`. -/
  Q : Fin 3 → (D →ₗ[ℂ] D)
  /-- The drift generators of the external force (a first-order term). -/
  drive : Fin 3 → (D →ₗ[ℂ] D)
  /-- The external force. -/
  force : Fin 3 → ℝ
  /-- The zeroth-order volume-preservation (pressure/ghost) constraint. -/
  constraintOp : D →ₗ[ℂ] D
  /-- The kinematic viscosity. -/
  nu : ℝ
  dense : Dense (D : Set F)
  P_symm : ∀ i, IsSymmetricDom (P i)
  Q_symm : ∀ i, IsSymmetricDom (Q i)
  drive_symm : ∀ i, IsSymmetricDom (drive i)
  constraint_symm : IsSymmetricDom constraintOp
  nu_nonneg : 0 ≤ nu

namespace LagrangianFullData

variable (L : LagrangianFullData F)

/-- The advective (kinetic) term `−½Δ_X = ½∑Pᵢ²` — a *positive* second-order
operator after the Lagrangian change of variables. -/
noncomputable def kinetic : L.D →ₗ[ℂ] L.D :=
  ((1 / 2 : ℝ) : ℂ) • ∑ i : Fin 3, (L.P i).comp (L.P i)

/-- The viscous term `−νΔ_{ξ,X} = ν∑Qᵢ²`, second order. -/
noncomputable def viscous : L.D →ₗ[ℂ] L.D :=
  ((L.nu : ℝ) : ℂ) • ∑ i : Fin 3, (L.Q i).comp (L.Q i)

/-- The force drift `∑fᵢDᵢ`, first order. -/
noncomputable def drift : L.D →ₗ[ℂ] L.D :=
  ∑ i : Fin 3, ((L.force i : ℝ) : ℂ) • L.drive i

/-- **The full transformed Navier–Stokes Hamiltonian**
`ĥ_full = −½Δ_X − νΔ_{ξ,X} − i f(X)·∇_X + Ĥ_constraint`, on the dense domain
`D`, with no truncation and no boundedness assumption. -/
noncomputable def hFull : L.D →ₗ[ℂ] L.D :=
  L.kinetic + L.viscous + L.drift + L.constraintOp













/-! ### Positivity of the second-order part -/











/-! ### Criteria for essential self-adjointness -/







/-- The eigenvalue of the transformed Hamiltonian on a common eigenvector of its
constituents: `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`. -/
noncomputable def eigenvalue (p q dr : Fin 3 → ℝ) (c : ℝ) : ℝ :=
  (1 / 2) * (∑ i : Fin 3, p i ^ 2) + L.nu * (∑ i : Fin 3, q i ^ 2)
    + (∑ i : Fin 3, L.force i * dr i) + c





end LagrangianFullData

end Abstract

/-! ## The change of variables transfers essential self-adjointness -/

section ChangeOfVariables

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]









end ChangeOfVariables

/-! ## An untruncated instance on `ℓ²(ℤ)`: the kinetic term is a discrete
Laplacian -/

section Lattice

open BookProof.ChapterContinuityUnitaryInfinite FullEsa

/-- **The transformed Navier–Stokes Hamiltonian of the lattice realization**, as
a bounded operator on `ℓ²(ℤ)`: the parcel momenta and the viscous gradients are
the symmetric-difference lattice momentum (so `½∑Pᵢ²` is a discrete Laplacian),
the drift generators and the constraint are multiplication by bounded real
fields. -/
noncomputable def latticeLagCLM (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) :
    L2Z →L[ℂ] L2Z :=
  ((1 / 2 : ℝ) : ℂ) • (∑ _i : Fin 3, momentum * momentum)
    + ((nu : ℝ) : ℂ) • (∑ _i : Fin 3, momentum * momentum)
    + (∑ i : Fin 3, ((fr i : ℝ) : ℂ) • velocityOp (v i))
    + velocityOp w





/-- **The untruncated transformed Navier–Stokes data on the lattice `ℓ²(ℤ)`**,
on the *proper* dense domain of finitely supported modes. -/
noncomputable def latticeLagData (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) : LagrangianFullData L2Z where
  D := finiteModes
  P _ := restrictCLM momentum finiteModes fun f => momentum_mem_finiteModes f.2
  Q _ := restrictCLM momentum finiteModes fun f => momentum_mem_finiteModes f.2
  drive i := restrictCLM (velocityOp (v i)) finiteModes fun f => velocityOp_mem_finiteModes _ f.2
  force := fr
  constraintOp := restrictCLM (velocityOp w) finiteModes fun f => velocityOp_mem_finiteModes _ f.2
  nu := nu
  dense := finiteModes_dense
  P_symm _ := by
    intro x y
    change (inner ℂ (momentum (x : L2Z)) (y : L2Z) : ℂ)
      = inner ℂ (x : L2Z) (momentum (y : L2Z))
    exact momentum_isSymmetric (x : L2Z) (y : L2Z)
  Q_symm _ := by
    intro x y
    change (inner ℂ (momentum (x : L2Z)) (y : L2Z) : ℂ)
      = inner ℂ (x : L2Z) (momentum (y : L2Z))
    exact momentum_isSymmetric (x : L2Z) (y : L2Z)
  drive_symm i := by
    intro x y
    change (inner ℂ (velocityOp (v i) (x : L2Z)) (y : L2Z) : ℂ)
      = inner ℂ (x : L2Z) (velocityOp (v i) (y : L2Z))
    exact velocityOp_isSymmetric (v i) (x : L2Z) (y : L2Z)
  constraint_symm := by
    intro x y
    change (inner ℂ (velocityOp w (x : L2Z)) (y : L2Z) : ℂ)
      = inner ℂ (x : L2Z) (velocityOp w (y : L2Z))
    exact velocityOp_isSymmetric w (x : L2Z) (y : L2Z)
  nu_nonneg := hnu





/-- The zero field of `ℓ^∞(ℤ)`, used to exhibit the purely kinetic realization. -/
noncomputable def zeroField : LinfZ := 0



end Lattice

/-! ## An **unbounded** untruncated instance on `ℓ²(ℕ)` -/

section Diagonal

open LpNat DiagonalEsa FullEsa

/-- The untruncated transformed Navier–Stokes data on `ℓ²(ℕ)` with **diagonal**
constituents: the symbols are arbitrary real sequences, in particular they may
be unbounded. -/
noncomputable def diagLagData (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) : LagrangianFullData L2N where
  D := lpFiniteModes ℕ
  P i := diagOp (p i)
  Q i := diagOp (q i)
  drive i := diagOp (dr i)
  force := fr
  constraintOp := diagOp c
  nu := nu
  dense := lpFiniteModes_dense
  P_symm i := diagOp_isSymmetricDom (p i)
  Q_symm i := diagOp_isSymmetricDom (q i)
  drive_symm i := diagOp_isSymmetricDom (dr i)
  constraint_symm := diagOp_isSymmetricDom c
  nu_nonneg := hnu

/-- The symbol of the diagonal transformed Hamiltonian:
`½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`. -/
noncomputable def diagLagSymbol (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ)
    (nu : ℝ) : ℕ → ℝ :=
  fun n => (1 / 2) * (∑ i : Fin 3, p i n * p i n) + nu * (∑ i : Fin 3, q i n * q i n)
    + (∑ i : Fin 3, fr i * dr i n) + c n





/-- A purely kinetic choice of transformed data whose parcel momentum grows
linearly: the transformed Hamiltonian is `½n²`, unbounded. -/
noncomputable def diagLagUnbounded : LagrangianFullData L2N :=
  diagLagData (fun i => if i = 0 then fun n => (n : ℝ) else fun _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (le_refl (0 : ℝ))







end Diagonal

/-! ## Sharpness: the transformed shape alone does not give ESA -/

section Sharpness

open LpNat JacobiDeficiency FullEsa

/-- Transformed Navier–Stokes data on `ℓ²(ℕ)` whose only nonzero term is the
first-order **drift**, realized by the tridiagonal (limit-circle) operator of
`BookProof.ChapterNavierStokesDeficiency`. -/
noncomputable def jacobiLagData : LagrangianFullData L2N where
  D := lpFiniteModes ℕ
  P _ := 0
  Q _ := 0
  drive i := if i = 0 then jacobiOp else 0
  force i := if i = 0 then 1 else 0
  constraintOp := 0
  nu := 0
  dense := lpFiniteModes_dense
  P_symm _ := IsSymmetricDom.zero
  Q_symm _ := IsSymmetricDom.zero
  drive_symm i := by
    by_cases hi : i = 0
    · rw [hi, if_pos rfl]
      exact fun x y => jacobiOp_symmetric x y
    · rw [if_neg hi]
      exact IsSymmetricDom.zero
  constraint_symm := IsSymmetricDom.zero
  nu_nonneg := le_refl 0





end Sharpness

end LagrangianEsa

end BookProof.NavierStokesFlow


