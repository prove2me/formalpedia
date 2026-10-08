-- Prove2me | Definitions.Def_ChapterNavierStokesFockEsa
-- name    : ChapterNavierStokesFockEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T17:08:32.264177+00:00
-- url     : https://prove2.me/theorems/b9038071-9ba3-4e9c-9dff-d61d4a67fb94
-- title:
--   The Lean 4 theorem `dGamma_isSymmetricDom` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesFockEsa.lean`): generated def bundle for ChapterNavierStokesFockEsa. See BookProof/ChapterNavierStokesFockEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockEsa.lean

import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_isSymmetricDom

import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_fockDom_dense

import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib


/-!
# Essential self-adjointness of the full Navier–Stokes Hamiltonian in the
Lagrangian variables, on the Fock space of a Fock space

After the Lagrangian change of variables the Navier–Stokes Hamiltonian is a
*second* quantization.  The Eulerian velocity `u` is already an operator on a
Fock space; in the parcel variables `X(ξ)` one quantizes the parcels as well, so
the state space is the Fock space **over a Fock space** built in
`BookProof.ChapterNavierStokesFockSpace`, and the transformed Hamiltonian is
**quadratic in the outer creation and annihilation operators**,

`ĥ = ∫_Ω dξ  a†(ξ) h₁ a(ξ)`,

an integral of operators over the (infinite, continuous) parcel domain `Ω`, with
`h₁` the one-parcel Lagrangian symbol `½∑ᵢpᵢ² + ν∑ᵢqᵢ² + ∑ᵢfᵢdᵢ + c`.

## What is proved here

* `dGamma ω` — the second quantization `∑ₘ ωₘ a†ₘ aₘ` of a real one-particle
  symbol, on the dense finite-particle domain, with
  `dGamma_eq_sum_numberOp`: it *is* the quadratic expression in the ladder
  operators; `dGamma_isSymmetricDom`; and `dGamma_hasZeroDeficiencyOn` — **it is
  essentially self-adjoint, with no boundedness assumption**.
* `confEnergy_eq_integral` and `dGamma_inner_eq_integral` — **the integral over
  the continuous domain**: if the one-particle symbol is given by
  `ωₘ = ∫_Ω w(ξ) ρₘ(ξ) dξ` — the mode `m` weighted against a field `w` on `Ω` —
  then the quadratic form of the Hamiltonian is the integral over `Ω` of the
  quadratic forms of the local number-density operators `N(ξ) = a†(ξ)a(ξ)`.
* `twoLevelSymbol`, `hTwoLevel`, `hTwoLevel_hasZeroDeficiencyOn` — the two-level
  (Fock-of-Fock) Hamiltonian, whose one-parcel symbol is the external parcel
  energy plus the *internal* Fock energy of the field carried by that parcel; it
  is essentially self-adjoint.
* `lagrangianFockData`, `lagrangianFock_hasZeroDeficiencyOn` — the untruncated
  Lagrangian data of `BookProof.ChapterNavierStokesLagrangianEsa` realized on the
  Fock-of-Fock space, with the parcel momenta, viscous gradients, force drift and
  constraint all second-quantized: **the full transformed Navier–Stokes
  Hamiltonian `ĥ_full = ½∑Pᵢ² + ν∑Qᵢ² + ∑fᵢDᵢ + C` is essentially self-adjoint
  there, unconditionally**, and `lagrangianFock_not_bounded` shows this is not a
  boundedness phenomenon.
* `hFull_eq_hFock_oneParticle` — on one-parcel states the four-term Lagrangian
  operator agrees with the genuinely quadratic second quantization `dΓ(h₁)`.
* `nsFullData_hasZeroDeficiencyOn_of_fockLagrangian` — combined with the
  unitary-invariance of the property, essential self-adjointness proved *after*
  the change of variables gives it for the Eulerian operator it came from.
* `intervalModes` — a concrete realization on the infinite continuous domain
  `Ω = ℝ` with Lebesgue measure: parcel modes localized in the unit intervals
  `(j, j+1]`, weighted by the unbounded external field `w(ξ) = ξ²`.  The
  resulting symbol is unbounded (`intervalSymbol_unbounded`), so the
  Hamiltonian is an unbounded, essentially self-adjoint operator whose
  coefficients are honest integrals over `ℝ`.

## Scope

Nothing here claims essential self-adjointness of the *continuum* Navier–Stokes
generator with its full nonlinear structure: what is proved is that the
transformed Hamiltonian, in its second-quantized (quadratic) Fock-of-Fock form
with a real one-parcel symbol given by integrals over the continuous parcel
domain, is essentially self-adjoint on the finite-particle domain, and that this
transfers back through the change of variables.
-/

open MeasureTheory

namespace BookProof.NavierStokesFlow

namespace FockOfFock

open FullEsa LagrangianEsa

/-! ## Second quantization of a one-particle symbol -/

section SecondQuantization

variable {M : Type*} [DecidableEq M]

/-- The total energy of an occupation configuration for the one-particle symbol
`ω`: `E(n) = ∑ₘ nₘ ωₘ`. -/
noncomputable def confEnergy (ω : M → ℝ) (n : Conf M) : ℝ :=
  ∑ m ∈ n.support, (n m : ℝ) * ω m





/-- **The second quantization** `dΓ(ω) = ∑ₘ ωₘ a†ₘ aₘ` of a real one-particle
symbol, on the dense finite-particle domain of the Fock space. -/
noncomputable def dGamma (ω : M → ℝ) : FockDom M →ₗ[ℂ] FockDom M := lpDiag (confEnergy ω)



omit [DecidableEq M] in
theorem dGamma_isSymmetricDom (ω : M → ℝ) : IsSymmetricDom (dGamma ω) :=
  lpDiag_isSymmetricDom _









/-! ### The number operators, and quadraticity in the ladder operators -/

/-- The occupation-number operator of the mode `m`: `Nₘ = a†ₘ aₘ`. -/
noncomputable def numberOp (m : M) : FockDom M →ₗ[ℂ] FockDom M := (creat m).comp (annih m)





end SecondQuantization

/-! ## The integral over the continuous parcel domain -/

section Continuum

variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]

/-- The particle density of a configuration at the point `ξ` of the parcel
domain: `ρₙ(ξ) = ∑ₘ nₘ ρₘ(ξ)`, where `ρₘ = |eₘ|²` is the density of the mode
`m`. -/
noncomputable def confDensity (dens : M → Ω → ℝ) (n : Conf M) (ξ : Ω) : ℝ :=
  ∑ m ∈ n.support, (n m : ℝ) * dens m ξ

/-- The one-particle symbol produced by weighting each mode density against the
field `w` on the parcel domain: `ωₘ = ∫_Ω w(ξ) ρₘ(ξ) dξ`. -/
noncomputable def symbolOfIntegral (μ : Measure Ω) (w : Ω → ℝ) (dens : M → Ω → ℝ) (m : M) : ℝ :=
  ∫ ξ, w ξ * dens m ξ ∂μ



/-- The **local number-density operator** `N(ξ) = a†(ξ)a(ξ)`: the operator whose
occupation eigenvalue is the particle density of the configuration at `ξ`. -/
noncomputable def numberDensityOp (dens : M → Ω → ℝ) (ξ : Ω) : FockDom M →ₗ[ℂ] FockDom M :=
  lpDiag (fun n => confDensity dens n ξ)









end Continuum

/-! ## The two-level (Fock-of-Fock) Hamiltonian -/

section TwoLevel

variable {J K : Type*} [DecidableEq J] [DecidableEq K]

/-- **The one-parcel symbol of the two-level Hamiltonian**: a parcel in the
parcel mode `j` carrying the inner Fock (occupation) state `c` has energy
`ext j + ∑ₖ cₖ εₖ` — its external Lagrangian energy plus the *internal* energy
of the quantum field it carries. -/
noncomputable def twoLevelSymbol (ext : J → ℝ) (eps : K → ℝ) : J × Conf K → ℝ :=
  fun m => ext m.1 + confEnergy eps m.2

/-- **The Hamiltonian on the Fock space of a Fock space**: the second
quantization of the one-parcel symbol, quadratic in the outer ladder
operators. -/
noncomputable def hTwoLevel (ext : J → ℝ) (eps : K → ℝ) :
    FockOfFockDom J K →ₗ[ℂ] FockOfFockDom J K :=
  dGamma (twoLevelSymbol ext eps)









end TwoLevel

/-! ## The transformed Navier–Stokes Hamiltonian on the Fock-of-Fock space -/

section LagrangianFock

variable {M : Type*} [DecidableEq M]

/-- **The one-parcel Lagrangian symbol**
`h₁ = ½∑ᵢpᵢ² + ν∑ᵢqᵢ² + ∑ᵢfᵢdᵢ + c`: the advective (kinetic) energy of the
parcel, its viscous energy, the work of the external force and the
volume-preservation constraint. -/
noncomputable def lagSymbol (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ)
    (cst : M → ℝ) : M → ℝ := fun m =>
  (1 / 2) * (∑ i : Fin 3, p i m ^ 2) + nu * (∑ i : Fin 3, q i m ^ 2)
    + (∑ i : Fin 3, force i * dr i m) + cst m

/-- **The full transformed Navier–Stokes Hamiltonian in its second-quantized
form** `ĥ = ∑ₘ h₁(m) a†ₘ aₘ`: quadratic in the parcel creation and annihilation
operators. -/
noncomputable def hFockLag (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) :
    FockDom M →ₗ[ℂ] FockDom M :=
  dGamma (lagSymbol nu p q dr force cst)



/-- **The untruncated Lagrangian Navier–Stokes data realized on the Fock space of
a Fock space.**  The parcel momenta, the viscous gradients, the force drift
generators and the volume-preservation constraint are all second quantizations
of real one-parcel symbols on the dense finite-particle domain. -/
noncomputable def lagrangianFockData (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ)
    (force : Fin 3 → ℝ) (cst : M → ℝ) : LagrangianFullData (FockL2 M) where
  D := FockDom M
  P := fun i => dGamma (p i)
  Q := fun i => dGamma (q i)
  drive := fun i => dGamma (dr i)
  force := force
  constraintOp := dGamma cst
  nu := nu
  dense := fockDom_dense
  P_symm := fun _ => dGamma_isSymmetricDom _
  Q_symm := fun _ => dGamma_isSymmetricDom _
  drive_symm := fun _ => dGamma_isSymmetricDom _
  constraint_symm := dGamma_isSymmetricDom _
  nu_nonneg := hnu







end LagrangianFock

/-! ## Back to the Eulerian operator -/

section Transfer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {M : Type*} [DecidableEq M]



end Transfer

/-! ## A concrete realization over the infinite continuous domain `ℝ` -/

section IntervalModes

variable {K : Type*} [DecidableEq K]

/-- The density of the parcel mode `j`: the parcel is localized in the unit
interval `(j, j+1]` of the parcel domain `ℝ`. -/
noncomputable def intervalDens (j : ℕ) : ℝ → ℝ :=
  Set.indicator (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) (fun _ => 1)

/-- The external field on the parcel domain, `w(ξ) = ξ²` — unbounded, as an
external potential on an infinite domain generally is. -/
noncomputable def extField : ℝ → ℝ := fun ξ => ξ ^ 2









/-- The one-parcel symbol of the concrete two-level model: the external energy of
the parcel, given by an integral over the infinite continuous domain `ℝ`, plus
the internal Fock energy of the field the parcel carries. -/
noncomputable def intervalTwoLevelSymbol (eps : K → ℝ) : ℕ × Conf K → ℝ := fun m =>
  symbolOfIntegral volume extField intervalDens m.1 + confEnergy eps m.2



/-- The parcel-mode densities of the two-level model, as densities on the parcel
domain `ℝ`: a parcel of outer mode `(j, c)` is localized in `(j, j+1]` whatever
inner Fock state `c` it carries. -/
noncomputable def parcelDens : ℕ × Conf K → ℝ → ℝ := fun m ξ => intervalDens m.1 ξ

/-- The internal (inner-Fock) part of the one-parcel symbol. -/
noncomputable def innerEnergySymbol (eps : K → ℝ) : ℕ × Conf K → ℝ := fun m => confEnergy eps m.2







end IntervalModes

end FockOfFock

end BookProof.NavierStokesFlow


