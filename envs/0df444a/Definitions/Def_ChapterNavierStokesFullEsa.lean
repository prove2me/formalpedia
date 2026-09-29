-- Prove2me | Definitions.Def_ChapterNavierStokesFullEsa
-- name    : ChapterNavierStokesFullEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:29:24.177637+00:00
-- url     : https://prove2.me/theorems/ddcc176d-9b66-4a30-8e66-f0ad1e7106c0
-- title:
--   `BookProof.ChapterNavierStokesFlow` builds the Navier–Stokes Hamiltonian `H = ∑_i (π_i A_i + A_i π_i)`, `A_i = ∑_j u_j u ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesFullEsa`, source chapter `BookProof/ChapterNavierStokesFullEsa.lean`).
--
--   `BookProof.ChapterNavierStokesFlow` builds the Navier–Stokes Hamiltonian `H = ∑_i (π_i A_i + A_i π_i)`, `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}`, for a **finite truncation**: the fifteen field modes and the three momenta are matrices on a finite-dimensional state space. This module removes the truncation: the modes and momenta are now (possibly unbounded) operators on a dense domain `D` of an arbitrary complex inner-product space, and `H` is the same polynomial expression in them.
--
--   * `NSFullData` — the untruncated data: a dense domain `D`, fifteen symmetric, pairwise commuting field modes and three symmetric momenta, all of them mapping `D` into `D`, and a viscosity `ν`. Nothing is finite-dimensional and nothing is bounded. * `NSFullData.hamiltonian_isSymmetricDom` — **the full Hamiltonian is symmetric on its domain**, unconditionally. * `NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow` — **essential self-adjointness of the full Hamiltonian from a complete unitary flow** (Nelson's route), and `NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors`, the eigenvector route. * `NSFullData.hasZeroDeficiencyOn_of_boundedRealization` — if the full Hamiltonian is the restriction of a bounded symmetric operator, it is essentially self-adjoint on `D`. * **A genuinely infinite-dimensional, untruncated instance**: on `ℓ²(ℤ)`, with all fifteen modes realized as multiplication by bounded real velocity fields and the momenta as the lattice (symmetric-difference) momentum, the full Navier–Stokes Hamiltonian is essentially self-adjoint on the **proper** dense domain of finitely supported modes: `latticeFull_hasZeroDeficiencyOn`. The operator is not the zero operator (`latticeFullHamiltonianCLM_ne_zero`). * **An unbounded instance**: on `ℓ²(ℕ)`, with all modes and momenta diagonal with (possibly unbounded) real symbols, the full Hamiltonian is essentially self-adjoint on the finite-mode domain (`diagFull_hasZeroDeficiencyOn`), and for a suitable choice of data it is genuinely unbounded (`diagFull_not_bounded`). So essential self-adjointness of the *full* Hamiltonian is not a boundedness phenomenon. * **Sharpness.** `exists_nsFullData_not_hasZeroDeficiencyOn`: there is untruncated Navier–Stokes data on `ℓ²(ℕ)` — dense domain, symmetric pairwise commuting modes, symmetric momenta, positive viscosity — whose full Hamiltonian is **not** essentially self-adjoint. Hence the structural hypotheses alone (Hermitian modes and momenta, degree ≤ 3) can never yield essential self-adjointness of the full operator: an analytic input such as completeness of the flow is indispensable. This is the formal counterpart of the `ẋ = x²` warning of the ODE chapter.
--
--   Essential self-adjointness of the *continuum* Navier–Stokes generator, and with it global existence for Navier–Stokes, is **not** claimed: the positive results above are unconditional for the realizations described (bounded lattice modes, diagonal modes), and conditional — on a complete unitary flow, resp. a total family of eigenvectors — in general, which by `exists_nsFullData_not_hasZeroDeficiencyOn` is the best possible shape for a statement about the abstract data.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFullEsa.lean

import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Mathlib

import Mathlib

/-!
# The **full** (untruncated) Navier–Stokes Hamiltonian and its essential
self-adjointness

`BookProof.ChapterNavierStokesFlow` builds the Navier–Stokes Hamiltonian
`H = ∑_i (π_i A_i + A_i π_i)`, `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}`, for a
**finite truncation**: the fifteen field modes and the three momenta are
matrices on a finite-dimensional state space.  This module removes the
truncation: the modes and momenta are now (possibly unbounded) operators on a
dense domain `D` of an arbitrary complex inner-product space, and `H` is the
same polynomial expression in them.

## What is proved here

* `NSFullData` — the untruncated data: a dense domain `D`, fifteen symmetric,
  pairwise commuting field modes and three symmetric momenta, all of them
  mapping `D` into `D`, and a viscosity `ν`.  Nothing is finite-dimensional and
  nothing is bounded.
* `NSFullData.hamiltonian_isSymmetricDom` — **the full Hamiltonian is symmetric
  on its domain**, unconditionally.
* `NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow` — **essential
  self-adjointness of the full Hamiltonian from a complete unitary flow**
  (Nelson's route), and `NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors`,
  the eigenvector route.
* `NSFullData.hasZeroDeficiencyOn_of_boundedRealization` — if the full
  Hamiltonian is the restriction of a bounded symmetric operator, it is
  essentially self-adjoint on `D`.
* **A genuinely infinite-dimensional, untruncated instance**: on `ℓ²(ℤ)`, with
  all fifteen modes realized as multiplication by bounded real velocity fields
  and the momenta as the lattice (symmetric-difference) momentum, the full
  Navier–Stokes Hamiltonian is essentially self-adjoint on the **proper** dense
  domain of finitely supported modes: `latticeFull_hasZeroDeficiencyOn`.  The
  operator is not the zero operator (`latticeFullHamiltonianCLM_ne_zero`).
* **An unbounded instance**: on `ℓ²(ℕ)`, with all modes and momenta diagonal
  with (possibly unbounded) real symbols, the full Hamiltonian is essentially
  self-adjoint on the finite-mode domain (`diagFull_hasZeroDeficiencyOn`), and
  for a suitable choice of data it is genuinely unbounded
  (`diagFull_not_bounded`).  So essential self-adjointness of the *full*
  Hamiltonian is not a boundedness phenomenon.
* **Sharpness.** `exists_nsFullData_not_hasZeroDeficiencyOn`: there is
  untruncated Navier–Stokes data on `ℓ²(ℕ)` — dense domain, symmetric pairwise
  commuting modes, symmetric momenta, positive viscosity — whose full
  Hamiltonian is **not** essentially self-adjoint.  Hence the structural
  hypotheses alone (Hermitian modes and momenta, degree ≤ 3) can never yield
  essential self-adjointness of the full operator: an analytic input such as
  completeness of the flow is indispensable.  This is the formal counterpart of
  the `ẋ = x²` warning of the ODE chapter.

## Scope

Essential self-adjointness of the *continuum* Navier–Stokes generator, and with
it global existence for Navier–Stokes, is **not** claimed: the positive results
above are unconditional for the realizations described (bounded lattice modes,
diagonal modes), and conditional — on a complete unitary flow, resp. a total
family of eigenvectors — in general, which by
`exists_nsFullData_not_hasZeroDeficiencyOn` is the best possible shape for a
statement about the abstract data.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace FullEsa

/-! ## Symmetry of domain-preserving operators -/

section SymmetricDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Symmetry of an operator that maps the domain `D` into itself. -/
def IsSymmetricDom {D : Submodule ℂ F} (A : D →ₗ[ℂ] D) : Prop :=
  ∀ x y : D, (inner ℂ ((A x : F)) (y : F) : ℂ) = inner ℂ (x : F) ((A y : F))

variable {D : Submodule ℂ F}





theorem IsSymmetricDom.real_smul {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (r : ℝ) :
    IsSymmetricDom ((r : ℂ) • A) := by
  intro x y
  simp only [LinearMap.smul_apply, Submodule.coe_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hA x y]

theorem IsSymmetricDom.zero : IsSymmetricDom (0 : D →ₗ[ℂ] D) := by
  intro x y
  simp







end SymmetricDom

/-! ## Transferring vanishing deficiency along an equality of operators -/

section Transfer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



/-- The restriction of a bounded operator to an invariant domain. -/
noncomputable def restrictCLM (A : F →L[ℂ] F) (D : Submodule ℂ F) (h : ∀ v : D, A (v : F) ∈ D) :
    D →ₗ[ℂ] D :=
  LinearMap.codRestrict D ((A : F →ₗ[ℂ] F).comp D.subtype) h





end Transfer

/-! ## The untruncated Navier–Stokes data and Hamiltonian -/

section AbstractFull

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The untruncated Navier–Stokes data.**  The fifteen field modes `u_k` and
the three momenta `π_i` of `book.tex` ~4151–4189, now as operators on a *dense
domain* `D` of an arbitrary complex inner-product space — no truncation, no
finite dimension, no boundedness.  The hypotheses are exactly the structural
ones of the truncated `NSTruncation`: the modes and momenta are symmetric on
`D`, they map `D` into itself, and the field modes commute with one another. -/
structure NSFullData (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  /-- The dense domain. -/
  D : Submodule ℂ F
  /-- The fifteen field modes. -/
  u : Fin 15 → (D →ₗ[ℂ] D)
  /-- The three momenta. -/
  mom : Fin 3 → (D →ₗ[ℂ] D)
  /-- The kinematic viscosity. -/
  nu : ℝ
  dense : Dense (D : Set F)
  u_symm : ∀ k, IsSymmetricDom (u k)
  mom_symm : ∀ i, IsSymmetricDom (mom i)
  u_comm : ∀ k l, (u k).comp (u l) = (u l).comp (u k)

namespace NSFullData

variable (d : NSFullData F)

/-- The velocity mode `u_j`. -/
def velocity (j : Fin 3) : d.D →ₗ[ℂ] d.D := d.u (nsVelIdx j)

/-- The derivative mode `u_{i,j}`. -/
def gradVelocity (i j : Fin 3) : d.D →ₗ[ℂ] d.D := d.u (nsGradIdx i j)

/-- The second-derivative mode `u_{i,jj}`. -/
def lapVelocity (i : Fin 3) : d.D →ₗ[ℂ] d.D := d.u (nsLapIdx i)

/-- The full Navier–Stokes term `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}`. -/
noncomputable def advection (i : Fin 3) : d.D →ₗ[ℂ] d.D :=
  (∑ j : Fin 3, (d.velocity j).comp (d.gradVelocity i j)) - (d.nu : ℂ) • d.lapVelocity i

/-- **The full (untruncated) Navier–Stokes Hamiltonian**
`H = ∑_i (π_i A_i + A_i π_i)`, on the dense domain `D`. -/
noncomputable def hamiltonian : d.D →ₗ[ℂ] d.D :=
  ∑ i : Fin 3, ((d.mom i).comp (d.advection i) + (d.advection i).comp (d.mom i))











end NSFullData

end AbstractFull

/-! ## An untruncated instance on `ℓ²(ℤ)`: all fifteen modes, no truncation -/

section Lattice

open BookProof.ChapterContinuityUnitaryInfinite

/-- Multiplication operators by bounded real fields commute. -/
theorem velocityOp_commute (a b : LinfZ) : Commute (velocityOp a) (velocityOp b) := by
  ext f n
  simp only [ContinuousLinearMap.mul_apply, velocityOp_apply]
  ring

theorem momentum_mem_finiteModes {f : L2Z} (hf : f ∈ finiteModes) : momentum f ∈ finiteModes := by
  have hstep := Submodule.smul_mem finiteModes (-Complex.I / 2)
    (Submodule.sub_mem finiteModes (shiftOp_mem_finiteModes 1 hf)
      (shiftOp_mem_finiteModes (-1) hf))
  simpa [momentum] using hstep

/-- The Navier–Stokes term `A_i` of the lattice realization, as a bounded
operator. -/
noncomputable def latticeAdvectionCLM (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) :
    L2Z →L[ℂ] L2Z :=
  (∑ j : Fin 3, velocityOp (v (nsVelIdx j)) * velocityOp (v (nsGradIdx i j)))
    - (nu : ℂ) • velocityOp (v (nsLapIdx i))

/-- **The full Navier–Stokes Hamiltonian of the lattice realization**, as a
bounded operator on `ℓ²(ℤ)`. -/
noncomputable def latticeFullHamiltonianCLM (v : Fin 15 → LinfZ) (nu : ℝ) : L2Z →L[ℂ] L2Z :=
  ∑ i : Fin 3, (momentum * latticeAdvectionCLM v nu i + latticeAdvectionCLM v nu i * momentum)











/-- **The untruncated Navier–Stokes data on the lattice `ℓ²(ℤ)`**: all fifteen
field modes are multiplication by bounded real velocity fields, the momenta are
the symmetric-difference lattice momentum, and the domain is the *proper* dense
subspace of finitely supported modes. -/
noncomputable def latticeFullData (v : Fin 15 → LinfZ) (nu : ℝ) : NSFullData L2Z where
  D := finiteModes
  u k := restrictCLM (velocityOp (v k)) finiteModes fun f => velocityOp_mem_finiteModes _ f.2
  mom _ := restrictCLM momentum finiteModes fun f => momentum_mem_finiteModes f.2
  nu := nu
  dense := finiteModes_dense
  u_symm k := by
    intro x y
    change (inner ℂ (velocityOp (v k) (x : L2Z)) (y : L2Z) : ℂ)
      = inner ℂ (x : L2Z) (velocityOp (v k) (y : L2Z))
    exact velocityOp_isSymmetric (v k) (x : L2Z) (y : L2Z)
  mom_symm _ := by
    intro x y
    change (inner ℂ (momentum (x : L2Z)) (y : L2Z) : ℂ)
      = inner ℂ (x : L2Z) (momentum (y : L2Z))
    exact momentum_isSymmetric (x : L2Z) (y : L2Z)
  u_comm k l := by
    refine LinearMap.ext fun f => Subtype.ext ?_
    change (velocityOp (v k)) ((velocityOp (v l)) (f : L2Z))
        = (velocityOp (v l)) ((velocityOp (v k)) (f : L2Z))
    have h := congrArg (fun T : L2Z →L[ℂ] L2Z => T (f : L2Z)) (velocityOp_commute (v k) (v l))
    simpa using h





/-- The constant real field on the lattice, as an element of `ℓ^∞(ℤ)`. -/
noncomputable def constField (r : ℝ) : LinfZ :=
  ⟨fun _ => r, memℓp_infty ⟨|r|, by rintro s ⟨k, rfl⟩; simp⟩⟩







end Lattice

/-! ## An **unbounded** untruncated instance on `ℓ²(ℕ)` -/

section Diagonal

open LpNat DiagonalEsa

theorem diagOp_isSymmetricDom (c : ℕ → ℝ) : IsSymmetricDom (diagOp c) := by
  intro x y
  obtain ⟨Nx, hNx⟩ := exists_tail_zero x.2
  obtain ⟨Ny, hNy⟩ := exists_tail_zero y.2
  set N := max Nx Ny with hN
  have hx : ∀ n, N ≤ n → ((x : L2N) : ℕ → ℂ) n = 0 :=
    fun n hn => hNx n (le_trans (le_max_left _ _) hn)
  have hy : ∀ n, N ≤ n → ((y : L2N) : ℕ → ℂ) n = 0 :=
    fun n hn => hNy n (le_trans (le_max_right _ _) hn)
  have hlhs := inner_eq_sum_range (f := ((diagOp c x : lpFiniteModes ℕ) : L2N))
    (g := ((y : lpFiniteModes ℕ) : L2N)) (N := N)
    (by simpa using diagFun_tail_zero c hx)
  have hrhs := inner_eq_sum_range (f := ((x : lpFiniteModes ℕ) : L2N))
    (g := ((diagOp c y : lpFiniteModes ℕ) : L2N)) (N := N) hx
  rw [hlhs, hrhs]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [diagOp_coe, diagFun, map_mul, Complex.conj_ofReal]
  ring

theorem diagOp_comp (a b : ℕ → ℝ) : (diagOp a).comp (diagOp b) = diagOp (fun n => a n * b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.comp_apply, diagOp_coe, diagFun, Complex.ofReal_mul]
  ring









/-- The untruncated Navier–Stokes data on `ℓ²(ℕ)` with **diagonal** modes and
momenta: the symbols `c k` and `p i` are arbitrary real sequences, in particular
they may be unbounded. -/
noncomputable def diagFullData (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) :
    NSFullData L2N where
  D := lpFiniteModes ℕ
  u k := diagOp (c k)
  mom i := diagOp (p i)
  nu := nu
  dense := lpFiniteModes_dense
  u_symm k := diagOp_isSymmetricDom (c k)
  mom_symm i := diagOp_isSymmetricDom (p i)
  u_comm k l := by rw [diagOp_comp, diagOp_comp]; simp [mul_comm]

/-- The symbol of the diagonal full Navier–Stokes Hamiltonian. -/
def diagFullSymbol (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) : ℕ → ℝ := fun n =>
  ∑ i : Fin 3, 2 * (p i n *
    ((∑ j : Fin 3, c (nsVelIdx j) n * c (nsGradIdx i j) n) - nu * c (nsLapIdx i) n))





/-- A choice of data whose full Hamiltonian is **unbounded**: the first momentum
grows linearly, the viscous mode is constant. -/
noncomputable def diagUnboundedData : NSFullData L2N :=
  diagFullData (fun k => if k = nsLapIdx 0 then fun _ => 1 else fun _ => 0)
    (fun i => if i = 0 then fun n => (n : ℝ) else fun _ => 0) 1







end Diagonal

/-! ## Sharpness: the structural hypotheses alone do not give ESA -/

section Sharpness

open LpNat JacobiDeficiency

/-- The constant field modes of the counterexample: `u_{0,jj} = -1/2`, all other
modes zero. -/
noncomputable def jacobiMode (k : Fin 15) : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
  if k = nsLapIdx 0 then ((-1 / 2 : ℝ) : ℂ) • LinearMap.id else 0

/-- The momenta of the counterexample: `π₀` is the tridiagonal operator, the
other two vanish. -/
noncomputable def jacobiMom (i : Fin 3) : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
  if i = 0 then jacobiOp else 0

theorem jacobiMode_lap : jacobiMode (nsLapIdx 0) = ((-1 / 2 : ℝ) : ℂ) • LinearMap.id :=
  if_pos rfl

theorem jacobiMode_of_ne {k : Fin 15} (h : k ≠ nsLapIdx 0) : jacobiMode k = 0 := if_neg h

theorem jacobiMom_zero : jacobiMom 0 = jacobiOp := if_pos rfl

theorem jacobiMom_of_ne {i : Fin 3} (h : i ≠ 0) : jacobiMom i = 0 := if_neg h

theorem jacobiMode_isSymmetricDom (k : Fin 15) : IsSymmetricDom (jacobiMode k) := by
  by_cases hk : k = nsLapIdx 0
  · rw [hk, jacobiMode_lap]
    exact IsSymmetricDom.real_smul
      (A := (LinearMap.id : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ)) (fun _ _ => rfl) (-1 / 2)
  · rw [jacobiMode_of_ne hk]
    exact IsSymmetricDom.zero

theorem jacobiMode_comm (k l : Fin 15) :
    (jacobiMode k).comp (jacobiMode l) = (jacobiMode l).comp (jacobiMode k) := by
  by_cases hk : k = nsLapIdx 0
  · by_cases hl : l = nsLapIdx 0
    · rw [hk, hl]
    · rw [jacobiMode_of_ne hl, LinearMap.comp_zero, LinearMap.zero_comp]
  · rw [jacobiMode_of_ne hk, LinearMap.comp_zero, LinearMap.zero_comp]

/-- Untruncated Navier–Stokes data on `ℓ²(ℕ)` whose full Hamiltonian is the
tridiagonal operator of `BookProof.ChapterNavierStokesDeficiency`: the field
modes are constants (a uniform velocity field with a constant viscous mode
`u_{0,jj} = −1/2`) and the first momentum is the Jacobi operator. -/
noncomputable def jacobiFullData : NSFullData L2N where
  D := lpFiniteModes ℕ
  u := jacobiMode
  mom := jacobiMom
  nu := 1
  dense := lpFiniteModes_dense
  u_symm := jacobiMode_isSymmetricDom
  mom_symm i := by
    by_cases hi : i = 0
    · rw [hi, jacobiMom_zero]
      exact fun x y => jacobiOp_symmetric x y
    · rw [jacobiMom_of_ne hi]
      exact IsSymmetricDom.zero
  u_comm := jacobiMode_comm





end Sharpness

end FullEsa

end BookProof.NavierStokesFlow


