-- Prove2me | Definitions.Def_ChapterNavierStokesCarleman
-- name    : ChapterNavierStokesCarleman
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T18:58:08.029977+00:00
-- url     : https://prove2.me/theorems/5573cf3d-da2f-438d-b479-c21ed51f90fb
-- title:
--   The Lean 4 theorem `tridiagFun_add` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesCarleman.lean`): generated def bundle for ChapterNavierStokesCarleman. See BookProof/ChapterNavierStokesCarleman.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesCarleman.lean

import Definitions.Def_ChapterNavierStokesFullEsa
import Mathlib


/-!
# Carleman's criterion, and an **unbounded, non-commuting** full Navier–Stokes
Hamiltonian that is essentially self-adjoint

`BookProof.ChapterNavierStokesFullEsa` proves essential self-adjointness of the
full (untruncated) Navier–Stokes Hamiltonian in two infinite-dimensional
realizations: a *bounded* one on `ℓ²(ℤ)`, and an *unbounded but diagonal* one on
`ℓ²(ℕ)`, where the momenta commute with the field modes.  Neither carries the
genuine difficulty of the continuum problem, in which the momentum does **not**
commute with the (possibly unbounded) velocity field.

This module supplies that case.  On the half-line lattice `ℓ²(ℕ)` the momentum
is the symmetric-difference operator `(p f)_n = -(i/2)(f_{n+1} - f_{n-1})`, the
field modes are multiplication by arbitrary real sequences — bounded or not —
and the Weyl-symmetrized Navier–Stokes Hamiltonian
`H = ∑_i (π_i A_i + A_i π_i)` is then a **tridiagonal (Jacobi) operator** whose
off-diagonal couplings are `c_n = -(i/2)(α_n + α_{n+1})`, `α` the total
Navier–Stokes symbol `∑_i (∑_j u_j u_{i,j} − ν u_{i,jj})`.

* `tridiagOp` — the tridiagonal operator with complex couplings `c`, on the
  finite-mode domain of `ℓ²(ℕ)`; `tridiagOp_isSymmetricDom` its symmetry.
* `tridiag_hasZeroDeficiencyOn_of_carleman` — **Carleman's criterion**: if
  `∑ 1/|c_n| = ∞` then the tridiagonal operator is essentially self-adjoint.
  The proof is the classical Wronskian argument: a deficiency vector `w`
  satisfies `c_n w_{n+1} + \bar c_{n-1} w_{n-1} = ± i w_n`, whose Wronskian
  telescopes to `2i ∑_{m ≤ n} |w_m|²`, forcing
  `|w_n| |w_{n+1}| ≥ (∑_{m ≤ n₀} |w_m|²)/|c_n|`; summing contradicts
  `∑ 1/|c_n| = ∞` because `∑ |w_n| |w_{n+1}| ≤ ‖w‖²`.
* `halfLineFullData` — the untruncated Navier–Stokes data on `ℓ²(ℕ)` with the
  symmetric-difference momentum and arbitrary real field modes, and
  `halfLineFullData_hamiltonian`, the identification of its full Hamiltonian
  with a tridiagonal operator.
* `halfLineFull_hasZeroDeficiencyOn` — **the headline**: the full Navier–Stokes
  Hamiltonian of this realization is essentially self-adjoint whenever the
  Navier–Stokes symbol satisfies Carleman's growth condition.
* `linearFull_hasZeroDeficiencyOn` together with `linearFull_not_bounded` — a
  concrete instance: a velocity/viscous field growing **linearly** gives an
  unbounded full Navier–Stokes Hamiltonian, with non-commuting momentum and
  field modes, which is essentially self-adjoint.

*The dichotomy.*  Carleman's condition is a growth restriction: `α_n ∼ n`
diverges (`∑ 1/n = ∞`) and gives essential self-adjointness, while for a field
growing fast enough the sum converges and the criterion is silent — as it must
be, since `BookProof.ChapterNavierStokesDeficiency` exhibits a tridiagonal
operator with geometrically growing couplings that is *not* essentially
self-adjoint, and `BookProof.ChapterNavierStokesFullEsa` realizes it as a full
Navier–Stokes Hamiltonian.  This is the lattice form of the ODE chapter's
`ẋ = x²` warning: quadratic (and faster) growth of the field can destroy
essential self-adjointness, subquadratic growth cannot.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace Carleman

open LpNat DiagonalEsa FullEsa

/-! ## The tridiagonal operator with complex couplings -/



/-- The coefficient action of the tridiagonal operator with couplings `c`:
`(T f)_n = \bar c_{n-1} f_{n-1} + c_n f_{n+1}` (zero diagonal). -/
def tridiagFun (c : ℕ → ℂ) (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => c 0 * f 1
  | (n + 1) => (starRingEnd ℂ) (c n) * f n + c (n + 1) * f (n + 2)

theorem tridiagFun_add (c f g : ℕ → ℂ) (n : ℕ) :
    tridiagFun c (f + g) n = tridiagFun c f n + tridiagFun c g n := by
  cases n with
  | zero => simp only [tridiagFun, Pi.add_apply]; ring
  | succ m => simp only [tridiagFun, Pi.add_apply]; ring

theorem tridiagFun_smul (c : ℕ → ℂ) (a : ℂ) (f : ℕ → ℂ) (n : ℕ) :
    tridiagFun c (a • f) n = a * tridiagFun c f n := by
  cases n with
  | zero => simp only [tridiagFun, Pi.smul_apply, smul_eq_mul]; ring
  | succ m => simp only [tridiagFun, Pi.smul_apply, smul_eq_mul]; ring

theorem tridiagFun_tail_zero (c : ℕ → ℂ) {f : ℕ → ℂ} {N : ℕ} (h : ∀ n, N ≤ n → f n = 0) :
    ∀ n, N + 1 ≤ n → tridiagFun c f n = 0 := by
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
    have hm : N ≤ m := by omega
    simp [tridiagFun, h m hm, h (m + 2) (by omega)]

/-- The tridiagonal operator on the finite-mode domain of `ℓ²(ℕ)`. -/
noncomputable def tridiagOp (c : ℕ → ℂ) : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ where
  toFun f :=
    ⟨⟨tridiagFun c ((f : L2N) : ℕ → ℂ), by
        obtain ⟨N, hN⟩ := exists_tail_zero f.2
        exact memLpTwo_of_tail_zero (tridiagFun_tail_zero c hN)⟩, by
      obtain ⟨N, hN⟩ := exists_tail_zero f.2
      exact mem_lpFiniteModes_of_tail_zero (N := N + 1) (tridiagFun_tail_zero c hN)⟩
  map_add' f g := by
    ext n
    have h := tridiagFun_add c ((f : L2N) : ℕ → ℂ) ((g : L2N) : ℕ → ℂ) n
    exact h.trans (Eq.symm (Pi.add_apply _ _ n))
  map_smul' a f := by
    ext n
    simpa using tridiagFun_smul c a ((f : L2N) : ℕ → ℂ) n

@[simp] theorem tridiagOp_coe (c : ℕ → ℂ) (f : lpFiniteModes ℕ) :
    (((tridiagOp c f : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) = tridiagFun c ((f : L2N) : ℕ → ℂ) := rfl

/-- **The discrete Green identity** for the tridiagonal operator: the failure of
symmetry on a truncated window is a pure boundary term. -/
theorem tridiag_wronskian (c x y : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        (starRingEnd ℂ (tridiagFun c x n) * y n - starRingEnd ℂ (x n) * tridiagFun c y n)
      = starRingEnd ℂ (c N) * (starRingEnd ℂ (x (N + 1)) * y N)
        - c N * (starRingEnd ℂ (x N) * y (N + 1)) := by
  induction N with
  | zero =>
    rw [zero_add, Finset.sum_range_one]
    simp only [tridiagFun, map_mul]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [tridiagFun, map_add, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    ring

/-- The tridiagonal operator is symmetric on the finite-mode domain. -/
theorem tridiagOp_isSymmetricDom (c : ℕ → ℂ) : IsSymmetricDom (tridiagOp c) := by
  intro x y
  obtain ⟨Nx, hNx⟩ := exists_tail_zero x.2
  obtain ⟨Ny, hNy⟩ := exists_tail_zero y.2
  set N := max Nx Ny with hN
  have hx : ∀ n, N ≤ n → ((x : L2N) : ℕ → ℂ) n = 0 :=
    fun n hn => hNx n (le_trans (le_max_left _ _) hn)
  have hy : ∀ n, N ≤ n → ((y : L2N) : ℕ → ℂ) n = 0 :=
    fun n hn => hNy n (le_trans (le_max_right _ _) hn)
  have hlhs := inner_eq_sum_range (f := ((tridiagOp c x : lpFiniteModes ℕ) : L2N))
    (g := ((y : lpFiniteModes ℕ) : L2N)) (N := N + 1)
    (by simpa using tridiagFun_tail_zero c hx)
  have hrhs := inner_eq_sum_range (f := ((x : lpFiniteModes ℕ) : L2N))
    (g := ((tridiagOp c y : lpFiniteModes ℕ) : L2N)) (N := N + 1)
    (fun n hn => hx n (by omega))
  rw [hlhs, hrhs, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [tridiagOp_coe]
  rw [tridiag_wronskian]
  rw [hx N le_rfl, hx (N + 1) (by omega)]
  simp

/-! ## The action on the canonical basis states -/





/-! ## From a deficiency vector to the three-term recursion -/



/-! ## The Wronskian and Carleman's criterion -/

/-- The Wronskian of a solution of the three-term recursion with its
conjugate. -/
noncomputable def wron (c w : ℕ → ℂ) (n : ℕ) : ℂ :=
  c n * (w (n + 1) * starRingEnd ℂ (w n))
    - starRingEnd ℂ (c n) * (starRingEnd ℂ (w (n + 1)) * w n)









/-! ## The half-line realization of the full Navier–Stokes Hamiltonian -/

section HalfLine

open NSFullData

/-- **The half-line momentum**: the symmetric-difference operator
`(p f)_n = -(i/2)(f_{n+1} - f_{n-1})` (with `f_{-1} = 0`), which is exactly the
tridiagonal operator with the constant coupling `-i/2`. -/
noncomputable def momOp : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ :=
  tridiagOp (fun _ => -(Complex.I / 2))

theorem momOp_isSymmetricDom : IsSymmetricDom momOp := tridiagOp_isSymmetricDom _

/-- The couplings produced by Weyl-symmetrizing the half-line momentum against
multiplication by the real sequence `a`. -/
noncomputable def nsCoupling (a : ℕ → ℝ) : ℕ → ℂ := fun n =>
  -(Complex.I / 2) * ((a n : ℂ) + (a (n + 1) : ℂ))







/-- **The untruncated Navier–Stokes data on the half-line lattice**: the fifteen
field modes are multiplication by *arbitrary* — in particular unbounded — real
sequences, and each of the three momenta is the symmetric-difference momentum,
which does **not** commute with the modes. -/
noncomputable def halfLineFullData (c : Fin 15 → ℕ → ℝ) (nu : ℝ) : NSFullData L2N where
  D := lpFiniteModes ℕ
  u k := diagOp (c k)
  mom _ := momOp
  nu := nu
  dense := lpFiniteModes_dense
  u_symm k := diagOp_isSymmetricDom (c k)
  mom_symm _ := momOp_isSymmetricDom
  u_comm k l := by rw [diagOp_comp, diagOp_comp]; simp [mul_comm]

/-- The Navier–Stokes term `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}` as a real
sequence. -/
def halfLineAlpha (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (i : Fin 3) : ℕ → ℝ := fun n =>
  (∑ j : Fin 3, c (nsVelIdx j) n * c (nsGradIdx i j) n) - nu * c (nsLapIdx i) n

/-- The total Navier–Stokes symbol `∑_i A_i`. -/
def halfLineSymbol (c : Fin 15 → ℕ → ℝ) (nu : ℝ) : ℕ → ℝ := fun n =>
  ∑ i : Fin 3, halfLineAlpha c nu i n







/-! ### A concrete unbounded instance: a linearly growing field -/

/-- The field modes of the linear instance: the viscous mode `u_{0,jj}` grows
linearly, every other mode vanishes. -/
noncomputable def linearMode (k : Fin 15) : ℕ → ℝ :=
  if k = nsLapIdx 0 then fun n => -((n : ℝ) + 1) else fun _ => 0

/-- The untruncated half-line Navier–Stokes data with a linearly growing viscous
mode and unit viscosity. -/
noncomputable def linearFullData : NSFullData L2N := halfLineFullData linearMode 1















end HalfLine

end Carleman

end BookProof.NavierStokesFlow


