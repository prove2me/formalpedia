-- Prove2me | Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- name    : ChapterNavierStokesAffineFiberEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:56:32.873631+00:00
-- url     : https://prove2.me/theorems/5e87950b-4e6f-400a-acb4-2cd07d637558
-- title:
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine inequalities, and hence essential self-adj ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesAffineFiberEsa`, source chapter `BookProof/ChapterNavierStokesAffineFiberEsa.lean`).
--
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine inequalities, and hence essential self-adjointness on the finite-mode core, for the Navier–Stokes fiber Hamiltonian `H = ½(π V + V π)` with a **linear** advection field `V(u) = κ u`. `BookProof.ChapterNavierStokesBilinearEsa` lifts that to the genuinely bilinear (quadratic-symbol) advection term by decomposing `ℓ²(ℕ × J)` into blocks, one for each eigenvalue `κ_j` of the derivative field.
--
--   The boundary recorded there was the **affine** fiber field
--
--   `V(u) = κ u + c`,
--
--   which is what the viscous term `−ν u_{i,jj}` and the cross terms `u_j u_{i,j}` with `j ≠ i` produce: they contribute a term that is *constant* in the velocity mode `u_i` being differentiated. In the Hermite basis of the fiber, `½(π V + V π) = κ · ½(π u + u π) + c · π`, and while `½(π u + u π) = (i/2)(a†² − a²)` is a `±2`-shift (the operator of `ChapterNavierStokes‐ HermiteFarisLavine`), the extra term `c · π = (i c/√2)(a† − a)` is a **`±1` shift**. This module removes that boundary.
--
--   The Faris–Lavine hypotheses used in this project (`BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`) are
--
--   * `H` symmetric, `N ≥ 0` with `N + 1` surjective, * a **relative bound** `‖Hx‖² ≤ a‖Nx‖² + b‖x‖²` — with *no* smallness requirement on `a`, and * a **commutator bound** `|⟪x, i[H, N]x⟫| ≤ c ⟪x, Nx⟫`.
--
--   All three are stable under sums: `‖(H₁+H₂)x‖² ≤ 2‖H₁x‖² + 2‖H₂x‖²` and the commutator form is additive in `H`. So two shift Hamiltonians sharing one comparison operator may simply be added. That is the content of `PairShift` below: a single symbol `σ` carrying two shifts at once.
--
--   * `PairShift.pairH` — the sum of two shift Hamiltonians with a common comparison symbol, on the maximal domain of that symbol; * `PairShift.pairH_symmetricOn`, `PairShift.pairH_relative_bound`, `PairShift.pairH_commForm_bound` — the two Faris–Lavine inequalities for the sum, with explicit constants; * `PairShift.pairH_essentiallySelfAdjointOn_core` — the sum is essentially self-adjoint on the finite-mode core; * `affH` — the affine Navier–Stokes fiber Hamiltonian `½(π V + V π)` for `V(u) = κ u + c`, in the Hermite basis of `ℓ²(ℕ)`; * `affH_symmetricOn`, `affH_essentiallySelfAdjointOn_core` — **the headline**: the affine fiber Hamiltonian is symmetric and essentially self-adjoint on the finite-mode core, for all `κ ≥ 0` and `c ≥ 0`; * `affH_coord_succ` and `affH_coord_succ_succ` — the two matrix entries of `H` on a Hermite basis vector: the `±1`-hopping `(c/√2)√(n+1)` of the constant part and the `±2`-hopping `(κ/2)√((n+1)(n+2))` of the linear part; * `affH_ne_zero_of_pos_shear` and `affH_not_bounded` — the `±1`-hopping really is present when `c > 0`, and the operator is genuinely unbounded when `κ > 0`.
--
--   `c ≥ 0` is assumed, only because a `ShiftData` amplitude is required to be non-negative; the case `c < 0` is the conjugate of the case `|c|` by the sign-flip unitary `x_n ↦ (−1)ⁿ x_n`, which reverses the sign of a `±1`-hopping and preserves a `±2`-hopping — that unitary equivalence is *not* formalized here, so nothing below is claimed for `c < 0`. The comparison operator used is `N = μ(2n+1) + 1` with `μ = κ + c + 1`, i.e. the harmonic-oscillator number operator rescaled so as to dominate both amplitudes. As in the modules quoted above, everything is stated on the abstract sequence space `ℓ²(ℕ)` with the operator given by its matrix in the Hermite basis; the differential realization on `L²(du)` is not built here. Only one velocity component is carried, and nothing here claims global regularity for the classical Navier–Stokes equation.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesAffineFiberEsa.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFreeFieldConstraint
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterU

import Mathlib

import Mathlib

/-!
# The **affine** Navier–Stokes fiber field: a `±1`-shift on top of the `±2`-shift

`BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine
inequalities, and hence essential self-adjointness on the finite-mode core, for
the Navier–Stokes fiber Hamiltonian `H = ½(π V + V π)` with a **linear**
advection field `V(u) = κ u`.  `BookProof.ChapterNavierStokesBilinearEsa` lifts
that to the genuinely bilinear (quadratic-symbol) advection term by decomposing
`ℓ²(ℕ × J)` into blocks, one for each eigenvalue `κ_j` of the derivative field.

The boundary recorded there was the **affine** fiber field

`V(u) = κ u + c`,

which is what the viscous term `−ν u_{i,jj}` and the cross terms `u_j u_{i,j}`
with `j ≠ i` produce: they contribute a term that is *constant* in the velocity
mode `u_i` being differentiated.  In the Hermite basis of the fiber,
`½(π V + V π) = κ · ½(π u + u π) + c · π`, and while `½(π u + u π) =
(i/2)(a†² − a²)` is a `±2`-shift (the operator of `ChapterNavierStokes‐
HermiteFarisLavine`), the extra term `c · π = (i c/√2)(a† − a)` is a **`±1`
shift**.  This module removes that boundary.

## The instrument: sums of shift Hamiltonians

The Faris–Lavine hypotheses used in this project
(`BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`) are

* `H` symmetric, `N ≥ 0` with `N + 1` surjective,
* a **relative bound** `‖Hx‖² ≤ a‖Nx‖² + b‖x‖²` — with *no* smallness
  requirement on `a`, and
* a **commutator bound** `|⟪x, i[H, N]x⟫| ≤ c ⟪x, Nx⟫`.

All three are stable under sums: `‖(H₁+H₂)x‖² ≤ 2‖H₁x‖² + 2‖H₂x‖²` and the
commutator form is additive in `H`.  So two shift Hamiltonians sharing one
comparison operator may simply be added.  That is the content of `PairShift`
below: a single symbol `σ` carrying two shifts at once.

## What is proved

* `PairShift.pairH` — the sum of two shift Hamiltonians with a common comparison
  symbol, on the maximal domain of that symbol;
* `PairShift.pairH_symmetricOn`, `PairShift.pairH_relative_bound`,
  `PairShift.pairH_commForm_bound` — the two Faris–Lavine inequalities for the
  sum, with explicit constants;
* `PairShift.pairH_essentiallySelfAdjointOn_core` — the sum is essentially
  self-adjoint on the finite-mode core;
* `affH` — the affine Navier–Stokes fiber Hamiltonian `½(π V + V π)` for
  `V(u) = κ u + c`, in the Hermite basis of `ℓ²(ℕ)`;
* `affH_symmetricOn`, `affH_essentiallySelfAdjointOn_core` — **the headline**:
  the affine fiber Hamiltonian is symmetric and essentially self-adjoint on the
  finite-mode core, for all `κ ≥ 0` and `c ≥ 0`;
* `affH_coord_succ` and `affH_coord_succ_succ` — the two matrix entries of `H`
  on a Hermite basis vector: the `±1`-hopping `(c/√2)√(n+1)` of the constant
  part and the `±2`-hopping `(κ/2)√((n+1)(n+2))` of the linear part;
* `affH_ne_zero_of_pos_shear` and `affH_not_bounded` — the `±1`-hopping really
  is present when `c > 0`, and the operator is genuinely unbounded when
  `κ > 0`.

## Honest boundary

`c ≥ 0` is assumed, only because a `ShiftData` amplitude is required to be
non-negative; the case `c < 0` is the conjugate of the case `|c|` by the
sign-flip unitary `x_n ↦ (−1)ⁿ x_n`, which reverses the sign of a `±1`-hopping
and preserves a `±2`-hopping — that unitary equivalence is *not* formalized
here, so nothing below is claimed for `c < 0`.  The comparison operator used is
`N = μ(2n+1) + 1` with `μ = κ + c + 1`, i.e. the harmonic-oscillator number
operator rescaled so as to dominate both amplitudes.  As in the modules quoted
above, everything is stated on the abstract sequence space `ℓ²(ℕ)` with the
operator given by its matrix in the Hermite basis; the differential realization
on `L²(du)` is not built here.  Only one velocity component is carried, and
nothing here claims global regularity for the classical Navier–Stokes equation.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace AffineFiber

open LpNat FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

/-! ## Additivity of the commutator form -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}



/-! ## Two matrix entries of a shift Hamiltonian -/













/-! ## Two shifts sharing one comparison symbol -/

/-- The data of two shift Hamiltonians sharing a single comparison symbol `σ ≥ 1`:
two injective shifts, two amplitudes dominated by `σ`, and constant symbol
increments along each shift. -/
structure PairShift (ι : Type*) where
  /-- The symbol of the common comparison operator `N`. -/
  sym : ι → ℝ
  /-- The first shift. -/
  shift₁ : ι → ι
  /-- The second shift. -/
  shift₂ : ι → ι
  /-- The hopping amplitude along the first shift. -/
  amp₁ : ι → ℝ
  /-- The hopping amplitude along the second shift. -/
  amp₂ : ι → ℝ
  /-- The additive constant in the domination of the amplitudes by the symbol. -/
  K : ℝ
  /-- The increment of the symbol along the first shift. -/
  step₁ : ℝ
  /-- The increment of the symbol along the second shift. -/
  step₂ : ℝ
  shift₁_injective : Function.Injective shift₁
  shift₂_injective : Function.Injective shift₂
  amp₁_nonneg : ∀ β, 0 ≤ amp₁ β
  amp₂_nonneg : ∀ β, 0 ≤ amp₂ β
  amp₁_mono : ∀ β, amp₁ β ≤ amp₁ (shift₁ β)
  amp₂_mono : ∀ β, amp₂ β ≤ amp₂ (shift₂ β)
  K_nonneg : 0 ≤ K
  step₁_nonneg : 0 ≤ step₁
  step₂_nonneg : 0 ≤ step₂
  sym_ge_one : ∀ β, 1 ≤ sym β
  amp₁_le : ∀ β, amp₁ β ≤ (1 / 4) * sym β + K
  amp₂_le : ∀ β, amp₂ β ≤ (1 / 4) * sym β + K
  sym_step₁ : ∀ β, sym (shift₁ β) = sym β + step₁
  sym_step₂ : ∀ β, sym (shift₂ β) = sym β + step₂

namespace PairShift

variable (P : PairShift ι)

/-- The first of the two shift Hamiltonians packaged by `P`. -/
@[reducible] def fst : ShiftData ι where
  sym := P.sym
  shift := P.shift₁
  amp := P.amp₁
  K := P.K
  step := P.step₁
  shift_injective := P.shift₁_injective
  amp_nonneg := P.amp₁_nonneg
  amp_mono := P.amp₁_mono
  K_nonneg := P.K_nonneg
  step_nonneg := P.step₁_nonneg
  sym_ge_one := P.sym_ge_one
  amp_le := P.amp₁_le
  sym_step := P.sym_step₁

/-- The second of the two shift Hamiltonians packaged by `P`. -/
@[reducible] def snd : ShiftData ι where
  sym := P.sym
  shift := P.shift₂
  amp := P.amp₂
  K := P.K
  step := P.step₂
  shift_injective := P.shift₂_injective
  amp_nonneg := P.amp₂_nonneg
  amp_mono := P.amp₂_mono
  K_nonneg := P.K_nonneg
  step_nonneg := P.step₂_nonneg
  sym_ge_one := P.sym_ge_one
  amp_le := P.amp₂_le
  sym_step := P.sym_step₂








/-- **The two-shift Hamiltonian**: the sum of the two shift Hamiltonians, on the
maximal domain of the common comparison symbol. -/
noncomputable def pairH : maxDom P.sym →ₗ[ℂ] L2I ι :=
  ShiftData.shiftH P.fst + ShiftData.shiftH P.snd













end PairShift

/-! ## The affine Navier–Stokes fiber Hamiltonian -/

/-- The comparison strength for the affine fiber field `V(u) = κ u + c`: large
enough to dominate both the `±2`-hopping `(κ/2)√((n+1)(n+2))` and the
`±1`-hopping `(c/√2)√(n+1)`. -/
noncomputable def affMu (κ c : ℝ) : ℝ := κ + c + 1

/-- The `±1`-hopping amplitude of `c · π = (i c/√2)(a† − a)`. -/
noncomputable def shear (c : ℝ) (n : ℕ) : ℝ := (c / Real.sqrt 2) * Real.sqrt (n + 1)

theorem shear_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) : 0 ≤ shear c n := by
  unfold shear
  positivity

theorem shear_mono {c : ℝ} (hc : 0 ≤ c) (n : ℕ) : shear c n ≤ shear c (n + 1) := by
  unfold shear
  have h : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (((n : ℝ) + 1) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcast : ((n + 1 : ℕ) : ℝ) + 1 = ((n : ℝ) + 1) + 1 := by push_cast; ring
  rw [hcast]
  have : 0 ≤ c / Real.sqrt 2 := by positivity
  exact mul_le_mul_of_nonneg_left h this

theorem sqrt_succ_le (n : ℕ) : Real.sqrt ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) / 2 := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hsq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt hnn
  nlinarith [Real.sqrt_nonneg ((n : ℝ) + 1), sq_nonneg (Real.sqrt ((n : ℝ) + 1) - 1)]

theorem shear_le {c : ℝ} (hc : 0 ≤ c) {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) :
    shear c n ≤ (1 / 4) * oscSymbol (affMu κ c) n + (κ + c) := by
  have hs : Real.sqrt ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) / 2 := sqrt_succ_le n
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hdiv : c / Real.sqrt 2 ≤ c := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hstep : shear c n ≤ c * (((n : ℝ) + 2) / 2) := by
    unfold shear
    have hpos : 0 ≤ c / Real.sqrt 2 := by positivity
    calc (c / Real.sqrt 2) * Real.sqrt ((n : ℝ) + 1)
        ≤ (c / Real.sqrt 2) * (((n : ℝ) + 2) / 2) := mul_le_mul_of_nonneg_left hs hpos
      _ ≤ c * (((n : ℝ) + 2) / 2) := by
          have : (0 : ℝ) ≤ ((n : ℝ) + 2) / 2 := by positivity
          exact mul_le_mul_of_nonneg_right hdiv this
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold oscSymbol affMu
  nlinarith

theorem amp_le_affine {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    amp κ n ≤ (1 / 4) * oscSymbol (affMu κ c) n + (κ + c) := by
  have hsq : Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ (n : ℝ) + 2 := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h := Real.sqrt_le_sqrt (show ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) ^ 2 by
      nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hstep : amp κ n ≤ (κ / 2) * ((n : ℝ) + 2) := by
    unfold amp
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  unfold oscSymbol affMu
  nlinarith

/-- The two-shift data of the **affine** Navier–Stokes fiber field
`V(u) = κ u + c`: the `±2`-hopping of `κ · ½(π u + u π)` and the `±1`-hopping of
`c · π`, both dominated by the number operator `μ(2n+1)+1` with
`μ = κ + c + 1`. -/
noncomputable def affData {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) : PairShift ℕ where
  sym := oscSymbol (affMu κ c)
  shift₁ := fun n => n + 2
  shift₂ := fun n => n + 1
  amp₁ := amp κ
  amp₂ := shear c
  K := κ + c
  step₁ := 4 * affMu κ c
  step₂ := 2 * affMu κ c
  shift₁_injective := fun a b hab => by simpa using hab
  shift₂_injective := fun a b hab => by simpa using hab
  amp₁_nonneg := amp_nonneg hκ
  amp₂_nonneg := shear_nonneg hc
  amp₁_mono := amp_le_amp_add_two hκ
  amp₂_mono := shear_mono hc
  K_nonneg := by linarith
  step₁_nonneg := by unfold affMu; linarith
  step₂_nonneg := by unfold affMu; linarith
  sym_ge_one := oscSymbol_ge_one (by unfold affMu; linarith)
  amp₁_le := amp_le_affine hκ hc
  amp₂_le := shear_le hc hκ
  sym_step₁ := fun n => oscSymbol_step n
  sym_step₂ := fun n => by unfold oscSymbol; push_cast; ring



/-- **The affine Navier–Stokes fiber Hamiltonian** `H = ½(π V + V π)` for the
affine advection field `V(u) = κ u + c`, in the Hermite basis of `ℓ²(ℕ)`: the
`±2`-hopping `(κ/2)√((n+1)(n+2))` of the linear part plus the `±1`-hopping
`(c/√2)√(n+1)` of the constant part. -/
noncomputable def affH {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) :
    maxDom (oscSymbol (affMu κ c)) →ₗ[ℂ] L2I ℕ :=
  PairShift.pairH (affData hκ hc)





/-! ## The `±1`-hopping is genuinely present -/









/-- The Hermite basis vector `eₙ`, as an element of the maximal domain of the
comparison operator. -/
noncomputable def basisState (κ c : ℝ) (n : ℕ) : maxDom (oscSymbol (affMu κ c)) :=
  ⟨lp.single 2 n (1 : ℂ), finiteModes_le_maxDom _ (lpSingle_mem_lpFiniteModes _ _)⟩











/-! ## The operator is genuinely unbounded -/







end AffineFiber

end BookProof.NavierStokesFlow


