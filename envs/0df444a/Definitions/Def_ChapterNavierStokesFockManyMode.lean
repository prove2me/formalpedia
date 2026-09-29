-- Prove2me | Definitions.Def_ChapterNavierStokesFockManyMode
-- name    : ChapterNavierStokesFockManyMode
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T14:49:18.432533+00:00
-- url     : https://prove2.me/theorems/656c6728-41cc-405c-9dbf-2ee50d96b8d9
-- title:
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine inequalities for the Navier–Stokes fiber H ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesFockManyMode`, source chapter `BookProof/ChapterNavierStokesFockManyMode.lean`).
--
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine inequalities for the Navier–Stokes fiber Hamiltonian of **one** degree of freedom. This module carries out the second quantization: the field has `d` modes, each with its own fiber coordinate `uᵢ`, its own momentum `πᵢ = -i ∂/∂uᵢ` and its own linear advection field `Vᵢ(u) = κᵢ uᵢ`, and the Hamiltonian and the comparison operator are the sums over the modes
--
--   `Ĥ = ∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)`, `N̂ = ∑ᵢ (πᵢ² + Vᵢ²) + I`.
--
--   In the Hermite (occupation-number) basis of the modes, the Hilbert space is `ℓ²(ℕᵈ)` — the Fock space of the `d`-mode boson field — the states are labelled by occupation configurations `α : Fin d → ℕ`, the comparison operator is multiplication by the total energy
--
--   `Σ(α) = ∑ᵢ κᵢ(2αᵢ + 1) + 1` (`fockSym`),
--
--   and the Hamiltonian is the sum over the modes of the pair creation/annihilation ("Bogoliubov") terms `(iκᵢ/2)(aᵢ†² − aᵢ²)`, each of which hops `α ↦ α ± 2eᵢ`.
--
--   Each mode contributes an abstract shift Hamiltonian in the sense of `BookProof.ChapterNavierStokesShiftHamiltonian` — with the **total** symbol `Σ` as its comparison symbol — so the one-mode analysis applies to each summand, and the many-mode inequalities follow by finitely many applications of `(∑ᵢ aᵢ)² ≤ d ∑ᵢ aᵢ²`.
--
--   * `fockH_symmetricOn` — `Ĥ` is symmetric on the maximal domain of `N̂`; * `fockH_relative_bound` — `‖Ĥx‖² ≤ (d²/2)‖N̂x‖² + 2d(∑ᵢκᵢ²)‖x‖²`; * `fockH_commForm_bound` — `|⟪x, i[Ĥ, N̂]x⟫| ≤ (∑ᵢ(2κᵢ + 4κᵢ²)) ⟪x, N̂x⟫`; * `fockH_essentiallySelfAdjointOn_core` — hence `Ĥ` is essentially self-adjoint on the finite-configuration core of the many-mode Fock space.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockManyMode.lean

import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Mathlib

import Mathlib

/-!
# The Navier–Stokes Hamiltonian of a many-mode field, and its Faris–Lavine bounds

`BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine
inequalities for the Navier–Stokes fiber Hamiltonian of **one** degree of
freedom.  This module carries out the second quantization: the field has `d`
modes, each with its own fiber coordinate `uᵢ`, its own momentum
`πᵢ = -i ∂/∂uᵢ` and its own linear advection field `Vᵢ(u) = κᵢ uᵢ`, and the
Hamiltonian and the comparison operator are the sums over the modes

`Ĥ = ∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)`,  `N̂ = ∑ᵢ (πᵢ² + Vᵢ²) + I`.

In the Hermite (occupation-number) basis of the modes, the Hilbert space is
`ℓ²(ℕᵈ)` — the Fock space of the `d`-mode boson field — the states are labelled
by occupation configurations `α : Fin d → ℕ`, the comparison operator is
multiplication by the total energy

`Σ(α) = ∑ᵢ κᵢ(2αᵢ + 1) + 1`  (`fockSym`),

and the Hamiltonian is the sum over the modes of the pair
creation/annihilation ("Bogoliubov") terms `(iκᵢ/2)(aᵢ†² − aᵢ²)`, each of which
hops `α ↦ α ± 2eᵢ`.

Each mode contributes an abstract shift Hamiltonian in the sense of
`BookProof.ChapterNavierStokesShiftHamiltonian` — with the **total** symbol `Σ`
as its comparison symbol — so the one-mode analysis applies to each summand, and
the many-mode inequalities follow by finitely many applications of
`(∑ᵢ aᵢ)² ≤ d ∑ᵢ aᵢ²`.

## What is proved

* `fockH_symmetricOn` — `Ĥ` is symmetric on the maximal domain of `N̂`;
* `fockH_relative_bound` — `‖Ĥx‖² ≤ (d²/2)‖N̂x‖² + 2d(∑ᵢκᵢ²)‖x‖²`;
* `fockH_commForm_bound` — `|⟪x, i[Ĥ, N̂]x⟫| ≤ (∑ᵢ(2κᵢ + 4κᵢ²)) ⟪x, N̂x⟫`;
* `fockH_essentiallySelfAdjointOn_core` — hence `Ĥ` is essentially self-adjoint
  on the finite-configuration core of the many-mode Fock space.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace FockManyMode

open LpNat FarisLavine IkebeKato ShiftHamiltonian

/-- An occupation-number configuration of the `d` field modes: `α i` quanta in
the Hermite level of the mode `i`.  `ℓ²(Occ d)` is the Fock space of the `d`-mode
boson field. -/
abbrev Occ (d : ℕ) := Fin d → ℕ

variable {d : ℕ} {κ : Fin d → ℝ}

/-- **The symbol of the many-mode comparison operator** `N̂ = ∑ᵢ(πᵢ² + Vᵢ²) + I`:
the total energy `Σ(α) = ∑ᵢ κᵢ(2αᵢ + 1) + 1`. -/
def fockSym (κ : Fin d → ℝ) : Occ d → ℝ := fun α => (∑ i, κ i * (2 * (α i : ℝ) + 1)) + 1

theorem fockSym_ge_one (hκ : ∀ i, 0 ≤ κ i) (α : Occ d) : 1 ≤ fockSym κ α := by
  have h : (0 : ℝ) ≤ ∑ i, κ i * (2 * (α i : ℝ) + 1) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hκ i) (by positivity)
  simp only [fockSym]
  linarith



/-- The single term of the total energy is dominated by the total energy. -/
theorem single_le_fockSym (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) (α : Occ d) :
    κ i * (2 * (α i : ℝ) + 1) ≤ fockSym κ α := by
  have h : κ i * (2 * (α i : ℝ) + 1) ≤ ∑ j, κ j * (2 * (α j : ℝ) + 1) :=
    Finset.single_le_sum (f := fun j => κ j * (2 * (α j : ℝ) + 1))
      (fun j _ => mul_nonneg (hκ j) (by positivity)) (Finset.mem_univ i)
  simp only [fockSym]
  linarith

/-! ## The mode-wise shift data -/

/-- The creation of two quanta in the mode `i`: `α ↦ α + 2eᵢ`. -/
def modeShift (i : Fin d) : Occ d → Occ d := fun α => Function.update α i (α i + 2)

@[simp] theorem modeShift_self (i : Fin d) (α : Occ d) : modeShift i α i = α i + 2 := by
  simp [modeShift]

theorem modeShift_injective (i : Fin d) : Function.Injective (modeShift i : Occ d → Occ d) := by
  intro α β h
  funext j
  by_cases hj : j = i
  · subst hj
    have hji := congrFun h j
    simp only [modeShift, Function.update_self] at hji
    omega
  · have hji := congrFun h j
    simpa [modeShift, hj] using hji

/-- The hopping amplitude of the mode `i`: `wᵢ(α) = (κᵢ/2)√((αᵢ+1)(αᵢ+2))`. -/
noncomputable def modeAmp (κ : Fin d → ℝ) (i : Fin d) : Occ d → ℝ :=
  fun α => (κ i / 2) * Real.sqrt (((α i : ℝ) + 1) * ((α i : ℝ) + 2))

theorem modeAmp_nonneg (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) (α : Occ d) : 0 ≤ modeAmp κ i α := by
  have h : (0 : ℝ) ≤ Real.sqrt (((α i : ℝ) + 1) * ((α i : ℝ) + 2)) := Real.sqrt_nonneg _
  have hi := hκ i
  simp only [modeAmp]
  positivity

theorem modeAmp_mono (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) (α : Occ d) :
    modeAmp κ i α ≤ modeAmp κ i (modeShift i α) := by
  have hmono : Real.sqrt (((α i : ℝ) + 1) * ((α i : ℝ) + 2))
      ≤ Real.sqrt ((((α i : ℝ) + 2) + 1) * (((α i : ℝ) + 2) + 2)) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [Nat.cast_nonneg (α := ℝ) (α i)]
  simp only [modeAmp, modeShift_self]
  push_cast
  nlinarith [hmono, Real.sqrt_nonneg (((α i : ℝ) + 1) * ((α i : ℝ) + 2)), hκ i]

/-- **The amplitude is dominated by the total energy**: `wᵢ ≤ ¼Σ + κᵢ/2`. -/
theorem modeAmp_le (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) (α : Occ d) :
    modeAmp κ i α ≤ (1 / 4) * fockSym κ α + κ i / 2 := by
  have hs : Real.sqrt (((α i : ℝ) + 1) * ((α i : ℝ) + 2)) ≤ (α i : ℝ) + 3 / 2 := by
    have h1 : ((α i : ℝ) + 1) * ((α i : ℝ) + 2) ≤ ((α i : ℝ) + 3 / 2) ^ 2 := by nlinarith
    calc Real.sqrt (((α i : ℝ) + 1) * ((α i : ℝ) + 2))
        ≤ Real.sqrt (((α i : ℝ) + 3 / 2) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (α i : ℝ) + 3 / 2 := by
          rw [Real.sqrt_sq (by positivity)]
  have hmul : (κ i / 2) * Real.sqrt (((α i : ℝ) + 1) * ((α i : ℝ) + 2))
      ≤ (κ i / 2) * ((α i : ℝ) + 3 / 2) :=
    mul_le_mul_of_nonneg_left hs (by linarith [hκ i])
  have hsym := single_le_fockSym hκ i α
  simp only [modeAmp]
  linarith

/-- The total energy increases by `4κᵢ` when two quanta are created in the mode
`i`. -/
theorem fockSym_step (i : Fin d) (α : Occ d) :
    fockSym κ (modeShift i α) = fockSym κ α + 4 * κ i := by
  have h : ∀ j : Fin d, κ j * (2 * ((modeShift i α) j : ℝ) + 1)
      = κ j * (2 * (α j : ℝ) + 1) + (if j = i then 4 * κ i else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [modeShift_self, if_pos]
      push_cast
      ring
    · simp only [modeShift, Function.update_of_ne hj, if_neg hj]
      ring
  simp only [fockSym]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i (fun _ => 4 * κ i)]
  simp only [Finset.mem_univ, if_pos]
  ring

/-- **The shift data of the mode `i`**: the hopping `α ↦ α + 2eᵢ` with amplitude
`wᵢ`, compared with the *total* energy `Σ`. -/
noncomputable def modeData (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) : ShiftData (Occ d) where
  sym := fockSym κ
  shift := modeShift i
  amp := modeAmp κ i
  K := κ i / 2
  step := 4 * κ i
  shift_injective := modeShift_injective i
  amp_nonneg := modeAmp_nonneg hκ i
  amp_mono := modeAmp_mono hκ i
  K_nonneg := by linarith [hκ i]
  step_nonneg := by linarith [hκ i]
  sym_ge_one := fockSym_ge_one hκ
  amp_le := modeAmp_le hκ i
  sym_step := fockSym_step i



/-! ## The many-mode Hamiltonian -/

/-- **The many-mode Navier–Stokes Hamiltonian** `Ĥ = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)`, on the
maximal domain of the comparison operator `N̂ = ∑ᵢ(πᵢ² + Vᵢ²) + I`. -/
noncomputable def fockH (hκ : ∀ i, 0 ≤ κ i) : maxDom (fockSym κ) →ₗ[ℂ] L2I (Occ d) :=
  ∑ i, ShiftData.shiftH (modeData hκ i)





/-! ## The first Faris–Lavine inequality -/



/-! ## The second Faris–Lavine inequality -/





/-! ## The commutator is genuinely non-zero -/

/-- The test state `e_0 + e_{2eᵢ}`: the vacuum plus two quanta in the mode `i`. -/
noncomputable def testState (κ : Fin d → ℝ) (i₀ : Fin d) : maxDom (fockSym κ) :=
  ⟨(lp.single 2 (0 : Occ d) (1 : ℂ) + lp.single 2 (modeShift i₀ (0 : Occ d)) (1 : ℂ)
      : L2I (Occ d)),
    finiteModes_le_maxDom _ (Submodule.add_mem _ (lpSingle_mem_lpFiniteModes _ (1 : ℂ))
      (lpSingle_mem_lpFiniteModes _ (1 : ℂ)))⟩























/-! ## Essential self-adjointness -/



end FockManyMode

end BookProof.NavierStokesFlow


