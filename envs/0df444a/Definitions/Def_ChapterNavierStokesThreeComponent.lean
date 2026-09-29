-- Prove2me | Definitions.Def_ChapterNavierStokesThreeComponent
-- name    : ChapterNavierStokesThreeComponent
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:59:33.566415+00:00
-- url     : https://prove2.me/theorems/432b85b3-0311-4055-a797-388d51da9b4e
-- title:
--   The Navier–Stokes fiber analysis carried out in `BookProof.ChapterNavierStokesAffineFiberEsa` and `BookProof.ChapterNavi ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesThreeComponent`, source chapter `BookProof/ChapterNavierStokesThreeComponent.lean`).
--
--   The Navier–Stokes fiber analysis carried out in `BookProof.ChapterNavierStokesAffineFiberEsa` and `BookProof.ChapterNavierStokesAffineBlockEsa` carries **one** velocity component: the fiber Hilbert space is `ℓ²(ℕ)`, the Hermite representation of a single degree of freedom `u`, and the fiber field is the affine `V(u) = κ u + c`. The recorded boundary was the coupling of the three velocity components.
--
--   This module removes it. At one fiber the velocity is now the vector `u = (u₁, u₂, u₃)`, the Hermite basis is indexed by `Vel = Fin 3 → ℕ`, the fiber fields are the affine
--
--   `V_i(u) = ∑_k A_{ik} u_k + c_i`,
--
--   with `A` an **arbitrary real** `3 × 3` matrix (the negative velocity gradient at the fiber, with no symmetry, positivity or sign assumption) and `c` an arbitrary real vector, and the fiber Hamiltonian is
--
--   `H = ∑_i ½(π_i V_i + V_i π_i)`.
--
--   Writing `u_i = (a_i + a_i†)/√2` and `π_i = i(a_i† − a_i)/√2`, the terms are
--
--   * `A_{ii} ½(π_i u_i + u_i π_i) = (i A_{ii}/2)(a_i†² − a_i²)` — a `±2`-hopping in the coordinate `i`, amplitude `(A_{ii}/2)√((β_i+1)(β_i+2))`; * for `i ≠ k`, `A_{ik} π_i u_k + A_{ki} π_k u_i = i S_{ik}(a_i†a_k† − a_i a_k) + i D_{ik}(a_i† a_k − a_i a_k†)` with `S = (A_{ik}+A_{ki})/2` and `D = (A_{ik}−A_{ki})/2` — a **double-raising** hopping `β ↦ β + e_i + e_k` of amplitude `S√((β_i+1)(β_k+1))` (the strain part) and a **number-conserving** hopping `β ↦ β + e_i − e_k` of amplitude `D√((β_i+1)β_k)` (the vorticity part); * `c_i π_i = (i c_i/√2)(a_i† − a_i)` — a `±1`-hopping, amplitude `(c_i/√2)√(β_i+1)`.
--
--   The vorticity hopping has an amplitude that is *not* monotone along its shift, and the strain rates and constants have arbitrary signs, so neither `ShiftHamiltonian.ShiftData` nor its two-shift version applies. The instrument used here is `SignedShift.listH_essentiallySelfAdjointOn_core`, which needs neither positivity nor monotonicity.
--
--   * `velH` — the coupled three-component fiber Hamiltonian on the maximal domain of the comparison symbol `N = μ(2|β| + 3) + 1` in `ℓ²(Vel)`; * `velH_symmetricOn` — it is symmetric; * `velH_essentiallySelfAdjointOn_core` — **the headline**: it is essentially self-adjoint on the finite-mode core of `ℓ²(Vel)`, for every real matrix `A` and every real vector `c`; * `velH_coord_pair`, `velH_coord_rot`, `velH_coord_shear`, `velH_coord_diag` — the matrix entries: the coupling between distinct components really is present; * `velH_not_bounded` — the operator is unbounded.
--
--   The setting is the abstract sequence space `ℓ²(Vel)` with the operator given by its matrix in the Hermite basis of the fiber. The canonical reading of that matrix — the ladder pairs, the canonical commutation relations, and the identity `∑_i ½(π_i V_i + V_i π_i) = velH A c` — is supplied by `BookProof.ChapterNavierStokesCanonicalVector`; the unitary transport of that picture to `L²(du₁du₂du₃)` is not built here, and nothing here claims global regularity for the classical Navier–Stokes equation.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterFarisLavineCore

import Mathlib

/-!
# The three coupled velocity components

The Navier–Stokes fiber analysis carried out in
`BookProof.ChapterNavierStokesAffineFiberEsa` and
`BookProof.ChapterNavierStokesAffineBlockEsa` carries **one** velocity
component: the fiber Hilbert space is `ℓ²(ℕ)`, the Hermite representation of a
single degree of freedom `u`, and the fiber field is the affine
`V(u) = κ u + c`.  The recorded boundary was the coupling of the three velocity
components.

This module removes it.  At one fiber the velocity is now the vector
`u = (u₁, u₂, u₃)`, the Hermite basis is indexed by `Vel = Fin 3 → ℕ`, the fiber
fields are the affine

`V_i(u) = ∑_k A_{ik} u_k + c_i`,

with `A` an **arbitrary real** `3 × 3` matrix (the negative velocity gradient at
the fiber, with no symmetry, positivity or sign assumption) and `c` an arbitrary
real vector, and the fiber Hamiltonian is

`H = ∑_i ½(π_i V_i + V_i π_i)`.

## The Hermite matrix of `H`

Writing `u_i = (a_i + a_i†)/√2` and `π_i = i(a_i† − a_i)/√2`, the terms are

* `A_{ii} ½(π_i u_i + u_i π_i) = (i A_{ii}/2)(a_i†² − a_i²)` — a `±2`-hopping in
  the coordinate `i`, amplitude `(A_{ii}/2)√((β_i+1)(β_i+2))`;
* for `i ≠ k`, `A_{ik} π_i u_k + A_{ki} π_k u_i = i S_{ik}(a_i†a_k† − a_i a_k)
  + i D_{ik}(a_i† a_k − a_i a_k†)` with `S = (A_{ik}+A_{ki})/2` and
  `D = (A_{ik}−A_{ki})/2` — a **double-raising** hopping `β ↦ β + e_i + e_k` of
  amplitude `S√((β_i+1)(β_k+1))` (the strain part) and a **number-conserving**
  hopping `β ↦ β + e_i − e_k` of amplitude `D√((β_i+1)β_k)` (the vorticity
  part);
* `c_i π_i = (i c_i/√2)(a_i† − a_i)` — a `±1`-hopping, amplitude
  `(c_i/√2)√(β_i+1)`.

The vorticity hopping has an amplitude that is *not* monotone along its shift,
and the strain rates and constants have arbitrary signs, so neither
`ShiftHamiltonian.ShiftData` nor its two-shift version applies.  The instrument
used here is `SignedShift.listH_essentiallySelfAdjointOn_core`, which needs
neither positivity nor monotonicity.

## What is proved

* `velH` — the coupled three-component fiber Hamiltonian on the maximal domain
  of the comparison symbol `N = μ(2|β| + 3) + 1` in `ℓ²(Vel)`;
* `velH_symmetricOn` — it is symmetric;
* `velH_essentiallySelfAdjointOn_core` — **the headline**: it is essentially
  self-adjoint on the finite-mode core of `ℓ²(Vel)`, for every real matrix `A`
  and every real vector `c`;
* `velH_coord_pair`, `velH_coord_rot`, `velH_coord_shear`, `velH_coord_diag` —
  the matrix entries: the coupling between distinct components really is
  present;
* `velH_not_bounded` — the operator is unbounded.

## Honest boundary

The setting is the abstract sequence space `ℓ²(Vel)` with the operator given by
its matrix in the Hermite basis of the fiber.  The canonical reading of that
matrix — the ladder pairs, the canonical commutation relations, and the identity
`∑_i ½(π_i V_i + V_i π_i) = velH A c` — is supplied by
`BookProof.ChapterNavierStokesCanonicalVector`; the unitary transport of that
picture to `L²(du₁du₂du₃)` is not built here, and nothing here claims global
regularity for the classical Navier–Stokes equation.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace ThreeComponent

open LpNat FarisLavine IkebeKato ShiftHamiltonian SignedShift

/-! ## The Hermite multi-index of the three components -/

/-- The Hermite multi-index of the three velocity components at one fiber. -/
abbrev Vel := Fin 3 → ℕ

/-- The total Hermite level `|β| = β₁ + β₂ + β₃`. -/
def total (β : Vel) : ℕ := ∑ i, β i

/-- Creation of one quantum in the component `i`. -/
def raise (i : Fin 3) (β : Vel) : Vel := Function.update β i (β i + 1)

/-- Annihilation of one quantum in the component `i` (truncated at `0`). -/
def lower (i : Fin 3) (β : Vel) : Vel := Function.update β i (β i - 1)

/-- Exchange of the components `i` and `k`. -/
def swapVel (i k : Fin 3) (β : Vel) : Vel := β ∘ Equiv.swap i k

@[simp] theorem raise_self (i : Fin 3) (β : Vel) : raise i β i = β i + 1 := by
  simp [raise]

theorem raise_of_ne {i j : Fin 3} (h : j ≠ i) (β : Vel) : raise i β j = β j := by
  simp [raise, Function.update_of_ne h]

@[simp] theorem lower_self (i : Fin 3) (β : Vel) : lower i β i = β i - 1 := by
  simp [lower]

theorem lower_of_ne {i j : Fin 3} (h : j ≠ i) (β : Vel) : lower i β j = β j := by
  simp [lower, Function.update_of_ne h]

@[simp] theorem swapVel_apply (i k : Fin 3) (β : Vel) (j : Fin 3) :
    swapVel i k β j = β (Equiv.swap i k j) := rfl

theorem raise_injective (i : Fin 3) : Function.Injective (raise i) := by
  intro β γ h
  funext j
  by_cases hj : j = i
  · subst hj
    have := congrFun h j
    simp only [raise_self] at this
    omega
  · have := congrFun h j
    rwa [raise_of_ne hj, raise_of_ne hj] at this

theorem swapVel_injective (i k : Fin 3) : Function.Injective (swapVel i k) := by
  intro β γ h
  funext j
  have := congrFun h (Equiv.swap i k j)
  simpa using this

theorem total_update (β : Vel) (i : Fin 3) (m : ℕ) :
    total (Function.update β i m) + β i = total β + m := by
  classical
  have h1 : total (Function.update β i m) = m + ∑ j ∈ Finset.univ \ {i}, β j := by
    rw [total, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h2 : total β = β i + ∑ j ∈ Finset.univ \ {i}, β j := by
    rw [total, ← Finset.sum_sdiff (Finset.subset_univ {i})]
    simp [add_comm]
  omega

@[simp] theorem total_raise (i : Fin 3) (β : Vel) : total (raise i β) = total β + 1 := by
  have := total_update β i (β i + 1)
  simp only [raise]
  omega

theorem total_lower (i : Fin 3) {β : Vel} (h : 1 ≤ β i) : total (lower i β) + 1 = total β := by
  have := total_update β i (β i - 1)
  simp only [lower]
  omega

@[simp] theorem total_swapVel (i k : Fin 3) (β : Vel) : total (swapVel i k β) = total β :=
  Equiv.sum_comp (Equiv.swap i k) β

theorem le_total (i : Fin 3) (β : Vel) : β i ≤ total β :=
  Finset.single_le_sum (f := fun j => β j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem add_le_total {i k : Fin 3} (h : i ≠ k) (β : Vel) : β i + β k ≤ total β := by
  classical
  have hsub : ({i, k} : Finset (Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
  have hsum : ∑ j ∈ ({i, k} : Finset (Fin 3)), β j = β i + β k := by
    rw [Finset.sum_pair h]
  calc β i + β k = ∑ j ∈ ({i, k} : Finset (Fin 3)), β j := hsum.symm
    _ ≤ total β := Finset.sum_le_sum_of_subset hsub

/-! ## The four shifts -/

/-- The `±2`-hopping shift of the diagonal (self-advection) term. -/
def shDiag (i : Fin 3) (β : Vel) : Vel := raise i (raise i β)

/-- The double-raising shift of the strain (symmetric cross) term. -/
def shPair (i k : Fin 3) (β : Vel) : Vel := raise i (raise k β)

/-- The `±1`-hopping shift of the constant (viscous and cross) term. -/
def shShear (i : Fin 3) (β : Vel) : Vel := raise i β

/-- The number-conserving shift of the vorticity (antisymmetric cross) term:
`β ↦ β + e_i − e_k` where that makes sense, extended off the domain by the
exchange of the two components (where the amplitude vanishes) so as to be a
globally injective map. -/
def shRot (i k : Fin 3) (β : Vel) : Vel :=
  if β k = 0 then swapVel i k β else raise i (lower k β)

theorem shDiag_injective (i : Fin 3) : Function.Injective (shDiag i) :=
  (raise_injective i).comp (raise_injective i)

theorem shPair_injective (i k : Fin 3) : Function.Injective (shPair i k) :=
  (raise_injective i).comp (raise_injective k)

theorem shShear_injective (i : Fin 3) : Function.Injective (shShear i) := raise_injective i

/-- The vorticity shift with equal indices is the identity (and its amplitude
vanishes there). -/
theorem shRot_self (i : Fin 3) (β : Vel) : shRot i i β = β := by
  unfold shRot
  by_cases hb : β i = 0
  · rw [if_pos hb]
    funext j
    simp [swapVel]
  · rw [if_neg hb]
    funext j
    by_cases hj : j = i
    · subst hj
      rw [raise_self, lower_self]
      omega
    · rw [raise_of_ne hj, lower_of_ne hj]

theorem shRot_injective (i k : Fin 3) : Function.Injective (shRot i k) := by
  intro β γ h
  by_cases hik : i = k
  · subst hik
    rwa [shRot_self, shRot_self] at h
  · by_cases hb : β k = 0 <;> by_cases hc : γ k = 0
    · rw [shRot, if_pos hb, shRot, if_pos hc] at h
      exact swapVel_injective i k h
    · exfalso
      rw [shRot, if_pos hb, shRot, if_neg hc] at h
      have := congrFun h i
      rw [swapVel_apply, Equiv.swap_apply_left, raise_self] at this
      omega
    · exfalso
      rw [shRot, if_neg hb, shRot, if_pos hc] at h
      have := congrFun h i
      rw [swapVel_apply, Equiv.swap_apply_left, raise_self] at this
      omega
    · rw [shRot, if_neg hb, shRot, if_neg hc] at h
      have hlow := raise_injective i h
      funext j
      by_cases hj : j = k
      · subst hj
        have := congrFun hlow j
        rw [lower_self, lower_self] at this
        omega
      · have := congrFun hlow j
        rwa [lower_of_ne hj, lower_of_ne hj] at this

@[simp] theorem total_shDiag (i : Fin 3) (β : Vel) : total (shDiag i β) = total β + 2 := by
  simp [shDiag]

@[simp] theorem total_shPair (i k : Fin 3) (β : Vel) : total (shPair i k β) = total β + 2 := by
  simp [shPair]

@[simp] theorem total_shShear (i : Fin 3) (β : Vel) : total (shShear i β) = total β + 1 := by
  simp [shShear]

@[simp] theorem total_shRot (i k : Fin 3) (β : Vel) : total (shRot i k β) = total β := by
  by_cases hb : β k = 0
  · simp [shRot, hb]
  · have hk : 1 ≤ β k := Nat.one_le_iff_ne_zero.mpr hb
    have := total_lower k hk
    simp only [shRot, if_neg hb, total_raise]
    omega

/-! ## The comparison symbol and the coefficient bound -/

/-- The comparison symbol of the three-component fiber: the harmonic-oscillator
number operator of the three modes, `N = μ(2|β| + 3) + 1`. -/
def velSym (mu : ℝ) (β : Vel) : ℝ := mu * (2 * total β + 3) + 1

/-- The comparison strength: one plus the total size of the coefficients of the
fiber field. -/
def velMu (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) : ℝ :=
  1 + (∑ i, ∑ k, |A i k|) + ∑ i, |c i|

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem one_le_velMu : 1 ≤ velMu A c := by
  have h1 : 0 ≤ ∑ i, ∑ k, |A i k| := by positivity
  have h2 : 0 ≤ ∑ i, |c i| := by positivity
  simp only [velMu]
  linarith

theorem velMu_nonneg : 0 ≤ velMu A c := le_trans zero_le_one (one_le_velMu A c)

theorem abs_entry_le_velMu (i k : Fin 3) : |A i k| ≤ velMu A c := by
  have hik : |A i k| ≤ ∑ k', |A i k'| :=
    Finset.single_le_sum (f := fun k' => |A i k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  have hi : (∑ k', |A i k'|) ≤ ∑ i', ∑ k', |A i' k'| :=
    Finset.single_le_sum (f := fun i' => ∑ k', |A i' k'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ i, |c i| := by positivity
  simp only [velMu]
  linarith

theorem abs_const_le_velMu (i : Fin 3) : |c i| ≤ velMu A c := by
  have hi : |c i| ≤ ∑ i', |c i'| :=
    Finset.single_le_sum (f := fun i' => |c i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h1 : 0 ≤ ∑ i, ∑ k, |A i k| := by positivity
  simp only [velMu]
  linarith

theorem velSym_ge_one {mu : ℝ} (hmu : 0 ≤ mu) (β : Vel) : 1 ≤ velSym mu β := by
  have : 0 ≤ mu * (2 * (total β : ℝ) + 3) := by positivity
  simp only [velSym]
  linarith



/-! ## The amplitudes -/

/-- The amplitude of the diagonal `±2`-hopping of the component `i`. -/
noncomputable def ampDiag (i : Fin 3) (β : Vel) : ℝ :=
  (A i i / 2) * Real.sqrt (((β i : ℝ) + 1) * ((β i : ℝ) + 2))

/-- The strain coefficient of the (unordered) pair `{i, k}`, halved because the
family runs over ordered pairs. -/
noncomputable def coefPair (i k : Fin 3) : ℝ := if i = k then 0 else (A i k + A k i) / 4

/-- The vorticity coefficient of the (unordered) pair `{i, k}`, halved because
the family runs over ordered pairs. -/
noncomputable def coefRot (i k : Fin 3) : ℝ := if i = k then 0 else (A i k - A k i) / 4

/-- The amplitude of the double-raising (strain) hopping of the pair `(i, k)`. -/
noncomputable def ampPair (i k : Fin 3) (β : Vel) : ℝ :=
  coefPair A i k * Real.sqrt (((β i : ℝ) + 1) * ((β k : ℝ) + 1))

/-- The amplitude of the number-conserving (vorticity) hopping of the pair
`(i, k)`. -/
noncomputable def ampRot (i k : Fin 3) (β : Vel) : ℝ :=
  coefRot A i k * Real.sqrt (((β i : ℝ) + 1) * (β k : ℝ))

/-- The amplitude of the `±1`-hopping of the constant part of the component
`i`. -/
noncomputable def ampShear (i : Fin 3) (β : Vel) : ℝ :=
  (c i / Real.sqrt 2) * Real.sqrt ((β i : ℝ) + 1)

/-! ## The amplitudes are dominated by the comparison symbol -/

theorem sqrt_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x * y) ≤ (x + y) / 2 := by
  have h : x * y ≤ ((x + y) / 2) ^ 2 := by nlinarith [sq_nonneg (x - y)]
  calc Real.sqrt (x * y) ≤ Real.sqrt (((x + y) / 2) ^ 2) := Real.sqrt_le_sqrt h
    _ = (x + y) / 2 := Real.sqrt_sq (by positivity)

theorem cast_le_total (i : Fin 3) (β : Vel) : ((β i : ℝ)) ≤ (total β : ℝ) := by
  exact_mod_cast le_total i β

theorem cast_add_le_total {i k : Fin 3} (h : i ≠ k) (β : Vel) :
    ((β i : ℝ)) + ((β k : ℝ)) ≤ (total β : ℝ) := by
  have := add_le_total h β
  exact_mod_cast this

theorem abs_ampDiag_le (i : Fin 3) (β : Vel) :
    |ampDiag A i β| ≤ (1 / 4) * velSym (velMu A c) β + velMu A c := by
  set q := velMu A c with hq
  have hq0 : 0 ≤ q := velMu_nonneg A c
  have hA : |A i i| ≤ q := abs_entry_le_velMu A c i i
  have hT : ((β i : ℝ)) ≤ (total β : ℝ) := cast_le_total i β
  have hs : Real.sqrt (((β i : ℝ) + 1) * ((β i : ℝ) + 2)) ≤ (β i : ℝ) + 3 / 2 := by
    have := sqrt_mul_le (x := ((β i : ℝ) + 1)) (y := ((β i : ℝ) + 2))
      (by positivity) (by positivity)
    linarith
  have hstep : |ampDiag A i β| ≤ (q / 2) * ((β i : ℝ) + 3 / 2) := by
    rw [ampDiag, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_div]
    have h2 : |A i i| / |(2 : ℝ)| ≤ q / 2 := by
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    exact mul_le_mul h2 hs (Real.sqrt_nonneg _) (by positivity)
  have hprod : (q / 2) * ((β i : ℝ) + 3 / 2) ≤ (q / 2) * ((total β : ℝ) + 3 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  simp only [velSym]
  linarith

theorem abs_ampPair_le (i k : Fin 3) (β : Vel) :
    |ampPair A i k β| ≤ (1 / 4) * velSym (velMu A c) β + velMu A c := by
  set q := velMu A c with hq
  have hq0 : 0 ≤ q := velMu_nonneg A c
  have hTpos : (0 : ℝ) ≤ (total β : ℝ) := Nat.cast_nonneg _
  have hRHS : 0 ≤ (1 / 4) * velSym q β + q := by
    have := velSym_ge_one (mu := q) hq0 β
    linarith
  by_cases hik : i = k
  · simp only [ampPair, coefPair, if_pos hik, zero_mul, abs_zero]
    exact hRHS
  · have hcoef : |coefPair A i k| ≤ q / 2 := by
      simp only [coefPair, if_neg hik]
      have h1 : |A i k| ≤ q := abs_entry_le_velMu A c i k
      have h2 : |A k i| ≤ q := abs_entry_le_velMu A c k i
      have h3 : |A i k + A k i| ≤ |A i k| + |A k i| := abs_add_le _ _
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      linarith
    have hsum : ((β i : ℝ)) + ((β k : ℝ)) ≤ (total β : ℝ) := cast_add_le_total hik β
    have hs : Real.sqrt (((β i : ℝ) + 1) * ((β k : ℝ) + 1)) ≤ ((total β : ℝ) + 2) / 2 := by
      have := sqrt_mul_le (x := ((β i : ℝ) + 1)) (y := ((β k : ℝ) + 1))
        (by positivity) (by positivity)
      linarith
    have hstep : |ampPair A i k β| ≤ (q / 2) * (((total β : ℝ) + 2) / 2) := by
      rw [ampPair, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul hcoef hs (Real.sqrt_nonneg _) (by positivity)
    simp only [velSym]
    nlinarith [hstep, hq0, hTpos]

theorem abs_ampRot_le (i k : Fin 3) (β : Vel) :
    |ampRot A i k β| ≤ (1 / 4) * velSym (velMu A c) β + velMu A c := by
  set q := velMu A c with hq
  have hq0 : 0 ≤ q := velMu_nonneg A c
  have hTpos : (0 : ℝ) ≤ (total β : ℝ) := Nat.cast_nonneg _
  have hRHS : 0 ≤ (1 / 4) * velSym q β + q := by
    have := velSym_ge_one (mu := q) hq0 β
    linarith
  by_cases hik : i = k
  · simp only [ampRot, coefRot, if_pos hik, zero_mul, abs_zero]
    exact hRHS
  · have hcoef : |coefRot A i k| ≤ q / 2 := by
      simp only [coefRot, if_neg hik]
      have h1 : |A i k| ≤ q := abs_entry_le_velMu A c i k
      have h2 : |A k i| ≤ q := abs_entry_le_velMu A c k i
      have h3 : |A i k - A k i| ≤ |A i k| + |A k i| := abs_sub _ _
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      linarith
    have hsum : ((β i : ℝ)) + ((β k : ℝ)) ≤ (total β : ℝ) := cast_add_le_total hik β
    have hs : Real.sqrt (((β i : ℝ) + 1) * (β k : ℝ)) ≤ ((total β : ℝ) + 1) / 2 := by
      have := sqrt_mul_le (x := ((β i : ℝ) + 1)) (y := ((β k : ℝ)))
        (by positivity) (by positivity)
      linarith
    have hstep : |ampRot A i k β| ≤ (q / 2) * (((total β : ℝ) + 1) / 2) := by
      rw [ampRot, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul hcoef hs (Real.sqrt_nonneg _) (by positivity)
    simp only [velSym]
    nlinarith [hstep, hq0, hTpos]

theorem abs_ampShear_le (i : Fin 3) (β : Vel) :
    |ampShear c i β| ≤ (1 / 4) * velSym (velMu A c) β + velMu A c := by
  set q := velMu A c with hq
  have hq0 : 0 ≤ q := velMu_nonneg A c
  have hTpos : (0 : ℝ) ≤ (total β : ℝ) := Nat.cast_nonneg _
  have hc : |c i| ≤ q := abs_const_le_velMu A c i
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hcoef : |c i / Real.sqrt 2| ≤ q := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg 2)]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (c i)]
  have hT : ((β i : ℝ)) ≤ (total β : ℝ) := cast_le_total i β
  have hs : Real.sqrt ((β i : ℝ) + 1) ≤ ((total β : ℝ) + 2) / 2 := by
    have := sqrt_mul_le (x := ((β i : ℝ) + 1)) (y := (1 : ℝ)) (by positivity) (by norm_num)
    rw [mul_one] at this
    linarith
  have hstep : |ampShear c i β| ≤ q * (((total β : ℝ) + 2) / 2) := by
    rw [ampShear, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul hcoef hs (Real.sqrt_nonneg _) hq0
  simp only [velSym]
  nlinarith [hstep, hq0, hTpos]

/-! ## The twenty-four hopping terms -/

/-- The diagonal (self-advection) hop of the component `i`. -/
noncomputable def diagHop (i : Fin 3) : SignedHop Vel (velSym (velMu A c)) where
  shift := shDiag i
  amp := ampDiag A i
  K := velMu A c
  step := 4 * velMu A c
  shift_injective := shDiag_injective i
  K_nonneg := velMu_nonneg A c
  step_nonneg := by have := velMu_nonneg A c; linarith
  sym_ge_one := velSym_ge_one (velMu_nonneg A c)
  abs_amp_le := abs_ampDiag_le A c i
  sym_step := fun β => by
    simp only [velSym, total_shDiag]
    push_cast
    ring

/-- The strain (symmetric cross) hop of the ordered pair `(i, k)`. -/
noncomputable def pairHop (i k : Fin 3) : SignedHop Vel (velSym (velMu A c)) where
  shift := shPair i k
  amp := ampPair A i k
  K := velMu A c
  step := 4 * velMu A c
  shift_injective := shPair_injective i k
  K_nonneg := velMu_nonneg A c
  step_nonneg := by have := velMu_nonneg A c; linarith
  sym_ge_one := velSym_ge_one (velMu_nonneg A c)
  abs_amp_le := abs_ampPair_le A c i k
  sym_step := fun β => by
    simp only [velSym, total_shPair]
    push_cast
    ring

/-- The vorticity (antisymmetric cross) hop of the ordered pair `(i, k)`: the
number-conserving one, whose amplitude is not monotone along its shift. -/
noncomputable def rotHop (i k : Fin 3) : SignedHop Vel (velSym (velMu A c)) where
  shift := shRot i k
  amp := ampRot A i k
  K := velMu A c
  step := 0
  shift_injective := shRot_injective i k
  K_nonneg := velMu_nonneg A c
  step_nonneg := le_rfl
  sym_ge_one := velSym_ge_one (velMu_nonneg A c)
  abs_amp_le := abs_ampRot_le A c i k
  sym_step := fun β => by
    simp only [velSym, total_shRot]
    ring

/-- The `±1`-hop of the constant part of the component `i`. -/
noncomputable def shearHop (i : Fin 3) : SignedHop Vel (velSym (velMu A c)) where
  shift := shShear i
  amp := ampShear c i
  K := velMu A c
  step := 2 * velMu A c
  shift_injective := shShear_injective i
  K_nonneg := velMu_nonneg A c
  step_nonneg := by have := velMu_nonneg A c; linarith
  sym_ge_one := velSym_ge_one (velMu_nonneg A c)
  abs_amp_le := abs_ampShear_le A c i
  sym_step := fun β => by
    simp only [velSym, total_shShear]
    push_cast
    ring

/-- The full family of hopping terms of the coupled three-component fiber
Hamiltonian: for each component a diagonal and a shear hop, and for each ordered
pair of components a strain and a vorticity hop. -/
noncomputable def hopList : List (SignedHop Vel (velSym (velMu A c))) :=
  (List.finRange 3).flatMap fun i =>
    diagHop A c i :: shearHop A c i ::
      (List.finRange 3).flatMap fun k => [pairHop A c i k, rotHop A c i k]

/-! ## The coupled three-component fiber Hamiltonian -/

/-- **The coupled three-component fiber Hamiltonian**
`H = ∑_i ½(π_i V_i + V_i π_i)` with `V_i(u) = ∑_k A_{ik} u_k + c_i`, written in
the Hermite basis of the three modes, on the maximal domain of the comparison
symbol. -/
noncomputable def velH : maxDom (velSym (velMu A c)) →ₗ[ℂ] L2I Vel :=
  SignedShift.listH (hopList A c)





/-! ## Matrix entries: the coupling really is present -/

/-- The Hermite basis vector `e_β` of the three-component fiber, as an element
of the maximal domain of the comparison operator. -/
noncomputable def velState (β : Vel) : maxDom (velSym (velMu A c)) :=
  ⟨lp.single 2 β 1, finiteModes_le_maxDom _ (lpSingle_mem_lpFiniteModes _ _)⟩






























/-! ## Unboundedness -/

















end ThreeComponent

end BookProof.NavierStokesFlow


