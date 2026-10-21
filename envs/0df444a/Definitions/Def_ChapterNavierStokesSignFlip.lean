-- Prove2me | Definitions.Def_ChapterNavierStokesSignFlip
-- name    : ChapterNavierStokesSignFlip
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-20T23:57:14.825989+00:00
-- url     : https://prove2.me/theorems/1d1ea556-5d05-41ef-abc8-17ee7492c22a
-- title:
--   The Lean 4 theorem `flipFun_flipFun` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesSignFlip.lean`): generated def bundle for ChapterNavierStokesSignFlip. See BookProof/ChapterNavierStokesSignFlip.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_add

import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_smul
import Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_coe
import Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_symmetricOn



import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_memLpTwo_of_le

import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_support_hFun
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_coe

import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_blockVec_mem_maxDom_prime
import Definitions.Def_ChapterNavierStokesEsa
import Mathlib
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_essentiallySelfAdjointOn_core
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_basisState_coe
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_eq_zero
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_shift_of_single
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_zero
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_embFun_of_ne
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_hasSum_inner_blocks
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_inner_of_block_supported
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNsAffineFiberGaps


/-!
# The sign-flip unitary: removing the `c ≥ 0` hypothesis

`BookProof.ChapterNavierStokesAffineFiberEsa` proves that the affine
Navier–Stokes fiber Hamiltonian `H = ½(π V + V π)` with `V(u) = κ u + c` is
essentially self-adjoint on the finite-mode core of `ℓ²(ℕ)`, but only for
`c ≥ 0`: the `±1`-hopping amplitude `(c/√2)√(n+1)` of a `ShiftData` is required
to be non-negative.  The recorded remedy was the **sign-flip unitary**
`(U x)_n = (−1)ⁿ x_n`, which reverses the sign of a `±1`-hopping and preserves a
`±2`-hopping.  This module formalizes it and removes the hypothesis.

## What is proved

* `deficiencyTrivialAt_of_intertwine`, `essentiallySelfAdjointOn_of_intertwine` —
  essential self-adjointness is a unitary invariant: if a unitary `U` of the
  ambient Hilbert space preserves the core and intertwines two operators on it,
  `U ∘ T = T' ∘ U`, then `T` is essentially self-adjoint iff `T'` is;
* `flipU` — the sign-flip unitary `(U x)_β = (−1)^{p β} x_β` attached to a parity
  function `p : ι → ℕ`, a `LinearIsometryEquiv` of `ℓ²(ι)` preserving the
  finite-mode core and every maximal domain;
* `hFun_flip`, `shiftH_flip` — the conjugation rule: a shift Hamiltonian whose
  shift changes the parity by `k` is conjugated by `U` into `(−1)^k` times
  itself;
* `saffH` — the affine fiber Hamiltonian for an **arbitrary real** constant `c`
  (the `±1`-hopping amplitude is the signed `(c/√2)√(n+1)`);
* `saffH_conj_flip` — the unitary equivalence `U (affH κ |c|) U = saffH κ c` for
  `c < 0`;
* `saffH_essentiallySelfAdjointOn_core` — **the headline for one fiber**: for
  every `κ ≥ 0` and **every** `c ∈ ℝ`, the affine fiber Hamiltonian is
  essentially self-adjoint on the finite-mode core;
* `saffBlockH_essentiallySelfAdjointOn_core` — the same over the strain-rate
  spectrum: on `ℓ²(ℕ × J)`, for arbitrary families `κ ≥ 0` and `c : J → ℝ` of
  **arbitrary sign**.

## Honest boundary

`κ ≥ 0` is still assumed (the sign-flip unitary preserves the `±2`-hopping, so
it cannot remove that one; it is removed instead in
`BookProof.ChapterNavierStokesSignedShift`).  As in the modules quoted above,
everything is stated on the abstract sequence space with the operator given by
its matrix in the Hermite basis, and nothing here claims global regularity for
the classical Navier–Stokes equation.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber

namespace SignFlip

open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

/-! ## Essential self-adjointness is a unitary invariant -/

section Transfer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- **Unitary transfer of the deficiency condition.**  If the unitary `U`
preserves the domain `D` and intertwines `T` with `T'`, then triviality of the
deficiency space of `T` at `z` implies that of `T'`. -/
theorem deficiencyTrivialAt_of_intertwine (U : F ≃ₗᵢ[ℂ] F) (T T' : D →ₗ[ℂ] F)
    (hU : ∀ v : D, U (v : F) ∈ D)
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩) (z : ℂ)
    (hT : DeficiencyTrivialAt D T z) : DeficiencyTrivialAt D T' z := by
  intro w hw
  have hw' : ∀ v : D, (inner ℂ (T v) (U.symm w) : ℂ) = z * inner ℂ (v : F) (U.symm w) := by
    intro v
    have h1 : (inner ℂ (T v) (U.symm w) : ℂ) = inner ℂ (U (T v)) w := by
      rw [← U.inner_map_map (T v) (U.symm w), U.apply_symm_apply]
    have h2 : (inner ℂ ((v : F)) (U.symm w) : ℂ) = inner ℂ (U (v : F)) w := by
      rw [← U.inner_map_map (v : F) (U.symm w), U.apply_symm_apply]
    rw [h1, h2, hcomm v]
    exact hw ⟨U (v : F), hU v⟩
  have hzero : U.symm w = 0 := hT _ hw'
  have := congrArg U hzero
  rwa [U.apply_symm_apply, map_zero] at this

/-- **Essential self-adjointness is a unitary invariant.** -/
theorem essentiallySelfAdjointOn_of_intertwine (U : F ≃ₗᵢ[ℂ] F) (T T' : D →ₗ[ℂ] F)
    (hU : ∀ v : D, U (v : F) ∈ D)
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩)
    (hT : EssentiallySelfAdjointOn D T) : EssentiallySelfAdjointOn D T' :=
  ⟨deficiencyTrivialAt_of_intertwine U T T' hU hcomm Complex.I hT.1,
   deficiencyTrivialAt_of_intertwine U T T' hU hcomm (-Complex.I) hT.2⟩

/-- **Unitary transfer of symmetry.** -/
theorem symmetricOn_of_intertwine (U : F ≃ₗᵢ[ℂ] F) (T T' : D →ₗ[ℂ] F)
    (hU : ∀ v : D, U (v : F) ∈ D) (hUsurj : ∀ v : D, ∃ u : D, U (u : F) = (v : F))
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩)
    (hT : SymmetricOn D T) : SymmetricOn D T' := by
  intro x y
  obtain ⟨a, ha⟩ := hUsurj x
  obtain ⟨b, hb⟩ := hUsurj y
  have hx : x = ⟨U (a : F), hU a⟩ := Subtype.ext ha.symm
  have hy : y = ⟨U (b : F), hU b⟩ := Subtype.ext hb.symm
  subst hx
  subst hy
  rw [← hcomm a, ← hcomm b]
  simpa [U.inner_map_map] using hT a b

end Transfer

/-! ## The sign-flip unitary -/

variable {ι : Type*}

/-- The coordinates of the sign-flip: multiplication by `(−1)^{p β}`. -/
noncomputable def flipFun (p : ι → ℕ) (X : ι → ℂ) : ι → ℂ := fun β => (-1 : ℂ) ^ p β * X β

@[simp] theorem norm_flipFun (p : ι → ℕ) (X : ι → ℂ) (β : ι) :
    ‖flipFun p X β‖ = ‖X β‖ := by
  simp [flipFun]

theorem flipFun_flipFun (p : ι → ℕ) (X : ι → ℂ) : flipFun p (flipFun p X) = X := by
  funext β
  simp only [flipFun, ← mul_assoc, ← pow_add]
  rw [show p β + p β = 2 * p β by ring, pow_mul]
  norm_num

/-- **The sign-flip map** on `ℓ²(ι)`, as a linear map. -/
noncomputable def flipMap (p : ι → ℕ) : L2I ι →ₗ[ℂ] L2I ι where
  toFun x := ⟨flipFun p ((x : L2I ι) : ι → ℂ),
    memLpTwo_of_le x fun k => le_of_eq (norm_flipFun p _ k)⟩
  map_add' x y := by
    refine lp.ext (funext fun β => ?_)
    simp only [flipFun, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' a x := by
    refine lp.ext (funext fun β => ?_)
    simp only [flipFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem flipMap_coe (p : ι → ℕ) (x : L2I ι) (β : ι) :
    ((flipMap p x : L2I ι) : ι → ℂ) β = (-1 : ℂ) ^ p β * ((x : ι → ℂ) β) := rfl

theorem flipMap_flipMap (p : ι → ℕ) (x : L2I ι) : flipMap p (flipMap p x) = x := by
  refine lp.ext (funext fun β => ?_)
  have := congrFun (flipFun_flipFun p ((x : L2I ι) : ι → ℂ)) β
  simpa [flipMap_coe, flipFun] using this

theorem norm_flipMap (p : ι → ℕ) (x : L2I ι) : ‖flipMap p x‖ = ‖x‖ := by
  have h1 : HasSum (fun k => ‖((flipMap p x : L2I ι) : ι → ℂ) k‖ ^ 2) (‖flipMap p x‖ ^ 2) :=
    ShiftData.hasSum_normSq _
  have h2 : HasSum (fun k => ‖((flipMap p x : L2I ι) : ι → ℂ) k‖ ^ 2) (‖x‖ ^ 2) := by
    have := ShiftData.hasSum_normSq x
    refine this.congr_fun fun k => ?_
    simp [flipMap_coe]
  have hsq : ‖flipMap p x‖ ^ 2 = ‖x‖ ^ 2 := h1.unique h2
  have := abs_eq_abs.mpr (Or.inl (by nlinarith [norm_nonneg (flipMap p x), norm_nonneg x] :
    ‖flipMap p x‖ = ‖x‖))
  nlinarith [norm_nonneg (flipMap p x), norm_nonneg x, hsq]

/-- **The sign-flip unitary** `(U x)_β = (−1)^{p β} x_β` of `ℓ²(ι)`. -/
noncomputable def flipU (p : ι → ℕ) : L2I ι ≃ₗᵢ[ℂ] L2I ι where
  toLinearEquiv :=
    LinearEquiv.ofLinear (flipMap p) (flipMap p)
      (LinearMap.ext fun x => flipMap_flipMap p x) (LinearMap.ext fun x => flipMap_flipMap p x)
  norm_map' := norm_flipMap p

@[simp] theorem flipU_coe (p : ι → ℕ) (x : L2I ι) (β : ι) :
    ((flipU p x : L2I ι) : ι → ℂ) β = (-1 : ℂ) ^ p β * ((x : ι → ℂ) β) := rfl

theorem flipU_apply (p : ι → ℕ) (x : L2I ι) : flipU p x = flipMap p x := rfl

/-- The sign-flip unitary preserves the finite-mode core. -/
theorem flipU_mem_finiteModes (p : ι → ℕ) {x : L2I ι} (hx : x ∈ lpFiniteModes ι) :
    flipU p x ∈ lpFiniteModes ι := by
  refine mem_lpFiniteModes.mpr (Set.Finite.subset (mem_lpFiniteModes.mp hx) fun β hβ => ?_)
  simp only [Function.mem_support, flipU_coe, ne_eq, mul_eq_zero, not_or] at hβ
  exact hβ.2

/-- The sign-flip unitary preserves every maximal domain. -/
theorem flipU_mem_maxDom (p : ι → ℕ) (s : ι → ℝ) {x : L2I ι} (hx : x ∈ maxDom s) :
    flipU p x ∈ maxDom s := by
  refine memLpTwo_of_le (⟨fun k => (s k : ℂ) * (x : ι → ℂ) k, hx⟩ : L2I ι) fun k => ?_
  simp [flipU_coe]

/-! ## Conjugating a shift Hamiltonian -/

/-- The sign of a parity shift is `±1`. -/
theorem negOne_pow_eq (k : ℕ) : (-1 : ℂ) ^ k = 1 ∨ (-1 : ℂ) ^ k = -1 := by
  rcases Nat.even_or_odd k with hk | hk
  · exact Or.inl hk.neg_one_pow
  · exact Or.inr hk.neg_one_pow

/-- **The conjugation rule.**  If the shift raises the parity by `k`, the
sign-flip unitary conjugates the shift Hamiltonian into `(−1)^k` times
itself. -/
theorem hFun_flip (S : ShiftData ι) (p : ι → ℕ) (k : ℕ)
    (hp : ∀ β, p (S.shift β) = p β + k) (X : ι → ℂ) (β : ι) :
    S.hFun (flipFun p X) β = (-1 : ℂ) ^ k * ((-1 : ℂ) ^ p β * S.hFun X β) := by
  rcases negOne_pow_eq k with hB | hB <;>
  · by_cases hb : ∃ α, S.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      simp only [ShiftData.hFun, ShiftData.hop_shift, flipFun, hp α, hp (S.shift α),
        pow_add, hB]
      ring
    · have hz : ∀ g : ι → ℂ, S.hop g β = 0 := fun g => ShiftData.hop_eq_zero S g hb
      simp only [ShiftData.hFun, hz, flipFun, hp β, pow_add, hB]
      ring

/-- The operator form of the conjugation rule. -/
theorem shiftH_flip (S : ShiftData ι) (p : ι → ℕ) (k : ℕ)
    (hp : ∀ β, p (S.shift β) = p β + k) (x : maxDom S.sym) :
    (flipU p (ShiftData.shiftH S x) : L2I ι)
      = (-1 : ℂ) ^ k • (ShiftData.shiftH S ⟨flipU p (x : L2I ι),
          flipU_mem_maxDom p S.sym x.2⟩ : L2I ι) := by
  refine lp.ext (funext fun β => ?_)
  have hX : ((⟨flipU p (x : L2I ι), flipU_mem_maxDom p S.sym x.2⟩ :
      maxDom S.sym) : L2I ι) = flipU p (x : L2I ι) := rfl
  simp only [flipU_coe, ShiftData.shiftH_coe, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hfun : ((flipU p (x : L2I ι) : L2I ι) : ι → ℂ) = flipFun p ((x : L2I ι) : ι → ℂ) := rfl
  rw [hfun, hFun_flip S p k hp]
  rcases negOne_pow_eq k with hB | hB <;> rw [hB] <;> ring

/-! ## The affine fiber Hamiltonian with a constant of arbitrary sign -/

/-- The sign of the constant part of the fiber field, as a scalar. -/
noncomputable def esgn (c : ℝ) : ℂ := if c < 0 then -1 else 1

@[simp] theorem esgn_of_nonneg {c : ℝ} (hc : 0 ≤ c) : esgn c = 1 := by
  simp [esgn, not_lt.mpr hc]

@[simp] theorem esgn_of_neg {c : ℝ} (hc : c < 0) : esgn c = -1 := by simp [esgn, hc]

theorem esgn_eq (c : ℝ) : esgn c = 1 ∨ esgn c = -1 := by
  rcases lt_or_ge c 0 with h | h
  · exact Or.inr (esgn_of_neg h)
  · exact Or.inl (esgn_of_nonneg h)

theorem conj_esgn (c : ℝ) : (starRingEnd ℂ) (esgn c) = esgn c := by
  rcases esgn_eq c with h | h <;> simp [h]

/-- The signed `±1`-hopping amplitude: `esgn c` times the amplitude of `|c|` is
the amplitude of `c` itself. -/
theorem esgn_mul_shear (c : ℝ) (n : ℕ) :
    esgn c * ((shear |c| n : ℝ) : ℂ) = ((shear c n : ℝ) : ℂ) := by
  rcases lt_or_ge c 0 with h | h
  · rw [esgn_of_neg h, abs_of_neg h]
    simp only [shear]
    push_cast
    ring
  · rw [esgn_of_nonneg h, abs_of_nonneg h, one_mul]

/-- **The affine Navier–Stokes fiber Hamiltonian for an arbitrary real
constant** `c`: the `±2`-hopping `(κ/2)√((n+1)(n+2))` of the linear part plus the
signed `±1`-hopping `(c/√2)√(n+1)` of the constant part.  For `c ≥ 0` it is
`AffineFiber.affH`; for `c < 0` it is its conjugate by the sign-flip unitary. -/
noncomputable def saffH {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) :
    maxDom (oscSymbol (affMu κ |c|)) →ₗ[ℂ] L2I ℕ :=
  ShiftData.shiftH (affData hκ (abs_nonneg c)).fst
    + esgn c • ShiftData.shiftH (affData hκ (abs_nonneg c)).snd

theorem saffH_coe {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) (x : maxDom (oscSymbol (affMu κ |c|)))
    (β : ℕ) :
    ((saffH hκ c x : L2I ℕ) : ℕ → ℂ) β
      = (affData hκ (abs_nonneg c)).fst.hFun ((x : L2I ℕ) : ℕ → ℂ) β
        + esgn c * (affData hκ (abs_nonneg c)).snd.hFun ((x : L2I ℕ) : ℕ → ℂ) β := by
  simp only [saffH, LinearMap.add_apply, LinearMap.smul_apply, lp.coeFn_add, lp.coeFn_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- For a non-negative constant the signed Hamiltonian is the one of
`ChapterNavierStokesAffineFiberEsa`. -/
theorem saffH_eq_affH {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : 0 ≤ c) :
    saffH hκ c = affH hκ (abs_nonneg c) := by
  simp only [saffH, esgn_of_nonneg hc, one_smul]
  rfl

/-- **The affine fiber Hamiltonian is symmetric for every real constant.** -/
theorem saffH_symmetricOn {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) :
    SymmetricOn (maxDom (oscSymbol (affMu κ |c|))) (saffH hκ c) := by
  intro x y
  have h₁ := ShiftData.shiftH_symmetricOn (affData hκ (abs_nonneg c)).fst x y
  have h₂ := ShiftData.shiftH_symmetricOn (affData hκ (abs_nonneg c)).snd x y
  change (inner ℂ (saffH hκ c x : L2I ℕ) (y : L2I ℕ) : ℂ)
    = inner ℂ (x : L2I ℕ) (saffH hκ c y : L2I ℕ)
  change (inner ℂ ((affData hκ (abs_nonneg c)).fst.shiftH x
      + esgn c • (affData hκ (abs_nonneg c)).snd.shiftH x) (y : L2I ℕ) : ℂ)
    = inner ℂ (x : L2I ℕ) ((affData hκ (abs_nonneg c)).fst.shiftH y
      + esgn c • (affData hκ (abs_nonneg c)).snd.shiftH y)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_esgn]
  first | linear_combination h₁ + esgn c * h₂ | trace_state

/-- **The sign-flip unitary conjugates the `|c|` fiber Hamiltonian into the `c`
fiber Hamiltonian**, for `c < 0`: it preserves the `±2`-hopping of the linear
part and reverses the `±1`-hopping of the constant part. -/
theorem saffH_conj_flip {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : c < 0)
    (x : maxDom (oscSymbol (affMu κ |c|))) :
    (flipU (fun n : ℕ => n) (affH hκ (abs_nonneg c) x) : L2I ℕ)
      = (saffH hκ c ⟨flipU (fun n : ℕ => n) (x : L2I ℕ),
          flipU_mem_maxDom _ (oscSymbol (affMu κ |c|)) x.2⟩ : L2I ℕ) := by
  refine lp.ext (funext fun β => ?_)
  have hx : ((⟨flipU (fun n : ℕ => n) (x : L2I ℕ),
      flipU_mem_maxDom _ (oscSymbol (affMu κ |c|)) x.2⟩ :
        maxDom (oscSymbol (affMu κ |c|))) : L2I ℕ) = flipU (fun n : ℕ => n) (x : L2I ℕ) := rfl
  have hfun : ((flipU (fun n : ℕ => n) (x : L2I ℕ) : L2I ℕ) : ℕ → ℂ)
      = flipFun (fun n : ℕ => n) ((x : L2I ℕ) : ℕ → ℂ) := rfl
  have hp₁ : ∀ β : ℕ, (affData hκ (abs_nonneg c)).fst.shift β = β + 2 := fun _ => rfl
  have hp₂ : ∀ β : ℕ, (affData hκ (abs_nonneg c)).snd.shift β = β + 1 := fun _ => rfl
  rw [saffH_coe, hx, hfun, hFun_flip _ (fun n : ℕ => n) 2 hp₁,
    hFun_flip _ (fun n : ℕ => n) 1 hp₂]
  have hcoord : ((affH hκ (abs_nonneg c) x : L2I ℕ) : ℕ → ℂ) β
      = (affData hκ (abs_nonneg c)).fst.hFun ((x : L2I ℕ) : ℕ → ℂ) β
        + (affData hκ (abs_nonneg c)).snd.hFun ((x : L2I ℕ) : ℕ → ℂ) β :=
    PairShift.pairH_coe (affData hκ (abs_nonneg c)) x β
  rw [flipU_coe, hcoord, esgn_of_neg hc]
  ring

/-- **The headline for one fiber.**  For every `κ ≥ 0` and **every real** `c`,
the affine Navier–Stokes fiber Hamiltonian `½(π V + V π)` with `V(u) = κ u + c`
is essentially self-adjoint on the finite-mode core of `ℓ²(ℕ)`.  The hypothesis
`c ≥ 0` of `AffineFiber.affH_essentiallySelfAdjointOn_core` is gone: for `c < 0`
the operator is the conjugate of the one for `|c|` by the sign-flip unitary. -/
theorem saffH_essentiallySelfAdjointOn_core {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((saffH hκ c).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ |c|))))) := by
  rcases lt_or_ge c 0 with hc | hc
  · refine essentiallySelfAdjointOn_of_intertwine (flipU (fun n : ℕ => n))
      ((affH hκ (abs_nonneg c)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ |c|))))) _
      (fun v => flipU_mem_finiteModes _ v.2) (fun v => ?_)
      (affH_essentiallySelfAdjointOn_core hκ (abs_nonneg c))
    exact saffH_conj_flip hκ hc _
  · rw [saffH_eq_affH hκ hc]
    exact affH_essentiallySelfAdjointOn_core hκ (abs_nonneg c)

/-! ## The signed `±1`-hopping is genuinely present -/

/-- The coordinate of `H eₙ` at Hermite level `n + 1` is the **signed**
`±1`-hopping amplitude `(c/√2)√(n+1)`. -/
theorem saffH_coord_succ {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) (n : ℕ) :
    ((saffH hκ c (basisState κ |c| n) : L2I ℕ) : ℕ → ℂ) (n + 1)
      = Complex.I * ((shear c n : ℝ) : ℂ) := by
  have hX := basisState_coe κ |c| n
  have hfst : (affData hκ (abs_nonneg c)).fst.hFun
      ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ) (n + 1) = 0 := by
    refine hFun_eq_zero _ (fun α hα => ?_) ?_
    · simp only [affData_shift₁] at hα
      rw [hX]
      have : α ≠ n := by omega
      simp [this]
    · simp only [PairShift.fst_shift, affData_shift₁, hX]
      norm_num
      omega
  have hsnd : (affData hκ (abs_nonneg c)).snd.hFun
      ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ) (n + 1)
      = Complex.I * ((shear |c| n : ℝ) : ℂ) := by
    have h := hFun_shift_of_single (affData hκ (abs_nonneg c)).snd
      (X := ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ)) (o := n)
      (by simp [hX]) (by simp [hX]; omega)
    -- `affData_amp₂` is not in the published `AffineFiberEsa` copy (leaf-dropped);
    -- the `rfl` fact is inlined so no extra import is needed.
    have hamp₂ : (affData hκ (abs_nonneg c)).amp₂ = shear |c| := rfl
    simpa [hamp₂] using h
  rw [saffH_coe, hfst, hsnd, zero_add, ← mul_assoc, mul_comm (esgn c) Complex.I, mul_assoc,
    esgn_mul_shear]

/-- The coordinate of `H eₙ` at Hermite level `n + 2` is the `±2`-hopping
amplitude `(κ/2)√((n+1)(n+2))` of the linear part, unchanged. -/
theorem saffH_coord_succ_succ {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) (n : ℕ) :
    ((saffH hκ c (basisState κ |c| n) : L2I ℕ) : ℕ → ℂ) (n + 2)
      = Complex.I * ((amp κ n : ℝ) : ℂ) := by
  have hX := basisState_coe κ |c| n
  have hsnd : (affData hκ (abs_nonneg c)).snd.hFun
      ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ) (n + 2) = 0 := by
    refine hFun_eq_zero _ (fun α hα => ?_) ?_
    · simp only [affData_shift₂] at hα
      rw [hX]
      have : α ≠ n := by omega
      simp [this]
    · simp only [PairShift.snd_shift, affData_shift₂, hX]
      norm_num
      omega
  have hfst : (affData hκ (abs_nonneg c)).fst.hFun
      ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ) (n + 2)
      = Complex.I * ((amp κ n : ℝ) : ℂ) := by
    have h := hFun_shift_of_single (affData hκ (abs_nonneg c)).fst
      (X := ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ)) (o := n)
      (by simp [hX]) (by simp [hX]; omega)
    -- `affData_amp₁` is leaf-dropped from the published copy; inlined `rfl` fact.
    have hamp₁ : (affData hκ (abs_nonneg c)).amp₁ = amp κ := rfl
    simpa [hamp₁] using h
  rw [saffH_coe, hfst, hsnd, mul_zero, add_zero]

/-- With a non-zero constant part — **of either sign** — the affine fiber
Hamiltonian does not vanish on the ground state. -/
theorem saffH_ne_zero_of_shear {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : c ≠ 0) :
    saffH hκ c (basisState κ |c| 0) ≠ 0 := by
  intro h0
  have hcoord := saffH_coord_succ hκ c 0
  rw [h0] at hcoord
  simp only [lp.coeFn_zero, Pi.zero_apply] at hcoord
  have hshear : shear c 0 ≠ 0 := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := by rw [Real.sqrt_pos]; norm_num
    have h1 : (0 : ℝ) < Real.sqrt (((0 : ℕ) : ℝ) + 1) := by rw [Real.sqrt_pos]; norm_num
    simp only [shear, ne_eq, mul_eq_zero, div_eq_zero_iff, not_or]
    exact ⟨⟨hc, ne_of_gt h2⟩, ne_of_gt h1⟩
  have hz : ((shear c 0 : ℝ) : ℂ) = 0 := by
    have h := hcoord.symm
    field_simp at h
    simpa using h
  exact hshear (by exact_mod_cast hz)

/-! ## The block assembly with constants of arbitrary sign -/

section Block

open BilinearEsa

variable {J : Type*}

/-- The coordinates of the Navier–Stokes generator whose block `j` carries the
affine field `V(u) = κ_j u + c_j` with `c_j` of **arbitrary sign**. -/
noncomputable def sblockFun (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (X : ℕ × J → ℂ) : ℕ × J → ℂ :=
  fun q => (affData (hκ q.2) (abs_nonneg (c q.2))).fst.hFun (fun n => X (n, q.2)) q.1
    + esgn (c q.2)
      * (affData (hκ q.2) (abs_nonneg (c q.2))).snd.hFun (fun n => X (n, q.2)) q.1

theorem support_sblockFun (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (X : ℕ × J → ℂ) :
    Function.support (sblockFun κ c hκ X)
      ⊆ (((fun q : ℕ × J => (q.1 + 2, q.2)) '' Function.support X)
          ∪ ((fun q : ℕ × J => (q.1 + 2, q.2)) ⁻¹' Function.support X))
        ∪ (((fun q : ℕ × J => (q.1 + 1, q.2)) '' Function.support X)
          ∪ ((fun q : ℕ × J => (q.1 + 1, q.2)) ⁻¹' Function.support X)) := by
  rintro ⟨m, j⟩ hq
  simp only [Function.mem_support, sblockFun] at hq
  by_cases h1 : (affData (hκ j) (abs_nonneg (c j))).fst.hFun (fun n => X (n, j)) m = 0
  · have h2 : (affData (hκ j) (abs_nonneg (c j))).snd.hFun (fun n => X (n, j)) m ≠ 0 := by
      intro h
      exact hq (by rw [h1, h]; ring)
    have hmem := support_hFun (affData (hκ j) (abs_nonneg (c j))).snd (fun n => X (n, j)) h2
    rcases hmem with ⟨a, ha, hae⟩ | hpre
    · refine Or.inr (Or.inl ⟨(a, j), ha, ?_⟩)
      simp only [Prod.mk.injEq]
      exact ⟨hae, trivial⟩
    · exact Or.inr (Or.inr hpre)
  · have hmem := support_hFun (affData (hκ j) (abs_nonneg (c j))).fst (fun n => X (n, j)) h1
    rcases hmem with ⟨a, ha, hae⟩ | hpre
    · refine Or.inl (Or.inl ⟨(a, j), ha, ?_⟩)
      simp only [Prod.mk.injEq]
      exact ⟨hae, trivial⟩
    · exact Or.inl (Or.inr hpre)

theorem sblockFun_finite_support (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (x : lpFiniteModes (ℕ × J)) :
    (Function.support (sblockFun κ c hκ (((x : L2I (ℕ × J))) : ℕ × J → ℂ))).Finite := by
  have hx := mem_lpFiniteModes.mp x.2
  refine Set.Finite.subset
    (((hx.image _).union (Set.Finite.preimage (AffineBlock.shiftProd_injective 2).injOn hx)).union
      ((hx.image _).union (Set.Finite.preimage (AffineBlock.shiftProd_injective 1).injOn hx)))
    (support_sblockFun κ c hκ _)

/-- **The Navier–Stokes generator with affine fiber fields of arbitrary sign**,
on the finite-mode core of `ℓ²(ℕ × J)`. -/
noncomputable def sblockH (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    lpFiniteModes (ℕ × J) →ₗ[ℂ] L2I (ℕ × J) where
  toFun x := ⟨sblockFun κ c hκ (((x : L2I (ℕ × J))) : ℕ × J → ℂ),
    memLpTwo_of_finite_support (sblockFun_finite_support κ c hκ x)⟩
  map_add' x y := by
    refine lp.ext (funext fun q => ?_)
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply, sblockFun]
    rw [hFun_add, hFun_add]
    ring
  map_smul' a x := by
    refine lp.ext (funext fun q => ?_)
    simp only [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      sblockFun]
    rw [hFun_smul, hFun_smul]
    ring

@[simp] theorem sblockH_coe (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (x : lpFiniteModes (ℕ × J))
    (q : ℕ × J) :
    ((sblockH κ c hκ x : L2I (ℕ × J)) : ℕ × J → ℂ) q
      = sblockFun κ c hκ (((x : L2I (ℕ × J))) : ℕ × J → ℂ) q := rfl

/-- The generator preserves the blocks, acting on the block `j` by the signed
affine fiber Hamiltonian. -/
theorem sblockFun_embFun (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (j : J) (a : ℕ → ℂ) :
    sblockFun κ c hκ (embFun j a)
      = embFun j (fun n => (affData (hκ j) (abs_nonneg (c j))).fst.hFun a n
          + esgn (c j) * (affData (hκ j) (abs_nonneg (c j))).snd.hFun a n) := by
  funext q
  obtain ⟨m, j'⟩ := q
  by_cases hj : j' = j
  · subst hj
    simp only [sblockFun, embFun_self]
  · simp only [sblockFun, hFun_zero, mul_zero, add_zero, embFun_of_ne _ _ hj]

/-- The block of the image is the signed affine fiber Hamiltonian applied to the
block. -/
theorem blockVec_sblockH (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (v : lpFiniteModes (ℕ × J)) (j : J) :
    blockVec ((sblockH κ c hκ v : L2I (ℕ × J))) j
      = saffH (hκ j) (c j)
          ⟨blockVec ((v : L2I (ℕ × J))) j, AffineBlock.blockVec_mem_maxDom_prime _ v j⟩ := by
  refine lp.ext (funext fun n => ?_)
  rw [show ((saffH (hκ j) (c j)
      ⟨blockVec ((v : L2I (ℕ × J))) j, AffineBlock.blockVec_mem_maxDom_prime _ v j⟩ :
        L2I ℕ) : ℕ → ℂ) n = _ from saffH_coe (hκ j) (c j) _ n]
  rfl

/-- **The generator is symmetric** on the finite-mode core. -/
theorem sblockH_symmetricOn (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    SymmetricOn (lpFiniteModes (ℕ × J)) (sblockH κ c hκ) := by
  intro x y
  have h1 := hasSum_inner_blocks ((sblockH κ c hκ x : L2I (ℕ × J))) ((y : L2I (ℕ × J)))
  have h2 := hasSum_inner_blocks ((x : L2I (ℕ × J))) ((sblockH κ c hκ y : L2I (ℕ × J)))
  have heq : ∀ j : J,
      (inner ℂ (blockVec ((sblockH κ c hκ x : L2I (ℕ × J))) j)
          (blockVec ((y : L2I (ℕ × J))) j) : ℂ)
        = inner ℂ (blockVec ((x : L2I (ℕ × J))) j)
            (blockVec ((sblockH κ c hκ y : L2I (ℕ × J))) j) := by
    intro j
    rw [blockVec_sblockH κ c hκ x j, blockVec_sblockH κ c hκ y j]
    exact saffH_symmetricOn (hκ j) (c j) ⟨_, AffineBlock.blockVec_mem_maxDom_prime _ x j⟩
      ⟨_, AffineBlock.blockVec_mem_maxDom_prime _ y j⟩
  simp only [heq] at h1
  exact h1.unique h2

/-- **Block reduction of the deficiency problem** for the signed generator. -/
theorem deficiencyTrivialAt_sblockH (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (z : ℂ)
    (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes ℕ)
      ((saffH (hκ j) (c j)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu (κ j) |c j|))))) z) :
    DeficiencyTrivialAt (lpFiniteModes (ℕ × J)) (sblockH κ c hκ) z := by
  intro w hw
  have hb : ∀ j, blockVec w j = 0 := by
    intro j
    refine hblk j (blockVec w j) ?_
    intro u
    have hv := hw (blockEmb j u)
    have hHcoe : ∀ q : ℕ × J,
        ((sblockH κ c hκ (blockEmb j u) : L2I (ℕ × J)) : ℕ × J → ℂ) q
          = embFun j (((((saffH (hκ j) (c j))
              (Submodule.inclusion
                (finiteModes_le_maxDom (oscSymbol (affMu (κ j) |c j|))) u) :
                L2I ℕ)) : ℕ → ℂ)) q := by
      intro q
      have hb0 : ((sblockH κ c hκ (blockEmb j u) : L2I (ℕ × J)) : ℕ × J → ℂ)
          = sblockFun κ c hκ (embFun j (((u : L2I ℕ)) : ℕ → ℂ)) := rfl
      rw [hb0, sblockFun_embFun]
      congr 1
    have h1 := inner_of_block_supported j
      ((sblockH κ c hκ (blockEmb j u) : L2I (ℕ × J)))
      (((saffH (hκ j) (c j))
        (Submodule.inclusion
          (finiteModes_le_maxDom (oscSymbol (affMu (κ j) |c j|))) u) : L2I ℕ)) hHcoe w
    have h2 := inner_of_block_supported j
      (((blockEmb j u : lpFiniteModes (ℕ × J)) : L2I (ℕ × J))) ((u : L2I ℕ))
      (fun _ => rfl) w
    rw [h1, h2] at hv
    exact hv
  refine lp.ext (funext fun q => ?_)
  obtain ⟨n, j⟩ := q
  have hz := congrArg (fun v : L2I ℕ => ((v : ℕ → ℂ)) n) (hb j)
  simpa using hz

/-- **The headline over the strain-rate spectrum.**  The Navier–Stokes generator
whose fiber fields are the affine `V(u) = κ_j u + c_j` is essentially
self-adjoint on the finite-mode core of `ℓ²(ℕ × J)` for arbitrary families
`κ ≥ 0` and `c : J → ℝ` **of arbitrary sign**. -/
theorem sblockH_essentiallySelfAdjointOn_core (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (sblockH κ c hκ) :=
  ⟨deficiencyTrivialAt_sblockH κ c hκ Complex.I
      fun j => (saffH_essentiallySelfAdjointOn_core (hκ j) (c j)).1,
   deficiencyTrivialAt_sblockH κ c hκ (-Complex.I)
      fun j => (saffH_essentiallySelfAdjointOn_core (hκ j) (c j)).2⟩

/-- The finite-mode core is dense, so the generator is densely defined. -/
theorem sblockH_domain_dense :
    Dense ((lpFiniteModes (ℕ × J) : Submodule ℂ (L2I (ℕ × J))) : Set (L2I (ℕ × J))) :=
  lpFiniteModes_dense

end Block

end SignFlip

end BookProof.NavierStokesFlow


