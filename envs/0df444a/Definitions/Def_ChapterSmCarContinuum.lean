-- Prove2me | Definitions.Def_ChapterSmCarContinuum
-- name    : ChapterSmCarContinuum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-16T20:40:31.060834+00:00
-- url     : https://prove2.me/theorems/efd06625-9ed5-4e95-8dec-4fd3747443ce
-- title:
--   ChapterSmCarContinuum
-- statement:
--   ChapterSmCarContinuum

import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_summable_normSq





import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Mathlib


/-!
# The continuum CAR algebra over an infinite-dimensional one-particle space

`BookProof.ChapterSmCarAlgebra` built the CAR algebra of **finitely many** fermionic modes,
and recorded the honest boundary: *“the continuum CAR algebra over an infinite-dimensional
one-particle space is not built here”*.  This module builds it.

## The construction

The mode set is `ℕ`, the one-particle space is `ℓ²(ℕ)` — infinite dimensional, and unitarily
any separable one-particle space, e.g. the `L²(ℝ³)` of a continuum field — and the Fock
space is the antisymmetric Fock space in its occupation-number presentation,

```
CFock = ℓ²( Finset ℕ ),
```

one orthonormal basis vector for each **finite** occupied set.  The single-mode ladder
operators carry the Jordan–Wigner sign of `BookProof.ChapterQuantumGravityFock`.

The point of the continuum algebra is not the single modes but the **smeared** operators
`a(f), a†(f)` for an arbitrary one-particle vector `f ∈ ℓ²(ℕ)`: these are the operators that
survive a change of one-particle basis, and their defining relation is
`{a(f), a†(g)} = ⟪f, g⟫`.  Note that `Σ_i |f_i|` may diverge, so `a†(f)` is *not* an
absolutely convergent sum of single-mode operators; it is bounded because of the fermionic
cancellations, which is exactly the content of the CAR.

## What is proved

* `cAnn`, `cCre` — the single-mode ladder operators as **bounded** operators on the
  infinite-mode Fock space (`norm_cAnn_le`, `norm_cCre_le`: contractions), with the four
  canonical anticommutation relations `car_cAnn_cCre_self`, `car_cAnn_cCre_of_ne`,
  `car_cAnn_cAnn`, `car_cCre_cCre`, and mutual adjointness `inner_cCre_left`,
  `inner_cAnn_left`.
* `cCreS f`, `cAnnS f` — the **smeared** creation and annihilation operators of an arbitrary
  one-particle vector `f ∈ ℓ²(ℕ)`, with
  * `cCreS_apply` — the occupation-number formula;
  * `cCreS_single` — the single-mode operators are the smearings of the basis vectors;
  * `cCreS_add`, `cCreS_smul`, `cCreS_sub` — linearity in the test vector;
  * **`norm_cCreS_le`**, `norm_cAnnS_le` — `‖a†(f)‖ ≤ ‖f‖`, the boundedness that has no
    bosonic analogue;
  * **`car_smeared`** — `{a(f), a†(g)} = ⟪f, g⟫ · 1`, and `car_cCreS_cCreS`,
    `car_cAnnS_cAnnS` — `{a†(f), a†(g)} = {a(f), a(g)} = 0`, for arbitrary `f, g ∈ ℓ²(ℕ)`.
* `oneParticleIsometry` — `f ↦ a†(f)Ω` is a **linear isometry** of the one-particle space
  `ℓ²(ℕ)` into the Fock space: the construction really is over an infinite-dimensional
  one-particle space, and `norm_cCreS_eq` upgrades the norm bound to `‖a†(f)‖ = ‖f‖`.
* **`carCre`, `carAnn`, `car_hilbert`, `car_hilbert_cre`, `norm_carCre_le`** — the CAR
  algebra over an *arbitrary* separable Hilbert space `H` presented by a Hilbert basis
  indexed by `ℕ` (so in particular over `L²(ℝ³)`): `{a(v), a†(w)} = ⟪v, w⟫ · 1`.

## Honest boundary

The one-particle space is separable and presented through a Hilbert basis; the
representation constructed is the Fock representation on the vacuum.  No statement is made
about inequivalent representations of the CAR algebra, about its C*-completion as an
abstract algebra, or about any Hamiltonian on this space.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmCarContinuum

open BookProof.QuantumGravityFock
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open scoped ENNReal NNReal

noncomputable section

/-- The one-particle space: `ℓ²(ℕ)`, infinite dimensional. -/
abbrev Ell2 : Type := lp (fun _ : ℕ => ℂ) 2

/-- The **fermionic Fock space over infinitely many modes**: `ℓ²` over the finite occupied
sets. -/
abbrev CFock : Type := lp (fun _ : Finset ℕ => ℂ) 2

/-- The Fock vacuum. -/
def vac : CFock := lp.single 2 (∅ : Finset ℕ) 1

/-! ## 0. `ℓ²` preliminaries -/

theorem lp2_norm_sq_tsum {ι : Type*} (x : lp (fun _ : ι => ℂ) 2) :
    ‖x‖ ^ 2 = ∑' i : ι, ‖x i‖ ^ 2 := by
  have h := lp.hasSum_norm (p := 2) (E := fun _ : ι => ℂ) (by norm_num) x
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at h
  have := h.tsum_eq
  simpa [Real.rpow_natCast] using this.symm

theorem lp2_sum_le_norm_sq {ι : Type*} (x : lp (fun _ : ι => ℂ) 2) (s : Finset ι) :
    ∑ i ∈ s, ‖x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [lp2_norm_sq_tsum]
  exact Summable.sum_le_tsum s (fun i _ => sq_nonneg _) (summable_normSq x)

theorem norm_le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

@[simp] theorem norm_jwSign (i : ℕ) (S : Finset ℕ) : ‖jwSign i S‖ = 1 := by
  simp [jwSign]

/-! ## 1. The single-mode ladder operators -/

/-- The involution of occupation sets that adds or removes the mode `i`. -/
def flipOcc (i : ℕ) : Finset ℕ ≃ Finset ℕ :=
  Function.Involutive.toPerm (fun S => if i ∈ S then S.erase i else insert i S) (by
    intro S
    by_cases h : i ∈ S
    · simp [h, Finset.insert_erase h]
    · simp [h, Finset.erase_insert h])

@[simp] theorem flipOcc_apply (i : ℕ) (S : Finset ℕ) :
    flipOcc i S = if i ∈ S then S.erase i else insert i S := rfl

/-- The coordinates of `a_i ψ`. -/
def annFun (i : ℕ) (ψ : CFock) : Finset ℕ → ℂ :=
  fun S => if i ∈ S then 0 else jwSign i S * ψ (insert i S)

/-- The coordinates of `a†_i ψ`. -/
def creFun (i : ℕ) (ψ : CFock) : Finset ℕ → ℂ :=
  fun S => if i ∈ S then jwSign i S * ψ (S.erase i) else 0

theorem norm_annFun_le (i : ℕ) (ψ : CFock) (S : Finset ℕ) :
    ‖annFun i ψ S‖ ≤ ‖ψ (flipOcc i S)‖ := by
  by_cases h : i ∈ S
  · simp [annFun, h]
  · simp [annFun, h]

theorem norm_creFun_le (i : ℕ) (ψ : CFock) (S : Finset ℕ) :
    ‖creFun i ψ S‖ ≤ ‖ψ (flipOcc i S)‖ := by
  by_cases h : i ∈ S
  · simp [creFun, h]
  · simp [creFun, h]

theorem sq_le_sq_of_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith

theorem summable_comp_flip (i : ℕ) (ψ : CFock) :
    Summable (fun S : Finset ℕ => ‖ψ (flipOcc i S)‖ ^ 2) := by
  have h : Summable ((fun S : Finset ℕ => ‖ψ S‖ ^ 2) ∘ (flipOcc i)) :=
    (Equiv.summable_iff (flipOcc i)).mpr (summable_normSq ψ)
  exact h

theorem memLp_annFun (i : ℕ) (ψ : CFock) : Memℓp (annFun i ψ) 2 :=
  memLpTwo_of_summable_normSq
    (Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun S => sq_le_sq_of_le_of_nonneg (norm_nonneg _) (norm_annFun_le i ψ S))
      (summable_comp_flip i ψ))

theorem memLp_creFun (i : ℕ) (ψ : CFock) : Memℓp (creFun i ψ) 2 :=
  memLpTwo_of_summable_normSq
    (Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun S => sq_le_sq_of_le_of_nonneg (norm_nonneg _) (norm_creFun_le i ψ S))
      (summable_comp_flip i ψ))

/-- The annihilation operator as a linear map. -/
def cAnnL (i : ℕ) : CFock →ₗ[ℂ] CFock where
  toFun ψ := ⟨annFun i ψ, memLp_annFun i ψ⟩
  map_add' x y := by
    refine lp.ext (funext fun S => ?_)
    show (annFun i (x + y)) S = (annFun i x + annFun i y) S
    by_cases h : i ∈ S <;> simp [annFun, h, mul_add]
  map_smul' c x := by
    refine lp.ext (funext fun S => ?_)
    by_cases h : i ∈ S <;> simp [annFun, h, mul_left_comm]

/-- The creation operator as a linear map. -/
def cCreL (i : ℕ) : CFock →ₗ[ℂ] CFock where
  toFun ψ := ⟨creFun i ψ, memLp_creFun i ψ⟩
  map_add' x y := by
    refine lp.ext (funext fun S => ?_)
    show (creFun i (x + y)) S = (creFun i x + creFun i y) S
    by_cases h : i ∈ S <;> simp [creFun, h, mul_add]
  map_smul' c x := by
    refine lp.ext (funext fun S => ?_)
    by_cases h : i ∈ S <;> simp [creFun, h, mul_left_comm]

@[simp] theorem cAnnL_apply (i : ℕ) (ψ : CFock) (S : Finset ℕ) :
    (cAnnL i ψ) S = if i ∈ S then 0 else jwSign i S * ψ (insert i S) := rfl

@[simp] theorem cCreL_apply (i : ℕ) (ψ : CFock) (S : Finset ℕ) :
    (cCreL i ψ) S = if i ∈ S then jwSign i S * ψ (S.erase i) else 0 := rfl

theorem norm_cAnnL_le (i : ℕ) (ψ : CFock) : ‖cAnnL i ψ‖ ≤ 1 * ‖ψ‖ := by
  rw [one_mul]
  refine norm_le_of_sq_le (norm_nonneg _) ?_
  rw [lp2_norm_sq_tsum, lp2_norm_sq_tsum]
  calc ∑' S : Finset ℕ, ‖(cAnnL i ψ) S‖ ^ 2
      ≤ ∑' S : Finset ℕ, ‖ψ (flipOcc i S)‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun S => ?_) (summable_normSq (cAnnL i ψ))
          (summable_comp_flip i ψ)
        exact sq_le_sq_of_le_of_nonneg (norm_nonneg _) (norm_annFun_le i ψ S)
    _ = ∑' S : Finset ℕ, ‖ψ S‖ ^ 2 := Equiv.tsum_eq (flipOcc i) fun S => ‖ψ S‖ ^ 2

theorem norm_cCreL_le (i : ℕ) (ψ : CFock) : ‖cCreL i ψ‖ ≤ 1 * ‖ψ‖ := by
  rw [one_mul]
  refine norm_le_of_sq_le (norm_nonneg _) ?_
  rw [lp2_norm_sq_tsum, lp2_norm_sq_tsum]
  calc ∑' S : Finset ℕ, ‖(cCreL i ψ) S‖ ^ 2
      ≤ ∑' S : Finset ℕ, ‖ψ (flipOcc i S)‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun S => ?_) (summable_normSq (cCreL i ψ))
          (summable_comp_flip i ψ)
        exact sq_le_sq_of_le_of_nonneg (norm_nonneg _) (norm_creFun_le i ψ S)
    _ = ∑' S : Finset ℕ, ‖ψ S‖ ^ 2 := Equiv.tsum_eq (flipOcc i) fun S => ‖ψ S‖ ^ 2

/-- **The annihilation operator** `a_i` of a single mode, as a bounded operator on the
infinite-mode Fock space. -/
def cAnn (i : ℕ) : CFock →L[ℂ] CFock := (cAnnL i).mkContinuous 1 (norm_cAnnL_le i)

/-- **The creation operator** `a†_i` of a single mode. -/
def cCre (i : ℕ) : CFock →L[ℂ] CFock := (cCreL i).mkContinuous 1 (norm_cCreL_le i)

@[simp] theorem cAnn_apply (i : ℕ) (ψ : CFock) (S : Finset ℕ) :
    (cAnn i ψ) S = if i ∈ S then 0 else jwSign i S * ψ (insert i S) := rfl

@[simp] theorem cCre_apply (i : ℕ) (ψ : CFock) (S : Finset ℕ) :
    (cCre i ψ) S = if i ∈ S then jwSign i S * ψ (S.erase i) else 0 := rfl

theorem norm_cAnn_le (i : ℕ) (ψ : CFock) : ‖cAnn i ψ‖ ≤ ‖ψ‖ := by
  have h := norm_cAnnL_le i ψ
  rw [one_mul] at h
  exact h

theorem norm_cCre_le (i : ℕ) (ψ : CFock) : ‖cCre i ψ‖ ≤ ‖ψ‖ := by
  have h := norm_cCreL_le i ψ
  rw [one_mul] at h
  exact h

/-! ## 2. The canonical anticommutation relations -/

/-- **`{a_i, a†_i} = 1`.** -/
theorem car_cAnn_cCre_self (i : ℕ) (ψ : CFock) :
    cAnn i (cCre i ψ) + cCre i (cAnn i ψ) = ψ := by
  refine lp.ext (funext fun S => ?_)
  simp only [lp.coeFn_add, Pi.add_apply, cAnn_apply, cCre_apply]
  by_cases h : i ∈ S
  · simp only [if_pos h, zero_add, if_neg (Finset.notMem_erase i S), jwSign_erase_self,
      Finset.insert_erase h, ← mul_assoc, jwSign_mul_self, one_mul]
  · simp only [if_neg h, add_zero, if_pos (Finset.mem_insert_self i S), jwSign_insert_self,
      Finset.erase_insert h, ← mul_assoc, jwSign_mul_self, one_mul]

/-- **`{a_i, a_j} = 0`** — in particular `a_i² = 0`, the Pauli principle. -/
theorem car_cAnn_cAnn (i j : ℕ) (ψ : CFock) :
    cAnn i (cAnn j ψ) + cAnn j (cAnn i ψ) = 0 := by
  refine lp.ext (funext fun S => ?_)
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_zero, Pi.zero_apply, cAnn_apply]
  rcases eq_or_ne i j with rfl | h
  · by_cases hi : i ∈ S
    · simp [hi]
    · rw [if_neg hi, if_pos (Finset.mem_insert_self i S)]
      ring
  · by_cases hi : i ∈ S
    · rw [if_pos hi, if_pos (Finset.mem_insert_of_mem hi)]
      split <;> ring
    · by_cases hj : j ∈ S
      · rw [if_neg hi, if_pos hj, if_pos (Finset.mem_insert_of_mem hj)]
        ring
      · rw [if_neg hi, if_neg hj, if_neg (by simp [hj, Ne.symm h]), if_neg (by simp [hi, h]),
          Finset.insert_comm j i S, ← mul_assoc, ← mul_assoc, jw_swap_insert h hi hj]
        ring

/-- **`{a†_i, a†_j} = 0`.** -/
theorem car_cCre_cCre (i j : ℕ) (ψ : CFock) :
    cCre i (cCre j ψ) + cCre j (cCre i ψ) = 0 := by
  refine lp.ext (funext fun S => ?_)
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_zero, Pi.zero_apply, cCre_apply]
  rcases eq_or_ne i j with rfl | h
  · by_cases hi : i ∈ S
    · rw [if_pos hi, if_neg (Finset.notMem_erase i S)]
      ring
    · simp [hi]
  · by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · rw [if_pos hi, if_pos hj, if_pos (by simp [hj, Ne.symm h] : j ∈ S.erase i),
          if_pos (by simp [hi, h] : i ∈ S.erase j), Finset.erase_right_comm (a := i) (b := j),
          ← mul_assoc, ← mul_assoc, jw_swap_erase h hi hj]
        ring
      · rw [if_pos hi, if_neg hj, if_neg (by simp [hj] : j ∉ S.erase i)]
        ring
    · by_cases hj : j ∈ S
      · rw [if_neg hi, if_pos hj, if_neg (by simp [hi] : i ∉ S.erase j)]
        ring
      · rw [if_neg hi, if_neg hj]
        ring

/-- **`{a_i, a†_j} = 0` for `i ≠ j`.** -/
theorem car_cAnn_cCre_of_ne {i j : ℕ} (h : i ≠ j) (ψ : CFock) :
    cAnn i (cCre j ψ) + cCre j (cAnn i ψ) = 0 := by
  refine lp.ext (funext fun S => ?_)
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_zero, Pi.zero_apply, cAnn_apply, cCre_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi, zero_add]
    by_cases hj : j ∈ S
    · rw [if_pos hj, if_pos (by simp [hi, h] : i ∈ S.erase j)]
      ring
    · rw [if_neg hj]
  · rw [if_neg hi]
    by_cases hj : j ∈ S
    · rw [if_pos hj, if_pos (by simp [hj] : j ∈ insert i S),
        if_neg (by simp [hi] : i ∉ S.erase j), Finset.erase_insert_of_ne h,
        ← mul_assoc, ← mul_assoc, jw_swap_mixed h hi hj]
      ring
    · rw [if_neg hj, if_neg (by simp [hj, Ne.symm h] : j ∉ insert i S)]
      ring

/-! ## 3. Adjointness -/

/-- **`a†_i` is the adjoint of `a_i`.** -/
theorem inner_cCre_left (i : ℕ) (ψ φ : CFock) :
    (inner ℂ (cCre i ψ) φ : ℂ) = inner ℂ ψ (cAnn i φ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← Equiv.tsum_eq (flipOcc i) (fun S => (inner ℂ (ψ S) ((cAnn i φ) S) : ℂ))]
  refine tsum_congr fun S => ?_
  by_cases h : i ∈ S
  · have h1 : i ∉ S.erase i := Finset.notMem_erase i S
    have h2 : insert i (S.erase i) = S := Finset.insert_erase h
    simp only [RCLike.inner_apply, cCre_apply, cAnn_apply, flipOcc_apply, if_pos h, if_neg h1,
      h2, map_mul, conj_jwSign, jwSign_erase_self]
    ring
  · have h1 : i ∈ insert i S := Finset.mem_insert_self i S
    simp only [RCLike.inner_apply, cCre_apply, cAnn_apply, flipOcc_apply, if_neg h, if_pos h1,
      map_zero, zero_mul, mul_zero]

/-- **`a_i` is the adjoint of `a†_i`.** -/
theorem inner_cAnn_left (i : ℕ) (ψ φ : CFock) :
    (inner ℂ (cAnn i ψ) φ : ℂ) = inner ℂ ψ (cCre i φ) := by
  have h := inner_cCre_left i φ ψ
  have h2 := congrArg (starRingEnd ℂ) h
  rw [inner_conj_symm, inner_conj_symm] at h2
  exact h2.symm

/-! ## 4. Smearing a finitely supported test vector -/

/-- The creation operator smeared over a finite set of modes. -/
def cCreFin (J : Finset ℕ) (f : ℕ → ℂ) : CFock →L[ℂ] CFock := ∑ i ∈ J, f i • cCre i

/-- The annihilation operator smeared over a finite set of modes. -/
def cAnnFin (J : Finset ℕ) (f : ℕ → ℂ) : CFock →L[ℂ] CFock :=
  ∑ i ∈ J, (starRingEnd ℂ) (f i) • cAnn i

theorem cCreFin_apply (J : Finset ℕ) (f : ℕ → ℂ) (ψ : CFock) (S : Finset ℕ) :
    (cCreFin J f ψ) S = ∑ i ∈ J, (if i ∈ S then f i * (jwSign i S * ψ (S.erase i)) else 0) := by
  rw [cCreFin]
  rw [ContinuousLinearMap.sum_apply]
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, lp.coeFn_smul,
    smul_eq_mul, cCre_apply]
  exact Finset.sum_congr rfl fun i _ => by split <;> simp

/-- Mutual adjointness of the finite smearings. -/
theorem inner_cCreFin_left (J : Finset ℕ) (f : ℕ → ℂ) (ψ φ : CFock) :
    (inner ℂ (cCreFin J f ψ) φ : ℂ) = inner ℂ ψ (cAnnFin J f φ) := by
  rw [cCreFin, cAnnFin, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply,
    sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, inner_smul_left, inner_smul_right]
  rw [inner_cCre_left]

/-- The anticommutator of two finite smearings. -/
theorem car_cCreFin (J : Finset ℕ) (f g : ℕ → ℂ) (ψ : CFock) :
    cAnnFin J f (cCreFin J g ψ) + cCreFin J g (cAnnFin J f ψ)
      = (∑ i ∈ J, (starRingEnd ℂ) (f i) * g i) • ψ := by
  have hL : cAnnFin J f (cCreFin J g ψ)
      = ∑ i ∈ J, ∑ j ∈ J, ((starRingEnd ℂ) (f i) * g j) • cAnn i (cCre j ψ) := by
    rw [cAnnFin, cCreFin, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_smul, smul_smul]
  have hR : cCreFin J g (cAnnFin J f ψ)
      = ∑ i ∈ J, ∑ j ∈ J, ((starRingEnd ℂ) (f i) * g j) • cCre j (cAnn i ψ) := by
    rw [cCreFin, cAnnFin, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_smul, smul_smul]
    rw [mul_comm (g i) ((starRingEnd ℂ) (f j))]
  rw [hL, hR, ← Finset.sum_add_distrib]
  have hterm : ∀ i ∈ J,
      ((∑ j ∈ J, ((starRingEnd ℂ) (f i) * g j) • cAnn i (cCre j ψ))
        + ∑ j ∈ J, ((starRingEnd ℂ) (f i) * g j) • cCre j (cAnn i ψ))
      = ((starRingEnd ℂ) (f i) * g i) • ψ := by
    intro i _
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_eq_single i]
    · rw [← smul_add, car_cAnn_cCre_self]
    · intro j _ hj
      rw [← smul_add, car_cAnn_cCre_of_ne (Ne.symm hj), smul_zero]
    · intro hi
      exact absurd hi (by simpa using ‹i ∈ J›)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul]

/-- **The sharp bound on a finite smearing**, the fermionic boundedness. -/
theorem norm_cCreFin_sq_le (J : Finset ℕ) (f : ℕ → ℂ) (ψ : CFock) :
    ‖cCreFin J f ψ‖ ^ 2 ≤ (∑ i ∈ J, ‖f i‖ ^ 2) * ‖ψ‖ ^ 2 := by
  set A := cCreFin J f with hA
  set B := cAnnFin J f with hB
  have hs : ∀ x : CFock, (inner ℂ x x : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hc : (∑ i ∈ J, (starRingEnd ℂ) (f i) * f i) = ((∑ i ∈ J, ‖f i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => RCLike.conj_mul (f i)
  have hcar : B (A ψ) = ((∑ i ∈ J, ‖f i‖ ^ 2 : ℝ) : ℂ) • ψ - A (B ψ) := by
    have h := car_cCreFin J f f ψ
    rw [hc] at h
    exact eq_sub_of_add_eq h
  have e3 : (inner ℂ ψ (A (B ψ)) : ℂ) = inner ℂ (B ψ) (B ψ) := by
    have h := inner_cCreFin_left J f (B ψ) ψ
    have h2 := congrArg (starRingEnd ℂ) h
    rw [inner_conj_symm, inner_conj_symm] at h2
    exact h2
  have key := inner_cCreFin_left J f ψ (A ψ)
  rw [hcar, inner_sub_right, inner_smul_right, e3, hs, hs, hs] at key
  have keyR : ‖A ψ‖ ^ 2 = (∑ i ∈ J, ‖f i‖ ^ 2) * ‖ψ‖ ^ 2 - ‖B ψ‖ ^ 2 := by
    exact_mod_cast key
  nlinarith [sq_nonneg ‖B ψ‖]

/-! ## 5. The smeared operators -/

/-- The coordinates of `a†(f) ψ`: for each occupation set the sum is finite. -/
def creSFun (f : Ell2) (ψ : CFock) : Finset ℕ → ℂ :=
  fun S => ∑ i ∈ S, f i * (jwSign i S * ψ (S.erase i))

/-- Every finite partial sum of `‖a†(f)ψ‖²` is bounded by `‖f‖²‖ψ‖²`: a finite family of
occupation sets only involves the finitely many modes it occupies, where the smeared
operator agrees with the finite smearing `cCreFin`. -/
theorem creSFun_sum_le (f : Ell2) (ψ : CFock) (F : Finset (Finset ℕ)) :
    ∑ S ∈ F, ‖creSFun f ψ S‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖ψ‖ ^ 2 := by
  set J := F.biUnion id with hJ
  have hEq : ∀ S ∈ F, creSFun f ψ S = (cCreFin J (fun i => f i) ψ) S := by
    intro S hS
    have hsub : S ⊆ J := fun i hi => Finset.mem_biUnion.mpr ⟨S, hS, hi⟩
    rw [cCreFin_apply, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    rfl
  calc ∑ S ∈ F, ‖creSFun f ψ S‖ ^ 2
      = ∑ S ∈ F, ‖(cCreFin J (fun i => f i) ψ) S‖ ^ 2 :=
        Finset.sum_congr rfl fun S hS => by rw [hEq S hS]
    _ ≤ ‖cCreFin J (fun i => f i) ψ‖ ^ 2 := lp2_sum_le_norm_sq _ F
    _ ≤ (∑ i ∈ J, ‖f i‖ ^ 2) * ‖ψ‖ ^ 2 := norm_cCreFin_sq_le J _ ψ
    _ ≤ ‖f‖ ^ 2 * ‖ψ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (lp2_sum_le_norm_sq f J) (sq_nonneg _)

theorem summable_creSFun_normSq (f : Ell2) (ψ : CFock) :
    Summable (fun S : Finset ℕ => ‖creSFun f ψ S‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (creSFun_sum_le f ψ)

theorem memLp_creSFun (f : Ell2) (ψ : CFock) : Memℓp (creSFun f ψ) 2 :=
  memLpTwo_of_summable_normSq (summable_creSFun_normSq f ψ)

/-- The smeared creation operator as a linear map. -/
def cCreSL (f : Ell2) : CFock →ₗ[ℂ] CFock where
  toFun ψ := ⟨creSFun f ψ, memLp_creSFun f ψ⟩
  map_add' x y := by
    refine lp.ext (funext fun S => ?_)
    simp only [creSFun, lp.coeFn_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  map_smul' c x := by
    refine lp.ext (funext fun S => ?_)
    simp only [creSFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem norm_cCreSL_le (f : Ell2) (ψ : CFock) : ‖cCreSL f ψ‖ ≤ ‖f‖ * ‖ψ‖ := by
  refine norm_le_of_sq_le (by positivity) ?_
  rw [lp2_norm_sq_tsum, mul_pow]
  exact Summable.tsum_le_of_sum_le (summable_creSFun_normSq f ψ) (creSFun_sum_le f ψ)

/-- **The smeared creation operator** `a†(f)` of a one-particle vector `f ∈ ℓ²(ℕ)`. -/
def cCreS (f : Ell2) : CFock →L[ℂ] CFock := (cCreSL f).mkContinuous ‖f‖ (norm_cCreSL_le f)

/-- **The smeared annihilation operator** `a(f)`, the adjoint of `a†(f)`. -/
def cAnnS (f : Ell2) : CFock →L[ℂ] CFock := ContinuousLinearMap.adjoint (cCreS f)

@[simp] theorem cCreS_apply (f : Ell2) (ψ : CFock) (S : Finset ℕ) :
    (cCreS f ψ) S = ∑ i ∈ S, f i * (jwSign i S * ψ (S.erase i)) := rfl

theorem cCreS_add (f g : Ell2) : cCreS (f + g) = cCreS f + cCreS g := by
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun S => ?_)
  simp only [cCreS_apply, ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cCreS_smul (c : ℂ) (f : Ell2) : cCreS (c • f) = c • cCreS f := by
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun S => ?_)
  simp only [cCreS_apply, ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cCreS_sub (f g : Ell2) : cCreS (f - g) = cCreS f - cCreS g := by
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun S => ?_)
  simp only [cCreS_apply, ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem norm_cCreS_le (f : Ell2) : ‖cCreS f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

theorem norm_cAnnS_le (f : Ell2) : ‖cAnnS f‖ ≤ ‖f‖ := by
  rw [cAnnS, LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (cCreS f)]
  exact norm_cCreS_le f

theorem cAnnS_sub (f g : Ell2) : cAnnS (f - g) = cAnnS f - cAnnS g := by
  simp only [cAnnS, cCreS_sub, map_sub]

/-- The single-mode creation operator is the smearing of a basis vector. -/
theorem cCreS_single (i : ℕ) : cCreS (lp.single 2 i (1 : ℂ)) = cCre i := by
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun S => ?_)
  rw [cCreS_apply, cCre_apply]
  by_cases h : i ∈ S
  · rw [if_pos h, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [lp.single_apply, hj]
    · intro hi
      exact absurd h hi
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hne : j ≠ i := fun e => h (e ▸ hj)
    simp [lp.single_apply, hne]

/-- **`{a†(f), a†(g)} = 0`.** -/
theorem car_cCreS_cCreS (f g : Ell2) (ψ : CFock) :
    cCreS f (cCreS g ψ) + cCreS g (cCreS f ψ) = 0 := by
  refine lp.ext (funext fun S => ?_)
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_zero, Pi.zero_apply, cCreS_apply]
  have expand : ∀ u v : Ell2,
      (∑ i ∈ S, (u : ℕ → ℂ) i * (jwSign i S *
          ∑ j ∈ S.erase i, (v : ℕ → ℂ) j * (jwSign j (S.erase i) * ψ ((S.erase i).erase j))))
        = ∑ i ∈ S, ∑ j ∈ S.erase i,
            (u : ℕ → ℂ) i * jwSign i S * ((v : ℕ → ℂ) j * jwSign j (S.erase i))
              * ψ ((S.erase i).erase j) := by
    intro u v
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [expand f g, expand g f]
  rw [Finset.sum_comm' (s := S) (t := fun i => S.erase i) (t' := S) (s' := fun j => S.erase j)
    (fun x y => by
      constructor
      · rintro ⟨hx, hy⟩
        exact ⟨Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hy).1 h.symm, hx⟩,
          (Finset.mem_erase.mp hy).2⟩
      · rintro ⟨hx, hy⟩
        exact ⟨(Finset.mem_erase.mp hx).2,
          Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hx).1 h.symm, hy⟩⟩)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
  have hsign : jwSign j S * jwSign i (S.erase j) = -(jwSign i S * jwSign j (S.erase i)) :=
    jw_swap_erase hji hjS hi
  rw [(Finset.erase_right_comm : (S.erase j).erase i = (S.erase i).erase j)]
  have hkey : (f : ℕ → ℂ) j * jwSign j S * ((g : ℕ → ℂ) i * jwSign i (S.erase j))
      = - ((g : ℕ → ℂ) i * jwSign i S * ((f : ℕ → ℂ) j * jwSign j (S.erase i))) := by
    calc (f : ℕ → ℂ) j * jwSign j S * ((g : ℕ → ℂ) i * jwSign i (S.erase j))
        = ((f : ℕ → ℂ) j * (g : ℕ → ℂ) i) * (jwSign j S * jwSign i (S.erase j)) := by ring
      _ = ((f : ℕ → ℂ) j * (g : ℕ → ℂ) i) * (-(jwSign i S * jwSign j (S.erase i))) := by
            rw [hsign]
      _ = - ((g : ℕ → ℂ) i * jwSign i S * ((f : ℕ → ℂ) j * jwSign j (S.erase i))) := by ring
  rw [hkey]
  ring

/-- On a finite mode set the smeared creation operator is the finite smearing. -/
theorem cCreS_eq_cCreFin {f : Ell2} {J : Finset ℕ} (h : ∀ i, (f : ℕ → ℂ) i ≠ 0 → i ∈ J) :
    cCreS f = cCreFin J (fun i => f i) := by
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun S => ?_)
  rw [cCreS_apply, cCreFin_apply, Finset.sum_ite_mem]
  refine (Finset.sum_subset Finset.inter_subset_right ?_).symm
  intro i hiS hi
  have hz : (f : ℕ → ℂ) i = 0 := by
    by_contra hne
    exact hi (Finset.mem_inter.mpr ⟨h i hne, hiS⟩)
  rw [hz, zero_mul]

/-- On a finite mode set the smeared annihilation operator is the finite smearing. -/
theorem cAnnS_eq_cAnnFin {f : Ell2} {J : Finset ℕ} (h : ∀ i, (f : ℕ → ℂ) i ≠ 0 → i ∈ J) :
    cAnnS f = cAnnFin J (fun i => f i) := by
  rw [cAnnS, cCreS_eq_cCreFin h]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have h1 := inner_cCreFin_left J (fun i => (f : ℕ → ℂ) i) y x
  have h2 := congrArg (starRingEnd ℂ) h1
  rw [inner_conj_symm, inner_conj_symm] at h2
  exact h2.symm

/-- The one-particle inner product of a finitely supported vector is a finite sum. -/
theorem inner_eq_finsum {f g : Ell2} {J : Finset ℕ} (hf : ∀ i, (f : ℕ → ℂ) i ≠ 0 → i ∈ J) :
    (inner ℂ f g : ℂ) = ∑ i ∈ J, (starRingEnd ℂ) ((f : ℕ → ℂ) i) * (g : ℕ → ℂ) i := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := J) (f := fun i => (inner ℂ ((f : ℕ → ℂ) i) ((g : ℕ → ℂ) i) : ℂ))
    (fun i hi => by
      have hz : (f : ℕ → ℂ) i = 0 := by
        by_contra hne; exact hi (hf i hne)
      simp [RCLike.inner_apply, hz])]
  exact Finset.sum_congr rfl fun i _ => by simp [RCLike.inner_apply, mul_comm]

/-- `f ↦ a(f)` is a contraction, hence continuous. -/
theorem lipschitz_cAnnS : LipschitzWith 1 (fun f : Ell2 => cAnnS f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← cAnnS_sub, NNReal.coe_one, one_mul]
  exact norm_cAnnS_le (x - y)

/-- `f ↦ a†(f)` is a contraction, hence continuous. -/
theorem lipschitz_cCreS : LipschitzWith 1 (fun f : Ell2 => cCreS f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← cCreS_sub, NNReal.coe_one, one_mul]
  exact norm_cCreS_le (x - y)

/-- The continuum CAR for finitely supported test vectors, where both operators reduce to
finite smearings. -/
theorem car_smeared_of_finite {f g : Ell2}
    (hf : f ∈ lpFiniteModes ℕ) (hg : g ∈ lpFiniteModes ℕ) (ψ : CFock) :
    cAnnS f (cCreS g ψ) + cCreS g (cAnnS f ψ) = (inner ℂ f g : ℂ) • ψ := by
  classical
  have hf' : (Function.support ((f : ℕ → ℂ))).Finite := hf
  have hg' : (Function.support ((g : ℕ → ℂ))).Finite := hg
  set J := hf'.toFinset ∪ hg'.toFinset with hJ
  have hfJ : ∀ i, (f : ℕ → ℂ) i ≠ 0 → i ∈ J := fun i hi =>
    Finset.mem_union_left _ (hf'.mem_toFinset.mpr hi)
  have hgJ : ∀ i, (g : ℕ → ℂ) i ≠ 0 → i ∈ J := fun i hi =>
    Finset.mem_union_right _ (hg'.mem_toFinset.mpr hi)
  rw [cAnnS_eq_cAnnFin hfJ, cCreS_eq_cCreFin hgJ, inner_eq_finsum (g := g) hfJ]
  exact car_cCreFin J _ _ ψ

/-- The continuum CAR for a finitely supported `g` and an arbitrary `f`, by density of the
finite-mode vectors. -/
theorem car_smeared_of_finite_right {g : Ell2} (hg : g ∈ lpFiniteModes ℕ) (ψ : CFock)
    (f : Ell2) :
    cAnnS f (cCreS g ψ) + cCreS g (cAnnS f ψ) = (inner ℂ f g : ℂ) • ψ := by
  have hcont1 : Continuous fun f : Ell2 => cAnnS f (cCreS g ψ) + cCreS g (cAnnS f ψ) :=
    ((ContinuousLinearMap.apply ℂ CFock (cCreS g ψ)).continuous.comp
        lipschitz_cAnnS.continuous).add
      ((cCreS g).continuous.comp
        ((ContinuousLinearMap.apply ℂ CFock ψ).continuous.comp lipschitz_cAnnS.continuous))
  have hcont2 : Continuous fun f : Ell2 => (inner ℂ f g : ℂ) • ψ := by fun_prop
  exact congrFun (Continuous.ext_on lpFiniteModes_dense hcont1 hcont2
    (fun x hx => car_smeared_of_finite hx hg ψ)) f

/-- **The continuum canonical anticommutation relation** `{a(f), a†(g)} = ⟪f, g⟫ · 1`, for
arbitrary one-particle vectors `f, g ∈ ℓ²(ℕ)`. -/
theorem car_smeared (f g : Ell2) (ψ : CFock) :
    cAnnS f (cCreS g ψ) + cCreS g (cAnnS f ψ) = (inner ℂ f g : ℂ) • ψ := by
  have hcont1 : Continuous fun g : Ell2 => cAnnS f (cCreS g ψ) + cCreS g (cAnnS f ψ) :=
    ((cAnnS f).continuous.comp
        ((ContinuousLinearMap.apply ℂ CFock ψ).continuous.comp lipschitz_cCreS.continuous)).add
      ((ContinuousLinearMap.apply ℂ CFock (cAnnS f ψ)).continuous.comp
        lipschitz_cCreS.continuous)
  have hcont2 : Continuous fun g : Ell2 => (inner ℂ f g : ℂ) • ψ := by fun_prop
  exact congrFun (Continuous.ext_on lpFiniteModes_dense hcont1 hcont2
    (fun x hx => car_smeared_of_finite_right hx ψ f)) g

/-- **`{a(f), a(g)} = 0`**, the adjoint relation of `car_cCreS_cCreS`. -/
theorem car_cAnnS_cAnnS (f g : Ell2) (ψ : CFock) :
    cAnnS f (cAnnS g ψ) + cAnnS g (cAnnS f ψ) = 0 := by
  have hop : (cCreS g).comp (cCreS f) + (cCreS f).comp (cCreS g) = 0 := by
    refine ContinuousLinearMap.ext fun φ => ?_
    simpa using car_cCreS_cCreS g f φ
  have hadj := congrArg ContinuousLinearMap.adjoint hop
  rw [map_add, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    map_zero] at hadj
  have h2 := congrArg (fun T : CFock →L[ℂ] CFock => T ψ) hadj
  simpa [cAnnS] using h2

/-! ## 6. The one-particle subspace -/

/-- `a†(f)Ω`: the one-particle state of the one-particle vector `f`. -/
def oneParticle (f : Ell2) : CFock := cCreS f vac

/-- The one-particle state `a†(f)Ω` is supported on the singleton occupation sets, where its
coordinate is the corresponding coordinate of `f`. -/
theorem oneParticle_singleton (f : Ell2) (i : ℕ) : (oneParticle f) ({i} : Finset ℕ) = f i := by
  have h1 : ({i} : Finset ℕ).erase i = ∅ := by simp
  have h2 : jwCount i ({i} : Finset ℕ) = 0 := by simp [jwCount]
  rw [oneParticle, cCreS_apply, Finset.sum_singleton, h1]
  simp [vac, lp.single_apply, jwSign, h2]

theorem oneParticle_of_not_singleton (f : Ell2) (S : Finset ℕ) (h : ∀ i, S ≠ {i}) :
    (oneParticle f) S = 0 := by
  rw [oneParticle, cCreS_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hne : S.erase i ≠ ∅ := by
    intro he
    exact h i (by rw [← Finset.insert_erase hi, he]; simp)
  simp [vac, lp.single_apply, Pi.single_eq_of_ne hne]

theorem norm_oneParticle (f : Ell2) : ‖oneParticle f‖ = ‖f‖ := by
  have hinj : Function.Injective (fun i : ℕ => ({i} : Finset ℕ)) := by
    intro a b hab
    simpa using hab
  have hsupp : Function.support (fun S : Finset ℕ => ‖(oneParticle f) S‖ ^ 2)
      ⊆ Set.range (fun i : ℕ => ({i} : Finset ℕ)) := by
    intro S hS
    by_contra hcon
    have hne : ∀ i, S ≠ {i} := fun i h => hcon ⟨i, h.symm⟩
    exact hS (by simp [oneParticle_of_not_singleton f S hne])
  have key : ‖oneParticle f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [lp2_norm_sq_tsum, lp2_norm_sq_tsum, ← hinj.tsum_eq hsupp]
    exact tsum_congr fun i => by rw [oneParticle_singleton]
  exact le_antisymm (norm_le_of_sq_le (norm_nonneg _) key.le)
    (norm_le_of_sq_le (norm_nonneg _) key.ge)

/-- **The one-particle space embeds isometrically in the Fock space**: the construction is a
CAR algebra over an infinite-dimensional one-particle space, not a truncation. -/
def oneParticleIsometry : Ell2 →ₗᵢ[ℂ] CFock where
  toFun := oneParticle
  map_add' f g := by
    simp only [oneParticle, cCreS_add]
    rfl
  map_smul' c f := by
    simp only [oneParticle, cCreS_smul]
    rfl
  norm_map' := norm_oneParticle

/-- `‖a†(f)‖ = ‖f‖`: the smearing map is isometric. -/
theorem norm_cCreS_eq (f : Ell2) : ‖cCreS f‖ = ‖f‖ := by
  refine le_antisymm (norm_cCreS_le f) ?_
  have hvac : ‖vac‖ = 1 := by
    rw [vac, lp.norm_single (by norm_num)]
    simp
  have hle := (cCreS f).le_opNorm vac
  rw [hvac, mul_one] at hle
  rw [← norm_oneParticle f]
  exact hle

/-! ## 7. The CAR algebra over an arbitrary separable one-particle space -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The creation operator of a vector of an arbitrary separable one-particle Hilbert
space**, through a Hilbert basis indexed by `ℕ` (for `H = L²(ℝ³)` this is the continuum
creation operator of a one-particle wave function). -/
def carCre (b : HilbertBasis ℕ ℂ H) (v : H) : CFock →L[ℂ] CFock := cCreS (b.repr v)

/-- The annihilation operator of a one-particle vector. -/
def carAnn (b : HilbertBasis ℕ ℂ H) (v : H) : CFock →L[ℂ] CFock :=
  ContinuousLinearMap.adjoint (carCre b v)

omit [CompleteSpace H] in
/-- **The canonical anticommutation relations over an arbitrary separable one-particle
space**: `{a(v), a†(w)} = ⟪v, w⟫ · 1`. -/
theorem car_hilbert (b : HilbertBasis ℕ ℂ H) (v w : H) (ψ : CFock) :
    carAnn b v (carCre b w ψ) + carCre b w (carAnn b v ψ) = (inner ℂ v w : ℂ) • ψ := by
  have hv : carAnn b v = cAnnS (b.repr v) := rfl
  have hinner : (inner ℂ (b.repr v) (b.repr w) : ℂ) = inner ℂ v w := b.repr.inner_map_map v w
  rw [hv, carCre, ← hinner]
  exact car_smeared _ _ ψ

omit [CompleteSpace H] in
/-- `‖a†(v)‖ ≤ ‖v‖` over an arbitrary separable one-particle space. -/
theorem norm_carCre_le (b : HilbertBasis ℕ ℂ H) (v : H) : ‖carCre b v‖ ≤ ‖v‖ := by
  rw [carCre]
  calc ‖cCreS (b.repr v)‖ ≤ ‖b.repr v‖ := norm_cCreS_le _
    _ = ‖v‖ := b.repr.norm_map v

omit [CompleteSpace H] in
/-- `{a†(v), a†(w)} = 0` over an arbitrary separable one-particle space. -/
theorem car_hilbert_cre (b : HilbertBasis ℕ ℂ H) (v w : H) (ψ : CFock) :
    carCre b v (carCre b w ψ) + carCre b w (carCre b v ψ) = 0 :=
  car_cCreS_cCreS (b.repr v) (b.repr w) ψ

end

end BookProof.SmCarContinuum


