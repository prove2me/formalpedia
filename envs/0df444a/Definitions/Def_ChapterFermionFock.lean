-- Prove2me | Definitions.Def_ChapterFermionFock
-- name    : ChapterFermionFock
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T12:43:19.009017+00:00
-- url     : https://prove2.me/theorems/f58a79ce-bc4e-40c1-bfc2-4ae6b6dff753
-- title:
--   The Lean 4 theorem `toLpF_mem` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFermionFock.lean`): generated def bundle for ChapterFermionFock. See BookProof/ChapterFermionFock.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFermionFock.lean

import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Theorems.Thm_BookProof_FockSecondQuantization_isHermCol_opCol
import Theorems.Thm_BookProof_FockSecondQuantization_isPosCol_opCol
import Theorems.Thm_BookProof_FockSecondQuantization_opCol_apply
import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists_complete
import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_hashimoto_selects
import Theorems.Thm_BookProof_BRSTNilpotent_brst_charge_nilpotent


/-!
# Chapter FermionFock — the fermionic (CAR) Fock space and its second quantization

`CONSOLIDATED_PLAN.md` §10.6.2 item 3 asks for the missing **fermionic half** of
the quantum-gravity second quantization: the project builds the bosonic Fock
space `Γˢ` over a one-particle core (`ChapterFockSecondQuantization`, occupation
numbers `Conf = ℕ →₀ ℕ`), but the antisymmetric factor `Γᵃ` — the ghost/fermion
sector, whose canonical **anticommutation** relations `ChapterBRSTNilpotent`
carries as the abstract hypothesis `GhostCAR` — is not constructed anywhere.

This chapter constructs it, in exactly the style of the bosonic one.

## Deliverables

* `FConf`, `FermiAlg`, `FermiFock` — a fermionic configuration is the **finite
  set of occupied modes**, the algebraic Fock space is `FConf →₀ ℂ`, and the
  Fock space is `ℓ²(FConf)`.
* `fsign` — the Jordan–Wigner sign `(−1)^{#\{i ∈ S : i < j\}}`, and the sign
  calculus it obeys (`fsign_mul_self`, `fsign_erase`, `fsign_insert_self`,
  `fsign_insert_of_ne`).
* `creF`, `annF` — creation and annihilation, with their coordinate formulas
  `creF_apply`, `annF_apply`.
* **The canonical anticommutation relations**, all four of them:
  `car_annF_creF_self` (`{c_j, c_j†} = 1`), `car_creF_creF` (`{c_j†, c_k†} = 0`,
  including `creF_creF_self`: `(c_j†)² = 0`, the Pauli principle),
  `car_annF_annF` (`{c_j, c_k} = 0`) and `car_annF_creF_of_ne`
  (`{c_j, c_k†} = 0` for `j ≠ k`).
* `inner_creF_left` — creation and annihilation are formal adjoints of each
  other on the finite-occupation domain.
* `dGammaF`, `dGammaOpF` — the fermionic second quantization
  `dΓᵃ(A) = Σ_{j,k} ⟪e_j, A e_k⟫ c_j† c_k`, its symmetry
  (`dGammaOpF_symmetricOn`) and positivity (`dGammaOpF_quadForm_nonneg`) for a
  Hermitian, positive semidefinite one-particle matrix.
* `dGammaF_friedrichs_extension`, `secondQuantizationF_friedrichs` — the
  fermionic second quantization of any symmetric positive one-particle operator
  has a positive self-adjoint (Friedrichs) extension …
* `dGammaF_hashimoto_selects`, `secondQuantizationF_hashimoto_selects` — … and
  the Hashimoto/SIRK shift-invert limit selects exactly that extension, with the
  Galerkin truncations converging strongly and in the resolvent sense.
* `parityF` — the fermion-number parity `(−1)^{N_f}`, the `ℤ₂` grading
  operator: an involution (`parityF_involutive`) that anticommutes with both
  creation and annihilation (`parityF_creF`, `parityF_annF`).
* `ghostCAR_creF_annF` — **the abstract ghost relations are realized**: the
  operators built here satisfy `BookProof.BRSTNilpotent.GhostCAR`, so the BRST
  chapter's hypotheses are not vacuous — and `brst_charge_nilpotent_fermiFock`
  is the resulting concrete nilpotency `Q² = 0`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.FermionFock

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization (IsHermCol IsPosCol opCol isHermCol_opCol isPosCol_opCol)

noncomputable section

/-! ## Configurations and the Jordan–Wigner sign -/

/-- A **fermionic configuration**: the (finite) set of occupied one-particle
modes.  The Pauli principle is built into the type: a mode is occupied or not. -/
abbrev FConf := Finset ℕ

/-- The **algebraic fermionic Fock space**: finite linear combinations of
configurations. -/
abbrev FermiAlg := FConf →₀ ℂ

/-- The **fermionic Fock space** `ℓ²(FConf)`. -/
abbrev FermiFock := L2I FConf

/-- The **Jordan–Wigner sign** `(−1)^{#\{i ∈ S : i < j\}}` picked up when a
fermion is created in, or removed from, the mode `j` of the configuration
`S`. -/
def fsign (j : ℕ) (S : FConf) : ℂ := (-1 : ℂ) ^ ((S.filter (fun i => i < j)).card)

theorem fsign_mul_self (j : ℕ) (S : FConf) : fsign j S * fsign j S = 1 := by
  rw [fsign, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem fsign_conj (j : ℕ) (S : FConf) : (starRingEnd ℂ) (fsign j S) = fsign j S := by
  rw [fsign, map_pow]
  norm_num

/-- Removing the mode `j` does not change its own sign. -/
theorem fsign_erase (j : ℕ) (S : FConf) : fsign j (S.erase j) = fsign j S := by
  rw [fsign, fsign]
  congr 1
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hi⟩, hlt⟩; exact ⟨hi, hlt⟩
  · rintro ⟨hi, hlt⟩; exact ⟨⟨by omega, hi⟩, hlt⟩

/-- Adding the mode `j` does not change its own sign. -/
theorem fsign_insert_self (j : ℕ) (S : FConf) : fsign j (insert j S) = fsign j S := by
  rw [fsign, fsign]
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hi | hi, hlt⟩
    · omega
    · exact ⟨hi, hlt⟩
  · rintro ⟨hi, hlt⟩; exact ⟨Or.inr hi, hlt⟩

/-- Adding a *different* mode `k` flips the sign of `j` exactly when `k < j`. -/
theorem fsign_insert_of_ne {j k : ℕ} (S : FConf) (hkS : k ∉ S) (hkj : k ≠ j) :
    fsign j (insert k S) = (if k < j then (-1 : ℂ) else 1) * fsign j S := by
  classical
  by_cases hlt : k < j
  · have hfil : (insert k S).filter (fun i => i < j)
        = insert k (S.filter (fun i => i < j)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi | hi, h2⟩
        · exact Or.inl hi
        · exact Or.inr ⟨hi, h2⟩
      · rintro (rfl | ⟨hi, h2⟩)
        · exact ⟨Or.inl rfl, hlt⟩
        · exact ⟨Or.inr hi, h2⟩
    have hnot : k ∉ S.filter (fun i => i < j) := fun h => hkS (Finset.mem_filter.mp h).1
    rw [fsign, fsign, hfil, Finset.card_insert_of_notMem hnot, pow_succ, if_pos hlt]
    ring
  · have hfil : (insert k S).filter (fun i => i < j) = S.filter (fun i => i < j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi | hi, h2⟩
        · exact absurd (hi ▸ h2) hlt
        · exact ⟨hi, h2⟩
      · rintro ⟨hi, h2⟩; exact ⟨Or.inr hi, h2⟩
    rw [fsign, fsign, hfil, if_neg hlt, one_mul]

/-! ## Creation and annihilation at the algebraic level -/

open Classical in
/-- **The fermionic creation operator of the mode `j`**:
`c_j†|S⟩ = 0` if `j ∈ S`, and `(−1)^{#\{i ∈ S : i < j\}}|S ∪ \{j\}⟩` otherwise. -/
def creF (j : ℕ) : FermiAlg →ₗ[ℂ] FermiAlg :=
  Finsupp.lsum ℂ fun S => LinearMap.toSpanSingleton ℂ FermiAlg
    (if j ∈ S then 0 else Finsupp.single (insert j S) (fsign j S))

open Classical in
/-- **The fermionic annihilation operator of the mode `j`**:
`c_j|S⟩ = (−1)^{#\{i ∈ S : i < j\}}|S \ \{j\}⟩` if `j ∈ S`, and `0` otherwise. -/
def annF (j : ℕ) : FermiAlg →ₗ[ℂ] FermiAlg :=
  Finsupp.lsum ℂ fun S => LinearMap.toSpanSingleton ℂ FermiAlg
    (if j ∈ S then Finsupp.single (S.erase j) (fsign j S) else 0)

@[simp] theorem creF_single (j : ℕ) (S : FConf) (c : ℂ) :
    creF j (Finsupp.single S c)
      = c • (if j ∈ S then 0 else Finsupp.single (insert j S) (fsign j S)) := by
  classical
  simp [creF, LinearMap.toSpanSingleton]

@[simp] theorem annF_single (j : ℕ) (S : FConf) (c : ℂ) :
    annF j (Finsupp.single S c)
      = c • (if j ∈ S then Finsupp.single (S.erase j) (fsign j S) else 0) := by
  classical
  simp [annF, LinearMap.toSpanSingleton]

/-- The coordinates of `c_j† u`. -/
theorem creF_apply (j : ℕ) (u : FermiAlg) (S : FConf) :
    creF j u S = if j ∈ S then fsign j S * u (S.erase j) else 0 := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply, hf, hg]
    by_cases h : j ∈ S <;> simp [h, mul_add]
  | single T c =>
    rw [creF_single]
    by_cases hT : j ∈ T
    · have hne : ∀ hS : j ∈ S, T ≠ S.erase j := by
        intro _ hc
        exact (Finset.notMem_erase j S) (hc ▸ hT)
      simp only [hT, if_true, smul_zero, Finsupp.zero_apply]
      by_cases hS : j ∈ S
      · rw [if_pos hS, Finsupp.single_apply, if_neg (hne hS), mul_zero]
      · rw [if_neg hS]
    · have hins : j ∈ insert j T := Finset.mem_insert_self j T
      by_cases hS : j ∈ S
      · rw [if_neg hT, if_pos hS, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        by_cases hTS : insert j T = S
        · subst hTS
          rw [if_pos rfl, Finsupp.single_apply,
            if_pos (Finset.erase_insert (by simpa using hT)).symm,
            fsign_insert_self]
          ring
        · rw [if_neg hTS, mul_zero, Finsupp.single_apply]
          have : T ≠ S.erase j := by
            intro hc
            exact hTS (by rw [hc, Finset.insert_erase hS])
          rw [if_neg this, mul_zero]
      · rw [if_neg hT, if_neg hS, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        have : insert j T ≠ S := fun hc => hS (hc ▸ hins)
        rw [if_neg this, mul_zero]

/-- The coordinates of `c_j u`. -/
theorem annF_apply (j : ℕ) (u : FermiAlg) (S : FConf) :
    annF j u S = if j ∈ S then 0 else fsign j S * u (insert j S) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply, hf, hg]
    by_cases h : j ∈ S <;> simp [h, mul_add]
  | single T c =>
    rw [annF_single]
    by_cases hT : j ∈ T
    · by_cases hS : j ∈ S
      · rw [if_pos hT, if_pos hS, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        have : T.erase j ≠ S := fun hc => (Finset.notMem_erase j T) (hc ▸ hS)
        rw [if_neg this, mul_zero]
      · rw [if_pos hT, if_neg hS, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
          Finsupp.single_apply]
        by_cases hTS : T.erase j = S
        · subst hTS
          rw [if_pos rfl, if_pos (Finset.insert_erase hT).symm, fsign_erase]
          ring
        · rw [if_neg hTS, mul_zero]
          have : T ≠ insert j S := by
            intro hc
            exact hTS (by rw [hc, Finset.erase_insert (by simpa using hS)])
          rw [if_neg this, mul_zero]
    · rw [if_neg hT, smul_zero, Finsupp.zero_apply]
      by_cases hS : j ∈ S
      · rw [if_pos hS]
      · rw [if_neg hS, Finsupp.single_apply]
        have : T ≠ insert j S := fun hc => hT (hc ▸ Finset.mem_insert_self j S)
        rw [if_neg this, mul_zero]

/-! ## The canonical anticommutation relations -/

/-- **CAR, the diagonal relation** `{c_j, c_j†} = 1`. -/
theorem car_annF_creF_self (j : ℕ) (u : FermiAlg) :
    annF j (creF j u) + creF j (annF j u) = u := by
  classical
  refine Finsupp.ext fun S => ?_
  simp only [Finsupp.add_apply, annF_apply, creF_apply]
  by_cases hS : j ∈ S
  · rw [if_pos hS, if_pos hS, zero_add, if_neg (Finset.notMem_erase j S),
      fsign_erase, Finset.insert_erase hS, ← mul_assoc, fsign_mul_self, one_mul]
  · rw [if_neg hS, if_neg hS, add_zero, if_pos (Finset.mem_insert_self j S),
      fsign_insert_self, Finset.erase_insert hS, ← mul_assoc, fsign_mul_self, one_mul]

/-- **CAR** `{c_j†, c_k†} = 0`; with `j = k` this is the Pauli principle
`(c_j†)² = 0`. -/
theorem car_creF_creF (j k : ℕ) (u : FermiAlg) :
    creF j (creF k u) + creF k (creF j u) = 0 := by
  classical
  refine Finsupp.ext fun S => ?_
  simp only [Finsupp.add_apply, creF_apply, Finsupp.zero_apply]
  rcases eq_or_ne j k with rfl | hjk
  · simp
  · by_cases hjS : j ∈ S
    · by_cases hkS : k ∈ S
      · rw [if_pos hjS, if_pos hkS,
          if_pos (Finset.mem_erase.mpr ⟨hjk.symm, hkS⟩),
          if_pos (Finset.mem_erase.mpr ⟨hjk, hjS⟩)]
        have hswap : (S.erase j).erase k = (S.erase k).erase j := Finset.erase_right_comm
        have hj : fsign j S = (if k < j then (-1 : ℂ) else 1) * fsign j (S.erase k) := by
          have h := fsign_insert_of_ne (j := j) (k := k) (S.erase k)
            (Finset.notMem_erase k S) hjk.symm
          rwa [Finset.insert_erase hkS] at h
        have hk : fsign k S = (if j < k then (-1 : ℂ) else 1) * fsign k (S.erase j) := by
          have h := fsign_insert_of_ne (j := k) (k := j) (S.erase j)
            (Finset.notMem_erase j S) hjk
          rwa [Finset.insert_erase hjS] at h
        rcases lt_or_gt_of_ne hjk with h | h
        · have e1 : fsign k (S.erase j) = -fsign k S := by
            rw [hk, if_pos h]; ring
          have e2 : fsign j (S.erase k) = fsign j S := by
            rw [hj, if_neg (by omega : ¬ k < j), one_mul]
          rw [hswap, e1, e2]; ring
        · have e1 : fsign j (S.erase k) = -fsign j S := by
            rw [hj, if_pos h]; ring
          have e2 : fsign k (S.erase j) = fsign k S := by
            rw [hk, if_neg (by omega : ¬ j < k), one_mul]
          rw [hswap, e1, e2]; ring
      · rw [if_pos hjS, if_neg hkS,
          if_neg (fun hc => hkS (Finset.mem_of_mem_erase hc))]
        ring
    · by_cases hkS : k ∈ S
      · rw [if_neg hjS, if_pos hkS,
          if_neg (fun hc => hjS (Finset.mem_of_mem_erase hc))]
        ring
      · rw [if_neg hjS, if_neg hkS]
        ring

/-- The Pauli principle: no mode can be occupied twice. -/
theorem creF_creF_self (j : ℕ) (u : FermiAlg) : creF j (creF j u) = 0 := by
  have h := car_creF_creF j j u
  have h2 : (2 : ℂ) • creF j (creF j u) = 0 := by
    rw [two_smul]; exact h
  simpa using h2

/-- **CAR** `{c_j, c_k} = 0`. -/
theorem car_annF_annF (j k : ℕ) (u : FermiAlg) :
    annF j (annF k u) + annF k (annF j u) = 0 := by
  classical
  refine Finsupp.ext fun S => ?_
  simp only [Finsupp.add_apply, annF_apply, Finsupp.zero_apply]
  rcases eq_or_ne j k with rfl | hjk
  · by_cases hS : j ∈ S
    · rw [if_pos hS]
      ring
    · rw [if_neg hS, if_pos (Finset.mem_insert_self j S)]
      ring
  · by_cases hjS : j ∈ S
    · rw [if_pos hjS, if_pos (Finset.mem_insert_of_mem hjS)]
      simp
    · by_cases hkS : k ∈ S
      · rw [if_neg hjS, if_pos hkS, if_pos (Finset.mem_insert_of_mem hkS)]
        ring
      · have hk' : k ∉ insert j S := by simp [Finset.mem_insert, hjk.symm, hkS]
        have hj' : j ∉ insert k S := by simp [Finset.mem_insert, hjk, hjS]
        rw [if_neg hjS, if_neg hkS, if_neg hk', if_neg hj']
        have hswap : insert k (insert j S) = insert j (insert k S) := Finset.insert_comm k j S
        have hj : fsign j (insert k S) = (if k < j then (-1 : ℂ) else 1) * fsign j S :=
          fsign_insert_of_ne S hkS hjk.symm
        have hk : fsign k (insert j S) = (if j < k then (-1 : ℂ) else 1) * fsign k S :=
          fsign_insert_of_ne S hjS hjk
        rw [hswap, hj, hk]
        rcases lt_or_gt_of_ne hjk with h | h
        · rw [if_neg (by omega : ¬ k < j), if_pos h]
          ring
        · rw [if_pos h, if_neg (by omega : ¬ j < k)]
          ring

/-- **CAR, the off-diagonal mixed relation** `{c_j, c_k†} = 0` for `j ≠ k`. -/
theorem car_annF_creF_of_ne {j k : ℕ} (hjk : j ≠ k) (u : FermiAlg) :
    annF j (creF k u) + creF k (annF j u) = 0 := by
  classical
  refine Finsupp.ext fun S => ?_
  simp only [Finsupp.add_apply, annF_apply, creF_apply, Finsupp.zero_apply]
  by_cases hjS : j ∈ S
  · rw [if_pos hjS, zero_add]
    by_cases hkS : k ∈ S
    · rw [if_pos hkS, if_pos (Finset.mem_erase.mpr ⟨hjk, hjS⟩), mul_zero]
    · rw [if_neg hkS]
  · rw [if_neg hjS]
    by_cases hkS : k ∈ S
    · rw [if_pos hkS, if_pos (Finset.mem_insert_of_mem hkS),
        if_neg (fun hc => hjS (Finset.mem_of_mem_erase hc))]
      have hset : (insert j S).erase k = insert j (S.erase k) :=
        Finset.erase_insert_of_ne hjk
      have hk : fsign k (insert j S) = (if j < k then (-1 : ℂ) else 1) * fsign k S :=
        fsign_insert_of_ne S hjS hjk
      have hj : fsign j S = (if k < j then (-1 : ℂ) else 1) * fsign j (S.erase k) := by
        have hk' : k ∉ S.erase k := Finset.notMem_erase k S
        have h := fsign_insert_of_ne (j := j) (k := k) (S.erase k) hk' hjk.symm
        rwa [Finset.insert_erase hkS] at h
      rcases lt_or_gt_of_ne hjk with h | h
      · have e1 : fsign k (insert j S) = -fsign k S := by rw [hk, if_pos h]; ring
        have e2 : fsign j (S.erase k) = fsign j S := by
          rw [hj, if_neg (by omega : ¬ k < j), one_mul]
        rw [hset, e1, e2]; ring
      · have e1 : fsign k (insert j S) = fsign k S := by
          rw [hk, if_neg (by omega : ¬ j < k), one_mul]
        have e2 : fsign j (S.erase k) = -fsign j S := by rw [hj, if_pos h]; ring
        rw [hset, e1, e2]; ring
    · rw [if_neg hkS, if_neg (fun hc => hkS (by
        rcases Finset.mem_insert.mp hc with h | h
        · exact absurd h.symm hjk
        · exact h)), mul_zero, add_zero]

/-! ## The occupied modes of a state -/

/-- The set of modes a state of the algebraic Fock space can occupy. -/
def modesF (u : FermiAlg) : Finset ℕ := u.support.biUnion id

theorem mem_modesF {u : FermiAlg} {S : FConf} (hS : S ∈ u.support) {i : ℕ} (hi : i ∈ S) :
    i ∈ modesF u := Finset.mem_biUnion.mpr ⟨S, hS, hi⟩

/-- A mode that no configuration of `u` occupies is annihilated by `c_k`. -/
theorem annF_eq_zero_of_not_mem_modesF {u : FermiAlg} {k : ℕ} (h : k ∉ modesF u) :
    annF k u = 0 := by
  classical
  refine Finsupp.ext fun S => ?_
  rw [annF_apply, Finsupp.zero_apply]
  by_cases hk : k ∈ S
  · rw [if_pos hk]
  · rw [if_neg hk]
    have hu : u (insert k S) = 0 := by
      by_contra hc
      exact h (mem_modesF (Finsupp.mem_support_iff.mpr hc) (Finset.mem_insert_self k S))
    rw [hu, mul_zero]

/-! ## Transport to `ℓ²(FConf)` -/

/-- A finitely supported fermionic state as an element of `ℓ²(FConf)`. -/
def toLpF (u : FermiAlg) : FermiFock :=
  ⟨fun S => u S, memLpTwo_of_finite_support u.finite_support⟩

@[simp] theorem toLpF_apply (u : FermiAlg) (S : FConf) :
    ((toLpF u : FermiFock) : FConf → ℂ) S = u S := rfl

/-- The transport map is linear. -/
def toLpFL : FermiAlg →ₗ[ℂ] FermiFock where
  toFun := toLpF
  map_add' u v := by
    refine lp.ext (funext fun S => ?_)
    simp [toLpF, Pi.add_apply]
    try rfl
  map_smul' c u := by
    refine lp.ext (funext fun S => ?_)
    simp [toLpF]

@[simp] theorem toLpFL_apply (u : FermiAlg) : toLpFL u = toLpF u := rfl

theorem toLpF_mem (u : FermiAlg) : toLpF u ∈ lpFiniteModes FConf := u.finite_support

theorem toLpF_injective : Function.Injective toLpF := by
  intro u v h
  refine Finsupp.ext fun S => ?_
  have := congrArg (fun f : FermiFock => (f : FConf → ℂ) S) h
  simpa using this

/-- The inner product of two finitely supported fermionic states is the finite
sum of the products of their coordinates. -/
theorem inner_toLpF_of_subset {u : FermiAlg} {s : Finset FConf} (hs : u.support ⊆ s)
    (v : FermiAlg) :
    (inner ℂ (toLpF u) (toLpF v) : ℂ) = ∑ S ∈ s, (starRingEnd ℂ) (u S) * v S := by
  rw [lp.inner_eq_tsum]
  have hcoord : ∀ S : FConf,
      (inner ℂ (((toLpF u : FermiFock) : FConf → ℂ) S)
        (((toLpF v : FermiFock) : FConf → ℂ) S) : ℂ) = (starRingEnd ℂ) (u S) * v S := by
    intro S
    simp [RCLike.inner_apply, mul_comm]
  rw [tsum_congr hcoord]
  refine tsum_eq_sum fun S hS => ?_
  have hu : u S = 0 := by
    by_contra hc
    exact hS (hs (Finsupp.mem_support_iff.mpr hc))
  rw [hu, map_zero, zero_mul]

theorem inner_toLpF (u v : FermiAlg) :
    (inner ℂ (toLpF u) (toLpF v) : ℂ) = ∑ S ∈ u.support, (starRingEnd ℂ) (u S) * v S :=
  inner_toLpF_of_subset (Finset.Subset.refl _) v

/-! ## Creation and annihilation are formal adjoints -/

/-- The involution of configurations that toggles the occupation of the mode
`j`; it matches the configurations `c_j†` connects. -/
def toggle (j : ℕ) (S : FConf) : FConf := if j ∈ S then S.erase j else insert j S

theorem toggle_of_mem {j : ℕ} {S : FConf} (h : j ∈ S) : toggle j S = S.erase j :=
  if_pos h

theorem toggle_of_not_mem {j : ℕ} {S : FConf} (h : j ∉ S) : toggle j S = insert j S :=
  if_neg h

theorem toggle_toggle (j : ℕ) (S : FConf) : toggle j (toggle j S) = S := by
  by_cases hS : j ∈ S
  · rw [toggle_of_mem hS, toggle_of_not_mem (Finset.notMem_erase j S), Finset.insert_erase hS]
  · rw [toggle_of_not_mem hS, toggle_of_mem (Finset.mem_insert_self j S),
      Finset.erase_insert hS]

theorem support_creF (j : ℕ) (u : FermiAlg) :
    (creF j u).support ⊆ u.support.image (toggle j) := by
  classical
  intro S hS
  have hS' := Finsupp.mem_support_iff.mp hS
  rw [creF_apply] at hS'
  by_cases hj : j ∈ S
  · rw [if_pos hj] at hS'
    have hu : u (S.erase j) ≠ 0 := fun h => hS' (by rw [h, mul_zero])
    refine Finset.mem_image.mpr ⟨S.erase j, Finsupp.mem_support_iff.mpr hu, ?_⟩
    rw [toggle_of_not_mem (Finset.notMem_erase j S), Finset.insert_erase hj]
  · rw [if_neg hj] at hS'
    exact absurd rfl hS'

theorem support_annF (j : ℕ) (u : FermiAlg) :
    (annF j u).support ⊆ u.support.image (toggle j) := by
  classical
  intro S hS
  have hS' := Finsupp.mem_support_iff.mp hS
  rw [annF_apply] at hS'
  by_cases hj : j ∈ S
  · rw [if_pos hj] at hS'
    exact absurd rfl hS'
  · rw [if_neg hj] at hS'
    have hu : u (insert j S) ≠ 0 := fun h => hS' (by rw [h, mul_zero])
    refine Finset.mem_image.mpr ⟨insert j S, Finsupp.mem_support_iff.mpr hu, ?_⟩
    rw [toggle_of_mem (Finset.mem_insert_self j S), Finset.erase_insert hj]

/-- **The adjoint pairing of creation and annihilation**: `⟪c_j† u, v⟫ = ⟪u, c_j v⟫`. -/
theorem inner_creF_left (j : ℕ) (u v : FermiAlg) :
    (inner ℂ (toLpF (creF j u)) (toLpF v) : ℂ) = inner ℂ (toLpF u) (toLpF (annF j v)) := by
  classical
  set s : Finset FConf := (creF j u).support ∪ u.support with hs
  set F : Finset FConf := s ∪ s.image (toggle j) with hF
  have hmemF : ∀ S ∈ F, toggle j S ∈ F := by
    intro S hS
    rcases Finset.mem_union.mp hS with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S, h, rfl⟩)
    · obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp h
      refine Finset.mem_union_left _ ?_
      rw [← hTS, toggle_toggle]
      exact hT
  have hcre : (creF j u).support ⊆ F :=
    fun S hS => Finset.mem_union_left _ (Finset.mem_union_left _ hS)
  have hu : u.support ⊆ F :=
    fun S hS => Finset.mem_union_left _ (Finset.mem_union_right _ hS)
  rw [inner_toLpF_of_subset hcre v, inner_toLpF_of_subset hu (annF j v)]
  refine Finset.sum_nbij' (i := toggle j) (j := toggle j)
    (fun S hS => hmemF S hS) (fun S hS => hmemF S hS)
    (fun S _ => toggle_toggle j S) (fun S _ => toggle_toggle j S) ?_
  intro S _
  by_cases hj : j ∈ S
  · rw [creF_apply, if_pos hj, toggle_of_mem hj, annF_apply,
      if_neg (Finset.notMem_erase j S), fsign_erase, Finset.insert_erase hj, map_mul,
      fsign_conj]
    ring
  · rw [creF_apply, if_neg hj, toggle_of_not_mem hj, annF_apply,
      if_pos (Finset.mem_insert_self j S), map_zero, zero_mul, mul_zero]

/-- The mirror image of `inner_creF_left`: `⟪u, c_j† v⟫ = ⟪c_j u, v⟫`. -/
theorem inner_creF_right (j : ℕ) (u v : FermiAlg) :
    (inner ℂ (toLpF u) (toLpF (creF j v)) : ℂ) = inner ℂ (toLpF (annF j u)) (toLpF v) := by
  have h := inner_creF_left j v u
  have := congrArg (starRingEnd ℂ) h
  rwa [inner_conj_symm, inner_conj_symm] at this

/-! ## The finite-occupation domain of the fermionic Fock space -/

/-- The algebraic fermionic Fock space **is** the finite-occupation subspace of
`ℓ²(FConf)`. -/
def fermiEquiv : FermiAlg ≃ₗ[ℂ] lpFiniteModes FConf := by
  classical
  refine LinearEquiv.ofBijective (toLpFL.codRestrict (lpFiniteModes FConf) toLpF_mem) ⟨?_, ?_⟩
  · intro u v h
    exact toLpF_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    refine ⟨Finsupp.onFinset hx.toFinset (fun S => (x : FConf → ℂ) S) ?_, ?_⟩
    · intro S hS
      exact hx.mem_toFinset.mpr hS
    · exact Subtype.ext (lp.ext (funext fun _ => rfl))

@[simp] theorem coe_fermiEquiv (u : FermiAlg) :
    ((fermiEquiv u : lpFiniteModes FConf) : FermiFock) = toLpF u := rfl

theorem coe_fermiEquiv_symm (x : lpFiniteModes FConf) :
    ((x : lpFiniteModes FConf) : FermiFock) = toLpF (fermiEquiv.symm x) := by
  rw [← coe_fermiEquiv, LinearEquiv.apply_symm_apply]

/-! ## Fermionic second quantization -/

/-- The creation operator of a finitely supported one-particle vector
`v = Σ_j v_j e_j`: `c†(v) = Σ_j v_j c_j†`. -/
def creVecF (v : ℕ →₀ ℂ) : FermiAlg →ₗ[ℂ] FermiAlg := ∑ j ∈ v.support, (v j) • creF j

/-- **The fermionic second quantization** `dΓᵃ(A) = Σ_k c†(A e_k) c_k` of the
one-particle operator whose `k`-th column of matrix elements is `col k` (so
`(col k) j = ⟪e_j, A e_k⟫`).  Because a fermionic configuration *is* its set of
occupied modes, the sum on a basis state `|S⟩` runs over `k ∈ S`. -/
def dGammaF (col : ℕ → (ℕ →₀ ℂ)) : FermiAlg →ₗ[ℂ] FermiAlg :=
  Finsupp.lsum ℂ fun S => LinearMap.toSpanSingleton ℂ FermiAlg
    (∑ k ∈ S, creVecF (col k) (annF k (Finsupp.single S 1)))

theorem creVecF_apply (v : ℕ →₀ ℂ) (x : FermiAlg) :
    creVecF v x = ∑ j ∈ v.support, v j • creF j x := by
  simp [creVecF, LinearMap.sum_apply]

@[simp] theorem dGammaF_single (col : ℕ → (ℕ →₀ ℂ)) (S : FConf) (c : ℂ) :
    dGammaF col (Finsupp.single S c)
      = c • ∑ k ∈ S, creVecF (col k) (annF k (Finsupp.single S 1)) := by
  simp [dGammaF, LinearMap.toSpanSingleton]

/-- Enlarging the index set beyond the occupied modes does not change the sum. -/
theorem sum_creVecF_annF_subset (col : ℕ → (ℕ →₀ ℂ)) (u : FermiAlg) {K L : Finset ℕ}
    (hKL : K ⊆ L) (hK : modesF u ⊆ K) :
    ∑ k ∈ K, creVecF (col k) (annF k u) = ∑ k ∈ L, creVecF (col k) (annF k u) :=
  Finset.sum_subset hKL fun k _ hk => by
    rw [annF_eq_zero_of_not_mem_modesF (fun hc => hk (hK hc)), map_zero]

theorem dGammaF_eq_sum_aux (col : ℕ → (ℕ →₀ ℂ)) (u : FermiAlg) :
    ∀ K : Finset ℕ, modesF u ⊆ K → dGammaF col u = ∑ k ∈ K, creVecF (col k) (annF k u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => intro K _; simp
  | add f g hf hg =>
    intro K hK
    have hL1 : modesF f ⊆ K ∪ (modesF f ∪ modesF g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_left _ hx)
    have hL2 : modesF g ⊆ K ∪ (modesF f ∪ modesF g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_right _ hx)
    have hKL : K ⊆ K ∪ (modesF f ∪ modesF g) := Finset.subset_union_left
    rw [map_add, hf _ hL1, hg _ hL2, ← Finset.sum_add_distrib,
      sum_creVecF_annF_subset col (f + g) hKL hK]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_add]
  | single T c =>
    intro K hK
    have hsingle : (Finsupp.single T c : FermiAlg) = c • Finsupp.single T (1 : ℂ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hc : c = 0
    · subst hc; simp
    have hT : T ⊆ K := by
      refine fun i hi => hK ?_
      exact Finset.mem_biUnion.mpr ⟨T, Finsupp.mem_support_iff.mpr (by simpa using hc), hi⟩
    have hzero : ∀ k ∈ K, k ∉ T → creVecF (col k) (annF k (Finsupp.single T c)) = 0 := by
      intro k _ hk
      rw [annF_single, if_neg hk, smul_zero, map_zero]
    rw [← Finset.sum_subset hT hzero, dGammaF_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsingle, map_smul, map_smul]

/-- On a state occupying only modes in `K`, the second quantization is the finite
sum `∑_{k ∈ K} c†(A e_k) c_k`. -/
theorem dGammaF_eq_sum (col : ℕ → (ℕ →₀ ℂ)) {u : FermiAlg} {K : Finset ℕ} (hK : modesF u ⊆ K) :
    dGammaF col u = ∑ k ∈ K, creVecF (col k) (annF k u) :=
  dGammaF_eq_sum_aux col u K hK

/-- **On the one-particle sector the fermionic second quantization is the
one-particle operator**: `dΓᵃ(A)|e_k⟩ = Σ_j ⟪e_j, A e_k⟫ |e_j⟩`. -/
theorem dGammaF_one_particle (col : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    dGammaF col (Finsupp.single ({k} : FConf) 1)
      = ∑ j ∈ (col k).support, (col k) j • Finsupp.single ({j} : FConf) (1 : ℂ) := by
  classical
  have hsign : ∀ j : ℕ, fsign j (∅ : FConf) = 1 := by
    intro j; simp [fsign]
  have hsk : fsign k ({k} : FConf) = 1 := by
    simp [fsign, Finset.filter_singleton]
  have hann : annF k (Finsupp.single ({k} : FConf) (1 : ℂ))
      = Finsupp.single (∅ : FConf) (1 : ℂ) := by
    rw [annF_single, if_pos (Finset.mem_singleton_self k), one_smul,
      Finset.erase_singleton, hsk]
  rw [dGammaF_single, Finset.sum_singleton, hann, one_smul, creVecF_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [creF_single, if_neg (Finset.notMem_empty j), one_smul, hsign]
  congr 1

/-! ### Symmetry and positivity of the fermionic second quantization -/

@[simp] theorem toLpF_zero : toLpF (0 : FermiAlg) = 0 := map_zero toLpFL

/-- One term of the double-sum expansion, on the left. -/
theorem inner_creVecF_annF (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) (k : ℕ) {L : Finset ℕ}
    (h : (col k).support ⊆ L) :
    (inner ℂ (toLpF (creVecF (col k) (annF k u))) (toLpF v) : ℂ)
      = ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
          * inner ℂ (toLpF (annF k u)) (toLpF (annF j v)) := by
  have hexp : toLpF (creVecF (col k) (annF k u))
      = ∑ j ∈ (col k).support, (col k) j • toLpF (creF j (annF k u)) := by
    rw [creVecF_apply, ← toLpFL_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, toLpFL_apply]
  rw [hexp, sum_inner, ← Finset.sum_subset h (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, map_zero, zero_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_creF_left]

/-- One term of the double-sum expansion, on the right. -/
theorem inner_annF_creVecF (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) (j : ℕ) {L : Finset ℕ}
    (h : (col j).support ⊆ L) :
    (inner ℂ (toLpF u) (toLpF (creVecF (col j) (annF j v))) : ℂ)
      = ∑ k ∈ L, (col j) k * inner ℂ (toLpF (annF k u)) (toLpF (annF j v)) := by
  have hexp : toLpF (creVecF (col j) (annF j v))
      = ∑ k ∈ (col j).support, (col j) k • toLpF (creF k (annF j v)) := by
    rw [creVecF_apply, ← toLpFL_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, toLpFL_apply]
  rw [hexp, inner_sum, ← Finset.sum_subset h (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.mp hk, zero_mul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, inner_creF_right]

/-- The double-sum expansion of the second-quantized sesquilinear form. -/
theorem inner_dGammaF_left (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) {L : Finset ℕ}
    (hu : modesF u ⊆ L)
    (hL : ∀ k ∈ modesF u ∪ modesF v, (col k).support ⊆ L) :
    (inner ℂ (toLpF (dGammaF col u)) (toLpF v) : ℂ)
      = ∑ k ∈ L, ∑ j ∈ L,
        (starRingEnd ℂ) ((col k) j) * inner ℂ (toLpF (annF k u)) (toLpF (annF j v)) := by
  have hsum : toLpF (dGammaF col u) = ∑ k ∈ L, toLpF (creVecF (col k) (annF k u)) := by
    rw [dGammaF_eq_sum col hu, ← toLpFL_apply, map_sum]
    rfl
  rw [hsum, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hku : k ∈ modesF u
  · exact inner_creVecF_annF col u v k (hL k (Finset.mem_union_left _ hku))
  · have h0 : annF k u = 0 := annF_eq_zero_of_not_mem_modesF hku
    rw [h0, map_zero]
    simp

theorem inner_dGammaF_right (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) {L : Finset ℕ}
    (hv : modesF v ⊆ L)
    (hL : ∀ k ∈ modesF u ∪ modesF v, (col k).support ⊆ L) :
    (inner ℂ (toLpF u) (toLpF (dGammaF col v)) : ℂ)
      = ∑ j ∈ L, ∑ k ∈ L,
        (col j) k * inner ℂ (toLpF (annF k u)) (toLpF (annF j v)) := by
  have hsum : toLpF (dGammaF col v) = ∑ j ∈ L, toLpF (creVecF (col j) (annF j v)) := by
    rw [dGammaF_eq_sum col hv, ← toLpFL_apply, map_sum]
    rfl
  rw [hsum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hjv : j ∈ modesF v
  · exact inner_annF_creVecF col u v j (hL j (Finset.mem_union_right _ hjv))
  · have h0 : annF j v = 0 := annF_eq_zero_of_not_mem_modesF hjv
    rw [h0, map_zero]
    simp

/-- A finite set of modes large enough for both states and for the columns of
the one-particle matrix over their modes. -/
def closureModesF (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) : Finset ℕ :=
  (modesF u ∪ modesF v) ∪ (modesF u ∪ modesF v).biUnion fun k => (col k).support

theorem modesF_left_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) :
    modesF u ⊆ closureModesF col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem modesF_right_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) :
    modesF v ⊆ closureModesF col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_right _ hx)

theorem colF_support_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) :
    ∀ k ∈ modesF u ∪ modesF v, (col k).support ⊆ closureModesF col u v := by
  intro k hk i hi
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩)

/-- **The fermionic second quantization of a Hermitian one-particle matrix is
symmetric.** -/
theorem inner_dGammaF_symm {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) (u v : FermiAlg) :
    (inner ℂ (toLpF (dGammaF col u)) (toLpF v) : ℂ)
      = inner ℂ (toLpF u) (toLpF (dGammaF col v)) := by
  rw [inner_dGammaF_left col u v (modesF_left_subset_closure col u v)
      (colF_support_subset_closure col u v),
    inner_dGammaF_right col u v (modesF_right_subset_closure col u v)
      (colF_support_subset_closure col u v),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hherm j k, Complex.conj_conj]

/-- **The fermionic second quantization of a positive one-particle matrix is
positive.** -/
theorem inner_dGammaF_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (u : FermiAlg) :
    0 ≤ (inner ℂ (toLpF u) (toLpF (dGammaF col u)) : ℂ).re := by
  classical
  set L := closureModesF col u u with hLdef
  set S : Finset FConf := L.biUnion fun k => (annF k u).support with hSdef
  rw [inner_dGammaF_right col u u (modesF_right_subset_closure col u u)
    (colF_support_subset_closure col u u)]
  have hinner : ∀ k ∈ L, ∀ j : ℕ,
      (inner ℂ (toLpF (annF k u)) (toLpF (annF j u)) : ℂ)
        = ∑ T ∈ S, (starRingEnd ℂ) ((annF k u) T) * (annF j u) T := by
    intro k hk j
    exact inner_toLpF_of_subset (fun T hT => Finset.mem_biUnion.mpr ⟨k, hk, hT⟩) _
  have hstep : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLpF (annF k u)) (toLpF (annF j u)))
      = ∑ T ∈ S, ∑ j ∈ L, ∑ k ∈ L,
          (starRingEnd ℂ) ((annF j u) T) * (col k) j * ((annF k u) T) := by
    have h1 : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLpF (annF k u)) (toLpF (annF j u)))
        = ∑ j ∈ L, ∑ k ∈ L, ∑ T ∈ S,
            (col j) k * ((starRingEnd ℂ) ((annF k u) T) * (annF j u) T) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k hk => ?_
      rw [hinner k hk j, Finset.mul_sum]
    rw [h1]
    rw [Finset.sum_comm (s := L) (t := L)]
    rw [show (∑ k ∈ L, ∑ j ∈ L, ∑ T ∈ S,
          (col j) k * ((starRingEnd ℂ) ((annF k u) T) * (annF j u) T))
        = ∑ k ∈ L, ∑ T ∈ S, ∑ j ∈ L,
          (col j) k * ((starRingEnd ℂ) ((annF k u) T) * (annF j u) T) from
      Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm (s := L) (t := S)]
    refine Finset.sum_congr rfl fun T _ => ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hstep, Complex.re_sum]
  refine Finset.sum_nonneg fun T _ => hpos L fun k => (annF k u) T

/-! ### The fermionic second-quantized operator on the finite-occupation domain -/

/-- **The fermionic second-quantized operator** on the finite-occupation domain
of the fermionic Fock space. -/
def dGammaOpF (col : ℕ → (ℕ →₀ ℂ)) : lpFiniteModes FConf →ₗ[ℂ] FermiFock :=
  (lpFiniteModes FConf).subtype.comp (fermiEquiv.conj (dGammaF col))

theorem coe_dGammaOpF (col : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes FConf) :
    dGammaOpF col x = toLpF (dGammaF col (fermiEquiv.symm x)) := by
  simp [dGammaOpF, LinearEquiv.conj_apply, coe_fermiEquiv]

theorem dGammaOpF_symmetricOn {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (lpFiniteModes FConf) (dGammaOpF col) := by
  intro x y
  rw [coe_dGammaOpF, coe_dGammaOpF, coe_fermiEquiv_symm x, coe_fermiEquiv_symm y]
  exact inner_dGammaF_symm hherm _ _

theorem dGammaOpF_quadForm_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : lpFiniteModes FConf) : 0 ≤ quadForm (dGammaOpF col) x := by
  rw [quadForm, coe_dGammaOpF, coe_fermiEquiv_symm x]
  exact inner_dGammaF_nonneg hpos _

/-- The finite-occupation domain is dense in the fermionic Fock space. -/
theorem finiteOccupationF_dense :
    Dense ((lpFiniteModes FConf : Submodule ℂ FermiFock) : Set FermiFock) :=
  lpFiniteModes_dense

/-- **The fermionic second-quantized Hamiltonian has a positive self-adjoint
(Friedrichs) extension.** -/
theorem dGammaF_friedrichs_extension {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col)
    (hpos : IsPosCol col) :
    ∃ (Dom : Submodule ℂ FermiFock) (A : Dom →ₗ[ℂ] FermiFock),
      IsPositiveSelfAdjointExtension (dGammaOpF col) A :=
  friedrichs_extension_exists_complete
    ⟨lpFiniteModes FConf, dGammaOpF col, dGammaOpF_symmetricOn hherm,
      dGammaOpF_quadForm_nonneg hpos⟩
    finiteOccupationF_dense

/-- **Fermionic second quantization of an arbitrary symmetric positive
one-particle operator.** -/
theorem secondQuantizationF_friedrichs {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    ∃ (Dom : Submodule ℂ FermiFock) (A' : Dom →ₗ[ℂ] FermiFock),
      IsPositiveSelfAdjointExtension (dGammaOpF (opCol b A)) A' :=
  dGammaF_friedrichs_extension (isHermCol_opCol hA) (isPosCol_opCol hpos)

/-! ## The fermion-number parity (the `ℤ₂` grading operator) -/

/-- **The fermion-number parity operator** `(−1)^{N_f}`: it multiplies the
configuration `S` by `(−1)^{|S|}`.  It is the grading operator of the fermionic
Fock space. -/
def parityF : FermiAlg →ₗ[ℂ] FermiAlg :=
  Finsupp.lsum ℂ fun S => LinearMap.toSpanSingleton ℂ FermiAlg
    (Finsupp.single S ((-1 : ℂ) ^ S.card))

@[simp] theorem parityF_apply (u : FermiAlg) (S : FConf) :
    parityF u S = (-1 : ℂ) ^ S.card * u S := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, mul_add]
  | single T c =>
    rw [parityF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
      Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases h : T = S
    · subst h; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg h, if_neg h, mul_zero, mul_zero]

/-- The parity operator is an involution. -/
theorem parityF_involutive (u : FermiAlg) : parityF (parityF u) = u := by
  refine Finsupp.ext fun S => ?_
  rw [parityF_apply, parityF_apply, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **Creation is odd**: it anticommutes with the parity operator. -/
theorem parityF_creF (j : ℕ) (u : FermiAlg) :
    parityF (creF j u) = - creF j (parityF u) := by
  classical
  refine Finsupp.ext fun S => ?_
  rw [parityF_apply, creF_apply, Finsupp.neg_apply, creF_apply]
  by_cases hj : j ∈ S
  · rw [if_pos hj, if_pos hj, parityF_apply]
    have hcard : S.card = (S.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    rw [hcard, pow_succ]
    ring
  · rw [if_neg hj, if_neg hj, mul_zero, neg_zero]

/-- **Annihilation is odd**: it anticommutes with the parity operator. -/
theorem parityF_annF (j : ℕ) (u : FermiAlg) :
    parityF (annF j u) = - annF j (parityF u) := by
  classical
  refine Finsupp.ext fun S => ?_
  rw [parityF_apply, annF_apply, Finsupp.neg_apply, annF_apply]
  by_cases hj : j ∈ S
  · rw [if_pos hj, if_pos hj, mul_zero, neg_zero]
  · rw [if_neg hj, if_neg hj, parityF_apply,
      Finset.card_insert_of_notMem hj, pow_succ]
    ring

/-! ## The Hashimoto/SIRK selection for the fermionic second quantization -/

section Selection

open Filter Topology

variable {ι : Type*} [DecidableEq ι]

/-- The canonical Hilbert basis of `ℓ²(ι)`, indexed by `ι` itself. -/
def l2Basis (ι : Type*) : HilbertBasis ι ℂ (L2I ι) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

theorem l2Basis_apply (α : ι) : l2Basis ι α = lp.single 2 α (1 : ℂ) := by
  rw [← HilbertBasis.repr_symm_single]
  rfl

/-- The canonical basis of `ℓ²(ι)` re-indexed by `ℕ`, the form in which the
abstract Friedrichs and Hashimoto theorems are stated. -/
def l2BasisN (ε : ℕ ≃ ι) : HilbertBasis ℕ ℂ (L2I ι) :=
  HilbertBasis.mk ((l2Basis ι).orthonormal.comp _ ε.injective)
    (by
      have h := (l2Basis ι).dense_span
      rw [Set.range_comp, ε.range_eq_univ, Set.image_univ]
      exact h.ge)

theorem l2BasisN_apply (ε : ℕ ≃ ι) (n : ℕ) :
    l2BasisN ε n = lp.single 2 (ε n) (1 : ℂ) := by
  rw [l2BasisN, HilbertBasis.coe_mk]
  exact l2Basis_apply _

theorem lp_sum_single_coordI (S : Finset ι) (f : ι → ℂ) (β : ι) :
    (((∑ α ∈ S, f α • lp.single 2 α (1 : ℂ)) : L2I ι) : ι → ℂ) β
      = if β ∈ S then f β else 0 := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.single_apply, ih]
    by_cases hb : β = a
    · subst hb
      simp [ha]
    · simp [hb, Finset.mem_insert]

omit [DecidableEq ι] in
/-- **The finite-mode domain of the canonical basis of `ℓ²(ι)` is exactly the
finitely supported subspace**, so the abstract theorems apply verbatim. -/
theorem finiteModeDomain_l2BasisN (ε : ℕ ≃ ι) :
    finiteModeDomain (l2BasisN ε) = lpFiniteModes ι := by
  classical
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx => ?_
  · rintro y ⟨n, rfl⟩
    rw [l2BasisN_apply]
    exact lpSingle_mem_lpFiniteModes _ _
  · set S : Finset ι := hx.toFinset with hS
    have hxeq : x = ∑ α ∈ S, ((x : ι → ℂ) α) • lp.single 2 α (1 : ℂ) := by
      refine lp.ext (funext fun β => ?_)
      rw [lp_sum_single_coordI]
      by_cases hb : β ∈ S
      · simp [hb]
      · have hz : (x : ι → ℂ) β = 0 := by
          by_contra hc
          exact hb (hx.mem_toFinset.mpr hc)
        simp [hb, hz]
    rw [hxeq]
    refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨ε.symm α, ?_⟩
    rw [l2BasisN_apply, Equiv.apply_symm_apply]

/-- The fermionic second-quantized operator on the finite-mode domain of
`l2BasisN ε` (the same subspace as `lpFiniteModes FConf`). -/
def dGammaOpFB (ε : ℕ ≃ FConf) (col : ℕ → (ℕ →₀ ℂ)) :
    finiteModeDomain (l2BasisN ε) →ₗ[ℂ] FermiFock :=
  (dGammaOpF col).comp (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε)).toLinearMap

theorem dGammaOpFB_symmetricOn {ε : ℕ ≃ FConf} {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (finiteModeDomain (l2BasisN ε)) (dGammaOpFB ε col) := by
  intro x y
  exact dGammaOpF_symmetricOn hherm
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε) x)
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε) y)

theorem dGammaOpFB_quadForm_nonneg {ε : ℕ ≃ FConf} {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : finiteModeDomain (l2BasisN ε)) : 0 ≤ quadForm (dGammaOpFB ε col) x :=
  dGammaOpF_quadForm_nonneg hpos
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε) x)

/-- **The Hashimoto/SIRK shift-invert limit selects the Friedrichs extension of
the fermionic second-quantized Hamiltonian.** -/
theorem dGammaF_hashimoto_selects (ε : ℕ ≃ FConf) {col : ℕ → (ℕ →₀ ℂ)}
    (hherm : IsHermCol col) (hpos : IsPosCol col) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ FermiFock) (A : Dom →ₗ[ℂ] FermiFock) (R : FermiFock →L[ℂ] FermiFock),
      IsPositiveSelfAdjointExtension (dGammaOpFB ε col) A ∧ IsShiftInvert A γ R ∧
        ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : FermiFock, Tendsto (fun k : ℕ => galerkinCompression R (l2BasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : FermiFock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (l2BasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ FermiFock) (A' : Dom' →ₗ[ℂ] FermiFock), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : FermiFock) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
            A' ⟨x, hx'⟩ = A ⟨x, hx⟩) :=
  friedrichs_hashimoto_selects (l2BasisN ε) (dGammaOpFB ε col)
    (dGammaOpFB_symmetricOn hherm) (dGammaOpFB_quadForm_nonneg hpos) hγ

/-- A concrete enumeration of the fermionic configurations, so that the
selection theorem is not vacuous. -/
def fermiEnum : ℕ ≃ FConf :=
  letI : Denumerable FConf := Denumerable.ofEncodableOfInfinite _
  (Denumerable.eqv FConf).symm

/-- **The Hashimoto/SIRK algorithm selects the Friedrichs extension of the
fermionic second quantization of an arbitrary symmetric positive one-particle
operator.** -/
theorem secondQuantizationF_hashimoto_selects {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (ε : ℕ ≃ FConf) (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ FermiFock) (A' : Dom →ₗ[ℂ] FermiFock) (R : FermiFock →L[ℂ] FermiFock),
      IsPositiveSelfAdjointExtension (dGammaOpFB ε (opCol b A)) A' ∧ IsShiftInvert A' γ R ∧
        ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : FermiFock, Tendsto (fun k : ℕ => galerkinCompression R (l2BasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : FermiFock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (l2BasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ FermiFock) (A'' : Dom' →ₗ[ℂ] FermiFock), IsShiftInvert A'' γ R →
          Dom' = Dom ∧ ∀ (x : FermiFock) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
            A'' ⟨x, hx'⟩ = A' ⟨x, hx⟩) :=
  dGammaF_hashimoto_selects ε (isHermCol_opCol hA) (isPosCol_opCol hpos) hγ

end Selection

/-! ## The BRST ghost relations are realized

`BookProof.BRSTNilpotent` proves the nilpotency `Q² = 0` of the cubic ghost BRST
charge from the *abstract* hypothesis `GhostCAR χ β`.  The operators built in
this chapter satisfy it, so those hypotheses are not vacuous. -/

/-- The ghost creation operators `χ_a = c_a†` on the fermionic Fock space. -/
def ghostChi (n : ℕ) : Fin n → Module.End ℂ FermiAlg := fun a => creF a.val

/-- The ghost annihilation operators `β_a = c_a` on the fermionic Fock space. -/
def ghostBeta (n : ℕ) : Fin n → Module.End ℂ FermiAlg := fun a => annF a.val

/-- **The abstract ghost anticommutation relations of `ChapterBRSTNilpotent` are
realized** by the creation and annihilation operators of the fermionic Fock
space. -/
theorem ghostCAR_creF_annF (n : ℕ) :
    BookProof.BRSTNilpotent.GhostCAR (ghostChi n) (ghostBeta n) where
  chichi a b := by
    refine LinearMap.ext fun u => ?_
    simpa [ghostChi, Module.End.mul_apply] using car_creF_creF a.val b.val u
  betabeta a b := by
    refine LinearMap.ext fun u => ?_
    simpa [ghostBeta, Module.End.mul_apply] using car_annF_annF a.val b.val u
  betachi a b := by
    refine LinearMap.ext fun u => ?_
    rcases eq_or_ne a b with rfl | hab
    · simpa [ghostChi, ghostBeta, Module.End.mul_apply] using car_annF_creF_self a.val u
    · have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
      simpa [ghostChi, ghostBeta, Module.End.mul_apply, hab] using
        car_annF_creF_of_ne hval u

/-- **The BRST charge is nilpotent on the concrete fermionic Fock space.**  This
is `BookProof.BRSTNilpotent.brst_charge_nilpotent` with the abstract ghost
algebra replaced by the operators constructed here. -/
theorem brst_charge_nilpotent_fermiFock {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin n,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    BookProof.BRSTNilpotent.Q f (ghostChi n) (ghostBeta n)
        * BookProof.BRSTNilpotent.Q f (ghostChi n) (ghostBeta n) = 0 :=
  BookProof.BRSTNilpotent.brst_charge_nilpotent f _ _ (ghostCAR_creF_annF n) hf12 hjac

end

end BookProof.FermionFock


