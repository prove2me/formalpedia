-- Prove2me | Definitions.Def_RPLib_S1_MainLemmaA
-- name    : RPLib_S1_MainLemmaA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:18:38.566816+00:00
-- url     : https://prove2.me/theorems/d4742d97-853d-4995-a8a8-7a07738c0db1
-- title:
--   Single-prime descent for the Atkin-Lehner-Li Main Lemma
-- statement:
--   Let $p$ be prime and $N = pM$. If $f \in S_k(\Gamma_1(N))$ has $a_n(f) = 0$ whenever $p \nmid n$, then $f = \iota_p g$ for a unique $g \in S_k(\Gamma_1(M))$, namely $g(\tau) = f(\tau/p)$, with $a_m(g) = a_{pm}(f)$. The file also proves the matrix-group fact $\Gamma_1(M) = \langle T, \beta^{-1}\Gamma(N)\beta\rangle$ with $\beta = \operatorname{diag}(1/p, 1)$ used in the descent.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.7

import Mathlib
import Definitions.Def_RPLib_S1_Level

/-!
# S1-MAINLEMMA-A: single-prime descent for the Atkin-Lehner-Li Main Lemma (RP project)

Diamond-Shurman §5.7, the single-prime step. Namespace `RamanujanPetersson.MainLemmaA`.
Imports Mathlib and `Definitions.Def_RPLib_S1_Level` (for `G1`, `dg`, `iotaCF`).

Notation: `p` prime, `M ≥ 1`, `N = p * M`, `β = diag(1/p, 1) = (dg p)⁻¹` (so `β • τ = τ / p`).

## 1. Generation (pure matrix algebra in `SL(2, ℤ)`)
* `CondG p M γ` : `a ≡ d ≡ 1 (mod pM)`, `p²M ∣ b`, `M ∣ c` -- this is `β⁻¹ Γ(pM) β`, the conjugate of `Γ(N)`
  (`exists_Gamma_conj`).
* `CondG1 p M γ` : `a ≡ d ≡ 1 (mod pM)`, `p ∣ b`, `M ∣ c` -- the conjugate of `Γ₁(N)`.
* `Gamma1_le_of_condG1`, `Gamma1_le_of_condG` : a subgroup of `SL(2, ℤ)` containing `T` and every `CondG1`
  (resp. `CondG`) matrix contains `Γ₁(M)`.  `Gamma1_eq_closure` : `Γ₁(M) = ⟨T, β⁻¹ Γ(N) β⟩` exactly.

## 2. Descent
* `exists_descent` : `f` a cusp form on any arithmetic `Γ`, invariant under `Γ(pM)` and under `τ ↦ τ + 1/p`
  ⟹ `τ ↦ f(τ/p)` is a cusp form `g` on `Γ₁(M)`.
* `exists_iotaCF_eq_of_translate`, `exists_iotaCF_eq_of_coeff`, `mainLemma_single_prime` :
  `f ∈ S_k(Γ₁(N))` with `a_n(f) = 0` unless `p ∣ n` (width-1 expansion) ⟹ `f = ι_p g`, `g ∈ S_k(Γ₁(N/p))`,
  `a_m(g) = a_{pm}(f)`.
-/

open UpperHalfPlane ModularForm Complex
open scoped Real MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.MainLemmaA

open CongruenceSubgroup ConjAct RamanujanPetersson.Level
open scoped Pointwise

/-! ## 1. Generation -/

section gen

/-- `β⁻¹ Γ(pM) β ∩ SL(2,ℤ)` with `β = diag(1/p, 1)`: `a ≡ d ≡ 1 (pM)`, `p²M ∣ b`, `M ∣ c`. -/
def CondG (p M : ℕ) (γ : SL(2, ℤ)) : Prop :=
  ((p * M : ℕ) : ℤ) ∣ γ 0 0 - 1 ∧ ((p * M : ℕ) : ℤ) ∣ γ 1 1 - 1 ∧
    ((p * (p * M) : ℕ) : ℤ) ∣ γ 0 1 ∧ (M : ℤ) ∣ γ 1 0

/-- `β⁻¹ Γ₁(pM) β ∩ SL(2,ℤ)`: `a ≡ d ≡ 1 (pM)`, `p ∣ b`, `M ∣ c`. -/
def CondG1 (p M : ℕ) (γ : SL(2, ℤ)) : Prop :=
  ((p * M : ℕ) : ℤ) ∣ γ 0 0 - 1 ∧ ((p * M : ℕ) : ℤ) ∣ γ 1 1 - 1 ∧ (p : ℤ) ∣ γ 0 1 ∧ (M : ℤ) ∣ γ 1 0

lemma det_eq (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

lemma dvd_sub_one_of_cast_eq_one {M : ℕ} {a : ℤ} (h : ((a : ℤ) : ZMod M) = 1) :
    (M : ℤ) ∣ a - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h, sub_self]

lemma cast_eq_one_of_dvd_sub_one {M : ℕ} {a : ℤ} (h : (M : ℤ) ∣ a - 1) :
    ((a : ℤ) : ZMod M) = 1 := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr h
  push_cast at this
  exact sub_eq_zero.mp this

lemma TzT_00 (γ : SL(2, ℤ)) (i j : ℤ) :
    (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 0 0 = γ 0 0 + i * γ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.vecMul, dotProduct]

lemma TzT_01 (γ : SL(2, ℤ)) (i j : ℤ) :
    (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 0 1 =
      j * (γ 0 0 + i * γ 1 0) + (γ 0 1 + i * γ 1 1) := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

lemma TzT_10 (γ : SL(2, ℤ)) (i j : ℤ) :
    (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 1 0 = γ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.vecMul, dotProduct]

lemma TzT_11 (γ : SL(2, ℤ)) (i j : ℤ) :
    (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 1 1 = γ 1 1 + j * γ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

/-- The lower unipotent `[[1, 0], [M, 1]]`. -/
def Lmat (M : ℕ) : SL(2, ℤ) :=
  ⟨!![1, 0; (M : ℤ), 1], by simp [Matrix.det_fin_two_of]⟩

lemma Lmat_mul_00 (M : ℕ) (γ : SL(2, ℤ)) : (Lmat M * γ) 0 0 = γ 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [Lmat, Matrix.mul_apply, Fin.sum_univ_two]

lemma Lmat_mul_01 (M : ℕ) (γ : SL(2, ℤ)) : (Lmat M * γ) 0 1 = γ 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [Lmat, Matrix.mul_apply, Fin.sum_univ_two]

lemma Lmat_mul_10 (M : ℕ) (γ : SL(2, ℤ)) : (Lmat M * γ) 1 0 = M * γ 0 0 + γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [Lmat, Matrix.mul_apply, Fin.sum_univ_two]

lemma Lmat_mul_11 (M : ℕ) (γ : SL(2, ℤ)) : (Lmat M * γ) 1 1 = M * γ 0 1 + γ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [Lmat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Euclid step: if `c = M κ` with `p ∤ κ`, then `T^i γ T^j` satisfies `CondG1` for suitable `i, j`. -/
lemma mem_of_not_dvd {p M : ℕ} (hp : p.Prime) (hM : M ≠ 0) {H : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ H) (hK : ∀ γ : SL(2, ℤ), CondG1 p M γ → γ ∈ H) (γ : SL(2, ℤ))
    {α δ κ : ℤ} (ha : γ 0 0 = 1 + M * α) (hd : γ 1 1 = 1 + M * δ) (hc : γ 1 0 = M * κ)
    (hκ : ¬ (p : ℤ) ∣ κ) : γ ∈ H := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) κ :=
    (Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hκ
  obtain ⟨i, hi⟩ : ∃ i : ℤ, i = -(α * v) := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = -(δ * v) := ⟨_, rfl⟩
  have h00 : (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 0 0 =
      1 + ((p * M : ℕ) : ℤ) * (α * u) := by
    rw [TzT_00, ha, hc, hi]
    push_cast
    linear_combination (-(M : ℤ) * α) * huv
  have h11 : (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 1 1 =
      1 + ((p * M : ℕ) : ℤ) * (δ * u) := by
    rw [TzT_11, hd, hc, hj]
    push_cast
    linear_combination (-(M : ℤ) * δ) * huv
  have h10 : (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 1 0 = M * κ := by
    rw [TzT_10, hc]
  have hdet := det_eq (ModularGroup.T ^ i * γ * ModularGroup.T ^ j)
  rw [h00, h11, h10] at hdet
  push_cast at hdet
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
  have hb : (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 0 1 * κ =
      p * (α * u + δ * u + p * M * (α * u) * (δ * u)) := by
    apply mul_left_cancel₀ hM'
    linear_combination -hdet
  have hpb : (p : ℤ) ∣ (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 0 1 := by
    have hdvd : (p : ℤ) ∣ (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) 0 1 * κ := ⟨_, hb⟩
    rcases hpZ.dvd_or_dvd hdvd with h | h
    · exact h
    · exact absurd h hκ
  have hmem : ModularGroup.T ^ i * γ * ModularGroup.T ^ j ∈ H :=
    hK _ ⟨⟨α * u, by rw [h00]; ring⟩, ⟨δ * u, by rw [h11]; ring⟩, hpb, ⟨κ, h10⟩⟩
  have hγ : γ = (ModularGroup.T ^ i)⁻¹ * (ModularGroup.T ^ i * γ * ModularGroup.T ^ j) *
      (ModularGroup.T ^ j)⁻¹ := by group
  rw [hγ]
  exact H.mul_mem (H.mul_mem (H.inv_mem (H.zpow_mem hT i)) hmem) (H.inv_mem (H.zpow_mem hT j))

/-- **Generation lemma (`Γ₁` form).** A subgroup of `SL(2, ℤ)` containing `T` and every matrix with
`a ≡ d ≡ 1 (pM)`, `p ∣ b`, `M ∣ c` contains `Γ₁(M)`. -/
theorem Gamma1_le_of_condG1 {p M : ℕ} (hp : p.Prime) [NeZero M] {H : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ H) (hK : ∀ γ : SL(2, ℤ), CondG1 p M γ → γ ∈ H) :
    Gamma1 M ≤ H := by
  intro γ hγ
  rw [Gamma1_mem] at hγ
  obtain ⟨h00, h11, h10⟩ := hγ
  obtain ⟨α, ha⟩ := dvd_sub_one_of_cast_eq_one h00
  obtain ⟨δ, hd⟩ := dvd_sub_one_of_cast_eq_one h11
  obtain ⟨κ, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hM : M ≠ 0 := NeZero.ne M
  by_cases hκ : (p : ℤ) ∣ κ
  · have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hLH : Lmat M ∈ H := hK _ ⟨⟨0, by simp [Lmat]⟩, ⟨0, by simp [Lmat]⟩, ⟨0, by simp [Lmat]⟩,
      ⟨1, by simp [Lmat]⟩⟩
    have hLγ : Lmat M * γ ∈ H := by
      refine mem_of_not_dvd hp hM hT hK (Lmat M * γ) (α := α) (δ := δ + γ 0 1)
        (κ := γ 0 0 + κ) ?_ ?_ ?_ ?_
      · rw [Lmat_mul_00]; linear_combination ha
      · rw [Lmat_mul_11]; linear_combination hd
      · rw [Lmat_mul_10]; linear_combination hc
      · intro hdiv
        have hpa : (p : ℤ) ∣ γ 0 0 := by
          have := dvd_sub hdiv hκ
          simpa using this
        have hpc : (p : ℤ) ∣ γ 1 0 := by
          rw [hc]
          exact dvd_mul_of_dvd_right hκ _
        have h1 : (p : ℤ) ∣ 1 := by
          rw [← det_eq γ]
          exact dvd_sub (dvd_mul_of_dvd_left hpa _) (dvd_mul_of_dvd_right hpc _)
        exact hpZ.not_isUnit (isUnit_of_dvd_one h1)
    have hγ : γ = (Lmat M)⁻¹ * (Lmat M * γ) := by group
    rw [hγ]
    exact H.mul_mem (H.inv_mem hLH) hLγ
  · exact mem_of_not_dvd hp hM hT hK γ (α := α) (δ := δ) (by linear_combination ha)
      (by linear_combination hd) hc hκ

/-- A subgroup containing `T` and `β⁻¹ Γ(pM) β` contains `β⁻¹ Γ₁(pM) β ∩ SL(2,ℤ)`:
`κ T^m` with `m = -b d` satisfies `CondG`. -/
theorem mem_of_condG1 {p M : ℕ} {H : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ H)
    (hK : ∀ γ : SL(2, ℤ), CondG p M γ → γ ∈ H) (γ : SL(2, ℤ)) (hγ : CondG1 p M γ) : γ ∈ H := by
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩, ⟨b0, hb0⟩, ⟨c0, hc0⟩⟩ := hγ
  have hdet := det_eq γ
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = -(γ 0 1 * γ 1 1) := ⟨_, rfl⟩
  push_cast at hX hY
  have key : CondG p M (ModularGroup.T ^ (0 : ℤ) * γ * ModularGroup.T ^ m) := by
    refine ⟨⟨X, ?_⟩, ⟨Y - γ 1 1 * (X + Y + p * M * X * Y), ?_⟩, ⟨-(b0 ^ 2 * c0), ?_⟩, ⟨c0, ?_⟩⟩
    · rw [TzT_00]
      push_cast
      linear_combination hX
    · rw [TzT_11, hm]
      push_cast
      linear_combination (-(γ 1 1) * (1 + p * M * Y)) * hX + (1 - γ 0 0 * γ 1 1) * hY +
        γ 1 1 * hdet
    · rw [TzT_01, hm]
      push_cast
      linear_combination (-(γ 0 1)) * hdet - ((γ 0 1 + p * b0) * γ 1 0) * hb0 -
        ((p : ℤ) ^ 2 * b0 ^ 2) * hc0
    · rw [TzT_10, hc0]
  have hmem := hK _ key
  have hγ : γ = (ModularGroup.T ^ (0 : ℤ))⁻¹ * (ModularGroup.T ^ (0 : ℤ) * γ * ModularGroup.T ^ m) *
      (ModularGroup.T ^ m)⁻¹ := by group
  rw [hγ]
  exact H.mul_mem (H.mul_mem (H.inv_mem (H.zpow_mem hT 0)) hmem) (H.inv_mem (H.zpow_mem hT m))

/-- **Generation lemma (`Γ(N)`-conjugate form).** A subgroup of `SL(2, ℤ)` containing `T` and the
conjugate `β⁻¹ Γ(pM) β` (`CondG`) contains `Γ₁(M)`. -/
theorem Gamma1_le_of_condG {p M : ℕ} (hp : p.Prime) [NeZero M] {H : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ H) (hK : ∀ γ : SL(2, ℤ), CondG p M γ → γ ∈ H) :
    Gamma1 M ≤ H :=
  Gamma1_le_of_condG1 hp hT (mem_of_condG1 hT hK)

lemma T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

lemma mem_Gamma1_of_condG {p M : ℕ} {γ : SL(2, ℤ)} (h : CondG p M γ) : γ ∈ Gamma1 M := by
  obtain ⟨h00, h11, -, h10⟩ := h
  have hMd : (M : ℤ) ∣ ((p * M : ℕ) : ℤ) := by
    push_cast
    exact dvd_mul_left _ _
  rw [Gamma1_mem]
  exact ⟨cast_eq_one_of_dvd_sub_one (hMd.trans h00), cast_eq_one_of_dvd_sub_one (hMd.trans h11),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h10⟩

/-- **`Γ₁(M)` is generated by `T` and the conjugate `β⁻¹ Γ(pM) β`** (`β = diag(1/p, 1)`). -/
theorem Gamma1_eq_closure {p M : ℕ} (hp : p.Prime) [NeZero M] :
    Gamma1 M = Subgroup.closure ({ModularGroup.T} ∪ {γ | CondG p M γ}) := by
  apply le_antisymm
  · exact Gamma1_le_of_condG hp (Subgroup.subset_closure (Or.inl rfl))
      (fun γ hγ => Subgroup.subset_closure (Or.inr hγ))
  · rw [Subgroup.closure_le]
    rintro γ (h | h)
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact T_mem_Gamma1 M
    · exact mem_Gamma1_of_condG h

end gen

/-! ## 2. The conjugation `β = diag(1/p, 1) = (dg p)⁻¹` -/

section conj

/-- `diag(d, 1)` over `ℚ`. -/
def dgQ (d : ℕ) [NeZero d] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(d : ℚ), 0; 0, 1]
    (by simpa [Matrix.det_fin_two_of] using NeZero.ne d)

lemma dgQ_val (d : ℕ) [NeZero d] :
    ((dgQ d : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(d : ℚ), 0; 0, 1] := rfl

lemma dgQ_map (d : ℕ) [NeZero d] : (dgQ d).map (Rat.castHom ℝ) = dg d := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, dgQ_val, dg_val]
  fin_cases i <;> fin_cases j <;> simp

lemma coe_dg_inv_smul (d : ℕ) [NeZero d] (τ : ℍ) : (((dg d)⁻¹ • τ : ℍ) : ℂ) = (τ : ℂ) / d := by
  have h := coe_dg_smul d ((dg d)⁻¹ • τ)
  rw [smul_inv_smul] at h
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [h, mul_div_cancel_left₀ _ hd]

lemma dg_inv_smul_vadd (d : ℕ) [NeZero d] (τ : ℍ) :
    (dg d)⁻¹ • ((1 : ℝ) +ᵥ τ) = ((d : ℝ)⁻¹) +ᵥ ((dg d)⁻¹ • τ) := by
  apply UpperHalfPlane.ext
  rw [coe_dg_inv_smul, coe_vadd, coe_vadd, coe_dg_inv_smul]
  push_cast
  rw [add_div, one_div]

variable {k : ℤ}

/-- `d^(k-1) • (F ∣[k] diag(1/d, 1))` is `τ ↦ F (τ / d)`. -/
lemma smul_slash_dg_inv_apply (d : ℕ) [NeZero d] (F : ℍ → ℂ) (τ : ℍ) :
    (((d : ℝ) ^ (k - 1)) • (F ∣[k] (dg d)⁻¹)) τ = F ((dg d)⁻¹ • τ) := by
  have h1 : (F ∣[k] (dg d)⁻¹) ∣[k] dg d = F := by
    rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  have h2 := congrFun h1 ((dg d)⁻¹ • τ)
  rw [dg_slash, smul_inv_smul] at h2
  rw [Pi.smul_apply, Complex.real_smul]
  push_cast
  exact h2

/-- `κ ∈ β⁻¹ Γ(pM) β` (`CondG`) comes from some `x ∈ Γ(pM)`: `dg p * x = κ * dg p`. -/
lemma exists_Gamma_conj {p M : ℕ} [NeZero p] (κ : SL(2, ℤ)) (hκ : CondG p M κ) :
    ∃ x ∈ CongruenceSubgroup.Gamma (p * M), dg p * Matrix.SpecialLinearGroup.mapGL ℝ x =
      Matrix.SpecialLinearGroup.mapGL ℝ κ * dg p := by
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩, ⟨t, ht⟩, ⟨c0, hc0⟩⟩ := hκ
  have hdet := det_eq κ
  obtain ⟨x, hx00, hx01, hx10, hx11⟩ : ∃ x : SL(2, ℤ), x 0 0 = κ 0 0 ∧
      x 0 1 = ((p * M : ℕ) : ℤ) * t ∧ x 1 0 = (p : ℤ) * κ 1 0 ∧ x 1 1 = κ 1 1 := by
    refine ⟨⟨!![κ 0 0, ((p * M : ℕ) : ℤ) * t; (p : ℤ) * κ 1 0, κ 1 1], ?_⟩, rfl, rfl, rfl, rfl⟩
    rw [Matrix.det_fin_two_of]
    rw [ht] at hdet
    push_cast at hdet ⊢
    linear_combination hdet
  refine ⟨x, ?_, ?_⟩
  · rw [Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hx00]
      exact_mod_cast cast_eq_one_of_dvd_sub_one ⟨X, hX⟩
    · rw [hx01]
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨t, rfl⟩
    · rw [hx10]
      have : ((p : ℤ) * κ 1 0) = ((p * M : ℕ) : ℤ) * c0 := by
        rw [hc0]
        push_cast
        ring
      rw [this]
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨c0, rfl⟩
    · rw [hx11]
      exact_mod_cast cast_eq_one_of_dvd_sub_one ⟨Y, hY⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, dg_val, Matrix.mul_apply,
        Fin.sum_univ_two, hx00, hx01, hx10, hx11, ht]
    all_goals ring

end conj

/-! ## 3. Descent -/

section descent

variable {k : ℤ}

/-- The weight-`k` stabilizer of a function in `SL(2, ℤ)`. -/
def stab (k : ℤ) (φ : ℍ → ℂ) : Subgroup SL(2, ℤ) where
  carrier := {γ | φ ∣[k] γ = φ}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, SlashAction.slash_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [SlashAction.slash_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    calc φ ∣[k] a⁻¹ = (φ ∣[k] a) ∣[k] a⁻¹ := by rw [ha]
      _ = φ := by rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

lemma mem_stab {φ : ℍ → ℂ} {γ : SL(2, ℤ)} : γ ∈ stab k φ ↔ φ ∣[k] γ = φ := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
lemma denom_T (τ : ℍ) : denom ModularGroup.T τ = 1 := by
  simp [ModularGroup.denom_apply, ModularGroup.T]

/-- Invariance of `F` under `τ ↦ τ + 1/d` gives `T`-invariance of `τ ↦ F(τ/d)`. -/
lemma T_mem_stab (d : ℕ) [NeZero d] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, F (((d : ℝ)⁻¹) +ᵥ τ) = F τ) :
    ModularGroup.T ∈ stab k (((d : ℝ) ^ (k - 1)) • (F ∣[k] (dg d)⁻¹)) := by
  rw [mem_stab]
  ext τ
  have key : (((d : ℝ) ^ (k - 1)) • (F ∣[k] (dg d)⁻¹)) ((1 : ℝ) +ᵥ τ) =
      (((d : ℝ) ^ (k - 1)) • (F ∣[k] (dg d)⁻¹)) τ := by
    rw [smul_slash_dg_inv_apply, smul_slash_dg_inv_apply, dg_inv_smul_vadd, hF]
  rw [SL_slash_apply, modular_T_smul, key, denom_T]
  simp

/-- `Γ(pM)`-invariance of `F` gives invariance of `τ ↦ F(τ/p)` under `β⁻¹ Γ(pM) β` (`CondG`). -/
lemma condG_mem_stab {p M : ℕ} [NeZero p] (F : ℍ → ℂ)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (p * M), F ∣[k] γ = F) (κ : SL(2, ℤ)) (hκ : CondG p M κ) :
    κ ∈ stab k (((p : ℝ) ^ (k - 1)) • (F ∣[k] (dg p)⁻¹)) := by
  obtain ⟨x, hx, hmat⟩ := exists_Gamma_conj κ hκ
  rw [mem_stab, SL_smul_slash]
  congr 1
  have hrel : (dg p)⁻¹ * Matrix.SpecialLinearGroup.mapGL ℝ κ =
      Matrix.SpecialLinearGroup.mapGL ℝ x * (dg p)⁻¹ := by
    calc (dg p)⁻¹ * Matrix.SpecialLinearGroup.mapGL ℝ κ =
        (dg p)⁻¹ * (Matrix.SpecialLinearGroup.mapGL ℝ κ * dg p) * (dg p)⁻¹ := by group
      _ = (dg p)⁻¹ * (dg p * Matrix.SpecialLinearGroup.mapGL ℝ x) * (dg p)⁻¹ := by rw [hmat]
      _ = Matrix.SpecialLinearGroup.mapGL ℝ x * (dg p)⁻¹ := by group
  have e1 : (F ∣[k] (dg p)⁻¹) ∣[k] κ =
      (F ∣[k] (dg p)⁻¹) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ κ) := rfl
  have e2 : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ x) = F := hinv x hx
  rw [e1, ← SlashAction.slash_mul, hrel, SlashAction.slash_mul, e2]

/-- **Single-prime descent (core).** Let `f` be a cusp form of weight `k` on an arithmetic group `Γ`,
invariant under `Γ(pM)` and under `τ ↦ τ + 1/p`. Then `τ ↦ f(τ/p)` is a cusp form on `Γ₁(M)`. -/
theorem exists_descent {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (p M : ℕ) [NeZero p]
    [NeZero M] (hp : p.Prime) (f : CuspForm Γ k)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (p * M), ⇑f ∣[k] γ = ⇑f)
    (htr : ∀ τ : ℍ, f (((p : ℝ)⁻¹) +ᵥ τ) = f τ) :
    ∃ g : CuspForm (G1 M) k, ∀ τ : ℍ, g τ = f ((dg p)⁻¹ • τ) := by
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : CuspForm (toConjAct ((dg p)⁻¹)⁻¹ • Γ) k,
      ⇑F₀ = ((p : ℝ) ^ (k - 1)) • (⇑f ∣[k] (dg p)⁻¹) :=
    ⟨((p : ℝ) ^ (k - 1)) • CuspForm.translate f (dg p)⁻¹, rfl⟩
  have hstab : Gamma1 M ≤ stab k ⇑F₀ := by
    rw [hF₀]
    exact Gamma1_le_of_condG hp (T_mem_stab p ⇑f htr) (condG_mem_stab ⇑f hinv)
  have : (toConjAct ((dg p)⁻¹)⁻¹ • Γ).IsArithmetic := by
    rw [inv_inv, ← dgQ_map]
    exact Subgroup.IsArithmetic.conj Γ (dgQ p)
  refine ⟨{ toFun := ⇑F₀
            slash_action_eq' := ?_
            holo' := CuspFormClass.holo F₀
            zero_at_cusps' := ?_ }, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_stab.mp (hstab hx)
  · intro c hc
    exact CuspFormClass.zero_at_cusps F₀
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (G1 M)).mp hc))
  · intro τ
    show F₀ τ = _
    rw [hF₀]
    exact smul_slash_dg_inv_apply p ⇑f τ

lemma Gamma_le_Gamma1' (N : ℕ) : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

/-- Coefficients supported on `p ∣ n` (width 1) give invariance under `τ ↦ τ + 1/p`. -/
theorem translate_eq_of_coeff {N p : ℕ} [NeZero N] [NeZero p] (f : CuspForm (G1 N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → (qExpansion 1 f).coeff n = 0) (τ : ℍ) :
    f (((p : ℝ)⁻¹) +ᵥ τ) = f τ := by
  have h1 := ModularForm.hasSum_qExpansion (f := f) one_pos (one_mem_strictPeriods_G1 N)
    (((p : ℝ)⁻¹) +ᵥ τ)
  have h2 := ModularForm.hasSum_qExpansion (f := f) one_pos (one_mem_strictPeriods_G1 N) τ
  refine h1.unique ?_
  convert h2 using 1
  funext n
  by_cases hn : p ∣ n
  · obtain ⟨m, rfl⟩ := hn
    congr 1
    rw [Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    rw [coe_vadd]
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    have hinv : (p : ℂ) * (p : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hp0
    push_cast
    linear_combination ((m : ℂ) * (2 * (π : ℂ) * Complex.I)) * hinv
  · rw [hf n hn, zero_mul, zero_mul]

/-- **Single-prime descent, `ι_p` form.** If `f ∈ S_k(Γ₁(pM))` is invariant under `τ ↦ τ + 1/p`,
then `f = ι_p g` for some `g ∈ S_k(Γ₁(M))`. -/
theorem exists_iotaCF_eq_of_translate {p M : ℕ} [NeZero p] [NeZero M] (hp : p.Prime)
    (f : CuspForm (G1 (p * M)) k) (htr : ∀ τ : ℍ, f (((p : ℝ)⁻¹) +ᵥ τ) = f τ) :
    ∃ g : CuspForm (G1 M) k, iotaCF p (dvd_refl (p * M)) k g = f := by
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (p * M), ⇑f ∣[k] γ = ⇑f := fun γ hγ =>
    SlashInvariantFormClass.slash_action_eq f _ ⟨γ, Gamma_le_Gamma1' _ hγ, rfl⟩
  obtain ⟨g, hg⟩ := exists_descent p M hp f hinv htr
  refine ⟨g, CuspForm.ext fun τ => ?_⟩
  rw [iotaCF_apply, hg, inv_smul_smul]

/-- **Single-prime descent, coefficient form.** If `f ∈ S_k(Γ₁(pM))` has `a_n(f) = 0` whenever
`p ∤ n`, then `f = ι_p g` with `g ∈ S_k(Γ₁(M))` and `a_m(g) = a_{pm}(f)`. -/
theorem exists_iotaCF_eq_of_coeff {p M : ℕ} [NeZero p] [NeZero M] (hp : p.Prime)
    (f : CuspForm (G1 (p * M)) k) (hf : ∀ n : ℕ, ¬ p ∣ n → (qExpansion 1 f).coeff n = 0) :
    ∃ g : CuspForm (G1 M) k, iotaCF p (dvd_refl (p * M)) k g = f ∧
      ∀ m : ℕ, (qExpansion 1 g).coeff m = (qExpansion 1 f).coeff (p * m) := by
  obtain ⟨g, hg⟩ := exists_iotaCF_eq_of_translate hp f (translate_eq_of_coeff f hf)
  refine ⟨g, hg, fun m => ?_⟩
  rw [← hg, coeff_iotaCF_mul]

lemma mul_div_dvd_self {p M : ℕ} (hpM : p ∣ M) : p * (M / p) ∣ M := by
  rw [Nat.mul_div_cancel' hpM]

/-- **Main Lemma, single prime (DS §5.7).** `M ≠ 0`, `p` prime, `p ∣ M`, `f ∈ S_k(Γ₁(M))` with
`a_n(f) = 0` unless `p ∣ n` (width-1 expansion). Then `f = ι_p g` for some `g ∈ S_k(Γ₁(M/p))`,
and `a_m(g) = a_{pm}(f)`. -/
theorem mainLemma_single_prime {M p : ℕ} [NeZero M] [NeZero p] (hp : p.Prime) (hpM : p ∣ M)
    (f : CuspForm (G1 M) k) (hf : ∀ n : ℕ, ¬ p ∣ n → (qExpansion 1 f).coeff n = 0) :
    ∃ g : CuspForm (G1 (M / p)) k, iotaCF p (mul_div_dvd_self hpM) k g = f ∧
      ∀ m : ℕ, (qExpansion 1 g).coeff m = (qExpansion 1 f).coeff (p * m) := by
  have : NeZero (M / p) := ⟨fun h => NeZero.ne M (by rw [← Nat.mul_div_cancel' hpM, h, mul_zero])⟩
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (p * (M / p)), ⇑f ∣[k] γ = ⇑f := by
    intro γ hγ
    rw [Nat.mul_div_cancel' hpM] at hγ
    exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, Gamma_le_Gamma1' _ hγ, rfl⟩
  obtain ⟨g, hg⟩ := exists_descent p (M / p) hp f hinv (translate_eq_of_coeff f hf)
  have hι : iotaCF p (mul_div_dvd_self hpM) k g = f := by
    refine CuspForm.ext fun τ => ?_
    rw [iotaCF_apply, hg, inv_smul_smul]
  refine ⟨g, hι, fun m => ?_⟩
  rw [← hι, coeff_iotaCF_mul]

end descent

end RamanujanPetersson.MainLemmaA

end


