-- Prove2me | Definitions.Def_RPLib_S3_KernelB2
-- name    : RPLib_S3_KernelB2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:00:57.618201+00:00
-- url     : https://prove2.me/theorems/0926679d-25b0-4f6f-ad42-666a48035673
-- title:
--   The Eichler-Selberg trace formula, kernel part B2: Hermite normal form coset representatives
-- statement:
--   For $n \ge 1$ coprime to $M$ and a unit $\delta'$ mod $M$, explicit representatives $\sigma_D \begin{pmatrix} A & B \\ 0 & D \end{pmatrix}$ ($AD = n$, $0 \le B < D$) of $\Gamma_1(M) \backslash \Delta$: the map $(\gamma, i) \mapsto \alpha_i \gamma$ is a bijection $\Gamma_1(M) \times I \to \Delta$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Proposition 5.2.1 and Section 5.3

import Mathlib
import Definitions.Def_RPLib_S3_KernelB1

/-!
# S3-Kernel, part B2: Hermite normal form representatives of `Δ^{(δ')}_n(M) / Γ₁(M)`

For `0 < n` coprime to `M` and a unit `δ'`:
* `HNFIdx n = Σ A ∣ n, Fin (n / A)` (pairs `(A, B)`, `D = n / A`, `0 ≤ B < D`);
* `sigmaD δ' D ∈ Γ₀(M)` with lower-right entry `≡ δ' D⁻¹ (mod M)`;
* `betaHNF n δ' (A, B) = σ_D [[A, B], [0, D]]` and `alphaHNF = adj betaHNF ∈ Δ^{(δ')}_n(M)`;
* `repMap_HNF_bijective`: `(γ, i) ↦ alphaHNF i * γ` is a bijection `Γ₁(M) × HNFIdx n → Δ^{(δ')}_n(M)`.
-/

open CongruenceSubgroup
open scoped MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Kernel

open RamanujanPetersson.Diamond

/-! ### Adjugates -/

lemma adjM_eq (g : Matrix (Fin 2) (Fin 2) ℤ) : adjM g = g.adjugate := by
  rw [Matrix.adjugate_fin_two]; rfl

lemma adjM_adjM (g : Matrix (Fin 2) (Fin 2) ℤ) : adjM (adjM g) = g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [adjM]

lemma adjM_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) : adjM (g * h) = adjM h * adjM g := by
  rw [adjM_eq, adjM_eq, adjM_eq, Matrix.adjugate_mul_distrib]

lemma adjM_SL (γ : SL(2, ℤ)) :
    adjM (γ : Matrix (Fin 2) (Fin 2) ℤ) = ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [adjM_eq, Matrix.SpecialLinearGroup.coe_inv]

lemma adjM_10 (g : Matrix (Fin 2) (Fin 2) ℤ) : adjM g 1 0 = -g 1 0 := by simp [adjM]

lemma adjM_00 (g : Matrix (Fin 2) (Fin 2) ℤ) : adjM g 0 0 = g 1 1 := by simp [adjM]

/-! ### Upper triangular matrices -/

/-- `[[A, B], [0, D]]` over `ℤ`. -/
def Tmat (A B D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![A, B; 0, D]

lemma Tmat_00 (A B D : ℤ) : Tmat A B D 0 0 = A := by simp [Tmat]
lemma Tmat_01 (A B D : ℤ) : Tmat A B D 0 1 = B := by simp [Tmat]
lemma Tmat_10 (A B D : ℤ) : Tmat A B D 1 0 = 0 := by simp [Tmat]
lemma Tmat_11 (A B D : ℤ) : Tmat A B D 1 1 = D := by simp [Tmat]

lemma mul_Tmat_00 (σ : Matrix (Fin 2) (Fin 2) ℤ) (A B D : ℤ) : (σ * Tmat A B D) 0 0 = σ 0 0 * A := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Tmat]
lemma mul_Tmat_01 (σ : Matrix (Fin 2) (Fin 2) ℤ) (A B D : ℤ) :
    (σ * Tmat A B D) 0 1 = σ 0 0 * B + σ 0 1 * D := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Tmat]
lemma mul_Tmat_10 (σ : Matrix (Fin 2) (Fin 2) ℤ) (A B D : ℤ) : (σ * Tmat A B D) 1 0 = σ 1 0 * A := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Tmat]
lemma mul_Tmat_11 (σ : Matrix (Fin 2) (Fin 2) ℤ) (A B D : ℤ) :
    (σ * Tmat A B D) 1 1 = σ 1 0 * B + σ 1 1 * D := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Tmat]

lemma det_Tmat (A B D : ℤ) : (Tmat A B D).det = A * D := by
  rw [Tmat, Matrix.det_fin_two_of]; ring

/-- **Uniqueness of the Hermite normal form.** -/
lemma hnf_unique {S : SL(2, ℤ)} {A B D A' B' D' : ℤ} (hA : 0 < A) (hA' : 0 < A') (hD' : 0 < D')
    (hB : 0 ≤ B) (hBD : B < D) (hB' : 0 ≤ B') (hBD' : B' < D')
    (h : (S : Matrix (Fin 2) (Fin 2) ℤ) * Tmat A' B' D' = Tmat A B D) :
    S = 1 ∧ A = A' ∧ B = B' ∧ D = D' := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  rw [mul_Tmat_00, Tmat_00] at h00
  rw [mul_Tmat_01, Tmat_01] at h01
  rw [mul_Tmat_10, Tmat_10] at h10
  rw [mul_Tmat_11, Tmat_11] at h11
  have hdet : S 0 0 * S 1 1 - S 0 1 * S 1 0 = 1 := by
    have := S.2
    rwa [Matrix.det_fin_two] at this
  have hc : S 1 0 = 0 := by
    rcases mul_eq_zero.1 h10 with h | h
    · exact h
    · omega
  rw [hc, mul_zero, sub_zero] at hdet
  rw [hc, zero_mul, zero_add] at h11
  have ha : 0 < S 0 0 := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have ha1 : S 0 0 = 1 := Int.eq_one_of_mul_eq_one_right ha.le hdet
  have hd1 : S 1 1 = 1 := by rw [ha1, one_mul] at hdet; exact hdet
  rw [ha1, one_mul] at h00 h01
  rw [hd1, one_mul] at h11
  subst h11
  have hb : S 0 1 = 0 := by
    rcases lt_trichotomy (S 0 1) 0 with hlt | heq | hgt
    · exfalso; nlinarith
    · exact heq
    · exfalso; nlinarith
  rw [hb, zero_mul, add_zero] at h01
  refine ⟨?_, h00.symm, h01.symm, rfl⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha1, hb, hc, hd1]

/-! ### The representatives -/

/-- Index set `{(A, B) : A ∣ n, 0 ≤ B < n / A}`. -/
abbrev HNFIdx (n : ℕ) : Type := Σ A : n.divisors, Fin (n / A.1)

/-- `D mod M` as a unit (`1` if `D` is not coprime to `M`). -/
def unitOf (M D : ℕ) : (ZMod M)ˣ := if h : D.Coprime M then ZMod.unitOfCoprime D h else 1

lemma coe_unitOf {M D : ℕ} (h : D.Coprime M) : ((unitOf M D : (ZMod M)ˣ) : ZMod M) = D := by
  rw [unitOf, dif_pos h, ZMod.coe_unitOfCoprime]

variable {M : ℕ} [NeZero M]

/-- `σ_D ∈ Γ₀(M)` with lower-right entry `≡ δ' D⁻¹`. -/
def sigmaD (δ' : (ZMod M)ˣ) (D : ℕ) : SL(2, ℤ) := ((lift0 (δ' * (unitOf M D)⁻¹) : Gamma0 M) : SL(2, ℤ))

lemma sigmaD_mem (δ' : (ZMod M)ˣ) (D : ℕ) : sigmaD δ' D ∈ Gamma0 M := (lift0 _).2

lemma sigmaD_10 (δ' : (ZMod M)ˣ) (D : ℕ) : ((sigmaD δ' D 1 0 : ℤ) : ZMod M) = 0 :=
  Gamma0_mem.1 (sigmaD_mem δ' D)

lemma sigmaD_11 (δ' : (ZMod M)ˣ) (D : ℕ) :
    ((sigmaD δ' D 1 1 : ℤ) : ZMod M) = ((δ' * (unitOf M D)⁻¹ : (ZMod M)ˣ) : ZMod M) := by
  show ((((lift0 (δ' * (unitOf M D)⁻¹) : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = _
  rw [← coe_unitMap, unitMap_lift0]

/-- `σ_D [[A, B], [0, D]]`. -/
def betaHNF (n : ℕ) (δ' : (ZMod M)ˣ) (i : HNFIdx n) : Matrix (Fin 2) (Fin 2) ℤ :=
  ((sigmaD δ' (n / i.1.1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
    Tmat (i.1.1 : ℤ) (i.2.1 : ℤ) ((n / i.1.1 : ℕ) : ℤ)

/-- The representative `adj (σ_D [[A, B], [0, D]]) ∈ Δ^{(δ')}_n(M)`. -/
def alphaHNF (n : ℕ) (δ' : (ZMod M)ˣ) (i : HNFIdx n) : Matrix (Fin 2) (Fin 2) ℤ := adjM (betaHNF n δ' i)

lemma adjM_alphaHNF (n : ℕ) (δ' : (ZMod M)ˣ) (i : HNFIdx n) : adjM (alphaHNF n δ' i) = betaHNF n δ' i :=
  adjM_adjM _

lemma idx_mul (n : ℕ) (i : HNFIdx n) : (i.1.1 : ℤ) * ((n / i.1.1 : ℕ) : ℤ) = n := by
  have h := Nat.dvd_of_mem_divisors i.1.2
  exact_mod_cast Nat.mul_div_cancel' h

omit [NeZero M] in
lemma idx_coprime {n : ℕ} (hnM : n.Coprime M) (i : HNFIdx n) : (n / i.1.1).Coprime M :=
  Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors i.1.2)) hnM

lemma det_betaHNF (n : ℕ) (δ' : (ZMod M)ˣ) (i : HNFIdx n) : (betaHNF n δ' i).det = n := by
  rw [betaHNF, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, det_Tmat, idx_mul]

theorem alphaHNF_mem {n : ℕ} (hnM : n.Coprime M) (δ' : (ZMod M)ˣ) (i : HNFIdx n) :
    alphaHNF n δ' i ∈ DeltaSet M n (δ' : ZMod M) := by
  refine mem_DeltaSet.2 ⟨?_, ?_, ?_⟩
  · rw [alphaHNF, det_adjM, det_betaHNF]
  · rw [alphaHNF, adjM_10, betaHNF, mul_Tmat_10]
    push_cast
    rw [sigmaD_10]
    ring
  · rw [alphaHNF, adjM_00, betaHNF, mul_Tmat_11]
    have hu := coe_unitOf (idx_coprime hnM i)
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [sigmaD_10, sigmaD_11, ← hu]
    simp

/-! ### Bijectivity -/

lemma HNFIdx_ext {n : ℕ} {i j : HNFIdx n} (h1 : i.1.1 = j.1.1) (h2 : i.2.1 = j.2.1) : i = j := by
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := i
  obtain ⟨⟨A', hA'⟩, ⟨B', hB'⟩⟩ := j
  simp only at h1 h2
  subst h1 h2
  rfl

theorem repMap_HNF_injective {n : ℕ} (_hn : 0 < n) (hnM : n.Coprime M) (δ' : (ZMod M)ˣ) :
    Function.Injective (repMap (alphaHNF n δ') (alphaHNF_mem hnM δ')) := by
  rintro ⟨γ, i⟩ ⟨γ', j⟩ hij
  have h := congrArg Subtype.val hij
  change alphaHNF n δ' i * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    alphaHNF n δ' j * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) at h
  -- apply the adjugate: `γ⁻¹ β_i = γ'⁻¹ β_j`
  have h' := congrArg adjM h
  rw [adjM_mul, adjM_mul, adjM_alphaHNF, adjM_alphaHNF, adjM_SL, adjM_SL] at h'
  set σi := sigmaD δ' (n / i.1.1)
  set σj := sigmaD δ' (n / j.1.1)
  set Ti := Tmat (i.1.1 : ℤ) (i.2.1 : ℤ) ((n / i.1.1 : ℕ) : ℤ)
  set Tj := Tmat (j.1.1 : ℤ) (j.2.1 : ℤ) ((n / j.1.1 : ℕ) : ℤ)
  have hbi : betaHNF n δ' i = (σi : Matrix (Fin 2) (Fin 2) ℤ) * Ti := rfl
  have hbj : betaHNF n δ' j = (σj : Matrix (Fin 2) (Fin 2) ℤ) * Tj := rfl
  rw [hbi, hbj] at h'
  set g1 : SL(2, ℤ) := (γ : SL(2, ℤ))
  set g2 : SL(2, ℤ) := (γ' : SL(2, ℤ))
  have key : ((σi⁻¹ * g1 * g2⁻¹ * σj : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tj = Ti := by
    have e1 : ((σi⁻¹ * g1 * g2⁻¹ * σj : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tj =
        ((σi⁻¹ * g1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (((g2⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * ((σj : Matrix (Fin 2) (Fin 2) ℤ) * Tj)) := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
    rw [e1, ← h', ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul]
    have e2 : σi⁻¹ * g1 * g1⁻¹ * σi = 1 := by group
    rw [e2, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  have hAi : (0 : ℤ) < i.1.1 := by exact_mod_cast Nat.pos_of_mem_divisors i.1.2
  have hAj : (0 : ℤ) < j.1.1 := by exact_mod_cast Nat.pos_of_mem_divisors j.1.2
  have hDj : (0 : ℤ) < ((n / j.1.1 : ℕ) : ℤ) := by
    have := Nat.div_pos (Nat.divisor_le j.1.2) (Nat.pos_of_mem_divisors j.1.2)
    exact_mod_cast this
  have hBi : ((i.2.1 : ℕ) : ℤ) < ((n / i.1.1 : ℕ) : ℤ) := by exact_mod_cast i.2.2
  have hBj : ((j.2.1 : ℕ) : ℤ) < ((n / j.1.1 : ℕ) : ℤ) := by exact_mod_cast j.2.2
  obtain ⟨hS, hA, hB, -⟩ := hnf_unique hAi hAj hDj (Int.natCast_nonneg _) hBi (Int.natCast_nonneg _) hBj key
  have hA' : i.1.1 = j.1.1 := by exact_mod_cast hA
  have hB' : i.2.1 = j.2.1 := by exact_mod_cast hB
  have hij' : i = j := HNFIdx_ext hA' hB'
  subst hij'
  have hg : g1 = g2 := by
    have e : σi⁻¹ * g1 * g2⁻¹ * σi = 1 := hS
    calc g1 = σi * (σi⁻¹ * g1 * g2⁻¹ * σi) * σi⁻¹ * g2 := by group
      _ = g2 := by rw [e]; group
  exact Prod.ext (Subtype.ext hg) rfl

/-- **Existence of the Hermite normal form**: every `g ∈ Δ^{(δ')}_n(M)` is `alphaHNF i * γ`. -/
theorem repMap_HNF_surjective {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ' : (ZMod M)ˣ) :
    Function.Surjective (repMap (alphaHNF n δ') (alphaHNF_mem hnM δ')) := by
  rintro ⟨g, hg⟩
  obtain ⟨hdet, hc, ha⟩ := mem_DeltaSet.1 hg
  have hdeth : g 0 0 * g 1 1 - g 0 1 * g 1 0 = n := by rw [← hdet, Matrix.det_fin_two]
  have hac : g 1 1 ≠ 0 ∨ -g 1 0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h10 : g 1 0 = 0 := by linarith [hcon.2]
    rw [hcon.1, h10] at hdeth
    have : (n : ℤ) = 0 := by rw [← hdeth]; ring
    omega
  have hAgpos : 0 < Int.gcd (g 1 1) (-g 1 0) := Int.gcd_pos_iff.2 hac
  obtain ⟨s, hs⟩ := Int.gcd_dvd_left (g 1 1) (-g 1 0)
  obtain ⟨ρ, hρ⟩ := Int.gcd_dvd_right (g 1 1) (-g 1 0)
  have hbez := Int.gcd_eq_gcd_ab (g 1 1) (-g 1 0)
  generalize Int.gcdA (g 1 1) (-g 1 0) = u at hbez
  generalize Int.gcdB (g 1 1) (-g 1 0) = v at hbez
  generalize Int.gcd (g 1 1) (-g 1 0) = Ag at hAgpos hs hρ hbez
  have hAgz : (0 : ℤ) < Ag := by exact_mod_cast hAgpos
  obtain ⟨D, hDdef⟩ : ∃ D : ℤ, D = ρ * g 0 1 + s * g 0 0 := ⟨_, rfl⟩
  have hAgD : (Ag : ℤ) * D = n := by
    rw [← hdeth, hDdef]; linear_combination (-g 0 0) * hs + (-g 0 1) * hρ
  have hDpos : 0 < D := by
    have : (0 : ℤ) < (Ag : ℤ) * D := by rw [hAgD]; exact_mod_cast hn
    by_contra hneg
    push Not at hneg
    nlinarith
  have hAgn : Ag ∣ n := by
    have : (Ag : ℤ) ∣ (n : ℤ) := ⟨D, hAgD.symm⟩
    exact_mod_cast this
  have hDn : ((n / Ag : ℕ) : ℤ) = D := by
    have h1 : (Ag : ℤ) * ((n / Ag : ℕ) : ℤ) = n := by exact_mod_cast Nat.mul_div_cancel' hAgn
    exact mul_left_cancel₀ hAgz.ne' (h1.trans hAgD.symm)
  have hus : u * s + v * ρ = 1 := by
    have h3 : (Ag : ℤ) * (u * s + v * ρ) = (Ag : ℤ) * 1 := by
      linear_combination (-u) * hs + (-v) * hρ - hbez
    exact mul_left_cancel₀ hAgz.ne' h3
  obtain ⟨E, hEdef⟩ : ∃ E : ℤ, E = -u * g 0 1 + v * g 0 0 := ⟨_, rfl⟩
  have hEq : E % D + D * (E / D) = E := Int.emod_add_mul_ediv E D
  have hB0 : 0 ≤ E % D := Int.emod_nonneg E hDpos.ne'
  have hBD : E % D < D := Int.emod_lt_of_pos E hDpos
  generalize E / D = q at hEq
  generalize E % D = B at hEq hB0 hBD
  have hτdet : (!![u + q * ρ, v - q * s; -ρ, s] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hus
  obtain ⟨τ, hτ⟩ : ∃ τ : SL(2, ℤ),
      (τ : Matrix (Fin 2) (Fin 2) ℤ) = !![u + q * ρ, v - q * s; -ρ, s] := ⟨⟨_, hτdet⟩, rfl⟩
  have hτh : (τ : Matrix (Fin 2) (Fin 2) ℤ) * adjM g = Tmat (Ag : ℤ) B D := by
    have hadj : adjM g = !![g 1 1, -g 0 1; -g 1 0, g 0 0] := rfl
    have e00 : (u + q * ρ) * g 1 1 + (v - q * s) * -g 1 0 = Ag := by
      linear_combination (u + q * ρ) * hs + (v - q * s) * hρ + (Ag : ℤ) * hus
    have e01 : (u + q * ρ) * -g 0 1 + (v - q * s) * g 0 0 = B := by
      linear_combination (-1 : ℤ) * hEdef + q * hDdef - hEq
    have e10 : -ρ * g 1 1 + s * -g 1 0 = 0 := by
      linear_combination (-ρ) * hs + s * hρ
    have e11 : -ρ * -g 0 1 + s * g 0 0 = D := by
      linear_combination (-1 : ℤ) * hDdef
    rw [hadj, hτ, Matrix.mul_fin_two, e00, e01, e10, e11]
    rfl
  have hAgcop : Ag.Coprime M := Nat.Coprime.coprime_dvd_left hAgn hnM
  have hρ0 : ((ρ : ℤ) : ZMod M) = 0 := by
    have h1 : ((Ag : ℤ) : ZMod M) * (ρ : ZMod M) = 0 := by
      rw [← Int.cast_mul, ← hρ, Int.cast_neg, hc, neg_zero]
    have hu : IsUnit ((Ag : ℤ) : ZMod M) := by
      rw [Int.cast_natCast, ← ZMod.coe_unitOfCoprime Ag hAgcop]
      exact Units.isUnit _
    exact hu.mul_right_eq_zero.1 h1
  have hAmem : Ag ∈ n.divisors := Nat.mem_divisors.2 ⟨hAgn, hn.ne'⟩
  have hBlt : B.toNat < n / Ag := by
    have : (B.toNat : ℤ) < ((n / Ag : ℕ) : ℤ) := by rw [Int.toNat_of_nonneg hB0, hDn]; exact hBD
    exact_mod_cast this
  let i : HNFIdx n := ⟨⟨Ag, hAmem⟩, ⟨B.toNat, hBlt⟩⟩
  have hbeta : betaHNF n δ' i =
      ((sigmaD δ' (n / Ag) * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * adjM g := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hτh]
    show ((sigmaD δ' (n / Ag) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      Tmat (Ag : ℤ) ((B.toNat : ℕ) : ℤ) ((n / Ag : ℕ) : ℤ) = _
    rw [Int.toNat_of_nonneg hB0, hDn]
  have hD_unit : ((unitOf M (n / Ag) : (ZMod M)ˣ) : ZMod M) = ((D : ℤ) : ZMod M) := by
    rw [coe_unitOf (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hAgn) hnM), ← hDn,
      Int.cast_natCast]
  have hsδ : ((s : ℤ) : ZMod M) * (δ' : ZMod M) = ((D : ℤ) : ZMod M) := by
    rw [hDdef]; push_cast; rw [hρ0, ha]; ring
  have h0 : sigmaD δ' (n / Ag) * τ ∈ Gamma0 M := by
    rw [Gamma0_mem, Matrix.SpecialLinearGroup.coe_mul, hτ, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [sigmaD_10, hρ0]
    ring
  have h11 : ((((sigmaD δ' (n / Ag) * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hτ, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [sigmaD_10, sigmaD_11, Units.val_mul, zero_mul, zero_add]
    have e : (δ' : ZMod M) * (((unitOf M (n / Ag))⁻¹ : (ZMod M)ˣ) : ZMod M) * ((s : ℤ) : ZMod M) =
        (((unitOf M (n / Ag))⁻¹ : (ZMod M)ˣ) : ZMod M) * (((s : ℤ) : ZMod M) * (δ' : ZMod M)) := by
      ring
    rw [e, hsδ, ← hD_unit, Units.inv_mul]
  have hγ : sigmaD δ' (n / Ag) * τ ∈ Gamma1 M :=
    (mem_Gamma1_iff _).2 ⟨h0, Units.ext (by rw [coe_unitMap, Units.val_one]; exact h11)⟩
  refine ⟨(⟨sigmaD δ' (n / Ag) * τ, hγ⟩, i), ?_⟩
  apply Subtype.ext
  show alphaHNF n δ' i * ((sigmaD δ' (n / Ag) * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = g
  rw [alphaHNF, hbeta, adjM_mul, adjM_adjM, adjM_SL, Matrix.mul_assoc,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_one]

theorem repMap_HNF_bijective {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ' : (ZMod M)ˣ) :
    Function.Bijective (repMap (alphaHNF n δ') (alphaHNF_mem hnM δ')) :=
  ⟨repMap_HNF_injective hn hnM δ', repMap_HNF_surjective hn hnM δ'⟩

end RamanujanPetersson.Kernel


