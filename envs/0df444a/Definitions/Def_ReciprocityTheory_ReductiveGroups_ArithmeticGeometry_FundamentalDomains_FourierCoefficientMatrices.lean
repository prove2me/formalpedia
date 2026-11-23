-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:26.905315+00:00
-- url     : https://prove2.me/theorems/467b09c3-e589-47a4-8a47-febf6e685ecc
-- title:
--   Fourier Coefficient Matrices
-- statement:
--   Definitions and structural lemmas for Fourier Coefficient Matrices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientMatrices.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
section Fam
variable {ι : Type} [Fintype ι]
def kap (b : ι → Fin 2 → Fin 2 → ℂ) : ι → Fin 2 → Fin 2 → ℝ :=
  fun τ i k => if (i : ℕ) ≤ k then (b τ i k).re else (b τ k i).im
def th (y : ι → Fin 2 → Fin 2 → ℝ) : ι → Fin 2 → Fin 2 → ℂ :=
  fun τ i k => if i = k then (y τ i k : ℂ) else if (i : ℕ) < k then (y τ i k : ℂ) + I * y τ k i
    else (y τ k i : ℂ) - I * y τ i k
def kapL : (ι → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (ι → Fin 2 → Fin 2 → ℝ) where
  toFun := kap
  map_add' b c := by
    funext τ i k; simp only [kap, Pi.add_apply]; split_ifs <;> simp
  map_smul' s b := by
    funext τ i k; simp only [kap, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp
def thL : (ι → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (ι → Fin 2 → Fin 2 → ℂ) where
  toFun := th
  map_add' y z := by
    funext τ i k; simp only [th, Pi.add_apply]; split_ifs <;> push_cast <;> ring
  map_smul' s y := by
    funext τ i k; simp only [th, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Complex.real_smul]
    split_ifs <;> push_cast <;> ring
lemma th_herm (y : ι → Fin 2 → Fin 2 → ℝ) : IsHermFam (th y) := by
  intro τ i k
  fin_cases i <;> fin_cases k <;> simp [th] <;> ring
lemma kap_th (y : ι → Fin 2 → Fin 2 → ℝ) : kap (th y) = y := by
  funext τ i k
  fin_cases i <;> fin_cases k <;> simp [kap, th]
lemma th_kap {b : ι → Fin 2 → Fin 2 → ℂ} (hb : IsHermFam b) : th (kap b) = b := by
  funext τ i k
  have h00 := hb τ 0 0
  have h11 := hb τ 1 1
  have h01 := hb τ 0 1
  rw [Complex.ext_iff] at h00 h11 h01
  simp at h00 h11 h01
  fin_cases i <;> fin_cases k <;> apply Complex.ext <;> simp [th, kap] <;> linarith
def hermSub : Submodule ℝ (ι → Fin 2 → Fin 2 → ℂ) where
  carrier := {b | IsHermFam b}
  add_mem' {a b} ha hb τ i k := by
    simp only [Pi.add_apply, map_add]; rw [ha τ i k, hb τ i k]
  zero_mem' τ i k := by simp
  smul_mem' s b hb τ i k := by
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]; rw [hb τ i k]
lemma conj_herm {χ : ι → Fin 2 → Fin 2 → ℂ} (h : IsHermFam χ) :
    IsHermFam (fun τ i k => conj (χ τ i k)) := by
  intro τ i k
  show conj (χ τ k i) = conj (conj (χ τ i k))
  rw [h τ i k]
def pr (χ b : ι → Fin 2 → Fin 2 → ℂ) : ℝ := (∑ τ, ∑ i, ∑ k, χ τ i k * b τ i k).re
lemma pr_add_right (χ b c : ι → Fin 2 → Fin 2 → ℂ) : pr χ (b + c) = pr χ b + pr χ c := by
  simp only [pr, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]
lemma pr_add_left (χ ψ b : ι → Fin 2 → Fin 2 → ℂ) : pr (χ + ψ) b = pr χ b + pr ψ b := by
  simp only [pr, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re]
lemma pr_smul_right (χ b : ι → Fin 2 → Fin 2 → ℂ) (s : ℝ) : pr χ ((s : ℂ) • b) = s * pr χ b := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, mul_left_comm _ (s : ℂ), ← Finset.mul_sum, Complex.re_ofReal_mul]
lemma pr_smul_left (χ b : ι → Fin 2 → Fin 2 → ℂ) (s : ℝ) : pr ((s : ℂ) • χ) b = s * pr χ b := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]
def prL (χ : ι → Fin 2 → Fin 2 → ℂ) : (ι → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] ℝ where
  toFun := pr χ
  map_add' := pr_add_right χ
  map_smul' s b := by rw [← Complex.coe_smul, pr_smul_right]; rfl
def prR (b : ι → Fin 2 → Fin 2 → ℂ) : (ι → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] ℝ where
  toFun χ := pr χ b
  map_add' χ ψ := pr_add_left χ ψ b
  map_smul' s χ := by simp only [RingHom.id_apply, smul_eq_mul]; rw [← Complex.coe_smul, pr_smul_left]
lemma pr_sum {N : ℕ} (χ : ι → Fin 2 → Fin 2 → ℂ) (c : Fin N → ℝ) (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ) :
    pr χ (∑ j, (c j : ℂ) • ω j) = ∑ j, c j * pr χ (ω j) := by
  show prL χ (∑ j, (c j : ℂ) • ω j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => pr_smul_right χ (ω j) (c j)
lemma eq_zero_of_pr_conj {χ : ι → Fin 2 → Fin 2 → ℂ}
    (h : pr χ (fun τ i k => conj (χ τ i k)) = 0) : χ = 0 := by
  simp only [pr, Complex.mul_conj] at h
  simp only [← Complex.ofReal_sum, Complex.ofReal_re] at h
  funext τ i k
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)] at h
  have h2 := h τ (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun k _ =>
    Complex.normSq_nonneg _)] at h2
  have h3 := h2 i (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)] at h3
  exact Complex.normSq_eq_zero.mp (h3 k (Finset.mem_univ _))
lemma finrank_rfam : Module.finrank ℝ (ι → Fin 2 → Fin 2 → ℝ) = 4 * Fintype.card ι := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_pi_fintype, mul_comm]
end Fam
section Basis
variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)
lemma kap_li (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) :
    LinearIndependent ℝ (fun j => kap (ω j)) := by
  rw [linearIndependent_iff'] at hli ⊢
  intro s g hg i hi
  refine hli s g ?_ i hi
  have h := congrArg thL hg
  rw [map_sum, map_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  exact congrArg _ (th_kap (hω j)).symm
def basR (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) (hN : N = 4 * Fintype.card ι) :
    Module.Basis (Fin N) ℝ (ι → Fin 2 → Fin 2 → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (kap_li ω hω hli) (by rw [Fintype.card_fin, finrank_rfam, hN])
lemma herm_eq_sum (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) {b : ι → Fin 2 → Fin 2 → ℂ} (hb : IsHermFam b) :
    ∃ s : Fin N → ℝ, b = ∑ j, (s j : ℂ) • ω j := by
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin N) ℝ (ι → Fin 2 → Fin 2 → ℝ), ⇑B = fun j => kap (ω j) :=
    ⟨basR ω hω hli hN, by unfold basR; exact coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  refine ⟨B.repr (kap b), ?_⟩
  have hsum := B.sum_repr (kap b)
  simp only [hB] at hsum
  calc b = thL (kap b) := (th_kap hb).symm
    _ = thL (∑ j, B.repr (kap b) j • kap (ω j)) := by rw [hsum]
    _ = ∑ j, (B.repr (kap b) j : ℂ) • ω j := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Complex.coe_smul]
        exact congrArg _ (th_kap (hω j))
def phiL : (ι → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  LinearMap.pi fun j => (2 : ℝ) • ((prR (ω j)).comp thL)
lemma phiL_apply (z : ι → Fin 2 → Fin 2 → ℝ) (j : Fin N) : phiL ω z j = 2 * pr (th z) (ω j) := rfl
lemma phiL_inj (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) : Function.Injective (phiL ω) := by
  refine (injective_iff_map_eq_zero (phiL ω)).mpr fun z hz => ?_
  have hp : ∀ j, pr (th z) (ω j) = 0 := fun j => by
    have h := congrFun hz j
    rw [phiL_apply] at h
    simpa using h
  obtain ⟨s, hs⟩ := herm_eq_sum ω hω hli hN (conj_herm (th_herm z))
  have h0 : pr (th z) (fun τ i k => conj (th z τ i k)) = 0 := by
    rw [hs, pr_sum]
    simp [hp]
  have hz0 := eq_zero_of_pr_conj h0
  rw [← kap_th z, hz0]
  funext τ i k
  simp [kap]
lemma phiL_surj (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) : Function.Surjective (phiL ω) := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_rfam, Module.finrank_fin_fun, hN])).mp (phiL_inj ω hω hli hN)
def chiOf (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) (m : Fin N → ℝ) : ι → Fin 2 → Fin 2 → ℂ :=
  th ((LinearEquiv.ofBijective (phiL ω) ⟨phiL_inj ω hω hli hN, phiL_surj ω hω hli hN⟩).symm m)
variable (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) (hN : N = 4 * Fintype.card ι)
end Basis
section ZbFacts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)
def fac (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)
end ZbFacts
end
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices


