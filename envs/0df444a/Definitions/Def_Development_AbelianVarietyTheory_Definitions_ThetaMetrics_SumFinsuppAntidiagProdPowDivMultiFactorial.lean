-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:33.439929+00:00
-- url     : https://prove2.me/theorems/a8250d8f-55c3-4ba3-9b52-a20f0219ada9
-- title:
--   Sum Finsupp Antidiag Prod Pow Div Multi Factorial
-- statement:
--   Definitions and structural lemmas for Sum Finsupp Antidiag Prod Pow Div Multi Factorial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
namespace GlobalTheory.MvPoly
variable {σ τ K L : Type*}
section Defs
variable [NormedCommRing K]
def l1Norm (P : MvPolynomial σ K) : ℝ := ∑ α ∈ P.support, ‖P.coeff α‖
def l2Norm (P : MvPolynomial σ K) : ℝ := √(∑ α ∈ P.support, ‖P.coeff α‖ ^ 2)
def supCoeff (P : MvPolynomial σ K) : ℝ := ((P.support.sup fun α ↦ ‖P.coeff α‖₊ : NNReal) : ℝ)
def multiFactorial (α : σ →₀ ℕ) : ℕ := α.prod fun _ n ↦ n.factorial
def fockNormSq (P : MvPolynomial σ K) : ℝ :=
  ∑ α ∈ P.support, (multiFactorial α : ℝ) * ‖P.coeff α‖ ^ 2
def fockInner {𝕜 : Type*} [RCLike 𝕜] (P Q : MvPolynomial σ 𝕜) : 𝕜 :=
  ∑ α ∈ P.support, (multiFactorial α : 𝕜) * (P.coeff α * starRingEnd 𝕜 (Q.coeff α))
def monomialsLE (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℕ) : Finset (σ →₀ ℕ) :=
  (range (d + 1)).biUnion fun k ↦ (univ : Finset σ).finsuppAntidiag k
end Defs
section L1
variable [NormedCommRing K] [NormedCommRing L]
theorem l1Norm_eq_sum_of_subset {P : MvPolynomial σ K} {s : Finset (σ →₀ ℕ)}
    (h : P.support ⊆ s) : l1Norm P = ∑ α ∈ s, ‖P.coeff α‖ :=
  sum_subset h fun α _ hα ↦ by rw [notMem_support_iff.mp hα, norm_zero]
theorem sum_norm_coeff_le_l1Norm (P : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) :
    ∑ α ∈ s, ‖P.coeff α‖ ≤ l1Norm P := by
  classical
  rw [l1Norm_eq_sum_of_subset (s := P.support ∪ s) subset_union_left]
  exact sum_le_sum_of_subset_of_nonneg subset_union_right fun _ _ _ ↦ norm_nonneg _
theorem norm_coeff_le_l1Norm (P : MvPolynomial σ K) (α : σ →₀ ℕ) : ‖P.coeff α‖ ≤ l1Norm P := by
  simpa using sum_norm_coeff_le_l1Norm P {α}
@[simp] theorem l1Norm_zero : l1Norm (0 : MvPolynomial σ K) = 0 := by simp [l1Norm]
@[simp] theorem l1Norm_eq_zero {P : MvPolynomial σ K} : l1Norm P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ l1Norm_zero⟩
  ext α
  simpa using norm_le_zero_iff.mp (h ▸ norm_coeff_le_l1Norm P α)
@[simp] theorem l1Norm_monomial (α : σ →₀ ℕ) (c : K) : l1Norm (monomial α c) = ‖c‖ := by
  classical
  rw [l1Norm_eq_sum_of_subset (s := {α}) support_monomial_subset]
  simp
@[simp] theorem l1Norm_C (c : K) : l1Norm (C c : MvPolynomial σ K) = ‖c‖ := l1Norm_monomial 0 c
@[simp] theorem l1Norm_one [NormOneClass K] : l1Norm (1 : MvPolynomial σ K) = 1 := by
  rw [← C_1, l1Norm_C, norm_one]
@[simp] theorem l1Norm_X [NormOneClass K] (i : σ) : l1Norm (X i : MvPolynomial σ K) = 1 := by
  rw [X, l1Norm_monomial, norm_one]
@[simp] theorem l1Norm_neg (P : MvPolynomial σ K) : l1Norm (-P) = l1Norm P := by
  simp [l1Norm]
theorem l1Norm_add_le (P Q : MvPolynomial σ K) : l1Norm (P + Q) ≤ l1Norm P + l1Norm Q := by
  classical
  rw [l1Norm_eq_sum_of_subset (s := P.support ∪ Q.support) support_add,
    l1Norm_eq_sum_of_subset (s := P.support ∪ Q.support) subset_union_left,
    l1Norm_eq_sum_of_subset (s := P.support ∪ Q.support) subset_union_right, ← sum_add_distrib]
  exact sum_le_sum fun α _ ↦ by rw [coeff_add]; exact norm_add_le _ _
theorem l1Norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) :=
  Finset.le_sum_of_subadditive l1Norm l1Norm_zero.le l1Norm_add_le s f
theorem l1Norm_mul_le (P Q : MvPolynomial σ K) : l1Norm (P * Q) ≤ l1Norm P * l1Norm Q := by
  conv_lhs => rw [P.as_sum, Q.as_sum, sum_mul_sum]
  refine (l1Norm_sum_le _ _).trans ?_
  rw [l1Norm, l1Norm, sum_mul_sum]
  refine sum_le_sum fun α _ ↦ (l1Norm_sum_le _ _).trans (sum_le_sum fun β _ ↦ ?_)
  rw [monomial_mul, l1Norm_monomial]
  exact norm_mul_le _ _
def l1RingNorm (σ K : Type*) [NormedCommRing K] : RingNorm (MvPolynomial σ K) where
  toFun := l1Norm
  map_zero' := l1Norm_zero
  add_le' := l1Norm_add_le
  neg' := l1Norm_neg
  mul_le' := l1Norm_mul_le
  eq_zero_of_map_eq_zero' _ := l1Norm_eq_zero.mp
@[simp] theorem l1RingNorm_apply (P : MvPolynomial σ K) : l1RingNorm σ K P = l1Norm P := rfl
def l1RingSeminorm (σ K : Type*) [NormedCommRing K] : RingSeminorm (MvPolynomial σ K) :=
  (l1RingNorm σ K).toRingSeminorm
@[simp] theorem l1RingSeminorm_apply (P : MvPolynomial σ K) :
    l1RingSeminorm σ K P = l1Norm P := rfl
end L1
section Linear
variable [NormedCommRing K]
theorem l1Norm_linearForm_le_sum {ι : Type*} (s : Finset ι) (v : ι → σ) (e : ι → K) :
    l1Norm (∑ k ∈ s, C (e k) * X (v k) : MvPolynomial σ K) ≤ ∑ k ∈ s, ‖e k‖ := by
  refine (l1Norm_sum_le _ _).trans_eq (sum_congr rfl fun k _ ↦ ?_)
  rw [C_mul_X_eq_monomial, l1Norm_monomial]
theorem l1Norm_linearForm_eq_sum {ι : Type*} (s : Finset ι) {v : ι → σ}
    (hv : Function.Injective v) (e : ι → K) :
    l1Norm (∑ k ∈ s, C (e k) * X (v k) : MvPolynomial σ K) = ∑ k ∈ s, ‖e k‖ := by
  classical
  refine (l1Norm_linearForm_le_sum s v e).antisymm ?_
  have hinj : Function.Injective fun k ↦ (Finsupp.single (v k) 1 : σ →₀ ℕ) :=
    fun a b h ↦ hv (Finsupp.single_left_injective one_ne_zero h)
  refine le_trans (le_of_eq ?_) (sum_norm_coeff_le_l1Norm _ (s.image fun k ↦ .single (v k) 1))
  rw [sum_image fun a _ b _ h ↦ hinj h]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [coeff_sum, sum_eq_single k]
  · simp [C_mul_X_eq_monomial]
  · intro b _ hb
    rw [C_mul_X_eq_monomial, coeff_monomial, if_neg fun h ↦ hb (hinj h)]
  · exact fun h ↦ (h hk).elim
end Linear
section Eval
variable [NormedCommRing K]
end Eval
section Count
variable [Fintype σ] [DecidableEq σ]
@[simp] theorem mem_monomialsLE {d : ℕ} {α : σ →₀ ℕ} : α ∈ monomialsLE σ d ↔ α.degree ≤ d := by
  simp [monomialsLE, mem_finsuppAntidiag, Finsupp.degree_eq_sum]
theorem card_monomialsLE (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℕ) :
    #(monomialsLE σ d) = (Fintype.card σ + d).choose d := by
  rw [monomialsLE, card_biUnion]
  · simp_rw [card_finsuppAntidiag_nat_eq_multichoose]
    rw [Nat.sum_range_multichoose, card_univ, add_comm d]
    exact Nat.choose_symm_add
  · intro a _ b _ hab
    refine disjoint_left.mpr fun α ha hb ↦ hab ?_
    rw [mem_finsuppAntidiag] at ha hb
    exact ha.1.symm.trans hb.1
end Count
section L2
variable [NormedCommRing K] [NormedCommRing L]
theorem fubiniStudy_l2Norm_sq_eq (P : MvPolynomial σ K) : l2Norm P ^ 2 = ∑ α ∈ P.support, ‖P.coeff α‖ ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun _ _ ↦ sq_nonneg _)
theorem l2Norm_eq_sqrt_sum_of_subset {P : MvPolynomial σ K} {s : Finset (σ →₀ ℕ)}
    (h : P.support ⊆ s) : l2Norm P = √(∑ α ∈ s, ‖P.coeff α‖ ^ 2) := by
  rw [l2Norm, sum_subset h fun α _ hα ↦ by simp [notMem_support_iff.mp hα]]
@[simp] theorem l2Norm_zero : l2Norm (0 : MvPolynomial σ K) = 0 := by simp [l2Norm]
@[simp] theorem l2Norm_monomial (α : σ →₀ ℕ) (c : K) : l2Norm (monomial α c) = ‖c‖ := by
  classical
  rw [l2Norm_eq_sqrt_sum_of_subset (s := {α}) support_monomial_subset]
  simp
@[simp] theorem l2Norm_neg (P : MvPolynomial σ K) : l2Norm (-P) = l2Norm P := by
  simp [l2Norm]
theorem norm_coeff_le_l2Norm (P : MvPolynomial σ K) (α : σ →₀ ℕ) : ‖P.coeff α‖ ≤ l2Norm P := by
  classical
  rw [l2Norm_eq_sqrt_sum_of_subset (s := insert α P.support) (subset_insert _ _)]
  exact Real.le_sqrt_of_sq_le
    (single_le_sum (f := fun β ↦ ‖P.coeff β‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_insert_self _ _))
@[simp] theorem l2Norm_eq_zero {P : MvPolynomial σ K} : l2Norm P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ l2Norm_zero⟩
  ext α
  simpa using norm_le_zero_iff.mp (h ▸ norm_coeff_le_l2Norm P α)
theorem supCoeff_nonneg (P : MvPolynomial σ K) : 0 ≤ supCoeff P := NNReal.coe_nonneg _
theorem norm_coeff_le_supCoeff (P : MvPolynomial σ K) (α : σ →₀ ℕ) :
    ‖P.coeff α‖ ≤ supCoeff P := by
  by_cases h : α ∈ P.support
  · exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun α ↦ ‖P.coeff α‖₊) h)
  · rw [notMem_support_iff.mp h, norm_zero]; exact supCoeff_nonneg P
theorem supCoeff_le_iff {P : MvPolynomial σ K} {B : ℝ} (hB : 0 ≤ B) :
    supCoeff P ≤ B ↔ ∀ α, ‖P.coeff α‖ ≤ B := by
  refine ⟨fun h α ↦ (norm_coeff_le_supCoeff P α).trans h, fun h ↦ ?_⟩
  lift B to NNReal using hB
  exact NNReal.coe_le_coe.mpr (Finset.sup_le fun α _ ↦ h α)
@[simp] theorem supCoeff_zero : supCoeff (0 : MvPolynomial σ K) = 0 := by simp [supCoeff]
@[simp] theorem supCoeff_eq_zero {P : MvPolynomial σ K} : supCoeff P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ supCoeff_zero⟩
  ext α
  simpa using norm_le_zero_iff.mp (h ▸ norm_coeff_le_supCoeff P α)
@[simp] theorem supCoeff_monomial (α : σ →₀ ℕ) (c : K) : supCoeff (monomial α c) = ‖c‖ := by
  classical
  refine le_antisymm ((supCoeff_le_iff (norm_nonneg c)).mpr fun β ↦ ?_) ?_
  · rw [coeff_monomial]; split_ifs <;> simp
  · simpa using norm_coeff_le_supCoeff (monomial α c) α
end L2
section Fock
theorem multiFactorial_pos (α : σ →₀ ℕ) : 0 < multiFactorial α :=
  prod_pos fun _ _ ↦ Nat.factorial_pos _
@[simp] theorem multiFactorial_zero : multiFactorial (0 : σ →₀ ℕ) = 1 := by simp [multiFactorial]
@[simp] theorem multiFactorial_single (i : σ) (n : ℕ) :
    multiFactorial (Finsupp.single i n) = n.factorial :=
  Finsupp.prod_single_index rfl
variable [NormedCommRing K] [NormedCommRing L]
theorem fockNormSq_eq_sum_of_subset {P : MvPolynomial σ K} {s : Finset (σ →₀ ℕ)}
    (h : P.support ⊆ s) : fockNormSq P = ∑ α ∈ s, (multiFactorial α : ℝ) * ‖P.coeff α‖ ^ 2 :=
  sum_subset h fun α _ hα ↦ by simp [notMem_support_iff.mp hα]
@[simp] theorem fockNormSq_zero : fockNormSq (0 : MvPolynomial σ K) = 0 := by simp [fockNormSq]
@[simp] theorem fockNormSq_monomial (α : σ →₀ ℕ) (c : K) :
    fockNormSq (monomial α c) = multiFactorial α * ‖c‖ ^ 2 := by
  classical
  rw [fockNormSq_eq_sum_of_subset (s := {α}) support_monomial_subset]
  simp
theorem l2Norm_sq_le_fockNormSq (P : MvPolynomial σ K) : l2Norm P ^ 2 ≤ fockNormSq P := by
  rw [fubiniStudy_l2Norm_sq_eq]
  exact sum_le_sum fun α _ ↦ le_mul_of_one_le_left (sq_nonneg _)
    (by exact_mod_cast multiFactorial_pos α)
@[simp] theorem fockNormSq_eq_zero {P : MvPolynomial σ K} : fockNormSq P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ l2Norm_eq_zero.mp ?_, fun h ↦ h ▸ fockNormSq_zero⟩
  exact pow_eq_zero_iff two_ne_zero |>.mp
    (le_antisymm (h ▸ l2Norm_sq_le_fockNormSq P) (sq_nonneg _))
variable {𝕜 : Type*} [RCLike 𝕜]
theorem fockInner_eq_sum_of_subset_left {P : MvPolynomial σ 𝕜} (Q : MvPolynomial σ 𝕜)
    {s : Finset (σ →₀ ℕ)} (h : P.support ⊆ s) : fockInner P Q =
      ∑ α ∈ s, (multiFactorial α : 𝕜) * (P.coeff α * starRingEnd 𝕜 (Q.coeff α)) :=
  sum_subset h fun α _ hα ↦ by simp [notMem_support_iff.mp hα]
theorem fockInner_eq_sum_of_subset_right (P : MvPolynomial σ 𝕜) {Q : MvPolynomial σ 𝕜}
    {s : Finset (σ →₀ ℕ)} (h : Q.support ⊆ s) : fockInner P Q =
      ∑ α ∈ s, (multiFactorial α : 𝕜) * (P.coeff α * starRingEnd 𝕜 (Q.coeff α)) := by
  classical
  rw [fockInner_eq_sum_of_subset_left Q (s := P.support ∪ s) subset_union_left]
  exact (sum_subset subset_union_right fun α _ hα ↦ by
    simp [notMem_support_iff.mp fun h' ↦ hα (h h')]).symm
theorem fockInner_add_left (P P' Q : MvPolynomial σ 𝕜) :
    fockInner (P + P') Q = fockInner P Q + fockInner P' Q := by
  simp only [fockInner_eq_sum_of_subset_right _ (subset_refl Q.support), coeff_add, add_mul,
    mul_add, sum_add_distrib]
theorem fockInner_smul_left (c : 𝕜) (P Q : MvPolynomial σ 𝕜) :
    fockInner (c • P) Q = c * fockInner P Q := by
  simp only [fockInner_eq_sum_of_subset_right _ (subset_refl Q.support), mul_sum]
  exact sum_congr rfl fun α _ ↦ by rw [coeff_smul, smul_eq_mul]; ring
theorem fockInner_add_right (P Q Q' : MvPolynomial σ 𝕜) :
    fockInner P (Q + Q') = fockInner P Q + fockInner P Q' := by
  simp only [fockInner, coeff_add, map_add, mul_add, sum_add_distrib]
theorem fockInner_smul_right (c : 𝕜) (P Q : MvPolynomial σ 𝕜) :
    fockInner P (c • Q) = starRingEnd 𝕜 c * fockInner P Q := by
  simp only [fockInner, mul_sum]
  exact sum_congr rfl fun α _ ↦ by rw [coeff_smul, smul_eq_mul, map_mul]; ring
def fockInnerₛₗ (σ 𝕜 : Type*) [RCLike 𝕜] :
    MvPolynomial σ 𝕜 →ₗ[𝕜] MvPolynomial σ 𝕜 →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd 𝕜) fockInner fockInner_add_left
    fockInner_smul_left fockInner_add_right fockInner_smul_right
@[simp] theorem fockInnerₛₗ_apply (P Q : MvPolynomial σ 𝕜) :
    fockInnerₛₗ σ 𝕜 P Q = fockInner P Q := rfl
theorem fockInner_monomial_right (P : MvPolynomial σ 𝕜) (α : σ →₀ ℕ) (c : 𝕜) :
    fockInner P (monomial α c) = multiFactorial α * (P.coeff α * starRingEnd 𝕜 c) := by
  classical
  rw [fockInner_eq_sum_of_subset_right P (s := {α}) support_monomial_subset]
  simp
end Fock
example : l1Norm (C 3 * X 0 + C (-4) * X 1 : MvPolynomial (Fin 2) ℂ) = 7 := by
  have := l1Norm_linearForm_eq_sum (K := ℂ) univ (v := id) Function.injective_id ![3, -4]
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, id] at this
  rw [this]
  norm_num
example : l2Norm (monomial 0 3 + monomial (Finsupp.single 0 1) 4 : MvPolynomial (Fin 1) ℂ) = 5 ∧
    supCoeff (monomial 0 3 + monomial (Finsupp.single 0 1) 4 : MvPolynomial (Fin 1) ℂ) = 4 := by
  have hne : (Finsupp.single 0 1 : Fin 1 →₀ ℕ) ≠ 0 := by simp
  constructor
  · rw [l2Norm_eq_sqrt_sum_of_subset (s := {0, Finsupp.single 0 1})
      (support_add.trans (union_subset (support_monomial_subset.trans (by simp))
        (support_monomial_subset.trans (by simp)))), sum_pair hne.symm]
    simp only [coeff_add, coeff_monomial, hne, hne.symm, if_true, if_false]
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  · refine le_antisymm ((supCoeff_le_iff (by norm_num)).mpr fun β ↦ ?_) ?_
    · simp only [coeff_add, coeff_monomial]
      split_ifs with h1 h2
      · exact (hne (h2.trans h1.symm)).elim
      all_goals norm_num
    · refine le_trans (le_of_eq ?_) (norm_coeff_le_supCoeff _ (Finsupp.single 0 1))
      simp [coeff_monomial, hne.symm]
example : fockNormSq (X 0 ^ 3 : MvPolynomial (Fin 2) ℂ) = 6 := by
  rw [X_pow_eq_monomial, fockNormSq_monomial, multiFactorial_single]
  norm_num [Nat.factorial]
example : fockInner (1 : MvPolynomial (Fin 1) ℂ) (C Complex.I) = -Complex.I := by
  rw [C_apply, fockInner_monomial_right]
  simp
example : #(monomialsLE (Fin 2) 2) = 6 := by
  rw [card_monomialsLE]; decide
end GlobalTheory.MvPoly


