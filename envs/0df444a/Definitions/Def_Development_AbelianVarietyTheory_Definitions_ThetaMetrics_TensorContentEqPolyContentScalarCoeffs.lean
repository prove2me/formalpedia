-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:46.590421+00:00
-- url     : https://prove2.me/theorems/841a2f28-ae15-4e6f-b673-82e60f34d085
-- title:
--   Tensor Content Eq Poly Content Scalar Coeffs
-- statement:
--   Definitions and structural lemmas for Tensor Content Eq Poly Content Scalar Coeffs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
section CoeffSup
variable {ι M Γ₀ : Type*} [Zero M] [LinearOrderedCommMonoidWithZero Γ₀]
def coeffSup (N : M → Γ₀) (c : ι →₀ M) : Γ₀ := c.support.sup fun i => N (c i)
variable {N : M → Γ₀}
@[simp] theorem coeffSup_zero : coeffSup N (0 : ι →₀ M) = 0 := by
  simp [coeffSup, bot_eq_zero]
theorem coeffSup_le_iff (h0 : N 0 = 0) {c : ι →₀ M} {γ : Γ₀} :
    coeffSup N c ≤ γ ↔ ∀ i, N (c i) ≤ γ := by
  rw [coeffSup, Finset.sup_le_iff]
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : i ∈ c.support
  · exact h i hi
  · rw [Finsupp.notMem_support_iff.mp hi, h0]; exact zero_le
theorem le_coeffSup (h0 : N 0 = 0) (c : ι →₀ M) (i : ι) : N (c i) ≤ coeffSup N c :=
  (coeffSup_le_iff h0).mp le_rfl i
theorem exists_mem_support_coeffSup_eq {c : ι →₀ M} (hc : c ≠ 0) :
    ∃ i ∈ c.support, coeffSup N c = N (c i) :=
  Finset.exists_mem_eq_sup _ (Finsupp.support_nonempty_iff.mpr hc) _
theorem coeffSup_eq_zero_iff (h0 : N 0 = 0) {c : ι →₀ M} :
    coeffSup N c = 0 ↔ ∀ i, N (c i) = 0 := by
  simp only [← le_zero_iff, coeffSup_le_iff h0]
theorem coeffSup_single (h0 : N 0 = 0) (i : ι) (a : M) :
    coeffSup N (Finsupp.single i a) = N a := by
  classical
  refine le_antisymm ((coeffSup_le_iff h0).mpr fun j => ?_) ?_
  · rw [Finsupp.single_apply]; split_ifs
    · exact le_rfl
    · rw [h0]; exact zero_le
  · simpa using le_coeffSup h0 (Finsupp.single i a) i
theorem coeffSup_eq_mul_of_forall (h0 : N 0 = 0) {M' : Type*} [Zero M'] {N' : M' → Γ₀}
    (h0' : N' 0 = 0) {c : ι →₀ M} {c' : ι →₀ M'} {γ : Γ₀} (h : ∀ i, N' (c' i) = γ * N (c i)) :
    coeffSup N' c' = γ * coeffSup N c := by
  refine le_antisymm ((coeffSup_le_iff h0').mpr fun i => ?_) ?_
  · rw [h i]; exact mul_le_mul_right (le_coeffSup h0 c i) γ
  · by_cases hc : c = 0
    · simp [hc]
    · obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := N) hc
      rw [hi, ← h i]; exact le_coeffSup h0' c' i
end CoeffSup
section MonoidAlgebra
variable {R G Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
theorem coeffSup_coeff_mul_le [Add G] (f g : AddMonoidAlgebra R G) :
    coeffSup v (f * g).coeff ≤ coeffSup v f.coeff * coeffSup v g.coeff := by
  classical
  refine (coeffSup_le_iff v.map_zero).mpr fun m => ?_
  rw [AddMonoidAlgebra.coeff_mul]
  refine v.map_sum_le fun a _ => v.map_sum_le fun b _ => ?_
  dsimp only
  split_ifs
  · rw [v.map_mul]
    exact mul_le_mul' (le_coeffSup v.map_zero _ _) (le_coeffSup v.map_zero _ _)
  · rw [v.map_zero]; exact zero_le
theorem coeffSup_coeff_mul [Add G] [UniqueSums G] (f g : AddMonoidAlgebra R G) :
    coeffSup v (f * g).coeff = coeffSup v f.coeff * coeffSup v g.coeff := by
  classical
  refine le_antisymm (coeffSup_coeff_mul_le v f g) ?_
  by_cases hf : coeffSup v f.coeff = 0
  · simp [hf]
  by_cases hg : coeffSup v g.coeff = 0
  · simp [hg]
  have hf' : f.coeff ≠ 0 := fun h => hf (by simp [h])
  have hg' : g.coeff ≠ 0 := fun h => hg (by simp [h])
  obtain ⟨a, ha, ha'⟩ := exists_mem_support_coeffSup_eq (N := v) hf'
  obtain ⟨b, hb, hb'⟩ := exists_mem_support_coeffSup_eq (N := v) hg'
  obtain ⟨a₀, ha₀, b₀, hb₀, hu⟩ := UniqueSums.uniqueAdd_of_nonempty
    (A := f.coeff.support.filter fun x => v (f.coeff x) = coeffSup v f.coeff)
    (B := g.coeff.support.filter fun x => v (g.coeff x) = coeffSup v g.coeff)
    ⟨a, Finset.mem_filter.mpr ⟨ha, ha'.symm⟩⟩ ⟨b, Finset.mem_filter.mpr ⟨hb, hb'.symm⟩⟩
  obtain ⟨ha₁, ha₂⟩ := Finset.mem_filter.mp ha₀
  obtain ⟨hb₁, hb₂⟩ := Finset.mem_filter.mp hb₀
  refine le_trans (le_of_eq ?_) (le_coeffSup v.map_zero _ (a₀ + b₀))
  have hpos : 0 < coeffSup v f.coeff * coeffSup v g.coeff := zero_lt_iff.mpr (mul_ne_zero hf hg)
  rw [AddMonoidAlgebra.coeff_mul]
  simp_rw [Finsupp.sum]
  rw [← Finset.sum_product', v.map_sum_eq_of_lt (j := (a₀, b₀))
    (Finset.mem_product.mpr ⟨ha₁, hb₁⟩)]
  · simp [ha₂, hb₂]
  · intro p hp
    obtain ⟨hp, hne⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_singleton] at hne
    simp only [if_true, map_mul, ha₂, hb₂]
    split_ifs with he
    · rw [map_mul]
      have h₁ := le_coeffSup v.map_zero f.coeff p.1
      have h₂ := le_coeffSup v.map_zero g.coeff p.2
      rcases h₁.eq_or_lt with h₁ | h₁
      · rcases h₂.eq_or_lt with h₂ | h₂
        · have := hu (Finset.mem_filter.mpr ⟨hp₁, h₁⟩) (Finset.mem_filter.mpr ⟨hp₂, h₂⟩) he
          exact absurd (Prod.ext this.1 this.2) hne
        · rw [h₁]; exact mul_lt_mul_of_pos_left h₂ (zero_lt_iff.mpr hf)
      · exact lt_of_le_of_lt (mul_le_mul_right h₂ _)
          (mul_lt_mul_of_pos_right h₁ (zero_lt_iff.mpr hg))
    · rw [map_zero]; exact hpos
variable [AddMonoid G] [UniqueSums G]
def gaussValAlg : Valuation (AddMonoidAlgebra R G) Γ₀ where
  toFun f := coeffSup v f.coeff
  map_zero' := by simp
  map_one' := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, coeffSup_single v.map_zero,
      v.map_one]
  map_mul' := coeffSup_coeff_mul v
  map_add_le_max' f g := (coeffSup_le_iff v.map_zero).mpr fun m => by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (v.map_add _ _).trans
      (max_le_max (le_coeffSup v.map_zero _ _) (le_coeffSup v.map_zero _ _))
theorem gaussValAlg_le_iff {f : AddMonoidAlgebra R G} {γ : Γ₀} :
    gaussValAlg v f ≤ γ ↔ ∀ m, v (f.coeff m) ≤ γ := coeffSup_le_iff v.map_zero
@[simp] theorem gaussValAlg_single (m : G) (a : R) :
    gaussValAlg v (AddMonoidAlgebra.single m a) = v a :=
  coeffSup_single v.map_zero m a
theorem gaussValAlg_eq_zero_iff {f : AddMonoidAlgebra R G} :
    gaussValAlg v f = 0 ↔ ∀ m, v (f.coeff m) = 0 := coeffSup_eq_zero_iff v.map_zero
end MonoidAlgebra
section Poly
open MvPolynomial
variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)
def gaussVal : Valuation (MvPolynomial σ R) Γ₀ := gaussValAlg v
theorem gaussVal_le_iff {f : MvPolynomial σ R} {γ : Γ₀} :
    gaussVal v f ≤ γ ↔ ∀ m, v (coeff m f) ≤ γ := gaussValAlg_le_iff v
theorem le_gaussVal (f : MvPolynomial σ R) (m : σ →₀ ℕ) : v (coeff m f) ≤ gaussVal v f :=
  (gaussVal_le_iff v).mp le_rfl m
theorem gaussVal_eq_zero_iff_forall {f : MvPolynomial σ R} :
    gaussVal v f = 0 ↔ ∀ m, v (coeff m f) = 0 := gaussValAlg_eq_zero_iff v
@[simp] theorem gaussVal_monomial (m : σ →₀ ℕ) (a : R) :
    gaussVal v (monomial m a) = v a := gaussValAlg_single v m a
@[simp] theorem gaussVal_C (a : R) : gaussVal v (C a : MvPolynomial σ R) = v a :=
  gaussVal_monomial v 0 a
@[simp] theorem gaussVal_X (i : σ) : gaussVal v (X i : MvPolynomial σ R) = 1 :=
  (gaussVal_monomial v _ 1).trans v.map_one
@[simp] theorem gaussVal_comap_C :
    (gaussVal v).comap (C : R →+* MvPolynomial σ R) = v := by
  ext a; simp
theorem gaussVal_supp :
    (gaussVal v).supp = v.supp.map (C : R →+* MvPolynomial σ R) := by
  ext f
  rw [Valuation.mem_supp_iff, gaussVal_eq_zero_iff_forall, mem_map_C_iff]
  simp only [Valuation.mem_supp_iff]
theorem gaussVal_supp_eq_bot_of_supp (hv : v.supp = ⊥) :
    (gaussVal (σ := σ) v).supp = ⊥ := by
  rw [gaussVal_supp, hv, Ideal.map_bot]
theorem gaussVal_eq_zero_iff_of_supp (hv : v.supp = ⊥) {f : MvPolynomial σ R} :
    gaussVal v f = 0 ↔ f = 0 := by
  rw [← Valuation.mem_supp_iff, gaussVal_supp_eq_bot_of_supp v hv, Ideal.mem_bot]
theorem gaussVal_sum_C_mul_X (s : Finset σ) (a : σ → R) :
    gaussVal v (∑ i ∈ s, C (a i) * X i : MvPolynomial σ R) = s.sup fun i => v (a i) := by
  classical
  refine le_antisymm (Valuation.map_sum_le _ fun i hi => ?_) (Finset.sup_le fun i hi => ?_)
  · rw [map_mul, gaussVal_C, gaussVal_X, mul_one]
    exact Finset.le_sup (f := fun i => v (a i)) hi
  · refine le_trans (le_of_eq ?_) (le_gaussVal v _ (Finsupp.single i 1))
    rw [coeff_sum, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
      exact fun h => hj (Finsupp.single_left_injective one_ne_zero h)
    · exact fun h => absurd hi h
theorem valuation_eval₂_le_gaussVal (w : Valuation S Γ₀) (φ : R →+* S)
    (h : ∀ a, w (φ a) ≤ v a) (x : σ → S) (hx : ∀ i, w (x i) ≤ 1) (f : MvPolynomial σ R) :
    w (eval₂ φ x f) ≤ gaussVal v f := by
  rw [eval₂_eq]
  refine w.map_sum_le fun m _ => ?_
  rw [map_mul, map_prod]
  refine le_trans (mul_le_mul' (h _) (Finset.prod_le_one' fun i _ => ?_)) ?_
  · rw [map_pow]; exact pow_le_one' (hx i) _
  · rw [mul_one]; exact le_gaussVal v f m
theorem valuation_aeval_le_gaussVal [Algebra R S] (w : Valuation S Γ₀)
    (h : ∀ a, w (algebraMap R S a) ≤ v a) (x : σ → S) (hx : ∀ i, w (x i) ≤ 1)
    (f : MvPolynomial σ R) : w (aeval x f) ≤ gaussVal v f :=
  valuation_eval₂_le_gaussVal v w _ h x hx f
theorem gaussVal_aeval_le (g : σ → MvPolynomial τ R) (hg : ∀ i, gaussVal v (g i) ≤ 1)
    (f : MvPolynomial σ R) : gaussVal v (aeval g f) ≤ gaussVal v f :=
  valuation_aeval_le_gaussVal v (gaussVal v) (fun a => by simp) g hg f
theorem gaussVal_rename_le (e : σ → τ) (f : MvPolynomial σ R) :
    gaussVal v (rename e f) ≤ gaussVal v f := by
  rw [rename_eq_aeval]
  exact gaussVal_aeval_le v _ (fun i => by simp) f
theorem gaussVal_rename {e : σ → τ} (he : Function.Injective e) (f : MvPolynomial σ R) :
    gaussVal v (rename e f) = gaussVal v f := by
  refine le_antisymm (gaussVal_rename_le v e f) ((gaussVal_le_iff v).mpr fun m => ?_)
  rw [← coeff_rename_mapDomain e he f m]
  exact le_gaussVal v _ _
@[simp] theorem gaussVal_renameEquiv (e : σ ≃ τ) (f : MvPolynomial σ R) :
    gaussVal v (renameEquiv R e f) = gaussVal v f :=
  gaussVal_rename v e.injective f
@[simp] theorem gaussVal_sumAlgEquiv (f : MvPolynomial (σ ⊕ τ) R) :
    gaussVal (gaussVal v) (sumAlgEquiv R σ τ f) = gaussVal v f := by
  refine le_antisymm ?_ ?_
  · have := valuation_aeval_le_gaussVal v (gaussVal (σ := σ) (gaussVal (σ := τ) v))
      (fun a => by simp) (fun i => sumAlgEquiv R σ τ (X i))
      (fun i => by cases i <;> simp) f
    convert this using 2
    exact DFunLike.congr_fun (aeval_unique (sumAlgEquiv R σ τ).toAlgHom) f
  · obtain ⟨g, rfl⟩ := (sumAlgEquiv R σ τ).symm.surjective f
    rw [AlgEquiv.apply_symm_apply]
    have := valuation_eval₂_le_gaussVal (gaussVal (σ := τ) v) (gaussVal (σ := σ ⊕ τ) v)
      (rename Sum.inr).toRingHom (fun a => gaussVal_rename_le v _ a) (fun i => X (Sum.inl i))
      (fun i => by simp) g
    convert this using 2
    have : ((sumAlgEquiv R σ τ).symm : MvPolynomial σ (MvPolynomial τ R) →+* _) =
        eval₂Hom (rename Sum.inr).toRingHom (fun i => X (Sum.inl i)) := by
      ext <;> simp
    exact DFunLike.congr_fun this g
@[simp] theorem gaussVal_sumAlgEquiv_symm (g : MvPolynomial σ (MvPolynomial τ R)) :
    gaussVal v ((sumAlgEquiv R σ τ).symm g) = gaussVal (gaussVal v) g := by
  rw [← gaussVal_sumAlgEquiv, AlgEquiv.apply_symm_apply]
end Poly
section Field
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
section Monoid
variable [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀] (v : Valuation K Γ₀)
theorem valuation_supp_eq_bot : v.supp = ⊥ :=
  (Ideal.eq_bot_or_top v.supp).resolve_right (Ideal.IsPrime.ne_top inferInstance)
@[simp] theorem gaussVal_eq_zero_iff {f : MvPolynomial σ K} : gaussVal v f = 0 ↔ f = 0 :=
  gaussVal_eq_zero_iff_of_supp v (valuation_supp_eq_bot v)
end Monoid
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
def gaussValFrac (σ F : Type*) [Field F] [Algebra (MvPolynomial σ K) F]
    [IsFractionRing (MvPolynomial σ K) F] : Valuation F Γ₀ :=
  (gaussVal (σ := σ) v).extendToLocalization (S := nonZeroDivisors (MvPolynomial σ K))
    (fun _ hf h => nonZeroDivisors.ne_zero hf ((gaussVal_eq_zero_iff v).mp h)) F
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]
@[simp] theorem gaussValFrac_algebraMap (f : MvPolynomial σ K) :
    gaussValFrac v σ F (algebraMap _ F f) = gaussVal v f :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ f
@[simp] theorem gaussValFrac_comap :
    (gaussValFrac v σ F).comap (algebraMap (MvPolynomial σ K) F) = gaussVal v := by
  ext f; simp
@[simp] theorem gaussValFrac_algebraMap_const [Algebra K F]
    [IsScalarTower K (MvPolynomial σ K) F] (a : K) :
    gaussValFrac v σ F (algebraMap K F a) = v a := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial σ K) F, gaussValFrac_algebraMap]
  simp
end Field
section Additive
open MvPolynomial
variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
def gaussAddVal : AddValuation (MvPolynomial σ R) Γ :=
  AddValuation.ofValuation (gaussVal (AddValuation.toValuation v))
theorem gaussAddVal_mul (f g : MvPolynomial σ R) :
    gaussAddVal v (f * g) = gaussAddVal v f + gaussAddVal v g := AddValuation.map_mul _ f g
@[simp] theorem gaussAddVal_C (a : R) : gaussAddVal v (C a : MvPolynomial σ R) = v a :=
  gaussVal_C (AddValuation.toValuation v) a
@[simp] theorem gaussAddVal_X (i : σ) : gaussAddVal v (X i : MvPolynomial σ R) = 0 :=
  gaussVal_X (AddValuation.toValuation v) i
@[simp] theorem gaussAddVal_sumAlgEquiv (f : MvPolynomial (σ ⊕ τ) R) :
    gaussAddVal (gaussAddVal v) (sumAlgEquiv R σ τ f) = gaussAddVal v f :=
  gaussVal_sumAlgEquiv (AddValuation.toValuation v) f
end Additive
section Abs
open MvPolynomial
variable {R σ τ : Type*} [CommRing R]
def absValuation [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a) :
    Valuation R ℝ≥0 where
  toFun x := NNReal.mk (a x) (a.nonneg x)
  map_zero' := NNReal.eq a.map_zero
  map_one' := NNReal.eq a.map_one
  map_mul' x y := NNReal.eq (a.map_mul x y)
  map_add_le_max' x y := by
    refine NNReal.coe_le_coe.mp ?_
    rw [NNReal.coe_max]
    exact ha x y
@[simp] theorem coe_absValuation [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)
    (x : R) : (absValuation a ha x : ℝ) = a x := rfl
theorem absValuation_supp [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a) :
    (absValuation a ha).supp = ⊥ := by
  ext x
  rw [Valuation.mem_supp_iff, ← NNReal.coe_eq_zero, coe_absValuation, a.eq_zero, Ideal.mem_bot]
def valuationAbs (v : Valuation R ℝ≥0) (hv : v.supp = ⊥) : AbsoluteValue R ℝ where
  toFun x := v x
  map_mul' x y := by simp
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by
    rw [NNReal.coe_eq_zero, ← Valuation.mem_supp_iff, hv, Ideal.mem_bot]
  add_le' x y := by
    have h : (v (x + y) : ℝ) ≤ max (v x : ℝ) (v y) := by exact_mod_cast v.map_add x y
    exact h.trans (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
@[simp] theorem valuationAbs_apply (v : Valuation R ℝ≥0) (hv : v.supp = ⊥) (x : R) :
    valuationAbs v hv x = v x := rfl
theorem isNonarchimedean_valuationAbs (v : Valuation R ℝ≥0) (hv : v.supp = ⊥) :
    IsNonarchimedean (valuationAbs v hv) := fun x y => by
  simp only [valuationAbs_apply]
  exact_mod_cast v.map_add x y
variable [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)
def gaussAbs : AbsoluteValue (MvPolynomial σ R) ℝ :=
  valuationAbs (gaussVal (absValuation a ha))
    (gaussVal_supp_eq_bot_of_supp _ (absValuation_supp a ha))
theorem gaussAbs_apply (f : MvPolynomial σ R) :
    gaussAbs a ha f = gaussVal (absValuation a ha) f := rfl
theorem isNonarchimedean_gaussAbs : IsNonarchimedean (gaussAbs (σ := σ) a ha) :=
  isNonarchimedean_valuationAbs _ _
@[simp] theorem gaussAbs_C (x : R) : gaussAbs a ha (C x : MvPolynomial σ R) = a x := by
  simp [gaussAbs_apply]
@[simp] theorem gaussAbs_X (i : σ) : gaussAbs a ha (X i : MvPolynomial σ R) = 1 := by
  simp [gaussAbs_apply]
variable {K : Type*} [Field K] (a : AbsoluteValue K ℝ) (ha : IsNonarchimedean a)
def gaussAbsFrac (σ F : Type*) [Field F] [Algebra (MvPolynomial σ K) F]
    [IsFractionRing (MvPolynomial σ K) F] : AbsoluteValue F ℝ :=
  valuationAbs (gaussValFrac (absValuation a ha) σ F) (valuation_supp_eq_bot _)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]
@[simp] theorem gaussAbsFrac_algebraMap (f : MvPolynomial σ K) :
    gaussAbsFrac a ha σ F (algebraMap _ F f) = gaussAbs a ha f :=
  congrArg NNReal.toReal (gaussValFrac_algebraMap (absValuation a ha) f)
end Abs
section Content
open MvPolynomial Module
variable {R Γ₀ ι κ σ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
def basisVal (b : Basis ι R M) (x : M) : Γ₀ := coeffSup v (b.repr x)
variable (b : Basis ι R M)
theorem basisVal_le_iff {x : M} {γ : Γ₀} : basisVal v b x ≤ γ ↔ ∀ i, v (b.repr x i) ≤ γ :=
  coeffSup_le_iff v.map_zero
@[simp] theorem basisVal_zero : basisVal v b 0 = 0 := by simp [basisVal]
@[simp] theorem basisVal_basis (i : ι) : basisVal v b (b i) = 1 := by
  rw [basisVal, b.repr_self, coeffSup_single v.map_zero, v.map_one]
theorem basisVal_smul (a : R) (x : M) : basisVal v b (a • x) = v a * basisVal v b x :=
  coeffSup_eq_mul_of_forall v.map_zero v.map_zero fun i => by simp
@[simp] theorem basisVal_neg (x : M) : basisVal v b (-x) = basisVal v b x := by
  rw [← neg_one_smul R x, basisVal_smul]; simp
def polyContent (c : (σ →₀ ℕ) →₀ M) : Γ₀ := coeffSup (basisVal v b) c
end Content
section Lattice
open Module
variable {R Γ₀ ι κ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
  {O : Type*} [CommRing O] [Algebra O R] [Module O M] [IsScalarTower O R M]
end Lattice
section Tensor
open MvPolynomial Module
variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)
def tensorContent (x : MvPolynomial σ R ⊗[O] M) : Γ₀ :=
  basisVal (gaussVal v) (b.baseChange (MvPolynomial σ R)) x
def tensorCoeffs : MvPolynomial σ R ⊗[O] M ≃ₗ[R] (σ →₀ ℕ) →₀ R ⊗[O] M :=
  open Classical in
  TensorProduct.AlgebraTensorModule.congr (AddMonoidAlgebra.coeffLinearEquiv R)
    (LinearEquiv.refl O M) ≪≫ₗ TensorProduct.finsuppLeft O R R M (σ →₀ ℕ)
@[simp] theorem tensorCoeffs_tmul (f : MvPolynomial σ R) (y : M) (m : σ →₀ ℕ) :
    tensorCoeffs (f ⊗ₜ[O] y) m = coeff m f ⊗ₜ[O] y := by
  simp [tensorCoeffs, coeff]
def scalarCoeffs {N : Type*} [AddCommGroup N] [Module R N] :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  tensorCoeffs ≪≫ₗ Finsupp.mapRange.linearEquiv (TensorProduct.lid R N)
@[simp] theorem scalarCoeffs_tmul {N : Type*} [AddCommGroup N] [Module R N]
    (f : MvPolynomial σ R) (y : N) (m : σ →₀ ℕ) :
    scalarCoeffs (f ⊗ₜ[R] y) m = coeff m f • y := by
  simp [scalarCoeffs]
end Tensor
section AdditiveContent
open MvPolynomial Module
variable {R Γ ι κ σ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
section
variable {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
def basisAddVal (x : M) : Γ :=
  OrderDual.ofDual (Multiplicative.toAdd (basisVal (AddValuation.toValuation v) b x))
theorem le_basisAddVal_iff {x : M} {γ : Γ} :
    γ ≤ basisAddVal v b x ↔ ∀ i, γ ≤ v (b.repr x i) :=
  basisVal_le_iff (AddValuation.toValuation v) b (γ := Multiplicative.ofAdd (OrderDual.toDual γ))
theorem basisAddVal_eq_inf_univ [Fintype ι] (x : M) :
    basisAddVal v b x = Finset.univ.inf fun i => v (b.repr x i) :=
  eq_of_forall_le_iff fun γ => by simp [le_basisAddVal_iff]
def polyAddContent (c : (σ →₀ ℕ) →₀ M) : Γ :=
  OrderDual.ofDual (Multiplicative.toAdd (polyContent (AddValuation.toValuation v) b c))
end
variable {O M : Type*} [CommRing O] [Algebra O R] [AddCommGroup M] [Module O M] (b : Basis ι O M)
def tensorAddContent (x : MvPolynomial σ R ⊗[O] M) : Γ :=
  basisAddVal (gaussAddVal v) (b.baseChange (MvPolynomial σ R)) x
end AdditiveContent
section More
open MvPolynomial Module IsDedekindDomain
def gaussAddValFrac {K Γ : Type*} [Field K] [LinearOrderedAddCommGroupWithTop Γ]
    (v : AddValuation K Γ) (σ F : Type*) [Field F] [Algebra (MvPolynomial σ K) F]
    [IsFractionRing (MvPolynomial σ K) F] : AddValuation F Γ :=
  AddValuation.ofValuation (gaussValFrac (AddValuation.toValuation v) σ F)
end More
section Examples
open MvPolynomial
example (p : ℕ) [Fact p.Prime] :
    ((gaussVal (NormedField.valuation (K := ℚ_[p]))
      (C (p : ℚ_[p]) * X 0 + C ((p : ℚ_[p]) ^ 2) * X 1 : MvPolynomial (Fin 2) ℚ_[p]) : ℝ≥0) : ℝ) =
      (p : ℝ)⁻¹ := by
  have h := gaussVal_sum_C_mul_X (NormedField.valuation (K := ℚ_[p])) Finset.univ
    (![(p : ℚ_[p]), (p : ℚ_[p]) ^ 2] : Fin 2 → ℚ_[p])
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h, Finset.univ_fin2, Finset.sup_insert, Finset.sup_singleton, NNReal.coe_max]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, NormedField.valuation_apply, coe_nnnorm,
    norm_pow, Padic.norm_p]
  refine max_eq_left ?_
  rw [sq]
  exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hp)
example {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) :
    gaussVal v (X 0 - X 1 : MvPolynomial (Fin 2) K) = 1 ∧
      gaussVal v (rename (fun _ => ()) (X 0 - X 1 : MvPolynomial (Fin 2) K)) = 0 := by
  refine ⟨?_, by simp⟩
  have h := gaussVal_sum_C_mul_X v Finset.univ (![1, -1] : Fin 2 → K)
  simpa [Fin.sum_univ_two, Finset.univ_fin2, ← sub_eq_add_neg] using h
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (h : Irreducible ϖ) :
    gaussAddVal (IsDiscreteValuationRing.addVal O) (C ϖ * X () : MvPolynomial Unit O) = 1 := by
  rw [gaussAddVal_mul, gaussAddVal_C, gaussAddVal_X, add_zero,
    IsDiscreteValuationRing.addVal_uniformizer h]
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (h : Irreducible ϖ) :
    basisAddVal (IsDiscreteValuationRing.addVal O) (Pi.basisFun O (Fin 2)) ![ϖ, ϖ ^ 2] = 1 := by
  rw [basisAddVal_eq_inf_univ, Finset.univ_fin2, Finset.inf_insert, Finset.inf_singleton]
  simp [IsDiscreteValuationRing.addVal_uniformizer h]
end Examples
end
end GlobalTheory


