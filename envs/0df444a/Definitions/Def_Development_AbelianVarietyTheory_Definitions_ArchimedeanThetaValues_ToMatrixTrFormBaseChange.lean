-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:12.590171+00:00
-- url     : https://prove2.me/theorems/e46fa615-7867-4b0c-a024-4814eec44ac4
-- title:
--   To Matrix Tr Form Base Change
-- statement:
--   Definitions and structural lemmas for To Matrix Tr Form Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ToMatrixTrFormBaseChange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Theorems.Thm_GlobalTheory_HostModel_coe_rt_sq
import Theorems.Thm_GlobalTheory_HostModel_finrank_rat_E21_eq_twelve
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_trForm_baseChange_pos
import Theorems.Thm_GlobalTheory_HostModel_trForm_injective
import Theorems.Thm_GlobalTheory_HostModel_trForm_mul_left
import Theorems.Thm_GlobalTheory_HostModel_trForm_symm
import Theorems.Thm_GlobalTheory_HostModel_trace_bar
import Theorems.Thm_UpperTheory_Reformulated_B_Gc4_conj_embedding_rt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def ConjDual (_H : Host E) : Type := Module.Dual ℤ (𝓞 E)
namespace ConjDual
variable {H : Host E}
instance instAddCommGroup : AddCommGroup (ConjDual H) :=
  inferInstanceAs (AddCommGroup (Module.Dual ℤ (𝓞 E)))
def toDual (H : Host E) : ConjDual H ≃ₗ[ℤ] Module.Dual ℤ (𝓞 E) :=
  (AddEquiv.refl (Module.Dual ℤ (𝓞 E)) : ConjDual H ≃+ Module.Dual ℤ (𝓞 E)).toIntLinearEquiv
@[ext] theorem ext {f g : ConjDual H} (h : ∀ x, toDual H f x = toDual H g x) : f = g :=
  (toDual H).injective (LinearMap.ext h)
instance instSMul : SMul (𝓞 E) (ConjDual H) :=
  ⟨fun a f => (toDual H).symm (toDual H f ∘ₗ LinearMap.mulLeft ℤ (H.bar a))⟩
@[simp] theorem smul_apply (a : 𝓞 E) (f : ConjDual H) (x : 𝓞 E) :
    toDual H (a • f) x = toDual H f (H.bar a * x) := rfl
instance instModule : Module (𝓞 E) (ConjDual H) where
  one_smul f := by ext; simp
  mul_smul a b f := by ext; simp [mul_left_comm, mul_assoc]
  smul_zero a := by ext; simp
  smul_add a f g := by ext; simp
  add_smul a b f := by ext; simp [add_mul]
  zero_smul f := by ext; simp
instance instFreeInt : Module.Free ℤ (ConjDual H) := .of_equiv (toDual H).symm
instance instFiniteInt : Module.Finite ℤ (ConjDual H) := .equiv (toDual H).symm
instance instFinite : Module.Finite (𝓞 E) (ConjDual H) := .of_restrictScalars_finite ℤ _ _
theorem finrank_int : finrank ℤ (ConjDual H) = finrank ℤ (𝓞 E) := by
  rw [(toDual H).finrank_eq, Module.finrank_linearMap_self]
instance instIsTorsionFree : Module.IsTorsionFree (𝓞 E) (ConjDual H) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have hb : H.bar a ≠ 0 := by simpa using ha
  ext x
  obtain ⟨c, hc⟩ := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 E) (H.bar a)
  have hn : Algebra.intNorm ℤ (𝓞 E) (H.bar a) ≠ 0 := by simpa using hb
  have h1 := congrArg (fun g => toDual H g (c * x)) h
  simp only [smul_apply, map_zero, LinearMap.zero_apply] at h1
  rw [← mul_assoc, ← hc, ← Algebra.smul_def, map_smul] at h1
  simpa [hn] using h1
instance instProjective : Module.Projective (𝓞 E) (ConjDual H) :=
  haveI := Module.finitePresentation_of_finite (𝓞 E) (ConjDual H)
  Module.Flat.projective_of_finitePresentation
end ConjDual
open ConjDual
def traceDual (H : Host E) : 𝓞 E →ₗ[𝓞 E] ConjDual H where
  toFun x := (toDual H).symm (trForm H x)
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp [trForm_mul_left]
@[simp] theorem toDual_traceDual (H : Host E) (x : 𝓞 E) : toDual H (traceDual H x) = trForm H x := rfl
theorem traceDual_injective (H : Host E) : Function.Injective (traceDual H) :=
  fun _ _ h => trForm_injective H (congrArg (toDual H) h)
theorem finrank_eq_of_injective {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module (𝓞 E) M] [Module (𝓞 E) N]
    [Module.Finite ℤ N] (φ : M →ₗ[𝓞 E] N) (hφ : Function.Injective φ) (h : finrank ℤ M = finrank ℤ N) :
    finrank (𝓞 E) M = finrank (𝓞 E) N := by
  haveI : Module.Finite (𝓞 E) N := .of_restrictScalars_finite ℤ _ _
  have h1 := Submodule.finrank_quotient_add_finrank ((LinearMap.range φ).restrictScalars ℤ)
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range φ)
  have e := LinearEquiv.ofInjective φ hφ
  have h3 : finrank ℤ ((LinearMap.range φ).restrictScalars ℤ) = finrank ℤ M :=
    (e.toAddEquiv.toIntLinearEquiv.finrank_eq).symm
  have h4 : finrank ℤ (N ⧸ (LinearMap.range φ).restrictScalars ℤ) = 0 := by omega
  have h5 : finrank (𝓞 E) (N ⧸ LinearMap.range φ) = 0 := by
    rw [Module.finrank_eq_zero_iff] at h4 ⊢
    intro x
    obtain ⟨n, hn, hx⟩ := h4 x
    refine ⟨(n : 𝓞 E), by exact_mod_cast hn, ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    exact hx
  rw [e.finrank_eq]
  omega
abbrev HypLattice (H : Host E) : Type := 𝓞 E × ConjDual H
theorem finrank_hypLattice (H : Host E) : finrank (𝓞 E) (HypLattice H) = 2 := by
  rw [← finrank_eq_of_injective (LinearMap.prodMap LinearMap.id (traceDual H))
    (Function.injective_id.prodMap (traceDual_injective H))
    (by rw [finrank_prod, finrank_prod, finrank_int])]
  simp
def hypForm (H : Host E) : LinearMap.BilinForm ℤ (HypLattice H) :=
  LinearMap.mk₂ ℤ (fun u v => toDual H u.2 v.1 - toDual H v.2 u.1)
    (fun u u' v => by simp; ring) (fun c u v => by simp [mul_sub, -zsmul_eq_mul, Prod.smul_fst, Prod.smul_snd])
    (fun u v v' => by simp; ring) (fun c u v => by simp [mul_sub, -zsmul_eq_mul, Prod.smul_fst, Prod.smul_snd])
@[simp] theorem hypForm_apply (H : Host E) (u v : HypLattice H) :
    hypForm H u v = toDual H u.2 v.1 - toDual H v.2 u.1 := rfl
theorem hypForm_self (H : Host E) (u : HypLattice H) : hypForm H u u = 0 := by simp
theorem hypForm_smul (H : Host E) (a : 𝓞 E) (u v : HypLattice H) :
    hypForm H (a • u) v = hypForm H u (H.bar a • v) := by simp
theorem hypForm_bijective (H : Host E) : Function.Bijective (hypForm H) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun u hu => Prod.ext ?_ ?_
    · refine (Module.forall_dual_apply_eq_zero_iff ℤ u.1).mp fun g => ?_
      simpa using LinearMap.congr_fun hu (0, (toDual H).symm g)
    · ext y
      simpa using LinearMap.congr_fun hu (y, 0)
  · intro φ
    obtain ⟨x, hx⟩ := (Module.evalEquiv ℤ (𝓞 E)).surjective
      (-(φ ∘ₗ LinearMap.inr ℤ _ _ ∘ₗ (toDual H).symm.toLinearMap))
    refine ⟨(x, (toDual H).symm (φ ∘ₗ LinearMap.inl ℤ _ _)), LinearMap.ext fun v => ?_⟩
    have h := LinearMap.congr_fun hx (toDual H v.2)
    simp at h
    simp [h, ← map_add]
abbrev BasisIndex (E : Type) [Field E] [NumberField E] : Type := Free.ChooseBasisIndex ℤ (𝓞 E)
def hypBasis (H : Host E) : Basis (BasisIndex E ⊕ BasisIndex E) ℤ (HypLattice H) :=
  (RingOfIntegers.basis E).prod ((RingOfIntegers.basis E).dualBasis.map (toDual H).symm)
theorem hypBasis_inl (H : Host E) (i : BasisIndex E) :
    hypBasis H (Sum.inl i) = (RingOfIntegers.basis E i, 0) := by
  ext <;> simp [hypBasis]
theorem hypBasis_inr (H : Host E) (i : BasisIndex E) :
    hypBasis H (Sum.inr i) = (0, (toDual H).symm ((RingOfIntegers.basis E).coord i)) := by
  ext <;> simp [hypBasis]
theorem hypBasis_repr_inl (H : Host E) (u : HypLattice H) (i : BasisIndex E) :
    (hypBasis H).repr u (Sum.inl i) = (RingOfIntegers.basis E).repr u.1 i := by
  simp [hypBasis]
theorem hypBasis_repr_inr (H : Host E) (u : HypLattice H) (i : BasisIndex E) :
    (hypBasis H).repr u (Sum.inr i) = toDual H u.2 (RingOfIntegers.basis E i) := by
  simp [hypBasis]
def hypRealBasis (H : Host E) : Basis (BasisIndex E ⊕ BasisIndex E) ℝ (ℝ ⊗[ℤ] HypLattice H) :=
  (hypBasis H).baseChange ℝ
def gram (H : Host E) : Matrix (BasisIndex E) (BasisIndex E) ℝ :=
  Matrix.of fun i j => (trForm H (RingOfIntegers.basis E i) (RingOfIntegers.basis E j) : ℤ)
theorem gram_transpose (H : Host E) : (gram H)ᵀ = gram H := by
  ext i j
  simp [gram, trForm_symm H (RingOfIntegers.basis E j)]
theorem toMatrix_trForm_baseChange (H : Host E) :
    LinearMap.BilinForm.toMatrix ((RingOfIntegers.basis E).baseChange ℝ) ((trForm H).baseChange ℝ) = gram H := by
  ext i j
  simp [gram]
theorem gram_posDef (H : Host E) : (gram H).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using gram_transpose H)
    fun x hx => ?_
  set b := (RingOfIntegers.basis E).baseChange ℝ
  have h := trForm_baseChange_pos H (v := b.equivFun.symm x) (by simpa only [ne_eq, map_eq_zero_iff _ b.equivFun.symm.injective] using hx)
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b, toMatrix_trForm_baseChange,
    ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] at h
  exact h
theorem isUnit_det_gram (H : Host E) : IsUnit (gram H).det := (gram_posDef H).det_pos.ne'.isUnit
def hypJ (H : Host E) : ℝ ⊗[ℤ] HypLattice H →ₗ[ℝ] ℝ ⊗[ℤ] HypLattice H :=
  Matrix.toLin (hypRealBasis H) (hypRealBasis H) (Matrix.fromBlocks 0 (-(gram H)⁻¹) (gram H) 0)
theorem toMatrix_hypJ (H : Host E) : LinearMap.toMatrix (hypRealBasis H) (hypRealBasis H) (hypJ H) =
    Matrix.fromBlocks 0 (-(gram H)⁻¹) (gram H) 0 := LinearMap.toMatrix_toLin _ _ _
theorem hypJ_hypJ (H : Host E) (x) : hypJ H (hypJ H x) = -x := by
  have : hypJ H ∘ₗ hypJ H = -LinearMap.id := by
    apply (LinearMap.toMatrix (hypRealBasis H) (hypRealBasis H)).injective
    rw [LinearMap.toMatrix_comp _ (hypRealBasis H), toMatrix_hypJ, map_neg, LinearMap.toMatrix_id,
      Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp [Matrix.mul_nonsing_inv _ (isUnit_det_gram H), Matrix.nonsing_inv_mul _ (isUnit_det_gram H)]
  exact LinearMap.congr_fun this x
theorem toMatrix_hypForm (H : Host E) :
    LinearMap.BilinForm.toMatrix (hypRealBasis H) ((hypForm H).baseChange ℝ) = Matrix.fromBlocks 0 (-1) 1 0 := by
  ext (i | i) (j | j) <;>
    simp [hypRealBasis, hypBasis_inl, hypBasis_inr, Matrix.one_apply, Finsupp.single_apply, eq_comm]
theorem hypForm_hypJ_hypJ (H : Host E) (x y) :
    (hypForm H).baseChange ℝ (hypJ H x) (hypJ H y) = (hypForm H).baseChange ℝ x y := by
  have : ((hypForm H).baseChange ℝ).comp (hypJ H) (hypJ H) = (hypForm H).baseChange ℝ := by
    apply (LinearMap.BilinForm.toMatrix (hypRealBasis H)).injective
    rw [LinearMap.BilinForm.toMatrix_comp (hypRealBasis H), toMatrix_hypJ, toMatrix_hypForm]
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_nonsing_inv, gram_transpose,
      Matrix.mul_nonsing_inv _ (isUnit_det_gram H), Matrix.nonsing_inv_mul _ (isUnit_det_gram H)]
  exact LinearMap.congr_fun₂ this x y
theorem hypForm_hypJ_pos (H : Host E) (x) (hx : x ≠ 0) : 0 < (hypForm H).baseChange ℝ (hypJ H x) x := by
  have h : LinearMap.BilinForm.toMatrix (hypRealBasis H) (((hypForm H).baseChange ℝ).compLeft (hypJ H)) =
      Matrix.fromBlocks (gram H) 0 0 (gram H)⁻¹ := by
    rw [LinearMap.BilinForm.toMatrix_compLeft, toMatrix_hypJ, toMatrix_hypForm]
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_nonsing_inv, gram_transpose]
  have h2 := LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec (hypRealBasis H)
    (((hypForm H).baseChange ℝ).compLeft (hypJ H)) x x
  rw [h, LinearMap.BilinForm.compLeft_apply] at h2
  have hc : (hypRealBasis H).repr x ≠ 0 := by simpa using hx
  set c : BasisIndex E ⊕ BasisIndex E → ℝ := ⇑((hypRealBasis H).repr x) with hc'
  rw [h2, ← Sum.elim_comp_inl_inr c, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, add_zero, zero_add,
    sumElim_dotProduct_sumElim]
  have p1 := gram_posDef H
  have p2 := p1.inv
  by_cases h1 : c ∘ Sum.inl = 0
  · have h3 : c ∘ Sum.inr ≠ 0 := by
      intro h3
      apply hc
      ext (i | i)
      exacts [congrFun h1 i, congrFun h3 i]
    simpa [h1] using p2.dotProduct_mulVec_pos h3
  · exact add_pos_of_pos_of_nonneg (by simpa using p1.dotProduct_mulVec_pos h1)
      (by simpa using p2.posSemidef.dotProduct_mulVec_nonneg (c ∘ Sum.inr))
def mulMatrix (a : 𝓞 E) : Matrix (BasisIndex E) (BasisIndex E) ℝ :=
  (Algebra.leftMulMatrix (RingOfIntegers.basis E) a).map Int.cast
theorem trace_mulMatrix (a : 𝓞 E) : (mulMatrix a).trace = (Algebra.trace ℤ (𝓞 E) a : ℤ) := by
  rw [Algebra.trace_eq_matrix_trace (RingOfIntegers.basis E)]
  simp [mulMatrix, Matrix.trace]
theorem gram_mul_mulMatrix (H : Host E) (a : 𝓞 E) :
    gram H * mulMatrix a = (mulMatrix (H.bar a))ᵀ * gram H := by
  have h : ∀ (a : 𝓞 E) i j, (gram H * mulMatrix a) i j =
      (trForm H (RingOfIntegers.basis E i) (a * RingOfIntegers.basis E j) : ℤ) := by
    intro a i j
    conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E j)]
    simp only [map_sum, map_zsmul]
    simp [Matrix.mul_apply, gram, mulMatrix, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]
  ext i j
  rw [← gram_transpose H, ← Matrix.transpose_mul, gram_transpose, Matrix.transpose_apply, h, h,
    trForm_symm, trForm_mul_left]
theorem toMatrix_of_smul (H : Host E) (a : 𝓞 E) (A : ℝ ⊗[ℤ] HypLattice H →ₗ[ℝ] ℝ ⊗[ℤ] HypLattice H)
    (hA : ∀ x, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) :
    LinearMap.toMatrix (hypRealBasis H) (hypRealBasis H) A =
      Matrix.fromBlocks (mulMatrix a) 0 0 (mulMatrix (H.bar a))ᵀ := by
  ext (i | i) (j | j) <;>
    simp [LinearMap.toMatrix_apply, hypRealBasis, hA, hypBasis_inl, hypBasis_inr, hypBasis_repr_inl,
      hypBasis_repr_inr, mulMatrix, Algebra.leftMulMatrix_eq_repr_mul]
theorem sum_add_conj_eq_trace (H : Host E) (a : 𝓞 E) :
    ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
      (τ (a : E) + starRingEnd ℂ (τ (a : E))) = (Algebra.trace ℤ (𝓞 E) a : ℤ) := by
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have h0 : -H.rt0 ≠ H.rt0 := by
    intro h
    have h1 : H.rt0 = 0 := by linear_combination (-1 / 2 : ℂ) * h
    have h2 := H.sqrt_neg_disc_sq
    rw [h1] at h2
    exact hd (by linear_combination h2)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 → τ (H.rt : E) = -H.rt0 := fun τ h => by
    have : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, coe_rt_sq, H.sqrt_neg_disc_sq]; simp
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp this).resolve_left h
  rw [coe_trace_eq_sum, Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    rw [ComplexEmbedding.conjugate_coe_eq, conj_embedding_rt, hτ]
    exact h0
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    rw [ComplexEmbedding.conjugate_coe_eq, conj_embedding_rt, hsq τ hτ, neg_neg]
  · intro τ _; exact star_star τ
  · intro τ _; exact star_star τ
  · intro τ _; rfl
section Action
variable (H : Host E) (a : 𝓞 E) (A : ℝ ⊗[ℤ] HypLattice H →ₗ[ℝ] ℝ ⊗[ℤ] HypLattice H)
  (hA : ∀ x, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x))
include hA
theorem hypJ_comm : hypJ H ∘ₗ A = A ∘ₗ hypJ H := by
  apply (LinearMap.toMatrix (hypRealBasis H) (hypRealBasis H)).injective
  have h : (gram H)⁻¹ * (mulMatrix (H.bar a))ᵀ = mulMatrix a * (gram H)⁻¹ := by
    rw [← Matrix.mul_nonsing_inv_cancel_right (gram H) (mulMatrix (H.bar a))ᵀ (isUnit_det_gram H),
      ← gram_mul_mulMatrix, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_gram H)]
  rw [LinearMap.toMatrix_comp _ (hypRealBasis H), LinearMap.toMatrix_comp _ (hypRealBasis H), toMatrix_hypJ,
    toMatrix_of_smul H a A hA]
  simp [Matrix.fromBlocks_multiply, gram_mul_mulMatrix, h]
theorem trace_of_smul : LinearMap.trace ℝ _ A = 2 * (Algebra.trace ℤ (𝓞 E) a : ℤ) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (hypRealBasis H), toMatrix_of_smul H a A hA, two_mul]
  have h1 := trace_mulMatrix a
  have h2 := trace_mulMatrix (H.bar a)
  rw [trace_bar] at h2
  simp only [Matrix.trace, Matrix.diag] at h1 h2
  simp [Matrix.trace, Fintype.sum_sum_type, h1, h2]
theorem trace_hypJ_comp : LinearMap.trace ℝ _ (hypJ H ∘ₗ A) = 0 := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (hypRealBasis H), LinearMap.toMatrix_comp _ (hypRealBasis H), toMatrix_hypJ,
    toMatrix_of_smul H a A hA]
  simp [Matrix.fromBlocks_multiply, Matrix.trace, Fintype.sum_sum_type]
end Action
@[reducible] def hypDatum (H : Host E) : Datum H where
  La := HypLattice H
  fin := inferInstance
  proj := inferInstance
  EF := hypForm H
  alt := hypForm_self H
  unimod := hypForm_bijective H
  adj := hypForm_smul H
  p := 1
  q := 1
  rank := finrank_hypLattice H
  dom := ⟨hypJ H, hypJ_hypJ H, hypForm_hypJ_hypJ H, hypForm_hypJ_pos H, fun a A t hA ht => by
    simp only [Nat.cast_one, one_mul, sum_add_conj_eq_trace] at ht
    refine ⟨hypJ_comm H a A hA, ?_, ?_⟩
    · rw [trace_of_smul H a A hA, ht, Complex.intCast_re]
    · rw [trace_hypJ_comp H a A hA, ht, Complex.intCast_im, mul_zero]⟩
instance instNonemptyDatum (H : Host E) : Nonempty (Datum H) := ⟨hypDatum H⟩
example (H : Host E) : finrank (𝓞 E) (hypDatum H).La = 2 := (hypDatum H).rank
example (H : Host E) : (hypDatum H).EF (0, traceDual H 1) (1, 0) = finrank ℚ E := by
  simp [trForm_one_one]
example (H : Host E) (f : ConjDual H) (x : 𝓞 E) : toDual H (H.rt • f) x = -toDual H f (H.rt * x) := by simp
example (H : Host E) (a : 𝓞 E) :
    LinearMap.trace ℝ _ ((DistribSMul.toLinearMap ℤ (HypLattice H) a).baseChange ℝ) =
      2 * (Algebra.trace ℤ (𝓞 E) a : ℤ) :=
  trace_of_smul H a _ fun _ => rfl
example : finrank ℤ (hypDatum host).La = 24 := by
  change finrank ℤ (𝓞 E21 × ConjDual host) = 24
  rw [finrank_prod, finrank_int, RingOfIntegers.rank, finrank_rat_E21_eq_twelve]
end GlobalTheory.HostModel


