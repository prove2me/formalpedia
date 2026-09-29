-- Prove2me | solution 1 for AutomorphicForm.map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/54e29c2b-ace9-5ab6-b440-612153c450b2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Theorems.Thm_AlgEquiv_algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions

noncomputable section

namespace KcSemiLocalSigmaLinGen

section FieldCase

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

local notation "n" => Module.finrank K L

include hgen

theorem orderOf_eq : orderOf σ = n := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem hgen_inv : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ⁻¹ := by
  intro τ; rw [Subgroup.zpowers_inv]; exact hgen τ

theorem algebraMap_norm_eq_prod_pow (τ : L ≃ₐ[K] L) (hτ : ∀ ρ : L ≃ₐ[K] L, ρ ∈ Subgroup.zpowers τ) (x : L) :
    algebraMap K L (Algebra.norm K x) = ∏ i ∈ Finset.range n, (τ ^ i) x := by
  rw [Algebra.norm_eq_prod_automorphisms, LT.TwistedNorm.prod_algEquiv_eq_prod_range_of_generator hτ]

theorem finrank_pos' : 0 < n := Module.finrank_pos

theorem det_sigma : LinearMap.det (σ : L →ₐ[K] L).toLinearMap = (-1) ^ (n - 1) := by
  have h := AlgEquiv.algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank K L σ (orderOf_eq σ hgen) 0
  rw [zero_smul, sub_zero] at h
  have h0 : ∏ i ∈ Finset.range n, (σ ^ i) (0 : L) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.2 (finrank_pos' σ hgen)) (map_zero _)
  rw [h0, sub_zero, mul_one] at h
  apply (algebraMap K L).injective
  rw [h, map_pow, map_neg, map_one]

theorem det_sigmaInv_sub (d : L) :
    LinearMap.det (((σ⁻¹ : L ≃ₐ[K] L) : L →ₐ[K] L).toLinearMap - d • LinearMap.id) = (-1) ^ (n - 1) * (1 - Algebra.norm K d) := by
  have h := AlgEquiv.algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank K L σ⁻¹
    (by rw [orderOf_inv]; exact orderOf_eq σ hgen) d
  rw [← algebraMap_norm_eq_prod_pow σ hgen σ⁻¹ (hgen_inv σ hgen) d] at h
  apply (algebraMap K L).injective
  rw [h, map_mul, map_pow, map_neg, map_one, map_sub, map_one]

theorem det_lmul_comp_sub_lmul (a c : L) :
    LinearMap.det (Algebra.lmul K L a ∘ₗ (σ : L →ₐ[K] L).toLinearMap - Algebra.lmul K L c) =
      (-1) ^ n * (Algebra.norm K c - Algebra.norm K a) := by
  have hn : n = (n - 1) + 1 := (Nat.sub_add_cancel (finrank_pos' σ hgen)).symm
  by_cases hc : c = 0
  ·
    have h1 : Algebra.lmul K L a ∘ₗ (σ : L →ₐ[K] L).toLinearMap - Algebra.lmul K L c =
        Algebra.lmul K L a ∘ₗ (σ : L →ₐ[K] L).toLinearMap := by
      rw [hc, map_zero, sub_zero]
    rw [h1, LinearMap.det_comp, det_sigma σ hgen, ← Algebra.norm_apply, hc, Algebra.norm_zero, zero_sub]
    conv_rhs => rw [hn, pow_succ]
    ring
  ·
    have hcu : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
    have h1 : Algebra.lmul K L a ∘ₗ (σ : L →ₐ[K] L).toLinearMap - Algebra.lmul K L c =
        Algebra.lmul K L (-c) ∘ₗ ((((σ⁻¹ : L ≃ₐ[K] L) : L →ₐ[K] L).toLinearMap - (c⁻¹ * a) • LinearMap.id) ∘ₗ
          (σ : L →ₐ[K] L).toLinearMap) := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_algHom,
        LinearMap.smul_apply, LinearMap.id_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
      rw [show σ⁻¹ (σ x) = x from σ.symm_apply_apply x, smul_eq_mul]
      have : -c * (x - c⁻¹ * a * σ x) = (c * c⁻¹) * a * σ x - c * x := by ring
      rw [this, hcu, one_mul]
    rw [h1, LinearMap.det_comp, LinearMap.det_comp, det_sigma σ hgen, det_sigmaInv_sub σ hgen, ← Algebra.norm_apply,
      map_mul]
    have hNc : Algebra.norm K c ≠ 0 := by
      intro h0
      have : Algebra.norm K (c * c⁻¹) = 0 := by rw [map_mul, h0, zero_mul]
      rw [hcu, map_one] at this
      exact one_ne_zero this
    have hinv : Algebra.norm K c * Algebra.norm K c⁻¹ = 1 := by rw [← map_mul, hcu, map_one]
    have hneg : Algebra.norm K (-c) = (-1) ^ n * Algebra.norm K c := by
      rw [← neg_one_mul, map_mul, show (-1 : L) = algebraMap K L (-1) by rw [map_neg, map_one],
        Algebra.norm_algebraMap]
    rw [hneg]
    have hsq : ((-1 : K) ^ (n - 1)) * (-1) ^ (n - 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc (-1) ^ n * Algebra.norm K c * ((-1) ^ (n - 1) * (1 - Algebra.norm K c⁻¹ * Algebra.norm K a) * (-1) ^ (n - 1))
        = (-1) ^ n * (((-1 : K) ^ (n - 1)) * (-1) ^ (n - 1)) *
            (Algebra.norm K c - (Algebra.norm K c * Algebra.norm K c⁻¹) * Algebra.norm K a) := by ring
      _ = (-1) ^ n * (Algebra.norm K c - Algebra.norm K a) := by rw [hsq, hinv]; ring

end FieldCase

section Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

local notation "n" => Module.finrank K L

def bK : Module.Basis (Fin n) K L := Module.finBasis K L

def μ (k j i : Fin n) : K := (bK K L).repr (bK K L k * bK K L j) i

def Mσ (σ : L ≃ₐ[K] L) : Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrix (bK K L) (bK K L) (σ : L →ₐ[K] L).toLinearMap

abbrev R₀ := MvPolynomial (Fin n ⊕ Fin n) K

def MX : Matrix (Fin n) (Fin n) (R₀ K L) :=
  fun i j => ∑ k, MvPolynomial.X (Sum.inl k) * MvPolynomial.C (μ K L k j i)

def MY : Matrix (Fin n) (Fin n) (R₀ K L) :=
  fun i j => ∑ k, MvPolynomial.X (Sum.inr k) * MvPolynomial.C (μ K L k j i)

def GS (σ : L ≃ₐ[K] L) : Matrix (Fin n) (Fin n) (R₀ K L) :=
  MX K L * (Mσ K L σ).map MvPolynomial.C - MY K L

variable {K L}

theorem basis_mul_basis (k j : Fin n) : bK K L k * bK K L j = ∑ i, μ K L k j i • bK K L i := by
  conv_lhs => rw [← (bK K L).sum_repr (bK K L k * bK K L j)]
  rfl

section EvalK

def aOf (x : Fin (Module.finrank K L) ⊕ Fin (Module.finrank K L) → K) : L := ∑ k, x (Sum.inl k) • bK K L k

def cOf (x : Fin (Module.finrank K L) ⊕ Fin (Module.finrank K L) → K) : L := ∑ k, x (Sum.inr k) • bK K L k

theorem eval_MX (x : Fin (Module.finrank K L) ⊕ Fin (Module.finrank K L) → K) :
    (MvPolynomial.eval x).mapMatrix (MX K L) = Algebra.leftMulMatrix (bK K L) (aOf x) := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, MX, map_sum, Algebra.leftMulMatrix_eq_repr_mul, aOf,
    Finset.sum_mul, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, smul_mul_assoc, map_smul, basis_mul_basis, map_sum,
    Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [map_smul, (bK K L).repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro i' _ hi'
    rw [map_smul, (bK K L).repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg hi', smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem eval_MY (x : Fin (Module.finrank K L) ⊕ Fin (Module.finrank K L) → K) :
    (MvPolynomial.eval x).mapMatrix (MY K L) = Algebra.leftMulMatrix (bK K L) (cOf x) := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, MY, map_sum, Algebra.leftMulMatrix_eq_repr_mul, cOf,
    Finset.sum_mul, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, smul_mul_assoc, map_smul, basis_mul_basis, map_sum,
    Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [map_smul, (bK K L).repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro i' _ hi'
    rw [map_smul, (bK K L).repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg hi', smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem eval_Mσ (x : Fin (Module.finrank K L) ⊕ Fin (Module.finrank K L) → K) (σ : L ≃ₐ[K] L) :
    (MvPolynomial.eval x).mapMatrix ((Mσ K L σ).map MvPolynomial.C) = Mσ K L σ := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, MvPolynomial.eval_C]

theorem eval_GS (x : Fin (Module.finrank K L) ⊕ Fin (Module.finrank K L) → K) (σ : L ≃ₐ[K] L) :
    (MvPolynomial.eval x).mapMatrix (GS K L σ) =
      LinearMap.toMatrix (bK K L) (bK K L)
        (Algebra.lmul K L (aOf x) ∘ₗ (σ : L →ₐ[K] L).toLinearMap - Algebra.lmul K L (cOf x)) := by
  rw [GS, map_sub, map_mul, eval_MX, eval_MY, eval_Mσ x, map_sub, LinearMap.toMatrix_comp (bK K L) (bK K L) (bK K L),
    Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply, Mσ]

theorem eval_det_GS [IsGalois K L] (x : Fin (Module.finrank K L) ⊕ Fin (Module.finrank K L) → K) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    MvPolynomial.eval x (GS K L σ).det =
      MvPolynomial.eval x ((-1) ^ n * ((MY K L).det - (MX K L).det)) := by
  rw [RingHom.map_det, eval_GS, LinearMap.det_toMatrix, det_lmul_comp_sub_lmul σ hgen, map_mul, map_sub,
    RingHom.map_det, RingHom.map_det, eval_MX, eval_MY, map_pow, map_neg, map_one,
    ← Algebra.norm_eq_matrix_det, ← Algebra.norm_eq_matrix_det]

end EvalK

theorem det_GS [IsGalois K L] [CharZero K] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (GS K L σ).det = (-1) ^ n * ((MY K L).det - (MX K L).det) := by
  haveI : Infinite K := Infinite.of_injective _ Nat.cast_injective
  exact MvPolynomial.funext fun x => eval_det_GS x σ hgen

end Generic

section SemiLocal

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "n" => Module.finrank K L

attribute [local instance 9999] Algebra.toModule

theorem isTopologicalRing_E : IsTopologicalRing E := AutomorphicForm.isTopologicalRing_tensor K L F
theorem t2Space_E : T2Space E := AutomorphicForm.t2Space_tensor K L F
theorem locallyCompactSpace_E : LocallyCompactSpace E := AutomorphicForm.locallyCompactSpace_tensor K L F
theorem continuousSMul_E : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
theorem isScalarTower_FEE : IsScalarTower F E E :=
  @IsScalarTower.right F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem smulCommClass_FEE : SMulCommClass F E E :=
  @Algebra.to_smulCommClass F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)

theorem finite_KL : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L

attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  isScalarTower_FEE smulCommClass_FEE finite_KL

variable (σ : L ≃ₐ[K] L)

def sigmaLin : E →ₗ[F] E where
  toFun := AutomorphicForm.sigmaTensor K L F σ
  map_add' x y := map_add _ x y
  map_smul' c x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)) ((1 : L) ⊗ₜ[K] c) = (1 : L) ⊗ₜ[K] c
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    simp

omit [NumberField L] in
@[scoped simp] theorem sigmaLin_apply (x : E) : sigmaLin (v := v) σ x = AutomorphicForm.sigmaTensor K L F σ x := rfl

omit [NumberField L] in
theorem sigmaTensor_tmul (l : L) (c : F) :
    AutomorphicForm.sigmaTensor K L F σ (l ⊗ₜ[K] c) = σ l ⊗ₜ[K] c := by
  show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)) (l ⊗ₜ[K] c) = σ l ⊗ₜ[K] c
  rw [Algebra.TensorProduct.map_tmul]; rfl

def S (a c : E) : E →ₗ[F] E := (Algebra.lmul F E a) ∘ₗ sigmaLin (v := v) σ - Algebra.lmul F E c

omit [NumberField L] in
@[scoped simp] theorem S_apply (a c x : E) :
    S (v := v) σ a c x = a * AutomorphicForm.sigmaTensor K L F σ x - c * x := by
  simp [S, Algebra.coe_lmul_eq_mul]

def bE : Module.Basis (Fin n) F E := (bK K L).rightBaseChange L

theorem bE_apply (i : Fin n) : bE (v := v) i = bK K L i ⊗ₜ[K] (1 : F) :=
  Module.Basis.rightBaseChange_apply L (bK K L) i

theorem algebraMap_smul_E (r : K) (x : E) : algebraMap K F r • x = r • x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, smul_zero]
  | tmul l f =>
      rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul,
        TensorProduct.comm_symm_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

theorem sum_smul_tmul_one (r : Fin n → K) :
    (∑ i, r i • bK K L i) ⊗ₜ[K] (1 : F) = ∑ i, algebraMap K F (r i) • bE (v := v) i := by
  rw [TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_smul_E, bE_apply, TensorProduct.smul_tmul']

theorem repr_sum_smul_bE (r : Fin n → F) (i : Fin n) :
    (bE (v := v)).repr (∑ k, r k • bE (v := v) k) i = r i := by
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, (bE (v := v)).repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro k _ hk
    rw [map_smul, (bE (v := v)).repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg hk, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

def ρ (a c : E) : Fin n ⊕ Fin n → F := Sum.elim (fun k => (bE (v := v)).repr a k) (fun k => (bE (v := v)).repr c k)

def spec (a c : E) : R₀ K L →+* F := (MvPolynomial.aeval (ρ (v := v) a c)).toRingHom

theorem spec_X (a c : E) (s : Fin n ⊕ Fin n) : spec (v := v) a c (MvPolynomial.X s) = ρ (v := v) a c s := by
  rw [spec, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]

theorem spec_C (a c : E) (r : K) : spec (v := v) a c (MvPolynomial.C r) = algebraMap K F r := by
  rw [spec, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.algHom_C]

theorem leftMulMatrix_bE (z : E) (i j : Fin n) :
    Algebra.leftMulMatrix (bE (v := v)) z i j = ∑ k, (bE (v := v)).repr z k * algebraMap K F (μ K L k j i) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [← (bE (v := v)).sum_repr z]
  rw [Finset.sum_mul, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  rw [bE_apply, bE_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, basis_mul_basis, sum_smul_tmul_one,
    repr_sum_smul_bE]

theorem spec_MX (a c : E) : (spec (v := v) a c).mapMatrix (MX K L) = Algebra.leftMulMatrix (bE (v := v)) a := by
  ext i j : 1
  rw [RingHom.mapMatrix_apply (spec (v := v) a c) (MX K L), Matrix.map_apply, MX, map_sum (spec (v := v) a c), leftMulMatrix_bE]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, spec_X, spec_C]; rfl

theorem spec_MY (a c : E) : (spec (v := v) a c).mapMatrix (MY K L) = Algebra.leftMulMatrix (bE (v := v)) c := by
  ext i j : 1
  rw [RingHom.mapMatrix_apply (spec (v := v) a c) (MY K L), Matrix.map_apply, MY, map_sum (spec (v := v) a c), leftMulMatrix_bE]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, spec_X, spec_C]; rfl

theorem toMatrix_sigmaLin :
    LinearMap.toMatrix (bE (v := v)) (bE (v := v)) (sigmaLin (v := v) σ) = (Mσ K L σ).map (algebraMap K F) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, sigmaLin_apply, bE_apply, sigmaTensor_tmul]
  have hσ : σ (bK K L j) = ∑ i', Mσ K L σ i' j • bK K L i' := by
    conv_lhs => rw [← (bK K L).sum_repr (σ (bK K L j))]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Mσ, LinearMap.toMatrix_apply]; rfl
  rw [hσ, sum_smul_tmul_one, repr_sum_smul_bE]

theorem spec_Mσ (a c : E) : (spec (v := v) a c).mapMatrix ((Mσ K L σ).map MvPolynomial.C) =
    LinearMap.toMatrix (bE (v := v)) (bE (v := v)) (sigmaLin (v := v) σ) := by
  rw [toMatrix_sigmaLin]
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, spec_C]

theorem spec_GS (a c : E) : (spec (v := v) a c).mapMatrix (GS K L σ) =
    LinearMap.toMatrix (bE (v := v)) (bE (v := v)) (S (v := v) σ a c) := by
  have h1 : LinearMap.toMatrix (bE (v := v)) (bE (v := v)) (S (v := v) σ a c) =
      LinearMap.toMatrix (bE (v := v)) (bE (v := v)) ((Algebra.lmul F E a) ∘ₗ sigmaLin (v := v) σ) -
        LinearMap.toMatrix (bE (v := v)) (bE (v := v)) (Algebra.lmul F E c) := by
    ext i j
    rw [Matrix.sub_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, S,
      LinearMap.sub_apply, map_sub, Finsupp.sub_apply]
  rw [h1, LinearMap.toMatrix_comp (bE (v := v)) (bE (v := v)) (bE (v := v)), ← Algebra.leftMulMatrix_apply,
    ← Algebra.leftMulMatrix_apply, GS, map_sub, map_mul, spec_MX, spec_MY, spec_Mσ]

theorem det_S [IsGalois K L] (a c : E) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    LinearMap.det (S (v := v) σ a c) = (-1) ^ n * (Algebra.norm F c - Algebra.norm F a) := by
  have h := congrArg (spec (v := v) a c) (det_GS (K := K) (L := L) σ hgen)
  rw [RingHom.map_det, spec_GS, LinearMap.det_toMatrix, map_mul, map_sub, RingHom.map_det, RingHom.map_det,
    spec_MX, spec_MY, ← Algebra.norm_eq_matrix_det, ← Algebra.norm_eq_matrix_det, map_pow, map_neg, map_one] at h
  exact h

theorem norm_det_S [IsGalois K L] (a c : E) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    ‖LinearMap.det (S (v := v) σ a c)‖ = ‖Algebra.norm F a - Algebra.norm F c‖ := by
  rw [det_S σ a c hgen, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← norm_neg, neg_sub]

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

theorem main [IsGalois K L] (a c : E) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hab : Algebra.norm F a ≠ Algebra.norm F c) :
    Measure.map (fun x : E => a * AutomorphicForm.sigmaTensor K L F σ x - c * x) ν =
      ENNReal.ofReal ‖Algebra.norm F a - Algebra.norm F c‖⁻¹ • ν := by
  have hnorm := norm_det_S σ a c hgen
  have hne : LinearMap.det (S (v := v) σ a c) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact hab (sub_eq_zero.1 (norm_eq_zero.1 hnorm.symm))
  have h := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure K v E ν
    (S (v := v) σ a c) hne
  have hfun : ((S (v := v) σ a c : E →ₗ[F] E) : E → E) =
      fun x : E => a * AutomorphicForm.sigmaTensor K L F σ x - c * x := by
    funext x; exact S_apply σ a c x
  rw [hfun, hnorm] at h
  exact h

end SemiLocal

end KcSemiLocalSigmaLinGen
p2m_reactivate "P2MW.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul.KcSemiLocalSigmaLinGen"

end
p2m_reactivate "P2MW.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul.KcSemiLocalSigmaLinGen"

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

open KcSemiLocalSigmaLinGen in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (a b : L ⊗[K] v.adicCompletion K)
    (hab : Algebra.norm (v.adicCompletion K) a ≠ Algebra.norm (v.adicCompletion K) b) :
    Measure.map (fun x : L ⊗[K] v.adicCompletion K =>
        a * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x - b * x) ν =
      ENNReal.ofReal
          ‖Algebra.norm (v.adicCompletion K) a - Algebra.norm (v.adicCompletion K) b‖⁻¹ • ν :=
  main σ ν a b hgen hab

end S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul
end P2MW
export P2MW.S_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul (solution)
