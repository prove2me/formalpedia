-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/44ecb04d-b394-5f81-a987-52928cba9bb0

import Mathlib
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple
import Theorems.Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_twistedCentralizer_scalar_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

namespace S6b

open AutomorphicForm

theorem val_mul_apply {R : Type*} [CommRing R] (x y : GL (Fin 2) R) (i j : Fin 2) :
    ((x * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (x : Matrix (Fin 2) (Fin 2) R) i 0 * (y : Matrix (Fin 2) (Fin 2) R) 0 j +
        (x : Matrix (Fin 2) (Fin 2) R) i 1 * (y : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem scalar_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (c : R) := rfl
  simp only [Units.val_mul, h]
  exact (Matrix.scalar_commute (c : R) (fun r' => mul_comm _ _) _).eq

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) z) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem pow_apply_zero_zero_of_diag {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (h01 : M 0 1 = 0) (h10 : M 1 0 = 0) (n : ℕ) :
    (M ^ n) 0 0 = (M 0 0) ^ n ∧ (M ^ n) 0 1 = 0 ∧ (M ^ n) 1 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h00, h01', h10'⟩ := ih
    rw [pow_succ, pow_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.mul_apply, Fin.sum_univ_two, h00, h10, mul_zero, add_zero]
    · rw [Matrix.mul_apply, Fin.sum_univ_two, h01, h01', mul_zero, zero_mul, add_zero]
    · rw [Matrix.mul_apply, Fin.sum_univ_two, h10', h10, zero_mul, mul_zero, add_zero]

def diagSubalgebra (R : Type*) [CommRing R] : Subalgebra R (Matrix (Fin 2) (Fin 2) R) where
  carrier := {M | M 0 1 = 0 ∧ M 1 0 = 0}
  mul_mem' := by
    rintro A B ⟨hA01, hA10⟩ ⟨hB01, hB10⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_apply, Fin.sum_univ_two, hA01, hB01, mul_zero, zero_mul, add_zero]
    · rw [Matrix.mul_apply, Fin.sum_univ_two, hA10, hB10, zero_mul, mul_zero, add_zero]
  add_mem' := by
    rintro A B ⟨hA01, hA10⟩ ⟨hB01, hB10⟩
    exact ⟨by rw [Matrix.add_apply, hA01, hB01, add_zero], by rw [Matrix.add_apply, hA10, hB10, add_zero]⟩
  algebraMap_mem' := by
    intro r
    refine ⟨?_, ?_⟩ <;> simp [Matrix.algebraMap_matrix_apply]

theorem integral_map_subgroupCast {G : Type*} [Group G] [TopologicalSpace G]
    (H₁ H₂ : Subgroup G) (e : H₂ = H₁) (τ : @Measure H₁ (borel H₁)) (g : G → ℝ) :
    ∫ t : H₂, g (t : G) ∂(@Measure.map H₁ H₂ (borel H₁) (borel H₂)
        (fun t => ⟨(t : G), e.symm ▸ t.2⟩) τ) =
      ∫ t : H₁, g (t : G) ∂τ := by
  subst e
  exact congrArg (fun ν => ∫ t : H₂, g (t : G) ∂ν) (@Measure.map_id H₂ (borel H₂) τ)

theorem isHaarMeasure_map_subgroupCast {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H₁ H₂ : Subgroup G) (e : H₂ = H₁) (τ : @Measure H₁ (borel H₁))
    (hτ : @Measure.IsHaarMeasure H₁ _ _ (borel H₁) τ) :
    @Measure.IsHaarMeasure H₂ _ _ (borel H₂) (@Measure.map H₁ H₂ (borel H₁) (borel H₂)
        (fun t => ⟨(t : G), e.symm ▸ t.2⟩) τ) := by
  subst e
  exact (@Measure.map_id H₂ (borel H₂) τ).symm ▸ hτ

theorem map_subgroupCast_apply_preimage {G : Type*} [Group G] [TopologicalSpace G]
    (H₁ H₂ : Subgroup G) (e : H₂ = H₁) (τ : @Measure H₁ (borel H₁)) (S : Set G) :
    (@Measure.map H₁ H₂ (borel H₁) (borel H₂) (fun t => ⟨(t : G), e.symm ▸ t.2⟩) τ) (Subtype.val ⁻¹' S) =
      τ (Subtype.val ⁻¹' S) := by
  subst e
  exact congrArg (fun ν => ν (Subtype.val ⁻¹' S)) (@Measure.map_id H₂ (borel H₂) τ)

section sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_includeRight (σ : L ≃ₐ[K] L) (a : A) :
    sigmaTensor K L A σ (Algebra.TensorProduct.includeRight (R := K) (A := L) a) =
      Algebra.TensorProduct.includeRight (R := K) (A := L) a := by
  change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) ((1 : L) ⊗ₜ a) = (1 : L) ⊗ₜ a
  rw [Algebra.TensorProduct.map_tmul]
  simp

theorem sigmaGL_toTensorGL (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A γ) = toTensorGL K L A γ := by
  apply Units.ext
  ext i j
  change sigmaTensor K L A σ (Algebra.TensorProduct.includeRight ((γ : Matrix (Fin 2) (Fin 2) A) i j)) =
    Algebra.TensorProduct.includeRight ((γ : Matrix (Fin 2) (Fin 2) A) i j)
  exact sigmaTensor_includeRight K L A σ _

def P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod

theorem P_succ (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ δ (n + 1) = P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] δ := by
  simp only [P, List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

theorem normString_eq_P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = P K L A σ δ (Module.finrank K L) := rfl

theorem iterate_sigmaGL_mul (σ : L ≃ₐ[K] L) (n : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] (x * y) = (⇑(sigmaGL K L A σ))^[n] x * (⇑(sigmaGL K L A σ))^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem P_mul_of_central (σ : L ≃ₐ[K] L) (t δ : GL (Fin 2) (L ⊗[K] A))
    (ht : sigmaGL K L A σ t = t) (hc : ∀ g : GL (Fin 2) (L ⊗[K] A), t * g = g * t) (n : ℕ) :
    P K L A σ (t * δ) n = t ^ n * P K L A σ δ n := by
  have hit : ∀ k : ℕ, (⇑(sigmaGL K L A σ))^[k] t = t := fun k => Function.iterate_fixed ht k
  induction n with
  | zero => simp [P]
  | succ n ih =>
    rw [P_succ, P_succ, ih, iterate_sigmaGL_mul, hit, pow_succ]

    rw [mul_assoc, mul_assoc, ← mul_assoc (P K L A σ δ n), ← hc (P K L A σ δ n), mul_assoc]

end sigma

theorem exists_nhds_root (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) (ha : (a : v.adicCompletion K) ≠ 1) (n : ℕ) (hn : 0 < n) :
    ∀ V ∈ nhds (1 : v.adicCompletion K), ∃ W ∈ nhds (1 : v.adicCompletion K),
      ∀ ε : (v.adicCompletion K)ˣ, (ε : v.adicCompletion K) ∈ W →
        ∃ η : (v.adicCompletion K)ˣ, (η : v.adicCompletion K) ∈ V ∧ η ^ n = ε := by
  intro V hV
  set γ₀ : GL (Fin 2) (v.adicCompletion K) := diagUnits2 a 1 with hγ₀
  have hγ₀val : (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![(a : v.adicCompletion K), 0; 0, 1] := by
    rw [hγ₀, LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl
  have hreg : IsRegularSemisimple γ₀ := by
    show IsUnit _
    rw [hγ₀val, Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    have : ((a : v.adicCompletion K) + 1) ^ 2 - 4 * ((a : v.adicCompletion K) * 1 - 0 * 0) =
        ((a : v.adicCompletion K) - 1) ^ 2 := by ring
    rw [this]
    exact IsUnit.pow 2 (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ha))

  have hV' : {g : GL (Fin 2) (v.adicCompletion K) | (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 ∈ V} ∈
      nhds (1 : GL (Fin 2) (v.adicCompletion K)) := by
    have hc : Continuous fun g : GL (Fin 2) (v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 :=
      Units.continuous_val.matrix_elem 0 0
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨W₂, hW₂, hroot⟩ :=
    AutomorphicForm.exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple K v γ₀ hreg 1 n hn _ hV'

  have hsc : Continuous fun ε : (v.adicCompletion K)ˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) ε : GL (Fin 2) (v.adicCompletion K)) := by
    rw [Units.continuous_iff]
    constructor
    · refine ((continuous_pi fun _ : Fin 2 => Units.continuous_val).matrix_diagonal).congr fun ε => ?_
      rfl
    · refine ((continuous_pi fun _ : Fin 2 => (Units.continuous_coe_inv : Continuous fun u : (v.adicCompletion K)ˣ => ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))).matrix_diagonal).congr fun ε => ?_
      show Matrix.diagonal (fun _ : Fin 2 => ((ε⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
        (((Matrix.GeneralLinearGroup.scalar (Fin 2) ε)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
      rw [← map_inv]
      rfl
  have hW₁ : (fun ε : (v.adicCompletion K)ˣ => Matrix.GeneralLinearGroup.scalar (Fin 2) ε) ⁻¹' W₂ ∈
      nhds (1 : (v.adicCompletion K)ˣ) :=
    hsc.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hW₂)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hW₁
  obtain ⟨W, hW, hWsub⟩ := hW₁
  refine ⟨W, by simpa using hW, fun ε hε => ?_⟩
  have hεW : Matrix.GeneralLinearGroup.scalar (Fin 2) ε ∈ W₂ := hWsub hε
  have hcent : Matrix.GeneralLinearGroup.scalar (Fin 2) ε ∈ localCentralizer K v γ₀ := by
    rw [Subgroup.mem_centralizer_iff]
    rintro g rfl
    exact (scalar_comm ε γ₀).symm
  obtain ⟨β, hβV, hβadj, hβpow⟩ := hroot _ hεW hcent
  rw [map_one, inv_one, one_mul] at hβpow

  have hβdiag : (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∈ diagSubalgebra (v.adicCompletion K) := by
    refine (Algebra.adjoin_le ?_) hβadj
    rintro M rfl
    refine ⟨?_, ?_⟩
    · rw [hγ₀val]; rfl
    · rw [hγ₀val]; rfl
  obtain ⟨hβ01, hβ10⟩ := hβdiag
  obtain ⟨hpow00, -, -⟩ := pow_apply_zero_zero_of_diag _ hβ01 hβ10 n
  have hβu : IsUnit ((β : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0) := by
    have hdet : IsUnit (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det := Matrix.isUnits_det_units β
    rw [Matrix.det_fin_two, hβ01, hβ10, mul_zero, sub_zero] at hdet
    exact (IsUnit.mul_iff.mp hdet).1
  refine ⟨hβu.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]; exact hβV
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← hpow00, ← Units.val_pow_eq_pow_val, hβpow]
    rfl

theorem continuous_scalar (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun ε : Rˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) ε : GL (Fin 2) R) := by
  rw [Units.continuous_iff]
  constructor
  · refine ((continuous_pi fun _ : Fin 2 => Units.continuous_val).matrix_diagonal).congr fun ε => ?_
    rfl
  · refine ((continuous_pi fun _ : Fin 2 => (Units.continuous_coe_inv : Continuous fun u : Rˣ => ((u⁻¹ : Rˣ) : R))).matrix_diagonal).congr fun ε => ?_
    show Matrix.diagonal (fun _ : Fin 2 => ((ε⁻¹ : Rˣ) : R)) =
      (((Matrix.GeneralLinearGroup.scalar (Fin 2) ε)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
    rw [← map_inv]
    rfl

theorem toTensorGL_scalar (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (z : Aˣ) :
    toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom : A →* L ⊗[K] A) z) :=
  map_scalar _ z

end S6b

open S6b AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) (ha : (a : v.adicCompletion K) ≠ 1)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv) :
    ∃ W ∈ nhds (1 : v.adicCompletion K), ∀ ε : (v.adicCompletion K)ˣ, (ε : v.adicCompletion K) ∈ W →
      ∀ (b : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) →
        ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)),
          τ'.IsHaarMeasure → τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 →
        ∀ J : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ δ τ' φv J →
          ∃ δ' : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
            AutomorphicForm.normString K L (v.adicCompletion K) σ δ' =
              AutomorphicForm.toTensorGL K L (v.adicCompletion K)
                (Matrix.GeneralLinearGroup.scalar (Fin 2) (b * ε) * diagUnits2 a 1) ∧
            ∃ τ'' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ'),
              τ''.IsHaarMeasure ∧ τ'' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 ∧
              AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ δ' τ'' φv J := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)

  obtain ⟨V₀, hV₀, hinv⟩ :=
    IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hφv.1 hφv.2
  have h1V₀ : (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ V₀ := mem_of_mem_nhds hV₀

  set f : v.adicCompletion K →+* L ⊗[K] v.adicCompletion K :=
    (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom with hf
  have hfc : Continuous f := by
    have h := IsModuleTopology.continuous_of_linearMap
      (Algebra.linearMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K))
    exact h
  have hθc : Continuous fun ε : (v.adicCompletion K)ˣ =>
      toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) ε) := by
    have h1 : Continuous (toTensorGL K L (v.adicCompletion K)) := by
      refine Continuous.units_map _ ?_
      exact continuous_id.matrix_map hfc
    exact h1.comp (continuous_scalar (v.adicCompletion K))
  have hpre : (fun ε : (v.adicCompletion K)ˣ =>
      toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) ε)) ⁻¹' V₀ ∈
      nhds (1 : (v.adicCompletion K)ˣ) :=
    hθc.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hV₀)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hpre
  obtain ⟨V, hV, hVsub⟩ := hpre

  obtain ⟨W, hW, hroot⟩ := S6b.exists_nhds_root K v a ha (Module.finrank K L) Module.finrank_pos V (by simpa using hV)
  refine ⟨W, hW, ?_⟩
  intro ε hε b δ hN τ' hτ' hτ'1 J hJ
  obtain ⟨η, hηV, hηpow⟩ := hroot ε hε

  set c : (L ⊗[K] v.adicCompletion K)ˣ := Units.map (f : v.adicCompletion K →* L ⊗[K] v.adicCompletion K) η with hc
  set t : GL (Fin 2) (L ⊗[K] v.adicCompletion K) := Matrix.GeneralLinearGroup.scalar (Fin 2) c with ht
  have hts : toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = t := by
    rw [ht, hc]; exact toTensorGL_scalar K L (v.adicCompletion K) η
  have htV₀ : t ∈ V₀ := by rw [← hts]; exact hVsub hηV
  have htc : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K), t * g = g * t := fun g => scalar_comm c g
  have htσ : sigmaGL K L (v.adicCompletion K) σ t = t := by
    rw [← hts]; exact sigmaGL_toTensorGL K L (v.adicCompletion K) σ _
  have hinvφ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K), φv (t * g) = φv g := by
    intro g
    have := hinv t htV₀ 1 h1V₀ g
    rwa [mul_one] at this
  have hconj : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      x⁻¹ * (t * δ) * sigmaGL K L (v.adicCompletion K) σ x =
        t * (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) := by
    intro x
    rw [← mul_assoc x⁻¹ t δ, ← htc x⁻¹]
    simp only [mul_assoc]
  have hTw : twistedCentralizer K L (v.adicCompletion K) σ (t * δ) =
      twistedCentralizer K L (v.adicCompletion K) σ δ :=
    AutomorphicForm.twistedCentralizer_scalar_mul K L (v.adicCompletion K) σ c δ
  refine ⟨t * δ, ?_, ?_⟩
  ·
    rw [normString_eq_P, P_mul_of_central K L (v.adicCompletion K) σ t δ htσ htc, ← normString_eq_P, hN,
      ← hts, ← map_pow, ← map_pow, hηpow, ← map_mul, ← mul_assoc, ← map_mul, mul_comm ε b]
  ·
    refine ⟨@Measure.map _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (twistedCentralizerBorel K L (v.adicCompletion K) σ (t * δ))
        (fun s => ⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), hTw.symm ▸ s.2⟩) τ', ?_, ?_, ?_⟩
    · exact isHaarMeasure_map_subgroupCast _ _ hTw τ' hτ'
    · rw [map_subgroupCast_apply_preimage _ _ hTw τ']; exact hτ'1
    · obtain ⟨s, ⟨hs0, hsm, hsc, hsint⟩, hJeq⟩ := hJ
      refine ⟨s, ⟨hs0, hsm, hsc, ?_⟩, ?_⟩
      · intro x hx
        rw [hconj, hinvφ] at hx
        rw [integral_map_subgroupCast _ _ hTw τ' (fun g => s (g * x))]
        exact hsint x hx
      · rw [hJeq]
        congr 1
        funext x
        rw [hconj, hinvφ]

end S_AutomorphicForm_exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2 (solution)
