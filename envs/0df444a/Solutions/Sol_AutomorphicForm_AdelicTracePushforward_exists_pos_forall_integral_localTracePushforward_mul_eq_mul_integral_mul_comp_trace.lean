-- Prove2me | solution 1 for AutomorphicForm.AdelicTracePushforward.exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e3056f2d-7535-5c57-97ed-669aaf846a88

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal NNReal
open scoped TensorProduct.RightActions

noncomputable section

namespace TraceCVW

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev m : ℕ := Module.finrank K (LinearMap.ker (Algebra.trace K L))

def kerVec (i : Fin (m K L)) : L := (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)

def bvec : Option (Fin (m K L)) → L := fun o => Option.casesOn' o ((Module.finrank K L : L)⁻¹) (kerVec K L)

theorem finrank_pos' : 0 < Module.finrank K L := Module.finrank_pos

theorem trace_inv_finrank : Algebra.trace K L ((Module.finrank K L : L)⁻¹) = 1 := by
  have h : ((Module.finrank K L : L)⁻¹) = algebraMap K L ((Module.finrank K L : K)⁻¹) := by
    rw [map_inv₀, map_natCast]
  rw [h, Algebra.trace_algebraMap, nsmul_eq_mul]
  have : (Module.finrank K L : K) ≠ 0 := by exact_mod_cast (finrank_pos' K L).ne'
  field_simp

theorem linearIndependent_kerVec : LinearIndependent K (kerVec K L) := by
  have h := (Module.finBasis K (LinearMap.ker (Algebra.trace K L))).linearIndependent
  exact h.map' (LinearMap.ker (Algebra.trace K L)).subtype (Submodule.ker_subtype _)

theorem linearIndependent_bvec : LinearIndependent K (bvec K L) := by
  refine (linearIndependent_kerVec K L).option ?_
  intro hmem
  have hle : Submodule.span K (Set.range (kerVec K L)) ≤ LinearMap.ker (Algebra.trace K L) := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i).2
  have h0 := hle hmem
  rw [LinearMap.mem_ker, trace_inv_finrank] at h0
  exact one_ne_zero h0

theorem card_eq_finrank : Fintype.card (Option (Fin (m K L))) = Module.finrank K L := by
  rw [Fintype.card_option, Fintype.card_fin]
  have h := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
  have hr : LinearMap.range (Algebra.trace K L) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    refine ⟨algebraMap K L (x / Module.finrank K L), ?_⟩
    rw [Algebra.trace_algebraMap, nsmul_eq_mul]
    have : (Module.finrank K L : K) ≠ 0 := by exact_mod_cast (finrank_pos' K L).ne'
    field_simp
  rw [hr, finrank_top, Module.finrank_self] at h
  unfold m
  omega

def basisL : Module.Basis (Option (Fin (m K L))) K L :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_bvec K L) (card_eq_finrank K L)

theorem basisL_apply (o : Option (Fin (m K L))) : basisL K L o = bvec K L o := by
  rw [basisL, coe_basisOfLinearIndependentOfCardEqFinrank]

variable (v : HeightOneSpectrum (𝓞 K))

def basisT : Module.Basis (Option (Fin (m K L))) (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
  (basisL K L).rightBaseChange L

theorem tmul_eq_smul_basisT (o : Option (Fin (m K L))) (c : v.adicCompletion K) :
    bvec K L o ⊗ₜ[K] c = c • basisT K L v o := by
  have h := Module.Basis.rightBaseChange_repr L (basisL K L) o c
  rw [basisL_apply] at h
  have h' := congrArg (basisT K L v).repr.symm h
  rw [basisT, LinearEquiv.symm_apply_apply] at h'
  rw [h', Module.Basis.repr_symm_single, basisT]

theorem localTraceFibre_eq (r : v.adicCompletion K) (w : Fin (m K L) → v.adicCompletion K) :
    AutomorphicForm.AdelicTracePushforward.localTraceFibre K L v r w =
      (basisT K L v).equivFun.symm (fun o => Option.casesOn' o r w) := by
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_option]
  simp only [Option.casesOn'_none, Option.casesOn'_some]
  rw [← tmul_eq_smul_basisT]
  simp_rw [← tmul_eq_smul_basisT]
  rfl

def coordEquiv : ((Fin (m K L) → v.adicCompletion K) × v.adicCompletion K) ≃ₗ[v.adicCompletion K]
    (Option (Fin (m K L)) → v.adicCompletion K) where
  toFun p := fun o => Option.casesOn' o p.2 p.1
  invFun c := (fun i => c (some i), c none)
  map_add' p q := by funext o; cases o <;> rfl
  map_smul' a p := by funext o; cases o <;> rfl
  left_inv p := by rfl
  right_inv c := by funext o; cases o <;> rfl

def T : ((Fin (m K L) → v.adicCompletion K) × v.adicCompletion K) ≃ₗ[v.adicCompletion K]
    (L ⊗[K] v.adicCompletion K) :=
  (coordEquiv K L v).trans (basisT K L v).equivFun.symm

theorem T_apply (p : (Fin (m K L) → v.adicCompletion K) × v.adicCompletion K) :
    T K L v p = AutomorphicForm.AdelicTracePushforward.localTraceFibre K L v p.2 p.1 := by
  rw [localTraceFibre_eq]
  rfl

theorem continuous_T : Continuous (T K L v) :=
  IsModuleTopology.continuous_of_linearMap (T K L v).toLinearMap

theorem continuous_T_symm : Continuous (T K L v).symm :=
  IsModuleTopology.continuous_of_linearMap (T K L v).symm.toLinearMap

def Th : ((Fin (m K L) → v.adicCompletion K) × v.adicCompletion K) ≃ₜ (L ⊗[K] v.adicCompletion K) where
  toEquiv := (T K L v).toEquiv
  continuous_toFun := continuous_T K L v
  continuous_invFun := continuous_T_symm K L v

theorem basisT_eq (o : Option (Fin (m K L))) :
    basisT K L v o = bvec K L o ⊗ₜ[K] (1 : v.adicCompletion K) := by
  have h := tmul_eq_smul_basisT K L v o 1
  rw [one_smul] at h
  exact h.symm

theorem basisT_mul_basisT (o j : Option (Fin (m K L))) :
    basisT K L v o * basisT K L v j =
      ∑ i, (algebraMap K (v.adicCompletion K) ((basisL K L).repr (bvec K L o * bvec K L j) i)) • basisT K L v i := by
  rw [basisT_eq, basisT_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  conv_lhs => rw [← (basisL K L).sum_repr (bvec K L o * bvec K L j)]
  rw [TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basisL_apply, TensorProduct.smul_tmul, tmul_eq_smul_basisT]
  simp only [Algebra.smul_def, mul_one, map_mul]

theorem leftMulMatrix_basisT (o i j : Option (Fin (m K L))) [DecidableEq (Option (Fin (m K L)))] :
    Algebra.leftMulMatrix (basisT K L v) (basisT K L v o) i j =
      algebraMap K (v.adicCompletion K) (Algebra.leftMulMatrix (basisL K L) (bvec K L o) i j) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisL_apply,
    basisT_mul_basisT, (basisT K L v).repr_sum_self]

theorem trace_basisT (o : Option (Fin (m K L))) :
    Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (basisT K L v o) =
      algebraMap K (v.adicCompletion K) (Algebra.trace K L (bvec K L o)) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (basisT K L v), Algebra.trace_eq_matrix_trace (basisL K L),
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, leftMulMatrix_basisT]

theorem trace_bvec_none : Algebra.trace K L (bvec K L none) = 1 := by
  show Algebra.trace K L ((Module.finrank K L : L)⁻¹) = 1
  exact trace_inv_finrank K L

theorem trace_bvec_some (i : Fin (m K L)) : Algebra.trace K L (bvec K L (some i)) = 0 := by
  show Algebra.trace K L (kerVec K L i) = 0
  exact (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i).2

theorem trace_T (p : (Fin (m K L) → v.adicCompletion K) × v.adicCompletion K) :
    Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (T K L v p) = p.2 := by
  have hT : T K L v p = ∑ o : Option (Fin (m K L)), (Option.casesOn' o p.2 p.1 : v.adicCompletion K) • basisT K L v o := by
    show (basisT K L v).equivFun.symm (fun o => Option.casesOn' o p.2 p.1) = _
    rw [Module.Basis.equivFun_symm_apply]
  rw [hT, map_sum]
  simp_rw [map_smul, trace_basisT, smul_eq_mul]
  rw [Fintype.sum_option]
  simp only [Option.casesOn'_none, Option.casesOn'_some, trace_bvec_none, trace_bvec_some, map_one, map_zero,
    mul_one, mul_zero, Finset.sum_const_zero, add_zero]

theorem main
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ (Φ : L ⊗[K] v.adicCompletion K → ℂ) (g : v.adicCompletion K → ℂ),
      IsLocallyConstant Φ → HasCompactSupport Φ → LocallyIntegrable g μ →
      Integrable (fun r => AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v Φ r * g r) μ ∧
      Integrable (fun x => Φ x * g (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x)) ν ∧
      ∫ r, AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v Φ r * g r ∂μ =
        (c : ℂ) * ∫ x, Φ x * g (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) ∂ν := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI : SecondCountableTopology (L ⊗[K] v.adicCompletion K) := (Th K L v).symm.secondCountableTopology

  set μ₀ : Measure (v.adicCompletion K) :=
    ((Measure.addHaar : Measure (v.adicCompletion K))
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
      (Measure.addHaar : Measure (v.adicCompletion K)) with hμ₀
  have hO0 : (Measure.addHaar : Measure (v.adicCompletion K))
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ≠ 0 :=
    ((NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v).measure_ne_zero _
      ⟨0, (v.adicCompletionIntegers K).zero_mem⟩
  have hOtop : (Measure.addHaar : Measure (v.adicCompletion K))
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ≠ ∞ :=
    (isCompact_iff_compactSpace.2
      (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)).measure_lt_top.ne
  haveI hμ₀H : μ₀.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hOtop) (ENNReal.inv_ne_top.mpr hO0)
  set π : Measure (Fin (m K L) → v.adicCompletion K) := Measure.pi fun _ => μ₀ with hπ
  haveI hπH : π.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI hπμ : (π.prod μ).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure π μ

  let Tm : ((Fin (m K L) → v.adicCompletion K) × v.adicCompletion K) ≃ᵐ (L ⊗[K] v.adicCompletion K) :=
    (Th K L v).toMeasurableEquiv
  have hTm : ∀ p, Tm p = T K L v p := fun _ => rfl
  haveI hρ : (Measure.map Tm (π.prod μ)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map (π.prod μ) (T K L v).toAddEquiv (continuous_T K L v) (continuous_T_symm K L v)
  set c : ℝ≥0 := Measure.addHaarScalarFactor (Measure.map Tm (π.prod μ)) ν with hc
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hmapeq : Measure.map Tm (π.prod μ) = c • ν := Measure.isAddLeftInvariant_eq_smul (Measure.map Tm (π.prod μ)) ν
  refine ⟨c, hcpos, fun Φ g hΦ hΦc hg => ?_⟩
  have hcont : Continuous Φ := hΦ.continuous
  obtain ⟨CΦ, hCΦ⟩ := hΦc.exists_bound_of_continuous hcont
  have hCΦ0 : 0 ≤ CΦ := le_trans (norm_nonneg _) (hCΦ 0)

  set G : L ⊗[K] v.adicCompletion K → ℂ :=
    fun x => Φ x * g (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) with hG
  have hGT : ∀ p, G (Tm p) = Φ (Tm p) * g p.2 := fun p => by
    simp only [hG, hTm, trace_T]

  have hKc : IsCompact (Tm ⁻¹' tsupport Φ) := by
    rw [show Tm ⁻¹' tsupport Φ = (Th K L v).symm '' tsupport Φ from
      ((Th K L v).toEquiv.image_symm_eq_preimage _).symm]
    exact hΦc.image (Th K L v).symm.continuous
  set A : Set (Fin (m K L) → v.adicCompletion K) := Prod.fst '' (Tm ⁻¹' tsupport Φ) with hA
  set B : Set (v.adicCompletion K) := Prod.snd '' (Tm ⁻¹' tsupport Φ) with hB
  have hAc : IsCompact A := hKc.image continuous_fst
  have hBc : IsCompact B := hKc.image continuous_snd
  have hsub : Tm ⁻¹' tsupport Φ ⊆ A ×ˢ B := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩

  have hGTm : Integrable (G ∘ Tm) (π.prod μ) := by
    have hmeas : AEStronglyMeasurable (G ∘ Tm) (π.prod μ) := by
      rw [show G ∘ Tm = fun p => Φ (Tm p) * g p.2 from funext fun p => hGT p]
      exact ((hcont.comp (continuous_T K L v)).aestronglyMeasurable).mul hg.aestronglyMeasurable.comp_snd
    have hA_int : Integrable (A.indicator fun _ => (CΦ : ℝ)) π := by
      rw [integrable_indicator_iff hAc.measurableSet]
      exact integrableOn_const (hs := hAc.measure_lt_top.ne)
    have hB_int : Integrable (B.indicator fun r => ‖g r‖) μ := by
      rw [integrable_indicator_iff hBc.measurableSet]
      exact (hg.integrableOn_isCompact hBc).norm
    refine Integrable.mono' (hA_int.mul_prod hB_int) hmeas (Filter.Eventually.of_forall fun p => ?_)
    rw [Function.comp_apply, hGT, norm_mul]
    by_cases hp : p ∈ Tm ⁻¹' tsupport Φ
    · obtain ⟨h1, h2⟩ := hsub hp
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      exact mul_le_mul_of_nonneg_right (hCΦ _) (norm_nonneg _)
    · have h0 : Φ (Tm p) = 0 := image_eq_zero_of_notMem_tsupport hp
      rw [h0, norm_zero, zero_mul]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => hCΦ0) _)
        (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
  have hGmap : Integrable G (Measure.map Tm (π.prod μ)) := (integrable_map_equiv Tm G).mpr hGTm

  have hGν : Integrable G ν := by
    rw [hmapeq] at hGmap
    exact (integrable_smul_measure (by exact_mod_cast hcpos.ne') ENNReal.coe_ne_top).mp hGmap

  have h1 : ∀ r : v.adicCompletion K,
      AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v Φ r * g r = ∫ w, (G ∘ Tm) (w, r) ∂π := by
    intro r
    simp only [Function.comp_apply, hGT]
    rw [integral_mul_const]
    simp only [hTm, T_apply]
    rfl
  refine ⟨?_, hGν, ?_⟩
  ·
    simp_rw [h1]
    exact hGTm.integral_prod_right
  · simp_rw [h1]
    rw [← integral_prod_symm _ hGTm]
    show (∫ z, G (Tm z) ∂π.prod μ) = _
    rw [← integral_map_equiv Tm G, hmapeq, integral_smul_nnreal_measure]
    rw [NNReal.smul_def, Complex.real_smul]

end TraceCVW

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ (Φ : L ⊗[K] v.adicCompletion K → ℂ) (g : v.adicCompletion K → ℂ),
      IsLocallyConstant Φ → HasCompactSupport Φ → LocallyIntegrable g μ →
      Integrable (fun r => AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v Φ r * g r) μ ∧
      Integrable (fun x => Φ x * g (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x)) ν ∧
      ∫ r, AutomorphicForm.AdelicTracePushforward.localTracePushforward K L v Φ r * g r ∂μ =
        (c : ℂ) * ∫ x, Φ x * g (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) x) ∂ν :=
  TraceCVW.main K L v μ ν

end

end S_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace
end P2MW
export P2MW.S_AutomorphicForm_AdelicTracePushforward_exists_pos_forall_integral_localTracePushforward_mul_eq_mul_integral_mul_comp_trace (solution)
