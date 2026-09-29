-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0bd771dc-8168-5f4d-886c-7b6835af4340

import Theorems.Thm_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_mul_map_eq_scalar_and_forall_isUnit_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
import Theorems.Thm_AutomorphicForm_isUnit_of_mem_twistedCommutant_map_of_ne_zero_of_not_isSigmaConjugate_scalar_tensorPlace
import Theorems.Thm_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_det_mem_integers_mul_relIndex_of_not_isSigmaConjugate_scalar
import Theorems.Thm_AutomorphicForm_setLIntegral_mem_closure_det_mem_integers_norm_det_eq_mul_inv_sub_one_mul_inv_one_sub_of_not_isSigmaConjugate_scalar
import Theorems.Thm_AutomorphicForm_absNorm_sq_mul_relIndex_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq_of_forall_isUnit
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem L2B_key (iM iΛ : ℕ) (lamΛ lamM tv : ℝ≥0∞) (qn : ℕ) (hqn : 2 ≤ qn) (n4 rd : ℝ) (hn4 : 0 ≤ n4) (hrd : 0 ≤ rd)
    (hiM : iM ≠ 0) (hscale : lamΛ * (iM : ℝ≥0∞) = lamM * (iΛ : ℝ≥0∞))
    (hUM : lamM = tv * (((qn : ℕ) : ℝ≥0∞) - 1)⁻¹ * (1 - ((qn : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹)
    (hD : ((qn : ℕ) : ℝ) ^ 2 * (iM : ℝ) ^ 2 * rd = n4 ^ 2 * (iΛ : ℝ) ^ 2) :
    lamΛ * ENNReal.ofReal n4 =
      tv * ENNReal.ofReal (Real.sqrt rd) *
        ((1 - ((qn : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹ * (1 - ((qn : ℕ) : ℝ≥0∞) ^ (1 - (2 : ℝ)))⁻¹) := by
  set q : ℝ≥0∞ := ((qn : ℕ) : ℝ≥0∞) with hq
  have hq0 : q ≠ 0 := by rw [hq]; exact_mod_cast (show qn ≠ 0 by omega)
  have hqT : q ≠ ⊤ := by rw [hq]; exact ENNReal.natCast_ne_top qn
  have hq1 : 1 < q := by rw [hq]; exact_mod_cast (show 1 < qn by omega)

  have h1 : ((qn : ℕ) : ℝ) * (iM : ℝ) * Real.sqrt rd = n4 * (iΛ : ℝ) := by
    have ha : Real.sqrt ((((qn : ℕ) : ℝ) * (iM : ℝ)) ^ 2 * rd) = ((qn : ℕ) : ℝ) * (iM : ℝ) * Real.sqrt rd := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hb : Real.sqrt (n4 ^ 2 * (iΛ : ℝ) ^ 2) = n4 * (iΛ : ℝ) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hn4, Real.sqrt_sq (by positivity)]
    rw [← ha, ← hb, ← hD]; ring_nf
  have h2 : q * (iM : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt rd) = ENNReal.ofReal n4 * (iΛ : ℝ≥0∞) := by
    have := congrArg ENNReal.ofReal h1
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hn4,
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at this
    rw [hq]; exact this
  have hiM0 : (iM : ℝ≥0∞) ≠ 0 := by exact_mod_cast hiM
  have hiMT : (iM : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top iM

  have hpow : q ^ (1 - (2 : ℝ)) = q⁻¹ := by
    rw [show (1 - (2 : ℝ)) = -1 by norm_num, ENNReal.rpow_neg_one]
  have hsub0 : q - 1 ≠ 0 := by
    intro h; rw [tsub_eq_zero_iff_le] at h; exact not_le.mpr hq1 h
  have hsubT : q - 1 ≠ ⊤ := ENNReal.sub_ne_top hqT
  have hz : (q - 1)⁻¹ * q = (1 - q ^ (1 - (2 : ℝ)))⁻¹ := by
    rw [hpow]
    have h3 : (q - 1) * q⁻¹ = 1 - q⁻¹ := by
      rw [ENNReal.sub_mul (fun _ _ => ENNReal.inv_ne_top.mpr hq0), ENNReal.mul_inv_cancel hq0 hqT, one_mul]
    rw [← h3, ENNReal.mul_inv (Or.inl hsub0) (Or.inl hsubT), inv_inv]
  have h3 : lamΛ * ENNReal.ofReal n4 * (iM : ℝ≥0∞) =
      tv * ENNReal.ofReal (Real.sqrt rd) * ((1 - q ^ (-(2 : ℝ)))⁻¹ * (1 - q ^ (1 - (2 : ℝ)))⁻¹) * (iM : ℝ≥0∞) := by
    rw [← hz]
    calc lamΛ * ENNReal.ofReal n4 * (iM : ℝ≥0∞) = lamΛ * (iM : ℝ≥0∞) * ENNReal.ofReal n4 := by ring
      _ = lamM * (iΛ : ℝ≥0∞) * ENNReal.ofReal n4 := by rw [hscale]
      _ = lamM * (ENNReal.ofReal n4 * (iΛ : ℝ≥0∞)) := by ring
      _ = lamM * (q * (iM : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt rd)) := by rw [h2]
      _ = tv * (q - 1)⁻¹ * (1 - q ^ (-(2 : ℝ)))⁻¹ * (q * (iM : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt rd)) := by rw [hUM]
      _ = tv * ENNReal.ofReal (Real.sqrt rd) * ((1 - q ^ (-(2 : ℝ)))⁻¹ * ((q - 1)⁻¹ * q)) * (iM : ℝ≥0∞) := by ring
  exact (ENNReal.mul_left_inj hiM0 hiMT).mp h3

set_option maxHeartbeats 3200000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : HeightOneSpectrum (𝓞 K))
    (τ : Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτ : τ.IsHaarMeasure) (tv : ℝ≥0∞)
    (hnsc : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (hshell : τ {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        tv +
          τ {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b)) :
    (∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) |
          ∃ a : ι → v.adicCompletion K, (∀ k, a k ∈ v.adicCompletionIntegers K) ∧
            ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k)}, ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ∂τ) *
        ENNReal.ofReal ‖(4 : v.adicCompletion K)‖ =
      tv * ENNReal.ofReal (Real.sqrt ‖algebraMap K (v.adicCompletion K) (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det‖) *
        ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - (2 : ℝ)))⁻¹) := by

  have hz := (AutomorphicForm.exists_mul_map_eq_scalar_and_forall_isUnit_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar K L h2 σ hgen δ₀ c u hN hns).1
  let D₀ : Submodule K (Matrix (Fin 2) (Fin 2) L) :=
    { carrier := {X | X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ}
      add_mem' := by
        intro X Y hX hY
        simp only [Set.mem_setOf_eq] at hX hY ⊢
        rw [add_mul, Matrix.map_add (σ : L → L) (map_add σ), mul_add, hX, hY]
      zero_mem' := by
        simp only [Set.mem_setOf_eq, zero_mul]
        rw [Matrix.map_zero (σ : L → L) (map_zero σ), mul_zero]
      smul_mem' := by
        intro a X hX
        simp only [Set.mem_setOf_eq] at hX ⊢
        have hmap' : (a • X).map σ = a • X.map σ := by
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
        rw [smul_mul_assoc, hmap', mul_smul_comm, hX] }
  have hmem : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X ∈ D₀ ↔ X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ := fun X => Iff.rfl
  set e₁ : Fin 2 → L := Pi.single 0 1 with he₁
  have he₁0 : e₁ ≠ 0 := by
    intro h; have := congrFun h 0; simp [he₁] at this
  have huniq := AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two K L h2 σ hgen δ₀ hz hns e₁ he₁0
  let φ : D₀ →ₗ[K] (Fin 2 → L) :=
    { toFun := fun X => (X : Matrix (Fin 2) (Fin 2) L).mulVec e₁
      map_add' := by intro X Y; simp [Matrix.add_mulVec]
      map_smul' := by intro a X; simp [Matrix.smul_mulVec] }
  have hφ : Function.Bijective φ := by
    refine ⟨fun X Y hXY => ?_, fun w => ?_⟩
    · obtain ⟨Z, hZ, hZu⟩ := huniq ((X : Matrix (Fin 2) (Fin 2) L).mulVec e₁)
      have h1 : (X : Matrix (Fin 2) (Fin 2) L) = Z := hZu _ ⟨(hmem _).mp X.2, rfl⟩
      have h2' : (Y : Matrix (Fin 2) (Fin 2) L) = Z := hZu _ ⟨(hmem _).mp Y.2, hXY.symm⟩
      exact Subtype.ext (h1.trans h2'.symm)
    · obtain ⟨Z, ⟨hZ, hZw⟩, -⟩ := huniq w
      exact ⟨⟨Z, (hmem Z).mpr hZ⟩, hZw⟩
  let Φ : D₀ ≃ₗ[K] (Fin 2 → L) := LinearEquiv.ofBijective φ hφ
  have hrank : Module.finrank K D₀ = 4 := by
    rw [Φ.finrank_eq, Module.finrank_pi_fintype K]
    simp [h2]
  have hD : Submodule.span K (Set.range b) = D₀ := by
    ext X; exact ((hbspan X).symm.trans (hmem X).symm)
  have hι : Fintype.card ι = 4 := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hb, Set.finrank, hD, hrank]

  have hdiv := AutomorphicForm.isUnit_of_mem_twistedCommutant_map_of_ne_zero_of_not_isSigmaConjugate_scalar_tensorPlace K L h2 σ hgen δ₀ c u hN hns v τ hτ tv hnsc hshell ι b hb hbspan

  have hD := AutomorphicForm.absNorm_sq_mul_relIndex_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq_of_forall_isUnit K L h2 σ hgen δ₀ hι b hb hbspan v hdiv

  obtain ⟨hiM, hiΛ, hscale⟩ := AutomorphicForm.setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_det_mem_integers_mul_relIndex_of_not_isSigmaConjugate_scalar K L h2 σ hgen δ₀ c u hN hns v τ hτ tv hnsc hshell ι b hb hbspan
  have hUM := AutomorphicForm.setLIntegral_mem_closure_det_mem_integers_norm_det_eq_mul_inv_sub_one_mul_inv_one_sub_of_not_isSigmaConjugate_scalar K L h2 σ hgen δ₀ c u hN hns v τ hτ tv hnsc hshell ι b hb hbspan
  have h16 : ‖(16 : v.adicCompletion K)‖ = ‖(4 : v.adicCompletion K)‖ ^ 2 := by rw [← norm_pow]; norm_num
  rw [h16] at hD
  have hq2 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega
  exact L2B_key _ _ _ _ _ (Ideal.absNorm v.asIdeal) hq2 ‖(4 : v.adicCompletion K)‖ _ (norm_nonneg _) (norm_nonneg _)
    hiM hscale hUM (by linarith [hD])

end S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar (solution)
