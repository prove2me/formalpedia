-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_map_conj_eq_smul_map_toTensorGL_localHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/23aaaeec-b9d8-578d-8728-5c516bfc778f

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_setLIntegral_mem_closure_conj_map_integers_norm_det_eq_mul_inv_one_sub_mul_inv_one_sub
import Theorems.Thm_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex
import Theorems.Thm_AutomorphicForm_conj_map_includeRight_mem_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar
import Theorems.Thm_AutomorphicForm_relIndex_conj_map_integers_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq
import Theorems.Thm_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_mul_map_eq_scalar_and_forall_isUnit_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_map_conj_eq_smul_map_toTensorGL_localHaar
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem L2A_key (iM iΛ : ℕ) (lamΛ lamM tv ζ : ℝ≥0∞) (r4 rd : ℝ) (hr4 : 0 ≤ r4)
    (hiM : iM ≠ 0) (hscale : lamΛ * (iM : ℝ≥0∞) = lamM * (iΛ : ℝ≥0∞)) (hUM : lamM = tv * ζ)
    (hD : (iM : ℝ) ^ 2 * rd = r4 ^ 2 * (iΛ : ℝ) ^ 2) :
    lamΛ * ENNReal.ofReal r4 = tv * ENNReal.ofReal (Real.sqrt rd) * ζ := by
  have h1 : (iM : ℝ) * Real.sqrt rd = r4 * (iΛ : ℝ) := by
    have ha : Real.sqrt ((iM : ℝ) ^ 2 * rd) = (iM : ℝ) * Real.sqrt rd := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hb : Real.sqrt (r4 ^ 2 * (iΛ : ℝ) ^ 2) = r4 * (iΛ : ℝ) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr4, Real.sqrt_sq (by positivity)]
    rw [← ha, ← hb, hD]
  have h2 : (iM : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt rd) = ENNReal.ofReal r4 * (iΛ : ℝ≥0∞) := by
    have := congrArg ENNReal.ofReal h1
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hr4, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast] at this
    exact this
  have hiM0 : (iM : ℝ≥0∞) ≠ 0 := by exact_mod_cast hiM
  have hiMT : (iM : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top iM
  have h3 : lamΛ * ENNReal.ofReal r4 * (iM : ℝ≥0∞) = tv * ENNReal.ofReal (Real.sqrt rd) * ζ * (iM : ℝ≥0∞) := by
    calc lamΛ * ENNReal.ofReal r4 * (iM : ℝ≥0∞) = lamΛ * (iM : ℝ≥0∞) * ENNReal.ofReal r4 := by ring
      _ = lamM * (iΛ : ℝ≥0∞) * ENNReal.ofReal r4 := by rw [hscale]
      _ = tv * ζ * (ENNReal.ofReal r4 * (iΛ : ℝ≥0∞)) := by rw [hUM]; ring
      _ = tv * ζ * ((iM : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt rd)) := by rw [h2]
      _ = tv * ENNReal.ofReal (Real.sqrt rd) * ζ * (iM : ℝ≥0∞) := by ring
  exact (ENNReal.mul_left_inj hiM0 hiMT).mp h3

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
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y)
    (hmap : letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ =
          tv • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v))
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

  have hCC := AutomorphicForm.conj_map_includeRight_mem_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar K L h2 σ hgen δ₀ c u hN hns v τ hτ tv y hy hmap

  obtain ⟨hiM, hiΛ, hscale⟩ := AutomorphicForm.setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex K L h2 σ hgen δ₀ c u hN hns v τ hτ y hCC ι b hb hbspan _ _ rfl rfl
  have hUM := AutomorphicForm.setLIntegral_mem_closure_conj_map_integers_norm_det_eq_mul_inv_one_sub_mul_inv_one_sub K L h2 σ hgen δ₀ c u hN hns v τ hτ tv y hy hmap _ rfl
  have hD13 := AutomorphicForm.relIndex_conj_map_integers_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq K L h2 σ hgen δ₀ hι b hb hbspan v y hCC
  have h16 : ‖(16 : v.adicCompletion K)‖ = ‖(4 : v.adicCompletion K)‖ ^ 2 := by
    rw [← norm_pow]; norm_num
  rw [h16] at hD13
  exact L2A_key _ _ _ _ _ _ _ _ (norm_nonneg _) hiM hscale hUM hD13

end S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_map_conj_eq_smul_map_toTensorGL_localHaar
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_map_conj_eq_smul_map_toTensorGL_localHaar (solution)
