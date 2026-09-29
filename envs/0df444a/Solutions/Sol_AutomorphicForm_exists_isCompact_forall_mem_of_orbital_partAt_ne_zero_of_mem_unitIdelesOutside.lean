-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3e2989fa-f7a0-5915-891a-27f248b21343

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_glArch_centralScalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_mul_diagUnits2
import Theorems.Thm_NumberField_AdeleRing_isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
import Theorems.Thm_NumberField_AdeleRing_isCompact_setOf_sq_mem_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace WindowSupport

theorem det_conj {n : Type} [Fintype n] [DecidableEq n] {R : Type} [CommRing R] (x g : GL n R) :
    Matrix.GeneralLinearGroup.det (x⁻¹ * g * x) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]

theorem continuous_det {n : Type} [Fintype n] [DecidableEq n] {R : Type} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (Matrix.GeneralLinearGroup.det : GL n R → Rˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : (Units.val ∘ (Matrix.GeneralLinearGroup.det : GL n R → Rˣ)) =
        fun g : GL n R => ((g : GL n R) : Matrix n n R).det := by
      funext g; rfl
    rw [h]
    exact Units.continuous_val.matrix_det
  · have h : (fun g : GL n R => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R)) =
        fun g : GL n R => (((g⁻¹ : GL n R)) : Matrix n n R).det := by
      funext g; rw [← map_inv]; rfl
    rw [h]
    exact Units.continuous_coe_inv.matrix_det

theorem det_diagUnits2 {R : Type} [CommRing R] (a b : Rˣ) :
    Matrix.GeneralLinearGroup.det (diagUnits2 a b) = a * b := by
  ext
  simp [Matrix.det_fin_two_of]

end WindowSupport

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfS : ∀ v ∈ S, AutomorphicForm.IsLocalTestFn K v (fS v))
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (τA : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (IA : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ z, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA z) fa (IA z))
    (IF : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ z, ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z v) (fS v) (IF z v)) :
    ∃ T : Set (AdeleRing (𝓞 K) K)ˣ, IsCompact T ∧
      ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) →
        IA (NumberField.Idele.partAt K S z) ≠ 0 →
        (∀ v ∈ S, IF (NumberField.Idele.partAt K S z) v ≠ 0) →
          z ∈ T := by
  classical

  let Ca : Set (InfiniteAdeleRing K)ˣ :=
    (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K)) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))⁻¹ * Matrix.GeneralLinearGroup.det g) '' tsupport fa
  have hCa : IsCompact Ca :=
    hfa.2.isCompact.image (continuous_const.mul WindowSupport.continuous_det)

  let uinv : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v => (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)
  have huinv : ∀ v : HeightOneSpectrum (𝓞 K), (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) * uinv v = 1 := by
    intro v
    have h : (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact h
  have huinv0 : ∀ v : HeightOneSpectrum (𝓞 K), uinv v ≠ 0 := fun v => right_ne_zero_of_mul_eq_one (huinv v)
  let Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K) := fun v =>
    (fun g : GL (Fin 2) (v.adicCompletion K) =>
      ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) * uinv v) '' tsupport (fS v)
  have hCf : ∀ v ∈ S, IsCompact (Cf v) := fun v hv =>
    (hfS v hv).2.isCompact.image
      ((Units.continuous_val.comp WindowSupport.continuous_det).mul continuous_const)
  have hCf0 : ∀ v ∈ S, (0 : v.adicCompletion K) ∉ Cf v := by
    intro v hv h0
    obtain ⟨g, -, hg⟩ := h0
    exact mul_ne_zero (Matrix.GeneralLinearGroup.det g).ne_zero (huinv0 v) hg
  have hBox :=
    NumberField.AdeleRing.isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
      K S Ca hCa Cf hCf hCf0
  refine ⟨_, NumberField.AdeleRing.isCompact_setOf_sq_mem_of_isCompact K _ hBox, ?_⟩
  intro z hzU hIA0 hIF0
  refine ⟨⟨?_, ?_⟩, pow_mem hzU 2⟩
  ·
    have key : ∀ {γ : GL (Fin 2) (InfiniteAdeleRing K)}
        {τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
          (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ)} {I : ℂ},
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA γ τ fa I → I ≠ 0 →
          ∃ x : GL (Fin 2) (InfiniteAdeleRing K), fa (x⁻¹ * γ * x) ≠ 0 := by
      intro γ τ I h hI
      by_contra hx
      push Not at hx
      obtain ⟨w, -, rfl⟩ := h
      exact hI (by simp [hx])
    obtain ⟨x, hx⟩ := key (hIA _) hIA0
    have hz' : (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K)) (NumberField.Idele.partAt K S z) = (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K)) z :=
      Units.ext (NumberField.Idele.partAt_fst K S z)
    refine ⟨x⁻¹ * _ * x, subset_tsupport _ (Function.mem_support.2 hx), ?_⟩
    show ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K)) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))⁻¹ * Matrix.GeneralLinearGroup.det (x⁻¹ * _ * x) = _
    rw [WindowSupport.det_conj, AutomorphicForm.glArch_centralScalar_mul_diagUnits2, map_mul,
      Matrix.GeneralLinearGroup.det_scalar, WindowSupport.det_diagUnits2, map_one, mul_one,
      Fintype.card_fin, hz', map_pow, inv_mul_cancel_comm_assoc]
  ·
    intro v hv
    have key : ∀ {γ : GL (Fin 2) (v.adicCompletion K)}
        {τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)}
        {I : ℂ}, AutomorphicForm.IsOrbitalIntegral K v γ τ (fS v) I → I ≠ 0 →
          ∃ x : GL (Fin 2) (v.adicCompletion K), fS v (x⁻¹ * γ * x) ≠ 0 := by
      intro γ τ I h hI
      by_contra hx
      push Not at hx
      obtain ⟨w, -, rfl⟩ := h
      exact hI (by simp [hx])
    obtain ⟨x, hx⟩ := key (hIF _ v hv) (hIF0 v hv)
    refine ⟨x⁻¹ * _ * x, subset_tsupport _ (Function.mem_support.2 hx), ?_⟩
    show ((Matrix.GeneralLinearGroup.det (x⁻¹ * _ * x) : (v.adicCompletion K)ˣ) : v.adicCompletion K) *
        uinv v = _
    rw [WindowSupport.det_conj, Matrix.GeneralLinearGroup.val_det_apply,
      AutomorphicForm.coe_finComponent_glFin_centralScalar_mul_diagUnits2, Matrix.det_diagonal,
      Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : ((((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := rfl
    have h2 : ((((z ^ 2 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = ((((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) * ((((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) := by
      rw [sq]; rfl
    rw [NumberField.Idele.partAt_snd_of_mem K S z hv, h1, h2, mul_one]
    linear_combination (((((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) * ((((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) * huinv v

end S_AutomorphicForm_exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_of_orbital_partAt_ne_zero_of_mem_unitIdelesOutside (solution)
