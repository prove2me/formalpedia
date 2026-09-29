-- Prove2me | solution 1 for AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e9c510a3-7d88-510f-9520-89deff878f9e

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_FnTwist
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

noncomputable section

namespace FlatFamilyThroughSection

open NumberField.AdelicHeight IsDedekindDomain FLT.SmoothVectors

section Local

variable {K : Type*} [NormedField K]

private theorem coe_mul (γ g : GL (Fin 2) K) :
    ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

variable [IsUltrametricDist K]

private theorem rowMaxNorm_mul_le (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hentry : ∀ j : Fin 2,
      ‖((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j‖
        ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    intro j
    rw [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 0 j)).trans (le_max_left _ _)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 1 j)).trans (le_max_right _ _)
  exact max_le (hentry 0) (hentry 1)

private theorem rowMaxNorm_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  refine le_antisymm (rowMaxNorm_mul_le g k hk) ?_
  have h := rowMaxNorm_mul_le (g * k) k⁻¹ hk'
  rwa [mul_inv_cancel_right] at h

private theorem norm_det_eq_one_of_integral (k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← coe_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  refine le_antisymm hd ?_
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt hd'
  rw [hprod] at this
  exact lt_irrefl _ this

private theorem finLocalHeight_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  unfold finLocalHeight
  rw [rowMaxNorm_mul_integral g k hk hk', coe_mul, Matrix.det_mul, norm_mul,
    norm_det_eq_one_of_integral k hk hk', mul_one]

end Local

variable {F : Type} [Field F] [NumberField F]

private theorem finHeight_mul_integral (g k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (hk : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1)
    (hk' : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k⁻¹ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1) :
    finHeight F (g * k) = finHeight F g := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_integral _ _ (hk v) fun i j => ?_
  rw [← map_inv]
  exact hk' v i j

private theorem norm_finComponent_le_one_of_mem {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    (∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
        ‖(finComponent (𝓞 F) F v k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
        ‖(finComponent (𝓞 F) F v k⁻¹ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1 := by
  rw [mem_finiteIntegralGL2_iff] at hk
  refine ⟨fun v i j => ?_, fun v i j => ?_⟩
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

private def InK (k : AdelicGL2 (𝓞 F) F) : Prop :=
  glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
    ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))

private theorem adelicHeight_mul_of_inK (g : AdelicGL2 (𝓞 F) F) {k : AdelicGL2 (𝓞 F) F}
    (hk : InK k) : adelicHeight F (g * k) = adelicHeight F g := by
  obtain ⟨h1, h2⟩ := norm_finComponent_le_one_of_mem hk.1
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_mul_rowIsometry F _ hk.2, finHeight_mul_integral _ _ h1 h2]

private theorem finLocalHeight_one' {K : Type*} [NormedField K] :
    finLocalHeight (1 : GL (Fin 2) K) = 1 := by
  unfold finLocalHeight rowMaxNorm
  rw [show ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, Matrix.det_one,
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq, norm_one, norm_zero,
    max_eq_right zero_le_one]
  norm_num

private theorem adelicHeight_one' : adelicHeight F 1 = 1 := by
  unfold adelicHeight
  rw [map_one, map_one, archHeight_one]
  unfold finHeight
  simp only [map_one, finLocalHeight_one', finprod_one, mul_one]

private theorem adelicHeight_eq_one_of_inK {k : AdelicGL2 (𝓞 F) F} (hk : InK k) :
    adelicHeight F k = 1 := by
  have h := adelicHeight_mul_of_inK (1 : AdelicGL2 (𝓞 F) F) hk
  rwa [one_mul, adelicHeight_one'] at h

private theorem inK_of_mem_archRowIsometrySubgroup (w : InfinitePlace F) {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ archRowIsometrySubgroup F w) : InK k := by
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
  refine ⟨?_, fun v => ?_⟩
  · show glFin (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w k₀)) ∈ finiteIntegralGL2 (𝓞 F) F
    rw [glFin_adelicArchGLIncl]
    exact one_mem _
  · show IsRowIsometry (archComponent F v (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w k₀))))
    rw [glArch_adelicArchGLIncl]
    by_cases hvw : v = w
    · subst hvw
      rw [archComponent_archGLIncl_self]
      exact hk₀
    · rw [archComponent_archGLIncl_of_ne F hvw]
      exact isRowIsometry_one

private theorem inK_of_mem_finiteAdelic {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ finiteAdelicGL2Subgroup F)
    (hi : glFin (𝓞 F) F u ∈ finiteIntegralGL2 (𝓞 F) F) : InK u := by
  refine ⟨hi, fun w => ?_⟩
  rw [(mem_finiteAdelicGL2Subgroup_iff F u).mp hu, map_one]
  exact isRowIsometry_one

private def hpow (t : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ := ((adelicHeight F g : ℝ) : ℂ) ^ t

private theorem hpow_mul_inK (t : ℂ) (g : AdelicGL2 (𝓞 F) F) {k : AdelicGL2 (𝓞 F) F} (hk : InK k) :
    hpow t (g * k) = hpow t g := by
  unfold hpow
  rw [adelicHeight_mul_of_inK g hk]

private theorem hpow_of_inK (t : ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : InK k) : hpow t k = 1 := by
  unfold hpow
  rw [adelicHeight_eq_one_of_inK hk, Complex.ofReal_one, Complex.one_cpow]

private theorem hpow_zero (g : AdelicGL2 (𝓞 F) F) : hpow 0 g = 1 := by
  unfold hpow
  exact Complex.cpow_zero _

private theorem isKfSmooth_hpow (t : ℂ) : IsKfSmooth F (hpow t) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer]
  refine Subgroup.isOpen_mono
    (H₁ := Subgroup.comap ((glFin (𝓞 F) F).comp (finiteAdelicGL2Subgroup F).subtype)
      (finiteIntegralGL2 (𝓞 F) F)) ?_ ?_
  · intro u hu
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    refine RightTranslationFn.ext fun g => ?_
    rw [RightTranslationFn.toFun_smul]
    exact hpow_mul_inK t g (inK_of_mem_finiteAdelic u.2 hu)
  · exact (isOpen_finiteLevelZero (𝓞 F) F top_ne_bot).preimage
      ((continuous_glFin (𝓞 F) F).comp continuous_subtype_val)

private theorem isKfSmooth_mul_hpow (t : ℂ) {φ₀ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsKfSmooth F φ₀) :
    IsKfSmooth F (fun g => φ₀ g * hpow t g) :=
  isSmoothVector_rightTranslationFn_mul h (isKfSmooth_hpow t)

private theorem isArchKFinite_mul_hpow (t : ℂ) {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsArchKFinite F φ₀) : IsArchKFinite F (fun g => φ₀ g * hpow t g) := by
  intro w
  obtain ⟨S, hS⟩ := h w
  classical
  let m : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun u => fun x => u x * hpow t x
      map_add' := by
        intro u v
        funext x
        simp only [Pi.add_apply, add_mul]
      map_smul' := by
        intro c u
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc] }
  refine ⟨S.image m, fun k hk => ?_⟩
  have hkK : InK k := inK_of_mem_archRowIsometrySubgroup w hk
  have h2 : m (fun x => φ₀ (x * k)) ∈ Submodule.map m (Submodule.span ℂ (S : Set _)) :=
    Submodule.mem_map_of_mem (hS k hk)
  rw [Submodule.map_span] at h2
  have e : (fun x => (fun g => φ₀ g * hpow t g) (x * k)) = m (fun x => φ₀ (x * k)) := by
    funext x
    show φ₀ (x * k) * hpow t (x * k) = φ₀ (x * k) * hpow t x
    rw [hpow_mul_inK t x hkK]
  rw [e, Finset.coe_image]
  exact h2

private theorem continuous_mul_hpow {φ₀ : AdelicGL2 (𝓞 F) F → ℂ} (hc : Continuous φ₀) (s₀ : ℂ) :
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ₀ p.2 * hpow (p.1 - s₀) p.2) := by
  refine (hc.comp continuous_snd).mul ?_
  unfold hpow
  refine Continuous.cpow ?_ (continuous_fst.sub continuous_const) ?_
  · exact Complex.continuous_ofReal.comp ((continuous_adelicHeight F).comp continuous_snd)
  · intro p
    exact Complex.ofReal_mem_slitPlane.mpr (adelicHeight_pos p.2)

private theorem differentiable_mul_hpow (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (s₀ : ℂ)
    (g : AdelicGL2 (𝓞 F) F) : Differentiable ℂ (fun s => φ₀ g * hpow (s - s₀) g) := by
  unfold hpow
  have h0 : ((adelicHeight F g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (adelicHeight_pos g).ne'
  exact ((differentiable_id.sub_const s₀).const_cpow (Or.inl h0)).const_mul _

private def alphaF (F : Type) [Field F] [NumberField F] : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

private theorem split_fst (hα : ∀ x, 0 < ((alphaF F x : ℝˣ) : ℝ)) (s₀ s : ℂ)
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)
      = (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (s₀ + 1 / 2) * (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (s - s₀) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne')]
  congr 1
  ring

private theorem split_snd (hα : ∀ x, 0 < ((alphaF F x : ℝˣ) : ℝ)) (s₀ s : ℂ)
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (-(s₀ + 1 / 2))
        * (((alphaF F x : ℝˣ) : ℝ) : ℂ) ^ (-(s - s₀)) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne')]
  congr 1
  ring

private theorem isInducedSection_mul_hpow (hα : ∀ x, 0 < ((alphaF F x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ s : ℂ) {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₀ : IsInducedSection (𝓞 F) F (etaFst μ (alphaF F) hα s₀) (etaSnd ν (alphaF F) hα s₀) φ₀) :
    IsInducedSection (𝓞 F) F (etaFst μ (alphaF F) hα s) (etaSnd ν (alphaF F) hα s)
      (fun g => φ₀ g * hpow (s - s₀) g) := by
  intro b hb g

  have hH : ((adelicHeight F (b * g) : ℝ) : ℂ) ^ (s - s₀ - 1 / 2 + 1 / 2)
      = ((etaFst 1 (alphaF F) hα (s - s₀ - 1 / 2) (borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ)
        * ((etaSnd 1 (alphaF F) hα (s - s₀ - 1 / 2) (borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ)
        * ((adelicHeight F g : ℝ) : ℂ) ^ (s - s₀ - 1 / 2 + 1 / 2) :=
    (isInducedSection_adelicHeight_cpow F).2.2 hα (s - s₀ - 1 / 2) b hb g
  have he : s - s₀ - 1 / 2 + 1 / 2 = s - s₀ := by ring
  simp only [etaFst_apply, etaSnd_apply, cpowChar_apply_val, MonoidHom.one_apply, one_mul, he] at hH
  have h₀' := h₀ b hb g
  simp only [etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val] at h₀'
  simp only [hpow, etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val]
  rw [hH, h₀', split_fst hα s₀ s, split_snd hα s₀ s]
  ring

end FlatFamilyThroughSection

end

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (s₀ : ℂ) (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀)
      (_hφ₀K : IsArchKFinite F φ₀)
      (_hφ₀f : IsKfSmooth F φ₀)
      (_hφ₀c : Continuous φ₀),
    ∃ ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      ψ s₀ = φ₀
      ∧ (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      ∧ (∀ s, IsArchKFinite F (ψ s))
      ∧ (∀ s, IsKfSmooth F (ψ s))
      ∧ Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2)
      ∧ (∀ g, Differentiable ℂ (fun s => ψ s g))
      ∧ ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ s k = ψ s' k := by
  intro α hα μ ν s₀ φ₀ hφ₀ hφ₀K hφ₀f hφ₀c
  refine ⟨fun s g => φ₀ g * FlatFamilyThroughSection.hpow (s - s₀) g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext g
    show φ₀ g * FlatFamilyThroughSection.hpow (s₀ - s₀) g = φ₀ g
    rw [sub_self, FlatFamilyThroughSection.hpow_zero, mul_one]
  · intro s
    exact FlatFamilyThroughSection.isInducedSection_mul_hpow (F := F) hα μ ν s₀ s hφ₀
  · intro s
    exact FlatFamilyThroughSection.isArchKFinite_mul_hpow (s - s₀) hφ₀K
  · intro s
    exact FlatFamilyThroughSection.isKfSmooth_mul_hpow (s - s₀) hφ₀f
  · exact FlatFamilyThroughSection.continuous_mul_hpow hφ₀c s₀
  · intro g
    exact FlatFamilyThroughSection.differentiable_mul_hpow φ₀ s₀ g
  · intro s s' k hk1 hk2
    show φ₀ k * FlatFamilyThroughSection.hpow (s - s₀) k = φ₀ k * FlatFamilyThroughSection.hpow (s' - s₀) k
    rw [FlatFamilyThroughSection.hpow_of_inK _ ⟨hk1, hk2⟩, FlatFamilyThroughSection.hpow_of_inK _ ⟨hk1, hk2⟩]

#print axioms solution

end S_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection
end P2MW
export P2MW.S_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection (solution)
