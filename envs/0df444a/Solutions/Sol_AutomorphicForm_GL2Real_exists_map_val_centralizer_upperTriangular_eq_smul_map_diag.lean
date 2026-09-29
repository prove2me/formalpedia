-- Prove2me | solution 1 for AutomorphicForm.GL2Real.exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6dcda278-7d6a-52ff-b475-fa4a7dd88636

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
set_option autoImplicit false
open MeasureTheory
p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag.AutomorphicForm.GL2Real"
open Topology

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "upperTriangular"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

private theorem mem_centralizer_upperTriangular_zero_iff (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂)
    (g : GL (Fin 2) ℝ) :
    g ∈ Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) ↔
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  have hγ : ((upperTriangular a₁ a₂ 0 h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, 0; 0, a₂] := rfl
  have hsub : a₁ - a₂ ≠ 0 := sub_ne_zero.2 hne
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [Matrix.GeneralLinearGroup.ext_iff]
  constructor
  · intro hg
    have h01 := hg 0 1
    have h10 := hg 1 0
    simp [Units.val_mul, hγ, Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
    constructor
    · have h1 : (a₁ - a₂) * (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by linarith
      exact (mul_eq_zero.1 h1).resolve_left hsub
    · have h2 : (a₁ - a₂) * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left hsub
  · rintro ⟨h01, h10⟩ i j
    fin_cases i <;> fin_cases j <;> simp [Units.val_mul, hγ, Matrix.mul_apply, Fin.sum_univ_two, h01, h10] <;> ring

private noncomputable def planeMap (a b c d : ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun z := (a * z.1 + b * z.2, c * z.1 + d * z.2)
  map_add' z w := by ext <;> simp <;> ring
  map_smul' t z := by ext <;> simp <;> ring

private theorem
    planeMap_apply (a b c d : ℝ) (z : ℝ × ℝ) : planeMap a b c d z = (a * z.1 + b * z.2, c * z.1 + d * z.2) :=
  rfl

private theorem det_planeMap (a b c d : ℝ) : LinearMap.det (planeMap a b c d) = a * d - b * c := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, planeMap_apply]
  try ring

private theorem
    map_withDensity_eq_self_of_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] E)
    (hL : LinearMap.det L ≠ 0) (g : E → ENNReal) (hg : Measurable g)
    (hgL : ∀ z, g (L z) = ENNReal.ofReal |LinearMap.det L|⁻¹ * g z) :
    Measure.map L (μ.withDensity g) = μ.withDensity g := by
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hdet : 0 < |LinearMap.det L| := abs_pos.2 hL
  have hD0 : ENNReal.ofReal |LinearMap.det L| ≠ 0 := (ENNReal.ofReal_pos.2 hdet).ne'
  have hDtop : ENNReal.ofReal |LinearMap.det L| ≠ ⊤ := ENNReal.ofReal_ne_top
  have hg' : ∀ z, g z = ENNReal.ofReal |LinearMap.det L| * g (L z) := by
    intro z
    rw [hgL z, ENNReal.ofReal_inv_of_pos hdet, ← mul_assoc, ENNReal.mul_inv_cancel hD0 hDtop, one_mul]
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  have hfL : Measurable fun a => f (L a) := hf.comp hLm
  have hgL : Measurable fun a => g (L a) := hg.comp hLm
  have hgf : Measurable fun a => g a * f a := hg.mul hf
  rw [lintegral_map hf hLm, lintegral_withDensity_eq_lintegral_mul _ hg hfL,
    lintegral_withDensity_eq_lintegral_mul _ hg hf]
  simp only [Pi.mul_apply]
  calc ∫⁻ a, g a * f (L a) ∂μ
      = ∫⁻ a, ENNReal.ofReal |LinearMap.det L| * (g (L a) * f (L a)) ∂μ := by
        congr 1
        funext a
        rw [hg' a, mul_assoc]
    _ = ENNReal.ofReal |LinearMap.det L| * ∫⁻ a, g (L a) * f (L a) ∂μ :=
        lintegral_const_mul _ (hgL.mul hfL)
    _ = ENNReal.ofReal |LinearMap.det L| * ∫⁻ b, g b * f b ∂(Measure.map L μ) := by
        rw [lintegral_map hgf hLm]
    _ = ENNReal.ofReal |LinearMap.det L| *
          ∫⁻ b, g b * f b ∂(ENNReal.ofReal |(LinearMap.det L)⁻¹| • μ) := by
        rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := μ) hL]
    _ = ∫⁻ b, g b * f b ∂μ := by
        rw [lintegral_smul_measure, smul_eq_mul, abs_inv, ENNReal.ofReal_inv_of_pos hdet, ← mul_assoc,
          ENNReal.mul_inv_cancel hD0 hDtop, one_mul]

private theorem withDensity_restrict_of_eq_zero_off {α : Type*} [MeasurableSpace α] (μ : Measure α) {D : Set α}
    (hD : MeasurableSet D) (g : α → ENNReal) (hg0 : ∀ x, x ∉ D → g x = 0) :
    (μ.restrict D).withDensity g = μ.withDensity g := by
  rw [← restrict_withDensity hD]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  show μ.withDensity g Dᶜ = 0
  rw [withDensity_apply _ hD.compl, setLIntegral_congr_fun hD.compl (fun x hx => hg0 x hx)]
  simp

private theorem map_planeMap_diag_withDensity (d₁ d₂ : ℝ) (hd : d₁ * d₂ ≠ 0) :
    Measure.map (planeMap d₁ 0 0 d₂) (volume.withDensity (fun α : ℝ × ℝ => ENNReal.ofReal |α.1 * α.2|⁻¹)) =
      volume.withDensity (fun α : ℝ × ℝ => ENNReal.ofReal |α.1 * α.2|⁻¹) := by
  have hdet : LinearMap.det (planeMap d₁ 0 0 d₂) = d₁ * d₂ := by rw [det_planeMap]; ring
  refine map_withDensity_eq_self_of_comp volume (planeMap d₁ 0 0 d₂) (by rw [hdet]; exact hd) _ ?_ ?_
  · exact ((continuous_abs.measurable.comp (measurable_fst.mul measurable_snd)).inv).ennreal_ofReal
  · intro z
    rw [hdet, planeMap_apply, ← ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg _))]
    congr 1
    simp only [zero_mul, add_zero, zero_add]
    rw [← mul_inv, ← abs_mul]
    congr 2
    ring

end AutomorphicForm.GL2Real

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "upperTriangular"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

private theorem continuousOn_matrixInv_isUnit' :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.fun_smul ?_
    (Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin 2) (Fin 2) ℝ))).continuousOn
  exact (Continuous.matrix_det continuous_id).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

private theorem isEmbedding_glVal' : IsEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  Units.isEmbedding_val_mk' continuousOn_matrixInv_isUnit' fun u => (Matrix.coe_units_inv u).symm

private theorem isOpen_range_glVal' : IsOpen (Set.range (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h : Set.range (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) =
      (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det) ⁻¹' {x | x ≠ 0} := by
    ext A
    constructor
    · rintro ⟨u, rfl⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
    · intro hA
      exact (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)
  rw [h]
  exact isOpen_ne.preimage (Continuous.matrix_det continuous_id)

private theorem isOpenEmbedding_glVal' : IsOpenEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨isEmbedding_glVal', isOpen_range_glVal'⟩

private theorem locallyCompactSpace_gl' : LocallyCompactSpace (GL (Fin 2) ℝ) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact isOpenEmbedding_glVal'.locallyCompactSpace

private theorem secondCountableTopology_gl' : SecondCountableTopology (GL (Fin 2) ℝ) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact isEmbedding_glVal'.secondCountableTopology

private theorem continuous_glEntry (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j :=
  isEmbedding_glVal'.continuous.matrix_elem i j

private theorem det_val_ne_zero (g : GL (Fin 2) ℝ) : (g : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

private theorem measurable_of_continuousOn_of_eq_one {P : ℝ × ℝ → GL (Fin 2) ℝ} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hPD : ContinuousOn P D) (hP1 : ∀ α, α ∉ D → P α = 1) :
    @Measurable (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ) P := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  classical
  have h : P = D.piecewise P (fun _ => 1) := by
    funext α
    by_cases hα : α ∈ D
    · simp [Set.piecewise, hα]
    · simp [Set.piecewise, hα, hP1 α hα]
  rw [h]
  exact hPD.measurable_piecewise continuousOn_const hD.measurableSet

private theorem measurable_of_continuousOn_of_eq_zero {w : ℝ × ℝ → ℝ} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hwD : ContinuousOn w D) (hw0 : ∀ α, α ∉ D → w α = 0) : Measurable w := by
  classical
  have h : w = D.piecewise w (fun _ => 0) := by
    funext α
    by_cases hα : α ∈ D
    · simp [Set.piecewise, hα]
    · simp [Set.piecewise, hα, hw0 α hα]
  rw [h]
  exact hwD.measurable_piecewise continuousOn_const hD.measurableSet

private theorem withDensity_ofReal_compl_eq_zero {D : Set (ℝ × ℝ)} (hD : MeasurableSet D) (w : ℝ × ℝ → ℝ)
    (hw0 : ∀ α, α ∉ D → w α = 0) : volume.withDensity (fun α => ENNReal.ofReal (w α)) Dᶜ = 0 := by
  have hEq : Set.EqOn (fun α => ENNReal.ofReal (w α)) (fun _ => (0 : ENNReal)) Dᶜ := by
    intro α hα
    show ENNReal.ofReal (w α) = 0
    rw [hw0 α hα, ENNReal.ofReal_zero]
  rw [withDensity_apply _ hD.compl, setLIntegral_congr_fun hD.compl hEq]
  simp

private theorem exists_map_val_eq_smul_map_of_planeModel (T : Subgroup (GL (Fin 2) ℝ))
    (hT : IsClosed (T : Set (GL (Fin 2) ℝ)))
    (P : ℝ × ℝ → GL (Fin 2) ℝ) (D : Set (ℝ × ℝ)) (hD : IsOpen D) (hPD : ContinuousOn P D)
    (hPT : ∀ α, P α ∈ T) (hP1 : ∀ α, α ∉ D → P α = 1)
    (coord : GL (Fin 2) ℝ → ℝ × ℝ) (hcoord : Continuous coord) (hcP : ∀ α ∈ D, coord (P α) = α)
    (hsurj : ∀ t ∈ T, coord t ∈ D ∧ P (coord t) = t)
    (w : ℝ × ℝ → ℝ) (hwD : ContinuousOn w D) (hwpos : ∀ α ∈ D, 0 < w α) (hw0 : ∀ α, α ∉ D → w α = 0)
    (hinv : ∀ t ∈ T, ∃ L : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ,
      Measure.map L (volume.withDensity (fun α => ENNReal.ofReal (w α))) =
          volume.withDensity (fun α => ENNReal.ofReal (w α)) ∧
        ∀ α ∈ D, t * P α = P (L α))
    (τ : @Measure T (borel T)) (hτ : @Measure.IsHaarMeasure T _ _ (borel T) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map T (GL (Fin 2) ℝ) (borel T) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ) P
          (volume.withDensity (fun α => ENNReal.ofReal (w α))) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  letI : MeasurableSpace T := borel T
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin 2) ℝ) := locallyCompactSpace_gl'
  haveI : SecondCountableTopology (GL (Fin 2) ℝ) := secondCountableTopology_gl'
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : SecondCountableTopology T := IsEmbedding.subtypeVal.secondCountableTopology
  haveI := hτ
  set g : ℝ × ℝ → ENNReal := fun α => ENNReal.ofReal (w α) with hg_def
  have hg : Measurable g := (measurable_of_continuousOn_of_eq_zero hD hwD hw0).ennreal_ofReal
  have hgne : ∀ α ∈ D, g α ≠ 0 := by
    intro α hα
    show ENNReal.ofReal (w α) ≠ 0
    exact (ENNReal.ofReal_pos.2 (hwpos α hα)).ne'
  have hDc : volume.withDensity g Dᶜ = 0 := withDensity_ofReal_compl_eq_zero hD.measurableSet w hw0
  have hae : ∀ᵐ α ∂(volume.withDensity g), α ∈ D := by
    rw [ae_iff]
    exact hDc
  have hPm : Measurable P := measurable_of_continuousOn_of_eq_one hD hPD hP1
  set Q : ℝ × ℝ → T := fun α => ⟨P α, hPT α⟩ with hQ_def
  have hQm : Measurable Q := by
    refine measurable_of_isOpen fun U hU => ?_
    obtain ⟨W, hW, hUW⟩ := isOpen_induced_iff.1 hU
    subst hUW
    have hQW : Q ⁻¹' (Subtype.val ⁻¹' W) = P ⁻¹' W := rfl
    rw [hQW]
    exact hPm hW.measurableSet
  have hvalm : Measurable (Subtype.val : T → GL (Fin 2) ℝ) := continuous_subtype_val.measurable
  have hvalQ : (Subtype.val ∘ Q : ℝ × ℝ → GL (Fin 2) ℝ) = P := rfl
  set m : Measure T := Measure.map Q (volume.withDensity g) with hm_def
  have hmval : Measure.map Subtype.val m = Measure.map P (volume.withDensity g) := by
    rw [hm_def, Measure.map_map hvalm hQm, hvalQ]
  have hm_left : ∀ t : T, Measure.map (fun s : T => t * s) m = m := by
    intro t
    obtain ⟨L, hLinv, hLP⟩ := hinv t t.2
    have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
    have hmul : Measurable (fun s : T => t * s) := (continuous_const.mul continuous_id).measurable
    have hfun : ((fun s : T => t * s) ∘ Q) =ᵐ[volume.withDensity g] (Q ∘ L) := by
      filter_upwards [hae] with α hα
      exact Subtype.ext (hLP α hα)
    rw [hm_def, Measure.map_map hmul hQm, Measure.map_congr hfun, ← Measure.map_map hQm hLm, hLinv]
  have hm_compact : ∀ K : Set T, IsCompact K → m K < ⊤ := by
    intro K hK
    rw [hm_def, Measure.map_apply hQm hK.isClosed.measurableSet]
    have hCc : IsCompact ((fun s : T => coord (s : GL (Fin 2) ℝ)) '' K) :=
      hK.image (hcoord.comp continuous_subtype_val)
    have hCD : (fun s : T => coord (s : GL (Fin 2) ℝ)) '' K ⊆ D := by
      rintro _ ⟨s, -, rfl⟩
      exact (hsurj s.1 s.2).1
    have hsub : Q ⁻¹' K ⊆ (fun s : T => coord (s : GL (Fin 2) ℝ)) '' K ∪ Dᶜ := by
      intro α hα
      by_cases hαD : α ∈ D
      · exact Or.inl ⟨Q α, hα, hcP α hαD⟩
      · exact Or.inr hαD
    obtain ⟨B, hB⟩ := hCc.bddAbove_image (hwD.mono hCD)
    have hgC : ∀ α ∈ (fun s : T => coord (s : GL (Fin 2) ℝ)) '' K, g α ≤ ENNReal.ofReal B := fun α hα =>
      ENNReal.ofReal_le_ofReal (hB (Set.mem_image_of_mem w hα))
    calc volume.withDensity g (Q ⁻¹' K)
        ≤ volume.withDensity g ((fun s : T => coord (s : GL (Fin 2) ℝ)) '' K ∪ Dᶜ) := measure_mono hsub
      _ ≤ volume.withDensity g ((fun s : T => coord (s : GL (Fin 2) ℝ)) '' K) + volume.withDensity g Dᶜ :=
          measure_union_le _ _
      _ = volume.withDensity g ((fun s : T => coord (s : GL (Fin 2) ℝ)) '' K) := by rw [hDc, add_zero]
      _ = ∫⁻ α in (fun s : T => coord (s : GL (Fin 2) ℝ)) '' K, g α :=
          withDensity_apply _ hCc.isClosed.measurableSet
      _ ≤ ∫⁻ _ in (fun s : T => coord (s : GL (Fin 2) ℝ)) '' K, ENNReal.ofReal B :=
          setLIntegral_mono' hCc.isClosed.measurableSet hgC
      _ = ENNReal.ofReal B * volume ((fun s : T => coord (s : GL (Fin 2) ℝ)) '' K) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCc.measure_lt_top
  have hm_open : ∀ U : Set T, IsOpen U → U.Nonempty → m U ≠ 0 := by
    intro U hU hne
    rw [hm_def, Measure.map_apply hQm hU.measurableSet]
    obtain ⟨W, hW, hUW⟩ := isOpen_induced_iff.1 hU
    subst hUW
    have hQW : Q ⁻¹' (Subtype.val ⁻¹' W) = P ⁻¹' W := rfl
    rw [hQW]
    have hVo : IsOpen (D ∩ P ⁻¹' W) := hPD.isOpen_inter_preimage hD hW
    have hVne : (D ∩ P ⁻¹' W).Nonempty := by
      obtain ⟨s, hs⟩ := hne
      refine ⟨coord (s : GL (Fin 2) ℝ), (hsurj s.1 s.2).1, ?_⟩
      show P (coord (s : GL (Fin 2) ℝ)) ∈ W
      rw [(hsurj s.1 s.2).2]
      exact hs
    intro h0
    apply hVo.measure_ne_zero volume hVne
    have h1 : volume.withDensity g (D ∩ P ⁻¹' W) = 0 := measure_mono_null Set.inter_subset_right h0
    rw [withDensity_apply_eq_zero hg] at h1
    have h2 : {α | g α ≠ 0} ∩ (D ∩ P ⁻¹' W) = D ∩ P ⁻¹' W := by
      ext α
      exact ⟨fun h => h.2, fun h => ⟨hgne α h.1, h⟩⟩
    rwa [h2] at h1
  haveI hmHaar : m.IsHaarMeasure :=
    { map_mul_left_eq_self := hm_left
      lt_top_of_isCompact := hm_compact
      open_pos := hm_open }
  have huniq := Measure.isMulLeftInvariant_eq_smul τ m
  refine ⟨τ.haarScalarFactor m, Measure.haarScalarFactor_pos_of_isHaarMeasure τ m, ?_⟩
  conv_lhs => rw [huniq]
  rw [Measure.map_smul]
  exact congrArg (fun ν => τ.haarScalarFactor m • ν) hmval

private theorem coe_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] :=
  rfl

private theorem upperTriangular_zero_mem_centralizer (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂) (b₁ b₂ : ℝ)
    (hb : b₁ * b₂ ≠ 0) :
    upperTriangular b₁ b₂ 0 hb ∈ Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) := by
  rw [mem_centralizer_upperTriangular_zero_iff a₁ a₂ h hne, coe_upperTriangular]
  simp

private theorem isClosed_centralizer_upperTriangular (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂) :
    IsClosed ((Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) :
      Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) := by
  have hset : ((Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) :
      Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) =
      {g : GL (Fin 2) ℝ | (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0} ∩
        {g : GL (Fin 2) ℝ | (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0} := by
    ext g
    exact mem_centralizer_upperTriangular_zero_iff a₁ a₂ h hne g
  rw [hset]
  exact (isClosed_eq (continuous_glEntry 0 1) continuous_const).inter
    (isClosed_eq (continuous_glEntry 1 0) continuous_const)

private theorem splitParam_apply_of_ne (α : ℝ × ℝ) (hα : α.1 * α.2 ≠ 0) :
    (if hα' : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα' else 1) = upperTriangular α.1 α.2 0 hα :=
  dif_pos hα

private theorem isOpen_splitDomain : IsOpen {α : ℝ × ℝ | α.1 * α.2 ≠ 0} :=
  isOpen_ne.preimage (continuous_fst.mul continuous_snd)

private theorem continuousOn_splitParam :
    ContinuousOn (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
      {α : ℝ × ℝ | α.1 * α.2 ≠ 0} := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have h : Set.EqOn
      (Units.val ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
      (fun α : ℝ × ℝ => !![α.1, 0; 0, α.2]) {α : ℝ × ℝ | α.1 * α.2 ≠ 0} := by
    intro α (hα : α.1 * α.2 ≠ 0)
    show ((if hα' : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα' else 1 : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![α.1, 0; 0, α.2]
    rw [splitParam_apply_of_ne α hα, coe_upperTriangular]
  refine ContinuousOn.congr ?_ h
  refine (continuous_matrix fun i j => ?_).continuousOn
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem exists_map_val_centralizer_upperTriangular_eq_smul_map_diag' (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0)
    (hne : a₁ ≠ a₂)
    (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
          (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) := by
  have hw0 : ∀ α : ℝ × ℝ, α ∉ {α : ℝ × ℝ | α.1 * α.2 ≠ 0} → |α.1 * α.2|⁻¹ = 0 := by
    intro α hα
    have h0 : α.1 * α.2 = 0 := by
      by_contra hne0
      exact hα hne0
    rw [h0, abs_zero, inv_zero]
  rw [withDensity_restrict_of_eq_zero_off volume isOpen_splitDomain.measurableSet
    (fun α : ℝ × ℝ => ENNReal.ofReal |α.1 * α.2|⁻¹)
    (fun α hα => by
      show ENNReal.ofReal |α.1 * α.2|⁻¹ = 0
      rw [hw0 α hα, ENNReal.ofReal_zero])]
  refine exists_map_val_eq_smul_map_of_planeModel
    (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
    (isClosed_centralizer_upperTriangular a₁ a₂ h hne)
    (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
    {α : ℝ × ℝ | α.1 * α.2 ≠ 0} isOpen_splitDomain continuousOn_splitParam ?_ ?_
    (fun g : GL (Fin 2) ℝ => ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1))
    ((continuous_glEntry 0 0).prodMk (continuous_glEntry 1 1)) ?_ ?_
    (fun α : ℝ × ℝ => |α.1 * α.2|⁻¹) ?_ ?_ hw0 ?_ τ hτ
  ·
    intro α
    by_cases hα : α.1 * α.2 ≠ 0
    · simp only [dif_pos hα]
      exact upperTriangular_zero_mem_centralizer a₁ a₂ h hne α.1 α.2 hα
    · simp only [dif_neg hα]
      exact Subgroup.one_mem _
  ·
    intro α hα
    have hα' : ¬ α.1 * α.2 ≠ 0 := hα
    simp only [dif_neg hα']
  ·
    intro α (hα : α.1 * α.2 ≠ 0)
    simp only [dif_pos hα, coe_upperTriangular]
    ext <;> simp
  ·
    intro t ht
    obtain ⟨h01, h10⟩ := (mem_centralizer_upperTriangular_zero_iff a₁ a₂ h hne t).1 ht
    have hdet : (t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (t : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ≠ 0 := by
      have hd := det_val_ne_zero t
      rwa [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hd
    refine ⟨hdet, ?_⟩
    simp only [dif_pos hdet]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [coe_upperTriangular]
    fin_cases i <;> fin_cases j <;> simp [h01, h10]
  ·
    exact (continuous_abs.comp (continuous_fst.mul continuous_snd)).continuousOn.inv₀
      fun α (hα : α.1 * α.2 ≠ 0) => abs_ne_zero.2 hα
  ·
    intro α (hα : α.1 * α.2 ≠ 0)
    exact inv_pos.2 (abs_pos.2 hα)
  ·
    intro t ht
    obtain ⟨h01, h10⟩ := (mem_centralizer_upperTriangular_zero_iff a₁ a₂ h hne t).1 ht
    have hd : (t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (t : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ≠ 0 := by
      have hd := det_val_ne_zero t
      rwa [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hd
    refine ⟨planeMap ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) 0 0 ((t : Matrix (Fin 2) (Fin 2) ℝ) 1 1),
      map_planeMap_diag_withDensity _ _ hd, ?_⟩
    intro α (hα : α.1 * α.2 ≠ 0)
    have hLα : (planeMap ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) 0 0 ((t : Matrix (Fin 2) (Fin 2) ℝ) 1 1) α).1 *
        (planeMap ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) 0 0 ((t : Matrix (Fin 2) (Fin 2) ℝ) 1 1) α).2 ≠ 0 := by
      show ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * α.1 + 0 * α.2) *
        (0 * α.1 + (t : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * α.2) ≠ 0
      have hprod : ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * α.1 + 0 * α.2) *
          (0 * α.1 + (t : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * α.2) =
          ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (t : Matrix (Fin 2) (Fin 2) ℝ) 1 1) * (α.1 * α.2) := by ring
      rw [hprod]
      exact mul_ne_zero hd hα
    simp only [dif_pos hα, dif_pos hLα]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, coe_upperTriangular, coe_upperTriangular, planeMap_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10]

end AutomorphicForm.GL2Real

theorem solution
    (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0)
    (hne : a₁ ≠ a₂)
    (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
          (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) :=
  exists_map_val_centralizer_upperTriangular_eq_smul_map_diag'
    a₁ a₂ h hne τ hτ

end S_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag (solution)
