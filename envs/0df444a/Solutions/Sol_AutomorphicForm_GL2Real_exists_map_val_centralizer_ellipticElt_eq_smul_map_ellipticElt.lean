-- Prove2me | solution 1 for AutomorphicForm.GL2Real.exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/66adee97-c253-5539-b138-eedba0acd13f

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt
set_option autoImplicit false
open MeasureTheory
p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt.AutomorphicForm.GL2Real"
open Topology

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "ellipticElt"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

private theorem mem_centralizer_ellipticElt_iff (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0) (g : GL (Fin 2) ℝ) :
    g ∈ Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) ↔
      (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∧
        (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) := by
  have hγ : ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] := rfl
  have hrs : r * Real.sin θ ≠ 0 := mul_ne_zero hr.ne' hθ
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [Matrix.GeneralLinearGroup.ext_iff]
  constructor
  · intro hg
    have h00 := hg 0 0
    have h01 := hg 0 1
    simp [Units.val_mul, hγ, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    constructor
    · have h1 : (r * Real.sin θ) *
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 - (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = 0 := by linarith
      have h2 := (mul_eq_zero.1 h1).resolve_left hrs
      linarith
    · have h1 : (r * Real.sin θ) *
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 + (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) = 0 := by linarith
      have h2 := (mul_eq_zero.1 h1).resolve_left hrs
      linarith
  · rintro ⟨h11, h10⟩ i j
    fin_cases i <;> fin_cases j <;> simp [Units.val_mul, hγ, Matrix.mul_apply, Fin.sum_univ_two, h11, h10] <;> ring

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

private theorem map_planeMap_rot_withDensity (p₀ q₀ : ℝ) (hw : p₀ ^ 2 + q₀ ^ 2 ≠ 0) :
    Measure.map (planeMap p₀ (-q₀) q₀ p₀)
        (volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹)) =
      volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹) := by
  have hdet : LinearMap.det (planeMap p₀ (-q₀) q₀ p₀) = p₀ ^ 2 + q₀ ^ 2 := by rw [det_planeMap]; ring
  have hpos : 0 < p₀ ^ 2 + q₀ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hw)
  refine map_withDensity_eq_self_of_comp volume (planeMap p₀ (-q₀) q₀ p₀) (by rw [hdet]; exact hw) _ ?_ ?_
  · exact (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).inv).ennreal_ofReal
  · intro z
    rw [hdet, planeMap_apply, abs_of_pos hpos, ← ENNReal.ofReal_mul (inv_nonneg.2 hpos.le)]
    congr 1
    rw [← mul_inv]
    congr 1
    ring

end AutomorphicForm.GL2Real

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "ellipticElt"
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

end AutomorphicForm.GL2Real

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "ellipticElt"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

private noncomputable def pqElt (p q : ℝ) (h : p ^ 2 + q ^ 2 ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![p, q; -q, p]
    (by
      rw [Matrix.det_fin_two_of]
      have e : p * p - q * -q = p ^ 2 + q ^ 2 := by ring
      rw [e]
      exact h)

private noncomputable def pqParam (z : ℝ × ℝ) : GL (Fin 2) ℝ :=
  if hz : z.1 ^ 2 + z.2 ^ 2 ≠ 0 then pqElt z.1 z.2 hz else 1

private theorem coe_pqElt (p q : ℝ) (h : p ^ 2 + q ^ 2 ≠ 0) :
    ((pqElt p q h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![p, q; -q, p] :=
  rfl

private theorem coe_ellipticElt (r θ : ℝ) (hr : 0 < r) :
    ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] :=
  rfl

private theorem pqParam_of_ne (z : ℝ × ℝ) (hz : z.1 ^ 2 + z.2 ^ 2 ≠ 0) : pqParam z = pqElt z.1 z.2 hz :=
  dif_pos hz

private theorem pqParam_of_eq (z : ℝ × ℝ) (hz : ¬ z.1 ^ 2 + z.2 ^ 2 ≠ 0) : pqParam z = 1 :=
  dif_neg hz

private theorem sq_add_sq_cos_sin (ρ φ : ℝ) : (ρ * Real.cos φ) ^ 2 + (ρ * Real.sin φ) ^ 2 = ρ ^ 2 := by
  have h := Real.cos_sq_add_sin_sq φ
  linear_combination ρ ^ 2 * h

private theorem pqElt_mem_centralizer (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0) (p q : ℝ) (h : p ^ 2 + q ^ 2 ≠ 0) :
    pqElt p q h ∈ Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) := by
  rw [mem_centralizer_ellipticElt_iff r θ hr hθ, coe_pqElt]
  simp

private theorem isClosed_centralizer_ellipticElt (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0) :
    IsClosed ((Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) :
      Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) := by
  have hset : ((Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) :
      Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) =
      {g : GL (Fin 2) ℝ | (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0} ∩
        {g : GL (Fin 2) ℝ | (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1)} := by
    ext g
    exact mem_centralizer_ellipticElt_iff r θ hr hθ g
  rw [hset]
  exact (isClosed_eq (continuous_glEntry 1 1) (continuous_glEntry 0 0)).inter
    (isClosed_eq (continuous_glEntry 1 0) (continuous_glEntry 0 1).neg)

private theorem isOpen_pqDomain : IsOpen {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≠ 0} :=
  isOpen_ne.preimage ((continuous_fst.pow 2).add (continuous_snd.pow 2))

private theorem continuousOn_pqParam : ContinuousOn pqParam {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≠ 0} := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have h : Set.EqOn (Units.val ∘ pqParam) (fun z : ℝ × ℝ => !![z.1, z.2; -z.2, z.1])
      {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≠ 0} := by
    intro z (hz : z.1 ^ 2 + z.2 ^ 2 ≠ 0)
    show ((pqParam z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![z.1, z.2; -z.2, z.1]
    rw [pqParam_of_ne z hz, coe_pqElt]
  refine ContinuousOn.congr ?_ h
  refine (continuous_matrix fun i j => ?_).continuousOn
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem sq_add_sq_ne_zero_of_mem_centralizer_ellipticElt (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0)
    (t : GL (Fin 2) ℝ) (ht : t ∈ Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))) :
    (t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ^ 2 ≠ 0 := by
  obtain ⟨h11, h10⟩ := (mem_centralizer_ellipticElt_iff r θ hr hθ t).1 ht
  have hd := det_val_ne_zero t
  rw [Matrix.det_fin_two, h11, h10] at hd
  have e : (t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 -
      (t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * -((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1) =
      (t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ^ 2 := by ring
  rwa [e] at hd

private theorem exists_map_val_centralizer_ellipticElt_eq_smul_map_pqParam (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ) pqParam
          (volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹)) := by
  refine exists_map_val_eq_smul_map_of_planeModel
    (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
    (isClosed_centralizer_ellipticElt r θ hr hθ) pqParam {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≠ 0} isOpen_pqDomain
    continuousOn_pqParam ?_ ?_
    (fun g : GL (Fin 2) ℝ => ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1))
    ((continuous_glEntry 0 0).prodMk (continuous_glEntry 0 1)) ?_ ?_
    (fun z : ℝ × ℝ => (z.1 ^ 2 + z.2 ^ 2)⁻¹) ?_ ?_ ?_ ?_ τ hτ
  ·
    intro z
    by_cases hz : z.1 ^ 2 + z.2 ^ 2 ≠ 0
    · rw [pqParam_of_ne z hz]
      exact pqElt_mem_centralizer r θ hr hθ z.1 z.2 hz
    · rw [pqParam_of_eq z hz]
      exact Subgroup.one_mem _
  ·
    intro z hz
    exact pqParam_of_eq z (by simpa using hz)
  ·
    intro z (hz : z.1 ^ 2 + z.2 ^ 2 ≠ 0)
    simp only [pqParam_of_ne z hz, coe_pqElt]
    ext <;> simp
  ·
    intro t ht
    have hpq := sq_add_sq_ne_zero_of_mem_centralizer_ellipticElt r θ hr hθ t ht
    obtain ⟨h11, h10⟩ := (mem_centralizer_ellipticElt_iff r θ hr hθ t).1 ht
    refine ⟨hpq, ?_⟩
    rw [pqParam_of_ne ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (t : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hpq]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [coe_pqElt]
    fin_cases i <;> fin_cases j <;> simp [h11, h10]
  ·
    exact ((continuous_fst.pow 2).add (continuous_snd.pow 2)).continuousOn.inv₀
      fun z (hz : z.1 ^ 2 + z.2 ^ 2 ≠ 0) => hz
  ·
    intro z (hz : z.1 ^ 2 + z.2 ^ 2 ≠ 0)
    exact inv_pos.2 (lt_of_le_of_ne (by positivity) (Ne.symm hz))
  ·
    intro z hz
    have h0 : z.1 ^ 2 + z.2 ^ 2 = 0 := by simpa using hz
    show (z.1 ^ 2 + z.2 ^ 2)⁻¹ = 0
    rw [h0, inv_zero]
  ·
    intro t ht
    have hpq := sq_add_sq_ne_zero_of_mem_centralizer_ellipticElt r θ hr hθ t ht
    obtain ⟨h11, h10⟩ := (mem_centralizer_ellipticElt_iff r θ hr hθ t).1 ht
    refine ⟨planeMap ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) (-((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1))
        ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0),
      map_planeMap_rot_withDensity _ _ hpq, ?_⟩
    intro z (hz : z.1 ^ 2 + z.2 ^ 2 ≠ 0)
    have hLz : (planeMap ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) (-((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1))
          ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) z).1 ^ 2 +
        (planeMap ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) (-((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1))
          ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) z).2 ^ 2 ≠ 0 := by
      show ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * z.1 + -((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1) * z.2) ^ 2 +
        ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * z.1 + (t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * z.2) ^ 2 ≠ 0
      have e : ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * z.1 + -((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1) * z.2) ^ 2 +
          ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * z.1 + (t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * z.2) ^ 2 =
          ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ^ 2) *
            (z.1 ^ 2 + z.2 ^ 2) := by ring
      rw [e]
      exact mul_ne_zero hpq hz
    rw [pqParam_of_ne z hz,
      pqParam_of_ne (planeMap ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) (-((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1))
        ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ((t : Matrix (Fin 2) (Fin 2) ℝ) 0 0) z) hLz]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, coe_pqElt, coe_pqElt, planeMap_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11, h10] <;> ring

private theorem map_neg_pqModel :
    Measure.map (fun z : ℝ × ℝ => -z) (volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹)) =
      volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹) := by
  have h := map_planeMap_rot_withDensity (-1) 0 (by norm_num)
  have hfun : (planeMap (-1) (-0) 0 (-1) : ℝ × ℝ → ℝ × ℝ) = fun z : ℝ × ℝ => -z := by
    funext z
    rw [planeMap_apply]
    ext <;> simp
  rwa [← hfun]

private theorem polarCoord_symm_eq (p : ℝ × ℝ) : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) :=
  rfl

private theorem polarCoord_target_eq : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi :=
  rfl

private theorem measurableSet_polarBox : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
  measurableSet_Ioi.prod measurableSet_Ioo

private theorem measurableSet_polarTarget : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
  measurableSet_Ioi.prod measurableSet_Ioo

private theorem preimage_add_pi_polarBox :
    (fun p : ℝ × ℝ => p + ((0 : ℝ), Real.pi)) ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) =
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := by
  ext p
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Prod.fst_add, Prod.snd_add, add_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩

private theorem setLIntegral_polarBox_eq (H : ℝ × ℝ → ENNReal) (hH : Measurable H) :
    ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), H p =
      ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, H (p + ((0 : ℝ), Real.pi)) := by
  have hadd : Measurable fun p : ℝ × ℝ => p + ((0 : ℝ), Real.pi) := measurable_add_const _
  calc ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), H p
      = ∫⁻ p, H p ∂((Measure.map (fun p : ℝ × ℝ => p + ((0 : ℝ), Real.pi)) volume).restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) := by
        rw [map_add_right_eq_self]
    _ = ∫⁻ p, H p ∂(Measure.map (fun p : ℝ × ℝ => p + ((0 : ℝ), Real.pi))
          (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi))) := by
        rw [Measure.restrict_map hadd measurableSet_polarBox, preimage_add_pi_polarBox]
    _ = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, H (p + ((0 : ℝ), Real.pi)) :=
        lintegral_map hH hadd

private theorem polarParam_add_pi_eq (p : ℝ × ℝ) (hp : 0 < p.1) :
    (if hq : 0 < (p + ((0 : ℝ), Real.pi)).1 then
        ellipticElt (p + ((0 : ℝ), Real.pi)).1 (p + ((0 : ℝ), Real.pi)).2 hq else 1) =
      pqParam (-(polarCoord.symm p)) := by
  have h1 : (p + ((0 : ℝ), Real.pi)).1 = p.1 := by simp
  have h2 : (p + ((0 : ℝ), Real.pi)).2 = p.2 + Real.pi := by simp
  have hpos : 0 < (p + ((0 : ℝ), Real.pi)).1 := by rw [h1]; exact hp
  have hz : (-(polarCoord.symm p)).1 ^ 2 + (-(polarCoord.symm p)).2 ^ 2 ≠ 0 := by
    rw [polarCoord_symm_eq]
    simp only [Prod.fst_neg, Prod.snd_neg, neg_sq]
    rw [sq_add_sq_cos_sin]
    positivity
  rw [dif_pos hpos, pqParam_of_ne (-(polarCoord.symm p)) hz]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [coe_ellipticElt, coe_pqElt, polarCoord_symm_eq]
  simp only [h1, h2, Real.cos_add_pi, Real.sin_add_pi, Prod.fst_neg, Prod.snd_neg]
  fin_cases i <;> fin_cases j <;> simp

private theorem ofReal_mul_pqDensity (p : ℝ × ℝ) (hp : 0 < p.1) :
    ENNReal.ofReal p.1 * ENNReal.ofReal ((-(polarCoord.symm p)).1 ^ 2 + (-(polarCoord.symm p)).2 ^ 2)⁻¹ =
      ENNReal.ofReal p.1⁻¹ := by
  rw [polarCoord_symm_eq]
  simp only [Prod.fst_neg, Prod.snd_neg, neg_sq]
  rw [sq_add_sq_cos_sin, ← ENNReal.ofReal_mul hp.le]
  congr 1
  rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]

private theorem isOpen_polarDomain : IsOpen {q : ℝ × ℝ | 0 < q.1} :=
  isOpen_lt continuous_const continuous_fst

private theorem measurable_polarParam :
    @Measurable (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ)
      (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1) := by
  refine measurable_of_continuousOn_of_eq_one isOpen_polarDomain ?_ ?_
  · rw [isEmbedding_glVal'.continuousOn_iff]
    have h : Set.EqOn
        (Units.val ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        (fun q : ℝ × ℝ => !![q.1 * Real.cos q.2, q.1 * Real.sin q.2; -(q.1 * Real.sin q.2), q.1 * Real.cos q.2])
        {q : ℝ × ℝ | 0 < q.1} := by
      intro q (hq : 0 < q.1)
      show ((if hq' : 0 < q.1 then ellipticElt q.1 q.2 hq' else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![q.1 * Real.cos q.2, q.1 * Real.sin q.2; -(q.1 * Real.sin q.2), q.1 * Real.cos q.2]
      rw [dif_pos hq, coe_ellipticElt]
    refine ContinuousOn.congr ?_ h
    refine (continuous_matrix fun i j => ?_).continuousOn
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · intro q hq
    exact dif_neg (by simpa using hq)

private theorem measurable_pqParam : @Measurable (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ) pqParam :=
  measurable_of_continuousOn_of_eq_one isOpen_pqDomain continuousOn_pqParam
    fun z hz => pqParam_of_eq z (by simpa using hz)

private theorem measurable_pqDensity : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹ :=
  (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).inv).ennreal_ofReal

private theorem measurable_polarDensity : Measurable fun q : ℝ × ℝ => ENNReal.ofReal q.1⁻¹ :=
  measurable_fst.inv.ennreal_ofReal

private theorem map_pqParam_pqModel_eq_map_polar :
    @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ) pqParam
        (volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹)) =
      @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
        (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  have hneg : Measurable fun z : ℝ × ℝ => -z := measurable_neg
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hfpq : Measurable fun z : ℝ × ℝ => f (pqParam z) := hf.comp measurable_pqParam
  have hfpol : Measurable fun q : ℝ × ℝ => f (if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1) :=
    hf.comp measurable_polarParam
  have hH : Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal q.1⁻¹ * f (if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1) :=
    measurable_polarDensity.mul hfpol
  rw [lintegral_map hf measurable_pqParam, lintegral_map hf measurable_polarParam,
    lintegral_withDensity_eq_lintegral_mul _ measurable_pqDensity hfpq,
    lintegral_withDensity_eq_lintegral_mul _ measurable_polarDensity hfpol]
  simp only [Pi.mul_apply]

  rw [setLIntegral_polarBox_eq _ hH]
  have hright : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal (p + ((0 : ℝ), Real.pi)).1⁻¹ *
          f (if hq : 0 < (p + ((0 : ℝ), Real.pi)).1 then
              ellipticElt (p + ((0 : ℝ), Real.pi)).1 (p + ((0 : ℝ), Real.pi)).2 hq else 1) =
        ENNReal.ofReal p.1 *
          (ENNReal.ofReal ((-(polarCoord.symm p)).1 ^ 2 + (-(polarCoord.symm p)).2 ^ 2)⁻¹ *
            f (pqParam (-(polarCoord.symm p)))) := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have h1 : (p + ((0 : ℝ), Real.pi)).1 = p.1 := by simp
    rw [polarParam_add_pi_eq p hp1, h1, ← mul_assoc, ofReal_mul_pqDensity p hp1]
  rw [setLIntegral_congr_fun measurableSet_polarTarget hright]

  have hleft : ∫⁻ z, ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹ * f (pqParam z) =
      ∫⁻ z, ENNReal.ofReal ((-z).1 ^ 2 + (-z).2 ^ 2)⁻¹ * f (pqParam (-z)) := by
    have hmeasneg : Measurable fun z : ℝ × ℝ => f (pqParam (-z)) := hfpq.comp hneg
    calc ∫⁻ z, ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹ * f (pqParam z)
        = ∫⁻ z, f (pqParam z) ∂(volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹)) := by
          rw [lintegral_withDensity_eq_lintegral_mul _ measurable_pqDensity hfpq]
          simp only [Pi.mul_apply]
      _ = ∫⁻ z, f (pqParam z) ∂(Measure.map (fun z : ℝ × ℝ => -z)
            (volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹))) := by
          rw [map_neg_pqModel]
      _ = ∫⁻ z, f (pqParam (-z)) ∂(volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹)) :=
          lintegral_map hfpq hneg
      _ = ∫⁻ z, ENNReal.ofReal (z.1 ^ 2 + z.2 ^ 2)⁻¹ * f (pqParam (-z)) := by
          rw [lintegral_withDensity_eq_lintegral_mul _ measurable_pqDensity hmeasneg]
          simp only [Pi.mul_apply]
      _ = ∫⁻ z, ENNReal.ofReal ((-z).1 ^ 2 + (-z).2 ^ 2)⁻¹ * f (pqParam (-z)) := by
          refine lintegral_congr fun z => ?_
          simp only [Prod.fst_neg, Prod.snd_neg, neg_sq]
  rw [hleft, ← lintegral_comp_polarCoord_symm
    (fun z : ℝ × ℝ => ENNReal.ofReal ((-z).1 ^ 2 + (-z).2 ^ 2)⁻¹ * f (pqParam (-z))), polarCoord_target_eq]
  simp only [smul_eq_mul]

private theorem exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt' (r θ : ℝ) (hr : 0 < r)
    (hθ : Real.sin θ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
          (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹)) := by
  obtain ⟨c, hc, hτc⟩ := exists_map_val_centralizer_ellipticElt_eq_smul_map_pqParam r θ hr hθ τ hτ
  refine ⟨c, hc, ?_⟩
  rw [hτc, map_pqParam_pqModel_eq_map_polar]

end AutomorphicForm.GL2Real

theorem solution (r θ : ℝ) (hr : 0 < r)
    (hθ : Real.sin θ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
          (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹)) :=
  exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt'
    r θ hr hθ τ hτ

end S_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt (solution)
