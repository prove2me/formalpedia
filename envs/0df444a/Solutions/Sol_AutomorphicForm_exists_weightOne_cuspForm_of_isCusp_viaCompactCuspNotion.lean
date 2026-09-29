-- Prove2me | solution 1 for AutomorphicForm.exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/23fccb2b-c4bb-5e46-bad2-35c7c13dd960

import Mathlib
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_FormalHecke_Eigensystem
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion

set_option autoImplicit false

section Part01

noncomputable section

namespace HeckeDictionary

open scoped UpperHalfPlane

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

private scoped instance compactSpace_rowIsometrySubgroup : CompactSpace (rowIsometrySubgroup ℝ) := by

  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))
  haveI : ProperSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (ProperSpace (Fin 2 → Fin 2 → ℝ))

  have hbd : ∀ k ∈ rowIsometrySubgroup ℝ,
      (k : Matrix (Fin 2) (Fin 2) ℝ) ∈ Metric.closedBall 0 1 := by
    intro k hk
    obtain ⟨_, hiso⟩ := (mem_rowIsometrySubgroup_iff.mp hk :)
    have h10 := hiso 1 0; have h01 := hiso 0 1
    simp only [one_mul, zero_mul, add_zero, zero_add, norm_one, one_pow, norm_zero,
      zero_pow two_ne_zero] at h10 h01
    rw [Metric.mem_closedBall, dist_zero_right]

    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
      simp only [Real.norm_eq_abs] at h10 h01 ⊢ <;>
      nlinarith [h10, h01, sq_abs ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 0),
        sq_abs ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 1),
        sq_abs ((k : Matrix (Fin 2) (Fin 2) ℝ) 1 0),
        sq_abs ((k : Matrix (Fin 2) (Fin 2) ℝ) 1 1),
        sq_nonneg ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 0),
        sq_nonneg ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 1),
        sq_nonneg ((k : Matrix (Fin 2) (Fin 2) ℝ) 1 0),
        sq_nonneg ((k : Matrix (Fin 2) (Fin 2) ℝ) 1 1),
        abs_nonneg ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 0),
        abs_nonneg ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 1),
        abs_nonneg ((k : Matrix (Fin 2) (Fin 2) ℝ) 1 0),
        abs_nonneg ((k : Matrix (Fin 2) (Fin 2) ℝ) 1 1)]

  have hcl : IsClosed (rowIsometrySubgroup ℝ : Set (GL (Fin 2) ℝ)) := by
    have heq : (rowIsometrySubgroup ℝ : Set (GL (Fin 2) ℝ)) =
        {k : GL (Fin 2) ℝ | ‖(k : Matrix (Fin 2) (Fin 2) ℝ).det‖ = 1} ∩
        ⋂ x : ℝ, ⋂ y : ℝ, {k : GL (Fin 2) ℝ |
          ‖x * (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0
            + y * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0‖ ^ 2
          + ‖x * (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1
            + y * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1‖ ^ 2
          = ‖x‖ ^ 2 + ‖y‖ ^ 2} := by
      ext k; simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe,
        mem_rowIsometrySubgroup_iff, IsRowIsometry]
    rw [heq]

    refine IsClosed.inter (isClosed_eq ?_ continuous_const)
      (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const) <;>
      fun_prop

  suffices h : IsCompact (rowIsometrySubgroup ℝ : Set (GL (Fin 2) ℝ)) from
    isCompact_iff_compactSpace.mp h
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  refine IsCompact.of_isClosed_subset
    ((isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℝ) 1).prod
      ((isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℝ) 1).image MulOpposite.continuous_op))
    (Units.isClosedEmbedding_embedProduct.isClosedMap _ hcl) ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨hbd k hk, ⟨_, hbd k⁻¹ ((rowIsometrySubgroup ℝ).inv_mem hk), rfl⟩⟩

@[reducible] private def realGLBorel : MeasurableSpace (GL (Fin 2) ℝ) := borel _

private theorem borelSpace_realGLBorel : @BorelSpace (GL (Fin 2) ℝ) _ realGLBorel :=
  @BorelSpace.mk _ _ realGLBorel rfl

private scoped instance instLCMatReal : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))

private scoped instance instLCGLReal : LocallyCompactSpace (GL (Fin 2) ℝ) := inferInstance

private scoped instance instSCGLReal : SecondCountableTopology (GL (Fin 2) ℝ) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private def realGLHaar : @Measure (GL (Fin 2) ℝ) realGLBorel := by
  letI := realGLBorel; haveI := borelSpace_realGLBorel; exact Measure.haar

@[reducible] private def rowIsoBorel : MeasurableSpace (rowIsometrySubgroup ℝ) := borel _

private theorem borelSpace_rowIsoBorel : @BorelSpace (rowIsometrySubgroup ℝ) _ rowIsoBorel :=
  @BorelSpace.mk _ _ rowIsoBorel rfl

private def haarRowIso : @Measure (rowIsometrySubgroup ℝ) rowIsoBorel := by
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel; exact Measure.haar

private def borelCoordGL (x y t : ℝ) (hy : 0 < y) (ht : 0 < t) : GL (Fin 2) ℝ :=
  upperUnit (t * y) (t * x) t (mul_pos ht hy).ne' ht.ne'

private def iwasawaParam (p : (ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ) : GL (Fin 2) ℝ :=
  (if h : 0 < p.1.2.1 ∧ 0 < p.1.2.2
    then borelCoordGL p.1.1 p.1.2.1 p.1.2.2 h.1 h.2 else 1) * (p.2 : GL (Fin 2) ℝ)

private def borelHaar₃ : Measure (ℝ × ℝ × ℝ) :=
  (volume.restrict (Set.univ ×ˢ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ))).withDensity
    (fun p => ENNReal.ofReal ((p.2.1 ^ 2)⁻¹ * p.2.2⁻¹))

private def iwasawaHaar : @Measure (GL (Fin 2) ℝ) realGLBorel := by
  letI := realGLBorel; letI := rowIsoBorel
  exact Measure.map iwasawaParam (borelHaar₃.prod haarRowIso)

private def iwasawaBox : Set (ℝ × ℝ × ℝ) := {q | 0 < q.2.1 ∧ 0 < q.2.2}

private theorem isOpen_iwasawaBox : IsOpen iwasawaBox :=
  (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
    (isOpen_lt continuous_const (continuous_snd.comp continuous_snd))

private def iwasawaBorelFactor (p : ℝ × ℝ × ℝ) : GL (Fin 2) ℝ :=
  if h : 0 < p.2.1 ∧ 0 < p.2.2 then borelCoordGL p.1 p.2.1 p.2.2 h.1 h.2 else 1

private theorem iwasawaParam_eq (p : (ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ) :
    iwasawaParam p = iwasawaBorelFactor p.1 * (p.2 : GL (Fin 2) ℝ) := rfl

private theorem val_iwasawaBorelFactor_box (p : (ℝ × ℝ × ℝ)) (hp : 0 < p.2.1 ∧ 0 < p.2.2) :
    (iwasawaBorelFactor p : Matrix (Fin 2) (Fin 2) ℝ)
      = !![p.2.2 * p.2.1, p.2.2 * p.1; 0, p.2.2] := by
  unfold iwasawaBorelFactor; rw [dif_pos hp]; ext i j
  fin_cases i <;> fin_cases j <;> simp [borelCoordGL]

private theorem continuous_val_iwasawaBorelFactor_box :
    Continuous (fun p : iwasawaBox => (iwasawaBorelFactor (↑p) : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have heq : (fun p : iwasawaBox => (iwasawaBorelFactor (↑p) : Matrix (Fin 2) (Fin 2) ℝ))
      = fun p : iwasawaBox => !![(p : ℝ × ℝ × ℝ).2.2 * (p : ℝ × ℝ × ℝ).2.1,
        (p : ℝ × ℝ × ℝ).2.2 * (p : ℝ × ℝ × ℝ).1; 0, (p : ℝ × ℝ × ℝ).2.2] :=
    funext fun p => val_iwasawaBorelFactor_box (p : ℝ × ℝ × ℝ) p.2
  rw [heq]; refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuousOn_iwasawaBorelFactor_box :
    ContinuousOn iwasawaBorelFactor iwasawaBox := by
  rw [continuousOn_iff_continuous_restrict, Units.isEmbedding_embedProduct.continuous_iff]
  refine continuous_prodMk.mpr ⟨continuous_val_iwasawaBorelFactor_box,
    MulOpposite.continuous_op.comp ?_⟩

  have hdet : ∀ p : iwasawaBox,
      (iwasawaBorelFactor (↑p) : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    intro p
    rw [val_iwasawaBorelFactor_box (↑p) p.2, Matrix.det_fin_two_of, mul_zero, sub_zero]
    have hy : (0:ℝ) < (↑p : ℝ × ℝ × ℝ).2.1 := p.2.1
    have ht : (0:ℝ) < (↑p : ℝ × ℝ × ℝ).2.2 := p.2.2
    positivity
  simp only [Set.restrict_apply, Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]
  exact ((continuous_val_iwasawaBorelFactor_box.matrix_det).inv₀ hdet).smul
    continuous_val_iwasawaBorelFactor_box.matrix_adjugate

private theorem measurable_iwasawaBorelFactor :
    letI := realGLBorel; Measurable iwasawaBorelFactor := by
  letI := realGLBorel; haveI := borelSpace_realGLBorel
  refine measurable_of_restrict_of_restrict_compl isOpen_iwasawaBox.measurableSet ?_ ?_
  ·
    exact (continuousOn_iff_continuous_restrict.mp
      continuousOn_iwasawaBorelFactor_box).measurable
  ·
    have heq : iwasawaBoxᶜ.restrict iwasawaBorelFactor = fun _ => (1 : GL (Fin 2) ℝ) :=
      funext fun p => dif_neg fun h => p.2 h
    exact (congrArg Measurable heq).mpr measurable_const

private theorem measurable_iwasawaParam :
    letI := realGLBorel; letI := rowIsoBorel
    Measurable iwasawaParam := by
  letI := realGLBorel; letI := rowIsoBorel
  haveI := borelSpace_realGLBorel; haveI := borelSpace_rowIsoBorel

  have hmul : Measurable (fun q : (GL (Fin 2) ℝ) × (GL (Fin 2) ℝ) => q.1 * q.2) :=
    continuous_mul.measurable

  exact hmul.comp (Measurable.prodMk
    (measurable_iwasawaBorelFactor.comp measurable_fst)
    (continuous_subtype_val.measurable.comp measurable_snd))

private scoped instance sFinite_borelHaar₃ : SFinite borelHaar₃ := by
  unfold borelHaar₃; infer_instance

private scoped instance sFinite_haarRowIso : letI := rowIsoBorel; SFinite haarRowIso := by
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel
  show SFinite (Measure.haar : Measure (rowIsometrySubgroup ℝ)); infer_instance

private theorem borelHaar₃_prod_haarRowIso_ne_zero :
    letI := rowIsoBorel; borelHaar₃.prod haarRowIso ≠ 0 := by
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel
  rw [ne_eq, ← Measure.measure_univ_eq_zero, ← Set.univ_prod_univ, Measure.prod_prod,
    mul_eq_zero, not_or]
  refine ⟨?_, ?_⟩
  ·
    unfold borelHaar₃
    rw [withDensity_apply_eq_zero (by fun_prop), Set.inter_univ]
    refine fun h => absurd h (ne_of_gt ?_)
    have hreg : (0 : ENNReal) < ((volume : Measure (ℝ × ℝ × ℝ)).restrict
        (Set.univ ×ˢ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)))
          (Set.univ ×ˢ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
      rw [Measure.restrict_apply_self]
      exact (isOpen_univ.prod (isOpen_Ioi.prod isOpen_Ioi)).measure_pos volume
        ⟨(0, 1, 1), by simp [Set.mem_prod, Set.mem_Ioi]⟩
    refine lt_of_lt_of_le hreg (measure_mono ?_)
    rintro ⟨x, y, t⟩ ⟨_, hy, ht⟩
    simp only [Set.mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos (inv_pos.2 (pow_pos hy 2)) (inv_pos.2 ht)
  ·
    show (Measure.haar : Measure (rowIsometrySubgroup ℝ)) Set.univ ≠ 0
    exact isOpen_univ.measure_ne_zero _ Set.univ_nonempty

private def topRowDotBottom (h : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := h 0 0 * h 1 0 + h 0 1 * h 1 1

private def iwasawaT (h : GL (Fin 2) ℝ) : ℝ := Real.sqrt (rowNormSq (h : Matrix (Fin 2) (Fin 2) ℝ))

private theorem iwasawaT_pos (h : GL (Fin 2) ℝ) : 0 < iwasawaT h :=
  Real.sqrt_pos.2 (rowNormSq_pos h)

private theorem iwasawaT_sq (h : GL (Fin 2) ℝ) :
    iwasawaT h ^ 2 = rowNormSq (h : Matrix (Fin 2) (Fin 2) ℝ) :=
  Real.sq_sqrt (rowNormSq_pos h).le

private def iwasawaY (h : GL (Fin 2) ℝ) : ℝ := localHeight h

private theorem iwasawaY_pos (h : GL (Fin 2) ℝ) : 0 < iwasawaY h := localHeight_pos h

private def iwasawaX (h : GL (Fin 2) ℝ) : ℝ :=
  topRowDotBottom (h : Matrix (Fin 2) (Fin 2) ℝ)
    / rowNormSq (h : Matrix (Fin 2) (Fin 2) ℝ)

private def iwasawaCoords (h : GL (Fin 2) ℝ) : ℝ × ℝ × ℝ := (iwasawaX h, iwasawaY h, iwasawaT h)

private theorem iwasawaCoords_mem_box (h : GL (Fin 2) ℝ) : iwasawaCoords h ∈ iwasawaBox :=
  ⟨iwasawaY_pos h, iwasawaT_pos h⟩

private def iwasawaBpart (h : GL (Fin 2) ℝ) : GL (Fin 2) ℝ := iwasawaBorelFactor (iwasawaCoords h)

private theorem iwasawaBpart_eq (h : GL (Fin 2) ℝ) :
    iwasawaBpart h = borelCoordGL (iwasawaX h) (iwasawaY h) (iwasawaT h)
      (iwasawaY_pos h) (iwasawaT_pos h) :=
  dif_pos (iwasawaCoords_mem_box h)

private theorem sq_det_eq_gram (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M.det ^ 2 = topNormSq M * rowNormSq M - topRowDotBottom M ^ 2 := by
  unfold topNormSq rowNormSq topRowDotBottom
  rw [Matrix.det_fin_two]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

private theorem val_iwasawaBpart (h : GL (Fin 2) ℝ) :
    (iwasawaBpart h : Matrix (Fin 2) (Fin 2) ℝ)
      = !![iwasawaT h * iwasawaY h, iwasawaT h * iwasawaX h; 0, iwasawaT h] := by
  have hv := val_iwasawaBorelFactor_box (iwasawaCoords h) (iwasawaCoords_mem_box h)
  simp only [iwasawaCoords] at hv; exact hv

private def iwasawaKpartGL (h : GL (Fin 2) ℝ) : GL (Fin 2) ℝ := (iwasawaBpart h)⁻¹ * h

private theorem val_iwasawaBpart_inv (h : GL (Fin 2) ℝ) :
    ((iwasawaBpart h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)
      = !![1 / (iwasawaT h * iwasawaY h), - iwasawaX h / (iwasawaT h * iwasawaY h);
           0, 1 / iwasawaT h] := by
  have hT := (iwasawaT_pos h).ne'
  have hY := (iwasawaY_pos h).ne'
  refine Matrix.inv_eq_right_inv ?_
  rw [val_iwasawaBpart]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

private theorem isRowIsometry_iwasawaKpartGL (h : GL (Fin 2) ℝ) :
    IsRowIsometry (iwasawaKpartGL h) := by
  have hTpos := iwasawaT_pos h; have hYpos := iwasawaY_pos h
  have hTne := hTpos.ne'; have hYne := hYpos.ne'
  set h00 := (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with hh00
  set h01 := (h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hh01
  set h10 := (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 with hh10
  set h11 := (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 with hh11

  have hTs : iwasawaT h ^ 2 = h10 ^ 2 + h11 ^ 2 := by
    rw [iwasawaT_sq]; unfold rowNormSq
    simp only [Real.norm_eq_abs, sq_abs, ← hh10, ← hh11]
  have hXs : iwasawaX h * iwasawaT h ^ 2 = h00 * h10 + h01 * h11 := by
    unfold iwasawaX topRowDotBottom
    rw [div_mul_eq_mul_div, iwasawaT_sq, mul_div_cancel_right₀ _ (rowNormSq_pos h).ne']
  have hDs : (iwasawaT h ^ 2 * iwasawaY h) ^ 2 = (h00 * h11 - h01 * h10) ^ 2 := by
    have key : iwasawaT h ^ 2 * iwasawaY h = ‖(h:Matrix (Fin 2) (Fin 2) ℝ).det‖ := by
      rw [iwasawaT_sq]; unfold iwasawaY localHeight
      field_simp [(rowNormSq_pos h).ne']
    rw [key, Real.norm_eq_abs, sq_abs, Matrix.det_fin_two]

  have hKval : (iwasawaKpartGL h : Matrix (Fin 2) (Fin 2) ℝ)
      = !![1 / (iwasawaT h * iwasawaY h), - iwasawaX h / (iwasawaT h * iwasawaY h);
           0, 1 / iwasawaT h] * (h : Matrix (Fin 2) (Fin 2) ℝ) := by
    show (((iwasawaBpart h)⁻¹ * h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.coe_units_inv, val_iwasawaBpart_inv]
  refine ⟨?_, fun a b => ?_⟩
  ·
    show ‖(((iwasawaBpart h)⁻¹ * h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det‖ = 1
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.coe_units_inv,
      val_iwasawaBpart_inv, Matrix.det_fin_two_of, Real.norm_eq_abs, abs_mul]
    have : |1 / (iwasawaT h * iwasawaY h) * (1 / iwasawaT h)
        - - iwasawaX h / (iwasawaT h * iwasawaY h) * 0|
        = 1 / (iwasawaT h ^ 2 * iwasawaY h) := by
      rw [mul_zero, sub_zero, abs_of_pos (by positivity)]; field_simp
    rw [this, Matrix.det_fin_two, ← hh00, ← hh01, ← hh10, ← hh11]
    have hP : (0:ℝ) < iwasawaT h ^ 2 * iwasawaY h := by positivity
    have hdetabs : |h00 * h11 - h01 * h10| = iwasawaT h ^ 2 * iwasawaY h := by
      nlinarith [hDs, sq_abs (h00 * h11 - h01 * h10),
        abs_nonneg (h00 * h11 - h01 * h10), hP]
    rw [hdetabs]; field_simp
  ·
    rw [hKval]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs,
      ← hh00, ← hh01, ← hh10, ← hh11, zero_mul, zero_add]

    have hcb : (h00 ^ 2 + h01 ^ 2) * (h10 ^ 2 + h11 ^ 2)
        = (h00 * h11 - h01 * h10) ^ 2 + (h00 * h10 + h01 * h11) ^ 2 := by ring
    have htop : h00 ^ 2 + h01 ^ 2
        = iwasawaT h ^ 2 * iwasawaX h ^ 2 + iwasawaT h ^ 2 * iwasawaY h ^ 2 := by
      have h1 : (h00 ^ 2 + h01 ^ 2) * iwasawaT h ^ 2
          = (iwasawaT h ^ 2 * iwasawaX h ^ 2 + iwasawaT h ^ 2 * iwasawaY h ^ 2)
            * iwasawaT h ^ 2 := by
        linear_combination hcb + (h00 ^ 2 + h01 ^ 2) * hTs - hDs
          - (iwasawaX h * iwasawaT h ^ 2 + (h00 * h10 + h01 * h11)) * hXs
      exact mul_right_cancel₀ (pow_ne_zero 2 hTne) h1
    field_simp
    linear_combination a ^ 2 * htop
      - (b * iwasawaY h - a * iwasawaX h) ^ 2 * hTs
      - 2 * a * (b * iwasawaY h - a * iwasawaX h) * hXs

private def iwasawaKpart (h : GL (Fin 2) ℝ) : rowIsometrySubgroup ℝ :=
  ⟨iwasawaKpartGL h, isRowIsometry_iwasawaKpartGL h⟩

private theorem iwasawaBpart_mul_iwasawaKpart (h : GL (Fin 2) ℝ) :
    iwasawaBpart h * (iwasawaKpart h : GL (Fin 2) ℝ) = h := by
  show iwasawaBpart h * ((iwasawaBpart h)⁻¹ * h) = h
  rw [mul_inv_cancel_left]

private theorem continuous_iwasawaCoords : Continuous iwasawaCoords := by
  have hrowcts : Continuous (fun h : GL (Fin 2) ℝ =>
      rowNormSq (h : Matrix (Fin 2) (Fin 2) ℝ)) := by
    unfold rowNormSq; fun_prop
  refine continuous_prodMk.mpr ⟨?_, continuous_prodMk.mpr ⟨?_, ?_⟩⟩
  ·
    refine Continuous.div ?_ hrowcts (fun h => (rowNormSq_pos h).ne')
    unfold topRowDotBottom; fun_prop
  ·
    refine Continuous.div ?_ hrowcts (fun h => (rowNormSq_pos h).ne')
    fun_prop
  ·
    exact Real.continuous_sqrt.comp hrowcts

private theorem continuous_iwasawaKpart : Continuous iwasawaKpart := by
  have hBcts : Continuous iwasawaBpart :=
    ContinuousOn.comp_continuous continuousOn_iwasawaBorelFactor_box
      continuous_iwasawaCoords iwasawaCoords_mem_box
  exact Continuous.subtype_mk (hBcts.inv.mul continuous_id) _

private def mulHaarReal : Measure ℝ :=
  (volume.restrict (Set.Ioi (0:ℝ))).withDensity (fun t => ENNReal.ofReal t⁻¹)

private scoped instance sFinite_mulHaarReal : SFinite mulHaarReal := by unfold mulHaarReal; infer_instance

private def upperHalfPlaneCoords (z : ℍ) : ℝ × ℝ := ((z : ℂ).re, (z : ℂ).im)

private theorem upperHalfPlaneCoords_eq :
    upperHalfPlaneCoords = Complex.measurableEquivRealProd ∘ UpperHalfPlane.coe := rfl

private theorem measurableEmbedding_upperHalfPlaneCoords :
    MeasurableEmbedding upperHalfPlaneCoords := by
  rw [upperHalfPlaneCoords_eq]
  exact Complex.measurableEquivRealProd.measurableEmbedding.comp
    UpperHalfPlane.measurableEmbedding_coe

private def hypHaar₂ : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.univ ×ˢ Set.Ioi (0:ℝ))).withDensity
    (fun p => ENNReal.ofReal ((p.2 ^ 2)⁻¹))

private scoped instance sFinite_hypHaar₂ : SFinite hypHaar₂ := by unfold hypHaar₂; infer_instance

private def hIwasawaCoords (p : ℍ × (ℝ × rowIsometrySubgroup ℝ)) :
    (ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ :=
  (((p.1 : ℂ).re, (p.1 : ℂ).im, p.2.1), p.2.2)

private theorem measurable_hIwasawaCoords :
    letI := rowIsoBorel; Measurable hIwasawaCoords := by
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel
  refine Measurable.prodMk (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)) ?_ <;> fun_prop

private def hIwasawaSource : letI := rowIsoBorel
    Measure (ℍ × (ℝ × rowIsometrySubgroup ℝ)) := by
  letI := rowIsoBorel
  exact (volume : Measure ℍ).prod (mulHaarReal.prod haarRowIso)

private scoped instance sFinite_hIwasawaSource :
    letI := rowIsoBorel; SFinite hIwasawaSource := by
  letI := rowIsoBorel
  show SFinite ((volume : Measure ℍ).prod (mulHaarReal.prod haarRowIso)); infer_instance

private theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ENNReal) (hf : Measurable f) :
    Measure.map e (μ.withDensity f) = (Measure.map e μ).withDensity (f ∘ e.symm) := by
  refine Measure.ext_of_lintegral _ (fun φ hφ => ?_)

  have hφe : Measurable (fun a => φ (e a)) := hφ.comp e.measurable
  rw [lintegral_map_equiv,
    lintegral_withDensity_eq_lintegral_mul₀ hf.aemeasurable hφe.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀
      (hf.comp e.symm.measurable).aemeasurable hφ.aemeasurable,
    lintegral_map_equiv]
  simp only [Pi.mul_apply, Function.comp_apply, MeasurableEquiv.symm_apply_apply]

private theorem map_upperHalfPlaneCoords_volume :
    Measure.map upperHalfPlaneCoords (volume : Measure ℍ) = hypHaar₂ := by

  have hdenℍ : Measurable
      (fun z : ℍ => (↑((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) : ENNReal)) := by
    refine Continuous.measurable (ENNReal.continuous_coe.comp ?_)
    refine .pow (.div₀ continuous_const ?_ ?_) _
    · exact UpperHalfPlane.continuous_im.subtype_mk _
    · exact fun z ↦ NNReal.ne_iff.mp z.im_ne_zero

  have hbase : Measure.map upperHalfPlaneCoords
      ((volume : Measure ℂ).comap UpperHalfPlane.coe)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.univ ×ˢ Set.Ioi (0:ℝ)) := by
    rw [upperHalfPlaneCoords_eq, ← Measure.map_map
      Complex.measurableEquivRealProd.measurable UpperHalfPlane.measurable_coe,
      UpperHalfPlane.measurableEmbedding_coe.map_comap,

      (Complex.volume_preserving_equiv_real_prod.restrict_image_emb
        Complex.measurableEquivRealProd.measurableEmbedding _).map_eq]
    congr 1
    rw [UpperHalfPlane.range_coe,
      Complex.measurableEquivRealProd.image_eq_preimage_symm]
    ext ⟨x, y⟩
    simp [UpperHalfPlane.upperHalfPlaneSet, Complex.measurableEquivRealProd_symm_apply]

  unfold hypHaar₂
  refine Measure.ext_of_lintegral _ (fun φ hφ => ?_)

  have hφθ : Measurable (fun z => φ (upperHalfPlaneCoords z)) :=
    hφ.comp measurableEmbedding_upperHalfPlaneCoords.measurable
  rw [MeasurableEmbedding.lintegral_map measurableEmbedding_upperHalfPlaneCoords,
    UpperHalfPlane.volume_def,
    lintegral_withDensity_eq_lintegral_mul₀ hdenℍ.aemeasurable hφθ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) hφ.aemeasurable,
    ← hbase, MeasurableEmbedding.lintegral_map measurableEmbedding_upperHalfPlaneCoords]
  refine lintegral_congr (fun z => ?_)
  simp only [Pi.mul_apply, upperHalfPlaneCoords]
  congr 1

  have him := z.im_pos
  rw [show (↑((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) : ENNReal)
      = ENNReal.ofReal ((1 / z.im) ^ 2) by
    rw [ENNReal.coe_nnreal_eq]; push_cast; ring_nf,
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
  rw [UpperHalfPlane.im]; field_simp

private theorem borelHaar₃_eq_map_prodAssoc :
    borelHaar₃ = Measure.map (⇑MeasurableEquiv.prodAssoc) (hypHaar₂.prod mulHaarReal) := by
  unfold hypHaar₂ mulHaarReal borelHaar₃

  rw [prod_withDensity (by fun_prop) (by fun_prop), Measure.prod_restrict,
    show ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))
      = (volume : Measure ((ℝ × ℝ) × ℝ)) from rfl,
    map_withDensity_measurableEquiv _ _ _ (by fun_prop),

    (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)).restrict_image_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding _ |>.map_eq,
    show (⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ))
        '' ((Set.univ ×ˢ Set.Ioi (0:ℝ)) ×ˢ Set.Ioi (0:ℝ))
      = Set.univ ×ˢ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) by
    rw [MeasurableEquiv.image_eq_preimage_symm]
    ext ⟨x, y, t⟩

    have : ((MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ)).symm (x, y, t))
        = ((x, y), t) := rfl
    simp only [Set.mem_preimage, this, Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and]]

  congr 1
  funext p
  simp only [Function.comp_apply]
  change ENNReal.ofReal _ = ENNReal.ofReal ((p.2.1 ^ 2)⁻¹) * ENNReal.ofReal (p.2.2⁻¹)
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg _))]

private theorem map_hIwasawaCoords_hIwasawaSource :
    letI := rowIsoBorel
    Measure.map hIwasawaCoords hIwasawaSource = borelHaar₃.prod haarRowIso := by
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel

  have hfact : hIwasawaCoords = Prod.map
      (⇑MeasurableEquiv.prodAssoc ∘ Prod.map upperHalfPlaneCoords id) id
      ∘ ⇑(MeasurableEquiv.prodAssoc (α := ℍ) (β := ℝ)
          (γ := rowIsometrySubgroup ℝ)).symm := by
    funext ⟨z, t, k⟩; rfl
  have hθ₃ : Measurable upperHalfPlaneCoords :=
    measurableEmbedding_upperHalfPlaneCoords.measurable
  have hθ₂ : Measurable
      (⇑MeasurableEquiv.prodAssoc ∘ Prod.map upperHalfPlaneCoords (id : ℝ → ℝ)) :=
    MeasurableEquiv.prodAssoc.measurable.comp (hθ₃.prodMap measurable_id)
  rw [hfact, show hIwasawaSource
      = (volume : Measure ℍ).prod (mulHaarReal.prod haarRowIso) from rfl,
    ← Measure.map_map (hθ₂.prodMap measurable_id)
      (MeasurableEquiv.prodAssoc (α := ℍ)).symm.measurable,
    (measurePreserving_prodAssoc (volume : Measure ℍ) mulHaarReal haarRowIso).symm.map_eq,
    ← Measure.map_prod_map _ _ hθ₂ measurable_id, Measure.map_id,
    ← Measure.map_map MeasurableEquiv.prodAssoc.measurable (hθ₃.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hθ₃ measurable_id, Measure.map_id,
    map_upperHalfPlaneCoords_volume, ← borelHaar₃_eq_map_prodAssoc]

private def hIwasawaParam (p : ℍ × (ℝ × rowIsometrySubgroup ℝ)) : GL (Fin 2) ℝ :=
  iwasawaParam (hIwasawaCoords p)

private theorem hIwasawaParam_eq (z : ℍ) (t : ℝ) (k : rowIsometrySubgroup ℝ) :
    hIwasawaParam (z, t, k)
      = iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t) * (k : GL (Fin 2) ℝ) := rfl

private def skewKpart (g : GL (Fin 2) ℝ) (z : ℍ) : rowIsometrySubgroup ℝ :=
  iwasawaKpart (g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, 1))

private theorem val_mul_iwasawaBorelFactor (g : GL (Fin 2) ℝ) (z : ℍ) {t : ℝ} (ht : 0 < t) :
    ((g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t) : GL (Fin 2) ℝ)
      : Matrix (Fin 2) (Fin 2) ℝ)
    = t • ((g : Matrix (Fin 2) (Fin 2) ℝ)
        * !![(z : ℂ).im, (z : ℂ).re; 0, 1]) := by
  rw [Matrix.GeneralLinearGroup.coe_mul,
    val_iwasawaBorelFactor_box _ ⟨z.coe_im ▸ z.im_pos, ht⟩]
  rw [show (!![t * (z : ℂ).im, t * (z : ℂ).re; 0, t] : Matrix (Fin 2) (Fin 2) ℝ)
      = t • !![(z : ℂ).im, (z : ℂ).re; 0, 1] by
    ext i j; fin_cases i <;> fin_cases j <;> simp]
  rw [Matrix.mul_smul]

private theorem iwasawaKpart_of_val_smul (h₁ h₂ : GL (Fin 2) ℝ) {c : ℝ} (hc : 0 < c)
    (heq : (h₁ : Matrix (Fin 2) (Fin 2) ℝ) = c • (h₂ : Matrix (Fin 2) (Fin 2) ℝ)) :
    iwasawaKpart h₁ = iwasawaKpart h₂ := by
  have hcne := hc.ne'

  have hrow : rowNormSq (h₁ : Matrix (Fin 2) (Fin 2) ℝ)
      = c ^ 2 * rowNormSq (h₂ : Matrix (Fin 2) (Fin 2) ℝ) := by
    unfold rowNormSq
    simp only [heq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  have hX : iwasawaX h₁ = iwasawaX h₂ := by
    unfold iwasawaX topRowDotBottom
    rw [hrow, heq]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have hrne := (rowNormSq_pos h₂).ne'
    field_simp
  have hY : iwasawaY h₁ = iwasawaY h₂ := by
    unfold iwasawaY localHeight
    rw [hrow, heq, Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow,
      Real.norm_eq_abs, abs_of_pos hc, mul_div_mul_left _ _ (pow_ne_zero 2 hcne)]
  have hT : iwasawaT h₁ = c * iwasawaT h₂ := by
    unfold iwasawaT
    rw [hrow, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]

  have hBp : (iwasawaBpart h₁ : Matrix (Fin 2) (Fin 2) ℝ)
      = c • (iwasawaBpart h₂ : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [val_iwasawaBpart, val_iwasawaBpart, hX, hY, hT]
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_assoc]

  have hrec₁ : (iwasawaBpart h₂ : Matrix (Fin 2) (Fin 2) ℝ)
      * ((iwasawaKpart h₁ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (h₂ : Matrix (Fin 2) (Fin 2) ℝ) := by
    have := congrArg (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)
      (iwasawaBpart_mul_iwasawaKpart h₁)
    rw [Matrix.GeneralLinearGroup.coe_mul, hBp, heq, Matrix.smul_mul] at this
    exact smul_right_injective _ hcne this
  have hKGL : (iwasawaKpart h₁ : GL (Fin 2) ℝ) = (iwasawaKpart h₂ : GL (Fin 2) ℝ) := by
    have hrec₂ := congrArg (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)
      (iwasawaBpart_mul_iwasawaKpart h₂)
    rw [Matrix.GeneralLinearGroup.coe_mul] at hrec₂
    refine mul_left_cancel (a := iwasawaBpart h₂) (Units.ext ?_)
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hrec₁, hrec₂]
  exact Subtype.ext hKGL

private theorem iwasawaT_mul_borelFactor (g : GL (Fin 2) ℝ) (z : ℍ) {t : ℝ} (ht : 0 < t) :
    iwasawaT (g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t))
      = ‖UpperHalfPlane.denom g (z : ℂ)‖ * t := by
  have hrow : rowNormSq ((g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t) : GL (Fin 2) ℝ)
        : Matrix (Fin 2) (Fin 2) ℝ)
      = (‖UpperHalfPlane.denom g (z : ℂ)‖ * t) ^ 2 := by
    rw [val_mul_iwasawaBorelFactor g z ht]
    unfold rowNormSq
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one,
      mul_zero, add_zero, mul_one, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs, abs_of_pos ht]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [UpperHalfPlane.denom, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
      add_zero]
    ring
  unfold iwasawaT
  rw [hrow, Real.sqrt_sq (by positivity)]

private theorem iwasawaY_mul_borelFactor (g : GL (Fin 2) ℝ) (z : ℍ) {t : ℝ} (ht : 0 < t) :
    iwasawaY (g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t))
      = (g • z).im := by
  rw [UpperHalfPlane.im_smul_eq_div_normSq g z]
  unfold iwasawaY localHeight
  have hTsq := iwasawaT_sq (g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t))
  rw [iwasawaT_mul_borelFactor g z ht, mul_pow, ← Complex.normSq_eq_norm_sq] at hTsq
  rw [← hTsq, val_mul_iwasawaBorelFactor g z ht, Matrix.det_smul, Fintype.card_fin,
    Matrix.det_mul, Matrix.det_fin_two_of, mul_zero, sub_zero,
    norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos ht]
  have hnsq : (0:ℝ) < Complex.normSq (UpperHalfPlane.denom g (z : ℂ)) :=
    UpperHalfPlane.normSq_denom_pos g (z.coe_im ▸ z.im_pos.ne')
  have him := z.im_pos
  simp only [mul_one, Real.norm_eq_abs, UpperHalfPlane.coe_im, abs_of_pos him,
    ← Matrix.GeneralLinearGroup.val_det_apply]
  field_simp

private theorem iwasawaX_mul_borelFactor (g : GL (Fin 2) ℝ) (z : ℍ) {t : ℝ} (ht : 0 < t) :
    iwasawaX (g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t))
      = (g • z).re := by
  rw [UpperHalfPlane.re_smul g z]
  unfold iwasawaX
  have hTsq := iwasawaT_sq (g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t))
  rw [iwasawaT_mul_borelFactor g z ht, mul_pow, ← Complex.normSq_eq_norm_sq] at hTsq
  rw [← hTsq]

  have htop : topRowDotBottom
        ((g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t) : GL (Fin 2) ℝ)
          : Matrix (Fin 2) (Fin 2) ℝ)
      = t ^ 2 * ((UpperHalfPlane.num g (z : ℂ)).re * (UpperHalfPlane.denom g (z : ℂ)).re
          + (UpperHalfPlane.num g (z : ℂ)).im * (UpperHalfPlane.denom g (z : ℂ)).im) := by
    rw [val_mul_iwasawaBorelFactor g z ht]
    unfold topRowDotBottom
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one,
      mul_zero, add_zero, mul_one]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
      mul_zero]
    ring
  rw [htop, Complex.div_re,
    mul_comm (Complex.normSq _) (t ^ 2),
    mul_div_mul_left _ _ (pow_ne_zero 2 ht.ne'), add_div]

private theorem mul_hIwasawaParam_eq (g : GL (Fin 2) ℝ) (z : ℍ) {t : ℝ} (ht : 0 < t)
    (k : rowIsometrySubgroup ℝ) :
    g * hIwasawaParam (z, t, k)
      = hIwasawaParam
          (g • z, ‖UpperHalfPlane.denom g (z : ℂ)‖ * t, skewKpart g z * k) := by
  set h := g * iwasawaBorelFactor ((z : ℂ).re, (z : ℂ).im, t) with hh

  have hcoords : iwasawaCoords h
      = ((g • z).re, (g • z).im, ‖UpperHalfPlane.denom g (z : ℂ)‖ * t) := by
    unfold iwasawaCoords
    rw [hh, iwasawaX_mul_borelFactor g z ht, iwasawaY_mul_borelFactor g z ht,
      iwasawaT_mul_borelFactor g z ht]

  have hK : iwasawaKpart h = skewKpart g z := by
    refine iwasawaKpart_of_val_smul _ _ ht ?_
    rw [hh, val_mul_iwasawaBorelFactor g z ht,
      val_mul_iwasawaBorelFactor g z one_pos, one_smul]
  rw [hIwasawaParam_eq, hIwasawaParam_eq, ← mul_assoc, ← hh,
    ← iwasawaBpart_mul_iwasawaKpart h, hK, mul_assoc,
    show (skewKpart g z : GL (Fin 2) ℝ) * (k : GL (Fin 2) ℝ)
      = ((skewKpart g z * k : rowIsometrySubgroup ℝ) : GL (Fin 2) ℝ) from rfl]
  congr 1
  unfold iwasawaBpart
  rw [hcoords, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]

private theorem measurePreserving_glSmul_upperHalfPlane (g : GL (Fin 2) ℝ) :
    MeasurePreserving (g • · : ℍ → ℍ) volume volume :=
  measurePreserving_smul g volume

private theorem map_mul_mulHaarReal {b : ℝ} (hb : 0 < b) :
    Measure.map (b * ·) mulHaarReal = mulHaarReal := by
  have hbne := hb.ne'
  set e := MeasurableEquiv.mulLeft₀ b hbne with he
  have hcoe : (b * ·) = ⇑e := rfl
  unfold mulHaarReal
  rw [hcoe, map_withDensity_measurableEquiv _ _ _ (by fun_prop)]

  have hIoi : e ⁻¹' Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) := by
    ext x; simp only [he, Set.mem_preimage, MeasurableEquiv.coe_mulLeft₀, Set.mem_Ioi,
      mul_pos_iff_of_pos_left hb]
  rw [show Measure.map (⇑e) ((volume : Measure ℝ).restrict (Set.Ioi (0:ℝ)))
      = ENNReal.ofReal b⁻¹ • ((volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))) by
    conv_lhs => rw [← hIoi, ← MeasurableEquiv.restrict_map]
    rw [show Measure.map (⇑e) (volume : Measure ℝ) = ENNReal.ofReal b⁻¹ • volume by
      rw [he, MeasurableEquiv.coe_mulLeft₀, Real.map_volume_mul_left hbne,
        abs_of_pos (inv_pos.2 hb)],
      Measure.restrict_smul]]

  rw [withDensity_smul_measure,
    ← withDensity_smul _ (by rw [he]; fun_prop)]
  congr 1
  funext s
  simp only [he, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    MeasurableEquiv.symm_mulLeft₀, MeasurableEquiv.coe_mulLeft₀, mul_inv, inv_inv]
  rw [← ENNReal.ofReal_mul (inv_pos.2 hb).le]
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ hbne, one_mul]

private theorem map_mul_haarRowIso (κ : rowIsometrySubgroup ℝ) :
    letI := rowIsoBorel
    Measure.map (κ * ·) haarRowIso = haarRowIso := by
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel
  show Measure.map (κ * ·) (Measure.haar : Measure (rowIsometrySubgroup ℝ)) = Measure.haar
  exact map_mul_left_eq_self Measure.haar κ

private theorem continuous_skewKpart (g : GL (Fin 2) ℝ) : Continuous (skewKpart g) := by
  refine continuous_iwasawaKpart.comp ((continuous_const_mul g).comp ?_)
  refine ContinuousOn.comp_continuous continuousOn_iwasawaBorelFactor_box ?_
    (fun z => ⟨z.coe_im ▸ z.im_pos, one_pos⟩)
  fun_prop

private def hIwasawaSkew (g : GL (Fin 2) ℝ) (p : ℍ × (ℝ × rowIsometrySubgroup ℝ)) :
    ℍ × (ℝ × rowIsometrySubgroup ℝ) :=
  (g • p.1, (‖UpperHalfPlane.denom g (p.1 : ℂ)‖ * p.2.1, skewKpart g p.1 * p.2.2))

private theorem measurable_hIwasawaSkew_fibre (g : GL (Fin 2) ℝ) :
    letI := rowIsoBorel
    Measurable (Function.uncurry fun (z : ℍ) (tk : ℝ × rowIsometrySubgroup ℝ) =>
      (‖UpperHalfPlane.denom g (z : ℂ)‖ * tk.1, skewKpart g z * tk.2)) := by
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel
  have hdenom : Continuous (fun z : ℍ => ‖UpperHalfPlane.denom g (z : ℂ)‖) := by
    refine continuous_norm.comp ?_
    unfold UpperHalfPlane.denom
    fun_prop
  refine Measurable.prodMk ?_ (Continuous.measurable ?_)
  · exact (hdenom.measurable.comp measurable_fst).mul (measurable_fst.comp measurable_snd)
  · exact ((continuous_skewKpart g).comp continuous_fst).mul
      (continuous_snd.comp continuous_snd)

private theorem measurePreserving_hIwasawaSkew (g : GL (Fin 2) ℝ) :
    letI := rowIsoBorel
    MeasurePreserving (hIwasawaSkew g) hIwasawaSource hIwasawaSource := by
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel
  show MeasurePreserving (hIwasawaSkew g)
    ((volume : Measure ℍ).prod (mulHaarReal.prod haarRowIso))
    ((volume : Measure ℍ).prod (mulHaarReal.prod haarRowIso))

  refine (measurePreserving_glSmul_upperHalfPlane g).skew_product
    (measurable_hIwasawaSkew_fibre g)
    (Filter.Eventually.of_forall fun z => ?_)

  have hbpos : (0:ℝ) < ‖UpperHalfPlane.denom g (z : ℂ)‖ :=
    norm_pos_iff.mpr (UpperHalfPlane.denom_ne_zero g z)
  rw [show (fun (tk : ℝ × rowIsometrySubgroup ℝ) =>
        (‖UpperHalfPlane.denom g (z : ℂ)‖ * tk.1, skewKpart g z * tk.2))
      = Prod.map (‖UpperHalfPlane.denom g (z : ℂ)‖ * ·) (skewKpart g z * ·) from rfl,
    ← Measure.map_prod_map _ _ (measurable_const_mul _) (measurable_const_mul _),
    map_mul_mulHaarReal hbpos, map_mul_haarRowIso]

private theorem mul_hIwasawaParam_ae_eq (g : GL (Fin 2) ℝ) :
    letI := rowIsoBorel
    (fun p => g * hIwasawaParam p) =ᵐ[hIwasawaSource]
      (fun p => hIwasawaParam (hIwasawaSkew g p)) := by
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel
  have h1 : ∀ᵐ t ∂mulHaarReal, (0:ℝ) < t := by
    unfold mulHaarReal
    refine (ae_withDensity_iff (by fun_prop)).mpr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht _
    exact ht
  have h2 : ∀ᵐ tk ∂(mulHaarReal.prod haarRowIso), (0:ℝ) < tk.1 := by
    refine (Measure.ae_prod_iff_ae_ae (p := fun tk => 0 < tk.1)
      (measurableSet_lt measurable_const measurable_fst)).mpr ?_
    filter_upwards [h1] with t ht
    exact Filter.Eventually.of_forall fun _ => ht
  have h3 : ∀ᵐ p ∂hIwasawaSource, (0:ℝ) < p.2.1 := by
    show ∀ᵐ p ∂((volume : Measure ℍ).prod (mulHaarReal.prod haarRowIso)), (0:ℝ) < p.2.1
    refine (Measure.ae_prod_iff_ae_ae
      (p := fun (p : ℍ × (ℝ × rowIsometrySubgroup ℝ)) => (0:ℝ) < p.2.1)
      (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd))).mpr ?_
    exact Filter.Eventually.of_forall fun _ => h2
  filter_upwards [h3] with p hp
  exact mul_hIwasawaParam_eq g p.1 hp p.2.2

private theorem isMulLeftInvariant_iwasawaHaar :
    letI := realGLBorel; haveI := borelSpace_realGLBorel; iwasawaHaar.IsMulLeftInvariant := by
  letI := realGLBorel; letI := rowIsoBorel
  haveI := borelSpace_realGLBorel; haveI := borelSpace_rowIsoBorel
  refine ⟨fun g => ?_⟩
  have hmΦ : Measurable hIwasawaParam :=
    measurable_iwasawaParam.comp measurable_hIwasawaCoords

  have hΨ : iwasawaHaar = Measure.map hIwasawaParam hIwasawaSource := by
    show Measure.map iwasawaParam (borelHaar₃.prod haarRowIso)
      = Measure.map hIwasawaParam hIwasawaSource
    rw [← map_hIwasawaCoords_hIwasawaSource,
      Measure.map_map measurable_iwasawaParam measurable_hIwasawaCoords]
    rfl
  have hmg : Measurable (g * · : GL (Fin 2) ℝ → GL (Fin 2) ℝ) :=
    (continuous_const_mul g).measurable
  rw [hΨ, Measure.map_map hmg hmΦ,
    show (g * ·) ∘ hIwasawaParam = fun p => g * hIwasawaParam p from rfl,
    Measure.map_congr (mul_hIwasawaParam_ae_eq g),
    show (fun p => hIwasawaParam (hIwasawaSkew g p)) = hIwasawaParam ∘ hIwasawaSkew g from rfl,
    ← Measure.map_map hmΦ (measurePreserving_hIwasawaSkew g).measurable,
    (measurePreserving_hIwasawaSkew g).map_eq]

private theorem iwasawaBox_eq_prodSet :
    iwasawaBox = Set.univ ×ˢ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) := by
  ext ⟨x, y, t⟩; simp [iwasawaBox, Set.mem_prod]

private theorem borelHaar₃_compl_iwasawaBox : borelHaar₃ iwasawaBoxᶜ = 0 := by
  unfold borelHaar₃
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply isOpen_iwasawaBox.measurableSet.compl, ← iwasawaBox_eq_prodSet,
    Set.compl_inter_self, measure_empty]

private theorem borelHaar₃_lt_top_of_isCompact_subset_box {C : Set (ℝ × ℝ × ℝ)}
    (hC : IsCompact C) (hCbox : C ⊆ iwasawaBox) : borelHaar₃ C < ⊤ := by
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · simp [hCe]

  have hdens : ContinuousOn (fun p : ℝ × ℝ × ℝ => (p.2.1 ^ 2)⁻¹ * p.2.2⁻¹) iwasawaBox := by
    refine ContinuousOn.mul (ContinuousOn.inv₀ (by fun_prop) ?_)
      (ContinuousOn.inv₀ (by fun_prop) ?_)
    · exact fun p hp => pow_ne_zero 2 hp.1.ne'
    · exact fun p hp => hp.2.ne'

  obtain ⟨M, hM⟩ := hC.bddAbove_image (hdens.mono hCbox)

  unfold borelHaar₃
  rw [withDensity_apply _ hC.measurableSet, ← iwasawaBox_eq_prodSet,
    Measure.restrict_restrict hC.measurableSet,
    Set.inter_eq_left.mpr hCbox]
  calc ∫⁻ p in C, ENNReal.ofReal ((p.2.1 ^ 2)⁻¹ * p.2.2⁻¹) ∂volume
      ≤ ∫⁻ _ in C, ENNReal.ofReal M ∂volume := by
        refine setLIntegral_mono' hC.measurableSet (fun p hp => ?_)
        exact ENNReal.ofReal_le_ofReal (hM ⟨p, hp, rfl⟩)
    _ = ENNReal.ofReal M * volume C := by
        rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

private theorem iwasawaCoords_iwasawaBorelFactor {q : ℝ × ℝ × ℝ} (hq : q ∈ iwasawaBox) :
    iwasawaCoords (iwasawaBorelFactor q) = q := by
  obtain ⟨x, y, t⟩ := q
  obtain ⟨hy, ht⟩ : 0 < y ∧ 0 < t := hq
  have hval := val_iwasawaBorelFactor_box (x, y, t) ⟨hy, ht⟩
  have hrow : rowNormSq ((iwasawaBorelFactor (x, y, t) : GL (Fin 2) ℝ)
      : Matrix (Fin 2) (Fin 2) ℝ) = t ^ 2 := by
    unfold rowNormSq; rw [hval]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    ring

  rw [hval] at hrow
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show iwasawaX _ = x
    unfold iwasawaX topRowDotBottom; rw [hval, hrow]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, zero_add]
    field_simp
  · show iwasawaY _ = y
    unfold iwasawaY localHeight; rw [hval, hrow, Matrix.det_fin_two_of]
    simp only [mul_zero, sub_zero, norm_mul, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hy]
    field_simp
  · show iwasawaT _ = t
    unfold iwasawaT; rw [hval, hrow, Real.sqrt_sq ht.le]

private theorem isFiniteMeasureOnCompacts_iwasawaHaar :
    letI := realGLBorel; IsFiniteMeasureOnCompacts iwasawaHaar := by
  letI := realGLBorel; letI := rowIsoBorel
  haveI := borelSpace_realGLBorel; haveI := borelSpace_rowIsoBorel

  haveI hFinK : IsFiniteMeasure haarRowIso := by
    show IsFiniteMeasure (Measure.haar : Measure (rowIsometrySubgroup ℝ)); infer_instance
  refine ⟨fun K hK => ?_⟩

  rw [show iwasawaHaar K = (borelHaar₃.prod haarRowIso) (iwasawaParam ⁻¹' K) from
    Measure.map_apply measurable_iwasawaParam hK.measurableSet]

  have hKO : IsCompact
      ((fun p : GL (Fin 2) ℝ × rowIsometrySubgroup ℝ => p.1 * (p.2 : GL (Fin 2) ℝ))
        '' (K ×ˢ Set.univ)) :=
    (hK.prod isCompact_univ).image
      (continuous_mul.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd)))
  set C := iwasawaCoords '' ((fun p : GL (Fin 2) ℝ × rowIsometrySubgroup ℝ =>
    p.1 * (p.2 : GL (Fin 2) ℝ)) '' (K ×ˢ Set.univ)) with hCdef
  have hC : IsCompact C := hKO.image continuous_iwasawaCoords
  have hCbox : C ⊆ iwasawaBox := by
    rintro _ ⟨h, _, rfl⟩; exact iwasawaCoords_mem_box h

  have hsub : iwasawaParam ⁻¹' K
      ⊆ (C ×ˢ Set.univ) ∪ (iwasawaBoxᶜ ×ˢ (Set.univ : Set (rowIsometrySubgroup ℝ))) := by
    rintro ⟨q, k⟩ hΨ
    rcases em (q ∈ iwasawaBox) with hqbox | hqbox
    ·
      refine Or.inl ⟨?_, trivial⟩
      rw [hCdef]
      exact ⟨iwasawaBorelFactor q,
        ⟨(iwasawaParam (q, k), k⁻¹), ⟨hΨ, trivial⟩, by
          simp only [iwasawaParam_eq]
          rw [mul_assoc, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, mul_one]⟩,
        iwasawaCoords_iwasawaBorelFactor hqbox⟩
    · exact Or.inr ⟨hqbox, trivial⟩

  calc (borelHaar₃.prod haarRowIso) (iwasawaParam ⁻¹' K)
      ≤ (borelHaar₃.prod haarRowIso) ((C ×ˢ Set.univ) ∪ (iwasawaBoxᶜ ×ˢ Set.univ)) :=
        measure_mono hsub
    _ ≤ (borelHaar₃.prod haarRowIso) (C ×ˢ Set.univ)
        + (borelHaar₃.prod haarRowIso) (iwasawaBoxᶜ ×ˢ Set.univ) :=
        measure_union_le _ _
    _ = borelHaar₃ C * haarRowIso Set.univ + 0 := by
        rw [Measure.prod_prod, Measure.prod_prod, borelHaar₃_compl_iwasawaBox, zero_mul]
    _ < ⊤ := by
        rw [add_zero]
        exact ENNReal.mul_lt_top (borelHaar₃_lt_top_of_isCompact_subset_box hC hCbox)
          (measure_lt_top _ _)

private theorem iwasawaHaar_ne_zero :
    letI := realGLBorel; iwasawaHaar ≠ 0 := by
  letI := realGLBorel; letI := rowIsoBorel
  haveI := borelSpace_realGLBorel; haveI := borelSpace_rowIsoBorel
  exact (Measure.map_ne_zero_iff measurable_iwasawaParam.aemeasurable).mpr
    borelHaar₃_prod_haarRowIso_ne_zero

private theorem realGLHaar_eq_smul_iwasawaHaar :
    letI := realGLBorel
    ∃ c : NNReal, 0 < c ∧ realGLHaar = c • iwasawaHaar := by
  letI := realGLBorel; haveI := borelSpace_realGLBorel
  haveI : realGLHaar.IsHaarMeasure := by
    show (Measure.haar : Measure (GL (Fin 2) ℝ)).IsHaarMeasure; infer_instance
  haveI := isMulLeftInvariant_iwasawaHaar
  haveI := isFiniteMeasureOnCompacts_iwasawaHaar

  obtain ⟨c, hceq⟩ : ∃ c : NNReal, iwasawaHaar = c • realGLHaar :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul iwasawaHaar realGLHaar⟩

  have hc : c ≠ 0 := fun h0 => iwasawaHaar_ne_zero (by rw [hceq, h0, zero_smul])
  refine ⟨c⁻¹, inv_pos.mpr (pos_iff_ne_zero.mpr hc), ?_⟩
  rw [hceq, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem lintegral_realGLHaar_eq_iwasawa (f : GL (Fin 2) ℝ → ENNReal)
    (hf : letI := realGLBorel; haveI := borelSpace_realGLBorel; AEMeasurable f realGLHaar) :
    letI := realGLBorel; letI := rowIsoBorel
    ∃ c : NNReal, 0 < c ∧
      ∫⁻ g, f g ∂realGLHaar = (c : ENNReal) * ∫⁻ p, f (iwasawaParam p)
        ∂(borelHaar₃.prod haarRowIso) := by
  letI := realGLBorel; letI := rowIsoBorel
  haveI := borelSpace_realGLBorel; haveI := borelSpace_rowIsoBorel
  obtain ⟨c, hc, heq⟩ := realGLHaar_eq_smul_iwasawaHaar
  refine ⟨c, hc, ?_⟩

  have hac : iwasawaHaar ≪ realGLHaar := by
    rw [heq]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc.ne')
  have hf' : AEMeasurable f iwasawaHaar := hf.mono_ac hac
  rw [heq, lintegral_smul_measure,
    show iwasawaHaar = Measure.map iwasawaParam (borelHaar₃.prod haarRowIso) from rfl,
    lintegral_map' hf' measurable_iwasawaParam.aemeasurable]
  rfl

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part01
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part02

noncomputable section

namespace HeckeDictionary

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.WindowedSiegel

open NumberField.AdelicHaar NumberField.AdelicLevel Set

p2m_open "AdelicDock IsDedekindDomain NumberField.InfinitePlace.Completion"

open scoped Real

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AdelicDock AutomorphicForm

open MeasureTheory IsDedekindDomain

private theorem glpair_ext {g h : AdelicGL2 (𝓞 ℚ) ℚ}
    (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ h) : g = h := by
  ext i j
  refine Prod.ext ?_ ?_
  · exact congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) ha
  · exact congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) hf

private theorem eq_archIncl_mul_finEmbed (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    g = adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ g)
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g) := by
  apply glpair_ext
  · rw [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  · rw [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]

private theorem continuous_finEmbed :
    Continuous (AdelicDock.finEmbed (𝓞 ℚ) ℚ) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
        (↑g⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

private theorem continuous_adelicMatrixProdEquiv_symm :
    Continuous (adelicMatrixProdEquiv ℚ).symm := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun p : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) ×
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
    ((p.1 i j, p.2 i j) : AdeleRing (𝓞 ℚ) ℚ)
  exact (continuous_fst.matrix_elem i j).prodMk (continuous_snd.matrix_elem i j)

private theorem continuous_adelicArchGLIncl :
    Continuous (adelicArchGLIncl ℚ) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · have heq : ∀ k : GL (Fin 2) (InfiniteAdeleRing ℚ),
        (((adelicArchGLIncl ℚ k) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j)
          = (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
              ((1 : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
            AdeleRing (𝓞 ℚ) ℚ) := fun k => rfl
    exact ((Units.continuous_val.matrix_elem i j).prodMk continuous_const).congr
      fun k => (heq k).symm
  · have heq : ∀ k : GL (Fin 2) (InfiniteAdeleRing ℚ),
        ((↑((adelicArchGLIncl ℚ k)⁻¹) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j)
          = (((↑k⁻¹ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
              ((1 : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
            AdeleRing (𝓞 ℚ) ℚ) := fun k => by
      rw [← map_inv]; rfl
    exact ((Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const).congr
      fun k => (heq k).symm

private def adelicGLProdEquiv :
    AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ*
      (GL (Fin 2) (InfiniteAdeleRing ℚ) × GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) where
  toFun g := (glArch (𝓞 ℚ) ℚ g, glFin (𝓞 ℚ) ℚ g)
  invFun p := adelicArchGLIncl ℚ p.1 * AdelicDock.finEmbed (𝓞 ℚ) ℚ p.2
  left_inv g := (eq_archIncl_mul_finEmbed g).symm
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp only [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
    · simp only [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]
  map_mul' g h := by simp only [map_mul, Prod.mk_mul_mk]
  continuous_toFun := (continuous_glArch (𝓞 ℚ) ℚ).prodMk (continuous_glFin (𝓞 ℚ) ℚ)
  continuous_invFun := by
    refine Continuous.mul ?_ ?_
    · exact continuous_adelicArchGLIncl.comp continuous_fst
    · exact continuous_finEmbed.comp continuous_snd

@[scoped simp] private theorem adelicGLProdEquiv_apply (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    adelicGLProdEquiv g = (glArch (𝓞 ℚ) ℚ g, glFin (𝓞 ℚ) ℚ g) := rfl

@[scoped simp] private theorem adelicGLProdEquiv_symm_apply
    (p : GL (Fin 2) (InfiniteAdeleRing ℚ) × GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    adelicGLProdEquiv.symm p = adelicArchGLIncl ℚ p.1 * AdelicDock.finEmbed (𝓞 ℚ) ℚ p.2 := rfl

private scoped instance instLCMatArch : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))

private scoped instance instLCMatFin : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ))

private scoped instance instLCGLArch : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing ℚ)) :=
  inferInstance

private scoped instance instLCGLFin : LocallyCompactSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstance

@[reducible] private def archGLBorel : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing ℚ)) := borel _

private theorem borelSpace_archGLBorel :
    @BorelSpace (GL (Fin 2) (InfiniteAdeleRing ℚ)) _ archGLBorel :=
  @BorelSpace.mk _ _ archGLBorel rfl

@[reducible] private def finGLBorel : MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := borel _

private theorem borelSpace_finGLBorel :
    @BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) _ finGLBorel :=
  @BorelSpace.mk _ _ finGLBorel rfl

private def archGLHaar : @Measure (GL (Fin 2) (InfiniteAdeleRing ℚ)) archGLBorel := by
  letI := archGLBorel; haveI := borelSpace_archGLBorel; exact Measure.haar

private def finGLHaar : @Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) finGLBorel := by
  letI := finGLBorel; haveI := borelSpace_finGLBorel; exact Measure.haar

private theorem isHaarMeasure_archGLHaar :
    letI := archGLBorel; archGLHaar.IsHaarMeasure := by
  letI := archGLBorel; haveI := borelSpace_archGLBorel
  exact Measure.isHaarMeasure_haarMeasure _

private theorem isHaarMeasure_finGLHaar :
    letI := finGLBorel; finGLHaar.IsHaarMeasure := by
  letI := finGLBorel; haveI := borelSpace_finGLBorel
  exact Measure.isHaarMeasure_haarMeasure _

private theorem regular_adelicGLHaar :
    letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
    (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).Regular := by
  letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  show (Measure.haar : Measure (AdelicGL2 (𝓞 ℚ) ℚ)).Regular
  infer_instance

private theorem regular_archGLHaar :
    letI := archGLBorel; archGLHaar.Regular := by
  letI := archGLBorel; haveI := borelSpace_archGLBorel
  show (Measure.haar : Measure (GL (Fin 2) (InfiniteAdeleRing ℚ))).Regular
  infer_instance

private theorem regular_finGLHaar :
    letI := finGLBorel; finGLHaar.Regular := by
  letI := finGLBorel; haveI := borelSpace_finGLBorel
  show (Measure.haar : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))).Regular
  infer_instance

private scoped instance sigmaCompactSpace_completion (v : InfinitePlace ℚ) : SigmaCompactSpace v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isClosedEmbedding.sigmaCompactSpace

private scoped instance sigmaCompactSpace_infiniteAdeleRing : SigmaCompactSpace (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SigmaCompactSpace ((v : InfinitePlace ℚ) → v.Completion))

private theorem countable_of_free_finite_int : Countable (𝓞 ℚ) :=
  Countable.of_equiv _ (Module.Free.chooseBasis ℤ (𝓞 ℚ)).equivFun.toEquiv.symm

private theorem iUnion_smul_integralFiniteAdeles :
    ⋃ s : 𝓞 ℚ, (fun z => algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ s)⁻¹ * z) ''
      NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨s, hs0, hs⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles (𝓞 ℚ) ℚ y
  refine Set.mem_iUnion.mpr ⟨s, _, hs, ?_⟩
  have hsK : algebraMap (𝓞 ℚ) ℚ s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).mpr hs0
  show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ s)⁻¹ *
      (algebraMap (𝓞 ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ) s * y) = y
  rw [← mul_assoc, IsScalarTower.algebraMap_apply (𝓞 ℚ) ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) s, ← map_mul,
    inv_mul_cancel₀ hsK, map_one, one_mul]

private theorem isCompact_integralFiniteAdeles :
    IsCompact (NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      CompactSpace ((v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) := fun v =>
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ))
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (A := fun v : HeightOneSpectrum (𝓞 ℚ) => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

private scoped instance sigmaCompactSpace_finiteAdeleRing : SigmaCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  haveI : Countable (𝓞 ℚ) := countable_of_free_finite_int
  refine ⟨?_⟩
  rw [← iUnion_smul_integralFiniteAdeles]
  exact isSigmaCompact_iUnion_of_isCompact _ fun s =>
    isCompact_integralFiniteAdeles.image (continuous_const.mul continuous_id)

private scoped instance instSCMatArch : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
  inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))

private scoped instance instSCMatFin : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ))

private scoped instance sigmaCompactSpace_adeleRing : SigmaCompactSpace (AdeleRing (𝓞 ℚ) ℚ) :=
  inferInstanceAs (SigmaCompactSpace (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ))

private scoped instance instSCMatAdele : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → AdeleRing (𝓞 ℚ) ℚ))

private scoped instance instSCMulOpposite {M : Type*} [TopologicalSpace M] [SigmaCompactSpace M] :
    SigmaCompactSpace Mᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace

private scoped instance instSCGLArch : SigmaCompactSpace (GL (Fin 2) (InfiniteAdeleRing ℚ)) :=
  Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private scoped instance instSCGLFin : SigmaCompactSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private scoped instance instSCGLAdele : SigmaCompactSpace (AdelicGL2 (𝓞 ℚ) ℚ) :=
  Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private theorem sigmaFinite_archGLHaar :
    letI := archGLBorel; SigmaFinite archGLHaar := by
  letI := archGLBorel; haveI := borelSpace_archGLBorel
  haveI := isHaarMeasure_archGLHaar
  exact Measure.IsHaarMeasure.sigmaFinite _

private theorem sigmaFinite_finGLHaar :
    letI := finGLBorel; SigmaFinite finGLHaar := by
  letI := finGLBorel; haveI := borelSpace_finGLBorel
  haveI := isHaarMeasure_finGLHaar
  exact Measure.IsHaarMeasure.sigmaFinite _

private theorem sigmaFinite_adelicGLHaar :
    letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
    SigmaFinite (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  letI := glBorel (Fin 2) (𝓞 ℚ) ℚ; haveI := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  exact Measure.IsHaarMeasure.sigmaFinite _

private theorem adelicGLHaar_eq_haarScalarFactor_smul_map_prod :
    letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
    letI := archGLBorel; letI := finGLBorel
    ∃ c : NNReal, 0 < c ∧
      adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
        = c • Measure.map (adelicGLProdEquiv.symm : _ → AdelicGL2 (𝓞 ℚ) ℚ)
            (archGLHaar.prod finGLHaar) := by
  letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  letI := archGLBorel; haveI := borelSpace_archGLBorel
  letI := finGLBorel; haveI := borelSpace_finGLBorel
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  haveI := isHaarMeasure_archGLHaar
  haveI := isHaarMeasure_finGLHaar
  haveI := sigmaFinite_archGLHaar
  haveI := sigmaFinite_finGLHaar

  haveI : ∀ v : InfinitePlace ℚ, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
    inferInstanceAs (SecondCountableTopology ((v : InfinitePlace ℚ) → v.Completion))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing ℚ)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing ℚ) × GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    Prod.borelSpace
  haveI : (archGLHaar.prod finGLHaar).IsHaarMeasure := by infer_instance
  set ν : Measure (AdelicGL2 (𝓞 ℚ) ℚ) :=
    Measure.map (⇑(adelicGLProdEquiv.symm : _ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ))
      (archGLHaar.prod finGLHaar) with hν_def
  haveI hνHaar : ν.IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map _ adelicGLProdEquiv.symm
  set c := (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).haarScalarFactor ν with hc_def
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨c, hc, ?_⟩

  have hopen : ∀ s, IsOpen s → adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ s = (c • ν) s := fun s hs => by
    have := Measure.measure_isHaarMeasure_eq_smul_of_isOpen
      (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ν hs
    simp only [Measure.coe_smul, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] at this ⊢
    exact this

  let K : CompactExhaustion (AdelicGL2 (𝓞 ℚ) ℚ) := CompactExhaustion.choice _
  refine Measure.ext_of_generateFrom_of_iUnion {s | IsOpen s} (fun n => interior (K (n + 1)))
    BorelSpace.measurable_eq isPiSystem_isOpen ?_
    (fun n => show IsOpen (interior (K (n + 1))) from isOpen_interior) ?_
    (fun s hs => hopen s hs)
  ·
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact Set.mem_iUnion.mpr ⟨n, K.subset_interior_succ n hn⟩
  ·
    intro n
    exact ((K.isCompact (n + 1)).measure_lt_top.trans_le' (measure_mono interior_subset)).ne

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm

p2m_open "MeasureTheory NumberField.InfinitePlace.Completion"

private theorem archGLIncl_archComponent (w : InfinitePlace ℚ) (g : GL (Fin 2) (InfiniteAdeleRing ℚ)) :
    archGLIncl ℚ w (archComponent ℚ w g) = g := by
  ext i j
  show archMatrixUpdate ℚ w ((archComponent ℚ w g : _)) i j = (g : _) i j
  funext v
  rw [Subsingleton.elim v w, archMatrixUpdate_apply_self, archComponent_apply]

private theorem continuous_archGLIncl (w : InfinitePlace ℚ) : Continuous (archGLIncl ℚ w) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · show Continuous fun k : GL (Fin 2) w.Completion =>
      archMatrixUpdate ℚ w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j
    refine continuous_pi fun v => ?_
    rw [show v = w from Subsingleton.elim v w]
    simp only [archMatrixUpdate_apply_self]
    exact Units.continuous_val.matrix_elem i j
  · show Continuous fun k : GL (Fin 2) w.Completion =>
      archMatrixUpdate ℚ w (↑k⁻¹ : Matrix (Fin 2) (Fin 2) w.Completion) i j
    refine continuous_pi fun v => ?_
    rw [show v = w from Subsingleton.elim v w]
    simp only [archMatrixUpdate_apply_self]
    exact Units.continuous_coe_inv.matrix_elem i j

private def archCompletionGLEquiv (w : InfinitePlace ℚ) :
    GL (Fin 2) (InfiniteAdeleRing ℚ) ≃ₜ* GL (Fin 2) w.Completion where
  toFun := archComponent ℚ w
  invFun := archGLIncl ℚ w
  left_inv := archGLIncl_archComponent w
  right_inv := archComponent_archGLIncl_self ℚ w
  map_mul' g h := map_mul (archComponent ℚ w) g h
  continuous_toFun := continuous_archComponent ℚ w
  continuous_invFun := continuous_archGLIncl w

@[scoped simp] private theorem archCompletionGLEquiv_apply (w : InfinitePlace ℚ)
    (g : GL (Fin 2) (InfiniteAdeleRing ℚ)) :
    archCompletionGLEquiv w g = archComponent ℚ w g := rfl

@[scoped simp] private theorem archCompletionGLEquiv_symm_apply (w : InfinitePlace ℚ)
    (k : GL (Fin 2) w.Completion) :
    (archCompletionGLEquiv w).symm k = archGLIncl ℚ w k := rfl

private def realGLEquiv (w : InfinitePlace ℚ) (hw : w.IsReal) :
    GL (Fin 2) w.Completion ≃ₜ* GL (Fin 2) ℝ where
  toMulEquiv := Units.mapEquiv (ringEquivRealOfIsReal hw).mapMatrix.toMulEquiv
  continuous_toFun := Continuous.units_map _ (continuous_id.matrix_map
    (isometryEquivRealOfIsReal hw).continuous)
  continuous_invFun := Continuous.units_map _ (continuous_id.matrix_map
    (isometryEquivRealOfIsReal hw).symm.continuous)

private theorem realGLEquiv_symm_eq_map (w : InfinitePlace ℚ) (hw : w.IsReal) :
    ((realGLEquiv w hw).symm : GL (Fin 2) ℝ → GL (Fin 2) w.Completion)
      = Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom := by
  ext g i j
  rfl

private def archCollapseEquiv (w : InfinitePlace ℚ) (hw : w.IsReal) :
    GL (Fin 2) (InfiniteAdeleRing ℚ) ≃ₜ* GL (Fin 2) ℝ :=
  (archCompletionGLEquiv w).trans (realGLEquiv w hw)

private theorem archCollapseEquiv_symm_apply (w : InfinitePlace ℚ) (hw : w.IsReal) (g : GL (Fin 2) ℝ) :
    adelicArchGLIncl ℚ ((archCollapseEquiv w hw).symm g)
      = adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          (ringEquivRealOfIsReal hw).symm.toRingHom g) := by
  show adelicArchGLIncl ℚ (archGLIncl ℚ w
      (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom g)) = _
  rfl

private scoped instance instLCMatCompletion (w : InfinitePlace ℚ) :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) w.Completion) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → w.Completion))

private scoped instance instLCGLCompletion (w : InfinitePlace ℚ) :
    LocallyCompactSpace (GL (Fin 2) w.Completion) := inferInstance

private scoped instance instSCGLCompletion (w : InfinitePlace ℚ) :
    SecondCountableTopology (GL (Fin 2) w.Completion) := by
  haveI : SecondCountableTopology w.Completion :=
    (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → w.Completion))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private scoped instance instSecondCountableGLArch : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing ℚ)) := by
  haveI : ∀ v : InfinitePlace ℚ, SecondCountableTopology v.Completion := fun v =>
    (isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
    inferInstanceAs (SecondCountableTopology ((v : InfinitePlace ℚ) → v.Completion))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem isHaarMeasure_realGLHaar :
    letI := realGLBorel; realGLHaar.IsHaarMeasure := by
  letI := realGLBorel; haveI := borelSpace_realGLBorel
  exact Measure.isHaarMeasure_haarMeasure _

private theorem archGLHaar_eq_smul_map_realGLHaar (w : InfinitePlace ℚ) (hw : w.IsReal) :
    letI := archGLBorel; letI := realGLBorel
    ∃ c : NNReal, 0 < c ∧
      archGLHaar = c • Measure.map ((archCollapseEquiv w hw).symm : _ → GL (Fin 2) (InfiniteAdeleRing ℚ))
        realGLHaar := by
  letI := archGLBorel; haveI := borelSpace_archGLBorel
  letI := realGLBorel; haveI := borelSpace_realGLBorel
  haveI : archGLHaar.IsHaarMeasure := by
    show (Measure.haar : Measure (GL (Fin 2) (InfiniteAdeleRing ℚ))).IsHaarMeasure
    infer_instance
  haveI := isHaarMeasure_realGLHaar
  set ν : Measure (GL (Fin 2) (InfiniteAdeleRing ℚ)) :=
    Measure.map (⇑((archCollapseEquiv w hw).symm : _ ≃ₜ* GL (Fin 2) (InfiniteAdeleRing ℚ)))
      realGLHaar with hν_def
  haveI : ν.IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map _ (archCollapseEquiv w hw).symm
  exact ⟨archGLHaar.haarScalarFactor ν, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul archGLHaar ν⟩

open AutomorphicForm.SiegelCoordinates

private theorem val_borelCoordGL (x y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    (borelCoordGL x y t hy ht : Matrix (Fin 2) (Fin 2) ℝ) = !![t * y, t * x; 0, t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [borelCoordGL]

private theorem det_borelCoordGL (x y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    (borelCoordGL x y t hy ht : Matrix (Fin 2) (Fin 2) ℝ).det = t ^ 2 * y := by
  rw [val_borelCoordGL, Matrix.det_fin_two_of]; ring

private theorem rowNormSq_borelCoordGL (x y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    rowNormSq (borelCoordGL x y t hy ht : Matrix (Fin 2) (Fin 2) ℝ) = t ^ 2 := by
  unfold rowNormSq
  rw [val_borelCoordGL]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_zero, abs_of_pos ht]; ring

private theorem topNormSq_borelCoordGL (x y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    topNormSq (borelCoordGL x y t hy ht : Matrix (Fin 2) (Fin 2) ℝ) = t ^ 2 * (y ^ 2 + x ^ 2) := by
  unfold topNormSq
  rw [val_borelCoordGL]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos ht, abs_of_pos hy,
    mul_pow, mul_pow, sq_abs]
  ring

private theorem localHeight_borelCoordGL_mul (x y t : ℝ) (hy : 0 < y) (ht : 0 < t)
    {k : GL (Fin 2) ℝ} (hk : IsRowIsometry k) :
    localHeight (borelCoordGL x y t hy ht * k) = y := by
  rw [localHeight_mul_rowIsometry _ hk]
  unfold localHeight
  rw [det_borelCoordGL, rowNormSq_borelCoordGL, Real.norm_eq_abs,
    abs_of_pos (mul_pos (pow_pos ht 2) hy)]
  field_simp

private theorem localHeight_borelCoordGL (x y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    localHeight (borelCoordGL x y t hy ht) = y := by
  have := localHeight_borelCoordGL_mul x y t hy ht (k := 1) isRowIsometry_one
  rwa [mul_one] at this

private theorem xWindowSq_borelCoordGL_mul (x y t : ℝ) (hy : 0 < y) (ht : 0 < t)
    {k : GL (Fin 2) ℝ} (hk : IsRowIsometry k) :
    xWindowSq (borelCoordGL x y t hy ht * k) = x ^ 2 := by
  rw [xWindowSq_mul_rowIsometry _ hk]
  unfold xWindowSq
  rw [topNormSq_borelCoordGL, rowNormSq_borelCoordGL, localHeight_borelCoordGL]
  field_simp
  ring

private theorem norm_det_borelCoordGL_mul (x y t : ℝ) (hy : 0 < y) (ht : 0 < t)
    {k : GL (Fin 2) ℝ} (hk : IsRowIsometry k) :
    ‖((borelCoordGL x y t hy ht * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det‖
      = t ^ 2 * y := by
  have hcoe : ((borelCoordGL x y t hy ht * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (borelCoordGL x y t hy ht : Matrix (Fin 2) (Fin 2) ℝ)
        * (k : Matrix (Fin 2) (Fin 2) ℝ) := rfl
  rw [hcoe, Matrix.det_mul, norm_mul, hk.1, mul_one, det_borelCoordGL, Real.norm_eq_abs,
    abs_of_pos (mul_pos (pow_pos ht 2) hy)]

private theorem det_eq_one_or_neg_one_of_isRowIsometry_real {k : GL (Fin 2) ℝ}
    (hk : IsRowIsometry k) :
    (k : Matrix (Fin 2) (Fin 2) ℝ).det = 1 ∨ (k : Matrix (Fin 2) (Fin 2) ℝ).det = -1 :=
  (abs_eq one_pos.le).mp (Real.norm_eq_abs _ ▸ hk.1)

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.WindowedSiegel

open NumberField.AdelicHaar NumberField.AdelicLevel Set

open scoped Real

private def fcoeff (f : ℂ → ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0:ℝ)..1, f (↑x + Complex.I) * Complex.exp (-(2 * ↑π * Complex.I * ↑n * (↑x + Complex.I)))

private def iwasawaSectionGL (z : UpperHalfPlane) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by
    simp [Matrix.det_fin_two_of]
    exact z.im_ne_zero)

private def descentFn (w : InfinitePlace ℚ) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (h : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ)) :
    ℂ → ℂ :=
  fun z => ((z.im : ℝ) : ℂ)⁻¹ *
    φ (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL (UpperHalfPlane.ofComplex z)))
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)

private theorem measure_cappedSiegelBlock_lt_top :
    letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
    adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ (cappedSiegelBlock ℚ (1/2:ℝ) 1 (1/2) 2) < ⊤ := by
  letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  exact IsCompact.measure_lt_top <| isCompact_cappedSiegelBlock (by norm_num) (by norm_num)

section C3Internal

private theorem fcoeff_eq_horizIntegral {f : ℂ → ℂ}
    (hfdiff : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hfper : Function.Periodic f 1) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    fcoeff f n = ∫ x in (0:ℝ)..1, f (↑x + ↑y * Complex.I)
      * Complex.exp (-(2 * ↑π * Complex.I * ↑n * (↑x + ↑y * Complex.I))) := by

  set g : ℂ → ℂ := fun z => f z * Complex.exp (-(2 * ↑π * Complex.I * ↑n * z)) with hg_def
  have hgdiff : DifferentiableOn ℂ g {z : ℂ | 0 < z.im} := by
    refine hfdiff.mul ?_
    exact (differentiable_id.const_mul _).neg.cexp.differentiableOn
  have hgper : Function.Periodic g 1 := by
    intro z
    simp only [hg_def, hfper z]
    congr 1
    have h1 : Complex.exp (-(2 * ↑π * Complex.I * ↑n)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I (-n)
      simpa [mul_comm, mul_assoc, mul_left_comm] using this
    calc Complex.exp (-(2 * ↑π * Complex.I * ↑n * (z + 1)))
        = Complex.exp (-(2 * ↑π * Complex.I * ↑n * z))
          * Complex.exp (-(2 * ↑π * Complex.I * ↑n)) := by
          rw [← Complex.exp_add]; ring_nf
      _ = Complex.exp (-(2 * ↑π * Complex.I * ↑n * z)) := by rw [h1, mul_one]

  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g
    (0 + Complex.I) (1 + ↑y * Complex.I) ?_
  swap
  ·
    refine hgdiff.mono ?_
    rintro w ⟨_, hw2⟩
    simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, Complex.I_im, add_zero,
      zero_add, Complex.mul_im, Complex.ofReal_re, Complex.I_re, mul_one, mul_zero,
      Set.mem_setOf_eq] at hw2 ⊢
    rcases le_or_gt 1 y with h1y | h1y
    · rw [Set.uIcc_of_le h1y] at hw2; linarith [hw2.1]
    · rw [Set.uIcc_of_ge h1y.le] at hw2; linarith [hw2.1]

  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.I_re,
    Complex.add_im, Complex.one_im, Complex.ofReal_im, Complex.I_im,
    Complex.mul_re, Complex.mul_im, mul_one, mul_zero, zero_add, add_zero,
    sub_zero] at hrect

  have hvert : (∫ t : ℝ in (1:ℝ)..y, g (↑(1:ℝ) + ↑t * Complex.I))
      = ∫ t : ℝ in (1:ℝ)..y, g (↑(0:ℝ) + ↑t * Complex.I) := by
    refine intervalIntegral.integral_congr fun t _ht => ?_
    have h0 : (↑(0:ℝ) + ↑t * Complex.I : ℂ) + 1 = ↑(1:ℝ) + ↑t * Complex.I := by
      push_cast; ring
    rw [← h0, hgper]
  rw [hvert, add_sub_assoc, ← smul_sub, sub_self, smul_zero, add_zero,
    sub_eq_zero] at hrect

  calc fcoeff f n = ∫ x in (0:ℝ)..1, g (↑x + Complex.I) := by
        unfold fcoeff; simp only [hg_def]
    _ = ∫ x in (0:ℝ)..1, g (↑x + ↑(1:ℝ) * Complex.I) := by norm_num
    _ = ∫ x in (0:ℝ)..1, g (↑x + ↑y * Complex.I) := hrect
    _ = _ := by simp only [hg_def]

private theorem sq_norm_fcoeff_le_integral_sq_norm {f : ℂ → ℂ}
    (hfdiff : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hfper : Function.Periodic f 1) {n : ℤ} (hn : n ≤ 0) {y : ℝ} (hy : 0 < y) :
    ‖fcoeff f n‖ ^ 2 ≤ ∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)‖ ^ 2 := by
  have h01 : (0:ℝ) < 1 := one_pos

  have hcont : Continuous fun x : ℝ => f (↑x + ↑y * Complex.I) := by
    refine hfdiff.continuousOn.comp_continuous (by fun_prop) (fun x => ?_)
    simpa using hy

  have hle : ‖fcoeff f n‖ ≤ ∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)‖ := by
    rw [fcoeff_eq_horizIntegral hfdiff hfper n hy]
    calc ‖∫ x in (0:ℝ)..1, f (↑x + ↑y * Complex.I)
            * Complex.exp (-(2 * ↑π * Complex.I * ↑n * (↑x + ↑y * Complex.I)))‖
        ≤ ∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)
            * Complex.exp (-(2 * ↑π * Complex.I * ↑n * (↑x + ↑y * Complex.I)))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)‖ := by
          refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
          · exact ((hcont.mul (by fun_prop)).norm).intervalIntegrable 0 1
          · exact hcont.norm.intervalIntegrable 0 1
          · intro x _hx
            rw [norm_mul, Complex.norm_exp]
            have hre : (-(2 * ↑π * Complex.I * ↑n * (↑x + ↑y * Complex.I))).re
                = 2 * π * n * y := by
              simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im,
                Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
                Complex.intCast_re, Complex.intCast_im, Complex.add_re, Complex.add_im,
                Complex.re_ofNat, Complex.im_ofNat]
              ring
            rw [hre]
            calc ‖f (↑x + ↑y * Complex.I)‖ * Real.exp (2 * π * n * y)
                ≤ ‖f (↑x + ↑y * Complex.I)‖ * 1 :=
                  mul_le_mul_of_nonneg_left
                    (Real.exp_le_one_iff.mpr (by
                      have hn' : (n : ℝ) ≤ 0 := Int.cast_nonpos.mpr hn
                      have hny : (n : ℝ) * y ≤ 0 :=
                        mul_nonpos_of_nonpos_of_nonneg hn' hy.le
                      nlinarith [Real.pi_pos]))
                    (norm_nonneg _)
              _ = ‖f (↑x + ↑y * Complex.I)‖ := mul_one _

  have hcs : (∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)‖) ^ 2
      ≤ ∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)‖ ^ 2 := by
    have hmem : MemLp (fun x : ℝ => ‖f (↑x + ↑y * Complex.I)‖) (ENNReal.ofReal 2)
        (volume.restrict (Ioc (0:ℝ) 1)) := by
      have : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) 1)) :=
        ⟨by simp [Real.volume_Ioc]⟩
      refine MemLp.of_bound hcont.norm.aestronglyMeasurable
        (sSup ((fun x : ℝ => ‖f (↑x + ↑y * Complex.I)‖) '' Icc 0 1)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact le_csSup (isCompact_Icc.bddAbove_image hcont.norm.continuousOn)
        ⟨x, Ioc_subset_Icc_self hx, rfl⟩
    have hconst : MemLp (fun _ : ℝ => (1:ℝ)) (ENNReal.ofReal 2)
        (volume.restrict (Ioc (0:ℝ) 1)) := by
      have : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) 1)) :=
        ⟨by simp [Real.volume_Ioc]⟩
      exact memLp_const 1
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (Ioc (0:ℝ) 1))
      (Real.holderConjugate_iff.mpr ⟨one_lt_two, by norm_num⟩)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun _ => zero_le_one)
      hmem hconst
    simp only [mul_one] at hCS
    have hvol : (∫ (_ : ℝ) in Ioc (0:ℝ) 1, (1:ℝ) ^ (2:ℝ)) ^ ((1:ℝ)/2) = 1 := by
      simp only [Real.one_rpow, setIntegral_const, smul_eq_mul, mul_one,
        measureReal_def, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1), Real.one_rpow]
    rw [hvol, mul_one] at hCS
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hnn : 0 ≤ ∫ x in Ioc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ ^ (2:ℝ) :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    calc (∫ x in Ioc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖) ^ 2
        ≤ ((∫ x in Ioc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ ^ (2:ℝ)) ^ (1/2 : ℝ)) ^ 2 := by
          refine sq_le_sq' ?_ hCS
          exact neg_nonpos_of_nonneg (Real.rpow_nonneg hnn _)
            |>.trans (integral_nonneg fun _ => norm_nonneg _)
      _ = ∫ x in Ioc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ ^ 2 := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnn]
          norm_num
  calc ‖fcoeff f n‖ ^ 2
      ≤ (∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ ≤ ∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)‖ ^ 2 := hcs

end C3Internal
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

private theorem fcoeff_nonpos_eq_zero_of_l2_box (f : ℂ → ℂ)
    (hfdiff : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hfper : Function.Periodic f 1)
    (hL2 : Integrable (fun p : ℝ × ℝ => ‖f (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2)
      (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)))) :
    ∀ n : ℤ, n ≤ 0 → fcoeff f n = 0 := by
  intro n hn

  have hbound : ∀ y ∈ Ici (1/2:ℝ),
      ENNReal.ofReal (‖fcoeff f n‖ ^ 2)
        ≤ ∫⁻ x in Icc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ₑ ^ 2 := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le (by norm_num) hy
    have hb := sq_norm_fcoeff_le_integral_sq_norm hfdiff hfper hn hy0

    have hcont : ContinuousOn (fun x : ℝ => f (↑x + ↑y * Complex.I)) (Icc 0 1) := by
      refine (hfdiff.continuousOn.comp (by fun_prop) ?_)
      intro x _hx
      simpa using hy0
    have hint : IntegrableOn (fun x : ℝ => ‖f (↑x + ↑y * Complex.I)‖ ^ 2) (Icc 0 1) :=
      ((hcont.norm.pow 2).integrableOn_Icc)
    calc ENNReal.ofReal (‖fcoeff f n‖ ^ 2)
        ≤ ENNReal.ofReal (∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ∫⁻ x in Icc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ₑ ^ 2 := by
          rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
            ← integral_Icc_eq_integral_Ioc,
            ofReal_integral_eq_lintegral_ofReal hint
              (Filter.Eventually.of_forall fun x => sq_nonneg _)]
          refine lintegral_congr fun x => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

  have hfinite : ∫⁻ y in Ici (1/2:ℝ),
      ∫⁻ x in Icc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ₑ ^ 2 < ⊤ := by

    have hmeas : AEMeasurable
        (fun p : ℝ × ℝ => ‖f (↑p.1 + ↑p.2 * Complex.I)‖ₑ ^ 2)
        (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ))) := by
      refine (hL2.1.enorm).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [enorm_pow, enorm_norm]
    have heq := setLIntegral_prod_symm (μ := volume) (ν := volume)
      (s := Icc (0:ℝ) 1) (t := Ici (1/2:ℝ))
      (fun p => ‖f (↑p.1 + ↑p.2 * Complex.I)‖ₑ ^ 2)
      (by rw [← Measure.volume_eq_prod]; exact hmeas)
    rw [← heq, ← Measure.volume_eq_prod]
    calc ∫⁻ p in Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ),
          ‖f (↑p.1 + ↑p.2 * Complex.I)‖ₑ ^ 2
        = ∫⁻ p in Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ),
          ‖(fun p : ℝ × ℝ => ‖f (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2) p‖ₑ := by
          refine lintegral_congr fun p => ?_
          simp only [enorm_pow, enorm_norm]
      _ < ⊤ := hL2.2
  have hmul : ENNReal.ofReal (‖fcoeff f n‖ ^ 2) * volume (Ici (1/2:ℝ))
      ≤ ∫⁻ y in Ici (1/2:ℝ),
        ∫⁻ x in Icc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ₑ ^ 2 := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_Ici hbound
  rw [Real.volume_Ici] at hmul
  have hfc0 : ‖fcoeff f n‖ ^ 2 = 0 := by
    by_contra h0
    have hp : 0 < ‖fcoeff f n‖ ^ 2 :=
      (sq_nonneg _).lt_of_ne' h0
    have h0' : ENNReal.ofReal (‖fcoeff f n‖ ^ 2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hp).ne'
    rw [ENNReal.mul_top h0'] at hmul
    exact absurd hfinite (not_lt.mpr (le_trans le_top hmul))
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hfc0)

private theorem fcoeff_nonpos_eq_zero_of_weighted_l2_box (f : ℂ → ℂ)
    (hfdiff : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hfper : Function.Periodic f 1)
    (hL2 : Integrable (fun p : ℝ × ℝ => ‖f (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹)
      (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)))) :
    ∀ n : ℤ, n ≤ 0 → fcoeff f n = 0 := by
  intro n hn

  have hbound : ∀ y ∈ Ici (1/2:ℝ),
      ENNReal.ofReal (‖fcoeff f n‖ ^ 2) * ENNReal.ofReal y⁻¹
        ≤ ∫⁻ x in Icc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le (by norm_num) hy
    have hb := sq_norm_fcoeff_le_integral_sq_norm hfdiff hfper hn hy0
    have hcont : ContinuousOn (fun x : ℝ => f (↑x + ↑y * Complex.I)) (Icc 0 1) := by
      refine (hfdiff.continuousOn.comp (by fun_prop) ?_)
      intro x _hx
      simpa using hy0
    have hint : IntegrableOn (fun x : ℝ => ‖f (↑x + ↑y * Complex.I)‖ ^ 2) (Icc 0 1) :=
      ((hcont.norm.pow 2).integrableOn_Icc)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_left ?_ _
    calc ENNReal.ofReal (‖fcoeff f n‖ ^ 2)
        ≤ ENNReal.ofReal (∫ x in (0:ℝ)..1, ‖f (↑x + ↑y * Complex.I)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ∫⁻ x in Icc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ₑ ^ 2 := by
          rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
            ← integral_Icc_eq_integral_Ioc,
            ofReal_integral_eq_lintegral_ofReal hint
              (Filter.Eventually.of_forall fun x => sq_nonneg _)]
          refine lintegral_congr fun x => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

  have hfinite : ∫⁻ y in Ici (1/2:ℝ),
      ∫⁻ x in Icc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ < ⊤ := by
    have hmeas : AEMeasurable
        (fun p : ℝ × ℝ => ‖f (↑p.1 + ↑p.2 * Complex.I)‖ₑ ^ 2 * ENNReal.ofReal p.2⁻¹)
        (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ))) := by
      refine (hL2.1.enorm).congr ?_
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Ici)]
        with p hp
      have hp2 : (0:ℝ) < p.2 := lt_of_lt_of_le (by norm_num) hp.2
      simp only [enorm_mul, enorm_pow, enorm_norm, Real.enorm_eq_ofReal (inv_pos.mpr hp2).le]
    have heq := setLIntegral_prod_symm (μ := volume) (ν := volume)
      (s := Icc (0:ℝ) 1) (t := Ici (1/2:ℝ))
      (fun p => ‖f (↑p.1 + ↑p.2 * Complex.I)‖ₑ ^ 2 * ENNReal.ofReal p.2⁻¹)
      (by rw [← Measure.volume_eq_prod]; exact hmeas)
    rw [← heq, ← Measure.volume_eq_prod]
    calc ∫⁻ p in Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ),
          ‖f (↑p.1 + ↑p.2 * Complex.I)‖ₑ ^ 2 * ENNReal.ofReal p.2⁻¹
        = ∫⁻ p in Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ),
          ‖(fun p : ℝ × ℝ => ‖f (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹) p‖ₑ := by
          refine setLIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Ici) ?_
          intro p hp
          have hp2 : (0:ℝ) < p.2 := lt_of_lt_of_le (by norm_num) hp.2
          simp only [enorm_mul, enorm_pow, enorm_norm,
            Real.enorm_eq_ofReal (inv_pos.mpr hp2).le]
      _ < ⊤ := hL2.2

  have hmul : ENNReal.ofReal (‖fcoeff f n‖ ^ 2) * ∫⁻ y in Ici (1/2:ℝ), ENNReal.ofReal y⁻¹
      ≤ ∫⁻ y in Ici (1/2:ℝ),
        ∫⁻ x in Icc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Ici hbound

  have hdiverge : ∫⁻ y in Ici (1/2:ℝ), ENNReal.ofReal y⁻¹ = ⊤ := by
    by_contra hfin
    have hint : IntegrableOn (fun y : ℝ => y⁻¹) (Ioi (1/2:ℝ)) := by
      refine ⟨measurable_inv.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ y in Ioi (1/2:ℝ), ‖y⁻¹‖ₑ
          = ∫⁻ y in Ioi (1/2:ℝ), ENNReal.ofReal y⁻¹ := by
            refine setLIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
            have hy0 : (0:ℝ) < y := lt_trans (by norm_num) hy
            rw [Real.enorm_eq_ofReal (inv_pos.mpr hy0).le]
        _ ≤ ∫⁻ y in Ici (1/2:ℝ), ENNReal.ofReal y⁻¹ :=
            lintegral_mono' (Measure.restrict_mono Ioi_subset_Ici_self le_rfl) le_rfl
        _ < ⊤ := lt_top_iff_ne_top.mpr hfin
    have hni : ¬ IntegrableOn (fun y : ℝ => y ^ (-1:ℝ)) (Ioi (1/2:ℝ)) := by
      rw [integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ) < 1/2)]
      norm_num
    exact hni (hint.congr_fun (fun y _ => (Real.rpow_neg_one y).symm) measurableSet_Ioi)
  rw [hdiverge] at hmul
  have hfc0 : ‖fcoeff f n‖ ^ 2 = 0 := by
    by_contra h0
    have hp : 0 < ‖fcoeff f n‖ ^ 2 := (sq_nonneg _).lt_of_ne' h0
    have h0' : ENNReal.ofReal (‖fcoeff f n‖ ^ 2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hp).ne'
    rw [ENNReal.mul_top h0'] at hmul
    exact absurd hfinite (not_lt.mpr (le_trans le_top hmul))
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hfc0)

section AssemblyHelpers

open AutomorphicForm.SiegelCoordinates

variable (w : InfinitePlace ℚ) (hw : w.IsReal)

private theorem isRowIsometry_glmap_of_ringEquiv {K L : Type*}
    [NontriviallyNormedField K] [NontriviallyNormedField L]
    (ψ : K ≃+* L) (hψ : ∀ z : K, ‖ψ z‖ = ‖z‖)
    {k : GL (Fin 2) K} (hk : IsRowIsometry k) :
    IsRowIsometry (Matrix.GeneralLinearGroup.map (ψ : K →+* L) k) := by
  have hψ' : ∀ z : L, ‖ψ.symm z‖ = ‖z‖ := fun z => by
    rw [← hψ (ψ.symm z), ψ.apply_symm_apply]
  have heq : ∀ i j,
      (Matrix.GeneralLinearGroup.map (ψ : K →+* L) k : Matrix (Fin 2) (Fin 2) L) i j
        = ψ ((k : Matrix (Fin 2) (Fin 2) K) i j) := fun i j => rfl
  refine ⟨?_, fun x y => ?_⟩
  · have hd : ((Matrix.GeneralLinearGroup.map (ψ : K →+* L) k : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L).det
        = ψ ((k : Matrix (Fin 2) (Fin 2) K).det) := by
      rw [SiegelCoordinates.coe_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [hd, hψ, hk.1]
  ·
    have hbr : ∀ a b : K, ‖x * ψ a + y * ψ b‖ = ‖ψ.symm x * a + ψ.symm y * b‖ := fun a b => by
      have : x * ψ a + y * ψ b = ψ (ψ.symm x * a + ψ.symm y * b) := by
        rw [map_add, map_mul, map_mul, ψ.apply_symm_apply, ψ.apply_symm_apply]
      rw [this, hψ]
    rw [heq, heq, heq, heq, hbr, hbr, hk.2, hψ', hψ']

private theorem isRowIsometry_glmap_of_ringEquiv' {K L : Type*}
    [NontriviallyNormedField K] [NontriviallyNormedField L]
    (ψ : K ≃+* L) (hψ : ∀ z : K, ‖ψ z‖ = ‖z‖)
    {k : GL (Fin 2) K} (hk : IsRowIsometry k) :
    IsRowIsometry (Matrix.GeneralLinearGroup.map ψ.toRingHom k) :=
  isRowIsometry_glmap_of_ringEquiv ψ hψ hk

private theorem det_glmap_toRingHom_eq_one {K L : Type*}
    [NontriviallyNormedField K] [NontriviallyNormedField L]
    (ψ : K ≃+* L) {k : GL (Fin 2) K}
    (hdet : ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1) :
    ((Matrix.GeneralLinearGroup.map ψ.toRingHom k : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L).det = 1 := by
  rw [SiegelCoordinates.coe_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
  exact map_one _

private theorem archInclAt_finEmbed_comm (k' : GL (Fin 2) w.Completion)
    (f : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    adelicArchGLInclAt ℚ w k' * AdelicDock.finEmbed (𝓞 ℚ) ℚ f
      = AdelicDock.finEmbed (𝓞 ℚ) ℚ f * adelicArchGLInclAt ℚ w k' := by
  refine glpair_ext ?_ ?_
  · show glArch (𝓞 ℚ) ℚ (adelicArchGLIncl ℚ _ * _)
      = glArch (𝓞 ℚ) ℚ (_ * adelicArchGLIncl ℚ _)
    rw [map_mul, map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one, one_mul]
  · show glFin (𝓞 ℚ) ℚ (adelicArchGLIncl ℚ _ * _)
      = glFin (𝓞 ℚ) ℚ (_ * adelicArchGLIncl ℚ _)
    rw [map_mul, map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul, mul_one]

private theorem borelCoordGL_eq_scalar_mul (x : ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    borelCoordGL x y t hy ht
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t ht.ne')
        * borelCoordGL x y 1 hy one_pos := by
  refine Units.ext ?_
  show (borelCoordGL x y t hy ht : Matrix (Fin 2) (Fin 2) ℝ)
    = ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t ht.ne') : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)
      * (borelCoordGL x y 1 hy one_pos : Matrix (Fin 2) (Fin 2) ℝ)
  rw [val_borelCoordGL, val_borelCoordGL]
  have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t ht.ne') : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal (fun _ => (t : ℝ)) := by
    ext i j
    show Matrix.scalar (Fin 2) (((Units.mk0 t ht.ne') : ℝˣ) : ℝ) i j = _
    rw [Matrix.scalar_apply]; rfl
  rw [hsc]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

private theorem iwasawaSectionGL_ofComplex_eq_borelCoordGL {x y : ℝ} (hy : 0 < y) :
    iwasawaSectionGL (UpperHalfPlane.ofComplex (↑x + ↑y * Complex.I))
      = borelCoordGL x y 1 hy one_pos := by
  have him : (0 : ℝ) < (↑x + ↑y * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]; exact hy
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  refine Units.ext ?_
  show ((Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(⟨↑x + ↑y*Complex.I, him⟩ : UpperHalfPlane).im,
        (⟨↑x + ↑y*Complex.I, him⟩ : UpperHalfPlane).re; 0, 1] _ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = (borelCoordGL x y 1 hy one_pos : Matrix (Fin 2) (Fin 2) ℝ)
  rw [val_borelCoordGL]
  have hre : (⟨↑x + ↑y*Complex.I, him⟩ : UpperHalfPlane).re = x := by
    show (↑x + ↑y * Complex.I).re = x; simp
  have hi3 : (⟨↑x + ↑y*Complex.I, him⟩ : UpperHalfPlane).im = y := by
    show (↑x + ↑y * Complex.I).im = y
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hre, hi3]

private theorem assemblyImage_mem_centreCutSiegelSet
    {x y t : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy12 : (1/2:ℝ) ≤ y) (ht : 0 < t)
    (htw : t ^ 2 * y ∈ Icc (1/2:ℝ) 2)
    (k : GL (Fin 2) ℝ) (hk : IsRowIsometry k)
    (hf : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ)) :
    adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
        (ringEquivRealOfIsReal hw).symm.toRingHom
        (borelCoordGL x y t (lt_of_lt_of_le (by norm_num) hy12) ht * k))
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf
    ∈ centreCutSiegelSet ℚ (1/2:ℝ) 1 (1/2) 2 := by
  set φ := (ringEquivRealOfIsReal hw).symm.toRingHom
  set Bk : GL (Fin 2) ℝ := borelCoordGL x y t (lt_of_lt_of_le (by norm_num) hy12) ht * k

  have hφ0 : (isometryEquivRealOfIsReal hw).symm (0:ℝ) = 0 :=
    (ringEquivRealOfIsReal hw).symm.map_zero
  have hφ : ∀ z : ℝ, ‖φ z‖ = ‖z‖ := fun z =>
    (isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero hφ0 z
  set g := adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map φ Bk)
    * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf

  have hgla : glArch (𝓞 ℚ) ℚ g = archGLIncl ℚ w (Matrix.GeneralLinearGroup.map φ Bk) := by
    show glArch (𝓞 ℚ) ℚ (adelicArchGLIncl ℚ (archGLIncl ℚ w _) * _) = _
    rw [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  have hglf : glFin (𝓞 ℚ) ℚ g = ↑hf := by
    show glFin (𝓞 ℚ) ℚ (adelicArchGLIncl ℚ (archGLIncl ℚ w _) * _) = _
    rw [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]

  have hcomp : archComponent ℚ w (glArch (𝓞 ℚ) ℚ g) = Matrix.GeneralLinearGroup.map φ Bk := by
    rw [hgla, archComponent_archGLIncl_self]
  refine mem_centreCutSiegelSet_iff.mpr ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  ·
    rw [hglf]; exact hf.2
  ·
    obtain rfl : v = w := Subsingleton.elim v w
    rw [hcomp, localHeight_map φ hφ, localHeight_borelCoordGL_mul _ _ _ _ _ hk]
    exact hy12
  ·
    obtain rfl : v = w := Subsingleton.elim v w
    rw [hcomp, xWindowSq_map φ hφ, xWindowSq_borelCoordGL_mul _ _ _ _ _ hk]
    have hx1 : x ≤ 1 := hx.2
    have hx0 : 0 ≤ x := hx.1
    nlinarith
  ·
    obtain rfl : v = w := Subsingleton.elim v w
    unfold NumberField.AdelicVolume.archDetNorm
    rw [hcomp, SiegelCoordinates.coe_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hφ]
    have hnd : ‖((Bk : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det‖ = t ^ 2 * y :=
      norm_det_borelCoordGL_mul x y t _ ht hk
    rw [hnd]; exact htw

private theorem enorm_phi_assemblyChain_eq_aux
    (ι : GL (Fin 2) ℝ → AdelicGL2 (𝓞 ℚ) ℚ)
    (hι_mul : ∀ a b : GL (Fin 2) ℝ, ι (a * b) = ι a * ι b)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (homegaR : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (ι (Matrix.GeneralLinearGroup.scalar (Fin 2) t) * g)
        = ((t : ℝ) : ℂ) * φ g)
    (L : Ideal (𝓞 ℚ))
    (hlev : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∀ u ∈ levelOne (𝓞 ℚ) ℚ L ⊓ MonoidHom.ker (glArch (𝓞 ℚ) ℚ), φ (g * u) = φ g)
    (h : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ))
    {x y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (k : GL (Fin 2) ℝ) (hf : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ))
    (hfh : (AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf
      ∈ levelOne (𝓞 ℚ) ℚ L ⊓ MonoidHom.ker (glArch (𝓞 ℚ) ℚ))
    (hKinfK : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ (g * ι k)‖ = ‖φ g‖)
    (hcommK : ι k * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf
      = AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf * ι k) :
    ‖φ (ι (borelCoordGL x y t hy ht * k) * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf)‖
      = t * ‖φ (ι (borelCoordGL x y 1 hy one_pos) * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)‖ := by

  calc ‖φ (ι (borelCoordGL x y t hy ht * k) * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf)‖
      = ‖((t : ℝ) : ℂ) * φ (ι (borelCoordGL x y 1 hy one_pos * k)
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf)‖ := by

        rw [borelCoordGL_eq_scalar_mul x hy ht, mul_assoc, hι_mul, mul_assoc,
          homegaR (Units.mk0 t ht.ne') ht _, Units.val_mk0]
    _ = t * ‖φ (ι (borelCoordGL x y 1 hy one_pos)
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf * ι k)‖ := by

        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
          hι_mul, mul_assoc, hcommK, ← mul_assoc]
    _ = t * ‖φ (ι (borelCoordGL x y 1 hy one_pos)
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf)‖ := by

        rw [hKinfK _]
    _ = t * ‖φ (ι (borelCoordGL x y 1 hy one_pos)
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)‖ := by

        congr 2
        conv_lhs => rw [show AdelicDock.finEmbed (𝓞 ℚ) ℚ (↑hf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h
            * ((AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf) by
          rw [← mul_assoc, mul_inv_cancel, one_mul]]
        rw [← mul_assoc]; exact hlev _ _ hfh

private theorem rowIso_glmap_wCompl (ψ : ℝ ≃+* w.Completion) (hψ : ∀ z : ℝ, ‖ψ z‖ = ‖z‖)
    {k₀ : GL (Fin 2) ℝ} (hk₀ : IsRowIsometry k₀) :
    IsRowIsometry (Matrix.GeneralLinearGroup.map ψ.toRingHom k₀) := by
  have hψ' : ∀ z : w.Completion, ‖ψ.symm z‖ = ‖z‖ := fun z => by
    rw [← hψ (ψ.symm z), ψ.apply_symm_apply]
  have heq : ∀ i j, (Matrix.GeneralLinearGroup.map ψ.toRingHom k₀ :
      Matrix (Fin 2) (Fin 2) w.Completion) i j = ψ ((k₀ : Matrix (Fin 2) (Fin 2) ℝ) i j) :=
    fun i j => rfl
  refine ⟨?_, fun x y => ?_⟩
  · have hd : ((Matrix.GeneralLinearGroup.map ψ.toRingHom k₀ : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det
        = ψ ((k₀ : Matrix (Fin 2) (Fin 2) ℝ).det) := by
      rw [SiegelCoordinates.coe_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [hd, hψ, hk₀.1]
  · have hbr : ∀ a b : ℝ, ‖x * ψ a + y * ψ b‖ = ‖ψ.symm x * a + ψ.symm y * b‖ := fun a b => by
      rw [show x * ψ a + y * ψ b = ψ (ψ.symm x * a + ψ.symm y * b) from by
        rw [map_add, map_mul, map_mul, ψ.apply_symm_apply, ψ.apply_symm_apply], hψ]
    rw [heq, heq, heq, heq, hbr, hbr, hk₀.2, hψ', hψ']

private theorem det_glmap_wCompl (ψ : ℝ ≃+* w.Completion) {k₀ : GL (Fin 2) ℝ}
    (hdet₀ : (↑k₀ : Matrix (Fin 2) (Fin 2) ℝ).det = 1) :
    ((Matrix.GeneralLinearGroup.map ψ.toRingHom k₀ : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
  rw [SiegelCoordinates.coe_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet₀]
  exact map_one _

set_option maxHeartbeats 6400000 in
private theorem hKinfR_of_hKinf (ψ : ℝ ≃+* w.Completion) (hψ : ∀ z : ℝ, ‖ψ z‖ = ‖z‖)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hKinf : ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
      (k : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ (g * adelicArchGLInclAt ℚ w k)‖ = ‖φ g‖)
    {k₀ : GL (Fin 2) ℝ} (hk₀ : IsRowIsometry k₀)
    (hdet₀ : (↑k₀ : Matrix (Fin 2) (Fin 2) ℝ).det = 1) :
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ‖φ (g * adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
        ψ.toRingHom k₀))‖ = ‖φ g‖ := by
  intro g

  have h1 : IsRowIsometry (Matrix.GeneralLinearGroup.map ψ.toRingHom k₀) :=
    rowIso_glmap_wCompl w ψ hψ hk₀
  have h2 : ((Matrix.GeneralLinearGroup.map ψ.toRingHom k₀ : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    det_glmap_wCompl w ψ hdet₀
  exact hKinf (Matrix.GeneralLinearGroup.map ψ.toRingHom k₀) h1 h2 g

set_option maxHeartbeats 3200000 in
private theorem archIncl_map_mul (a b : GL (Fin 2) ℝ) :
    adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
        (ringEquivRealOfIsReal hw).symm.toRingHom (a * b))
      = adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          (ringEquivRealOfIsReal hw).symm.toRingHom a)
        * adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          (ringEquivRealOfIsReal hw).symm.toRingHom b) := by
  rw [map_mul, map_mul]

private theorem descentFn_eq_of_im_pos
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (h : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ))
    {x y : ℝ} (hy : 0 < y) :
    descentFn w hw φ h (↑x + ↑y * Complex.I)
      = ((y : ℝ) : ℂ)⁻¹ * φ (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
            (ringEquivRealOfIsReal hw).symm.toRingHom (borelCoordGL x y 1 hy one_pos))
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h) := by
  have hi2 : (↑x + ↑y * Complex.I).im = y := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
  unfold descentFn
  rw [iwasawaSectionGL_ofComplex_eq_borelCoordGL hy, hi2]

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
private theorem enorm_phi_assemblyImage_eq
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          (ringEquivRealOfIsReal hw).symm.toRingHom
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * φ g)
    (L : Ideal (𝓞 ℚ))
    (hlev : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∀ u ∈ levelOne (𝓞 ℚ) ℚ L ⊓ MonoidHom.ker (glArch (𝓞 ℚ) ℚ), φ (g * u) = φ g)
    (hKinf : ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
      (k : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ (g * adelicArchGLInclAt ℚ w k)‖ = ‖φ g‖)
    (h : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ))
    {x y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (k : GL (Fin 2) ℝ) (hk : IsRowIsometry k)
    (hdet : (↑k : Matrix (Fin 2) (Fin 2) ℝ).det = 1)
    (hf : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ))
    (hfh : (AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf
      ∈ levelOne (𝓞 ℚ) ℚ L ⊓ MonoidHom.ker (glArch (𝓞 ℚ) ℚ)) :
    ‖φ (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          (ringEquivRealOfIsReal hw).symm.toRingHom
          (borelCoordGL x y t hy ht * k))
        * AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑hf)‖
      = t * y * ‖descentFn w hw φ h (↑x + ↑y * Complex.I)‖ := by

  have hφiso : ∀ z : ℝ, ‖(ringEquivRealOfIsReal hw).symm z‖ = ‖z‖ := fun z =>
    (isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
      (ringEquivRealOfIsReal hw).symm.map_zero z

  refine (enorm_phi_assemblyChain_eq_aux
    (fun g₀ => adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
      (ringEquivRealOfIsReal hw).symm.toRingHom g₀))
    (archIncl_map_mul w hw) φ homega L hlev h hy ht k hf hfh
    (hKinfR_of_hKinf w (ringEquivRealOfIsReal hw).symm hφiso φ hKinf hk hdet)
    (archInclAt_finEmbed_comm w _ ↑hf)).trans ?_

  rw [descentFn_eq_of_im_pos w hw φ h hy, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hy, mul_assoc, ← mul_assoc y, mul_inv_cancel₀ hy.ne', one_mul]

private theorem lintegral_tWindow_eq {y : ℝ} (hy : 0 < y) :
    ∫⁻ t in {t : ℝ | 0 < t ∧ t ^ 2 * y ∈ Icc (1/2:ℝ) 2},
      ENNReal.ofReal t ∂volume = ENNReal.ofReal (3 / (4 * y)) := by
  set a : ℝ := √(1 / (2 * y)) with ha_def
  set b : ℝ := √(2 / y) with hb_def
  have ha2 : a ^ 2 = 1 / (2 * y) := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = 2 / y := Real.sq_sqrt (by positivity)
  have ha0 : (0 : ℝ) < a := Real.sqrt_pos.mpr (by positivity)
  have hab : a ≤ b := by
    rw [ha_def, hb_def]
    exact Real.sqrt_le_sqrt (by rw [div_le_div_iff₀ (by positivity) hy]; linarith)

  have hset : {t : ℝ | 0 < t ∧ t ^ 2 * y ∈ Icc (1/2:ℝ) 2} = Icc a b := by
    ext t
    simp only [mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨ht0, ht1, ht2⟩
      refine ⟨?_, ?_⟩
      · rw [ha_def, ← Real.sqrt_sq ht0.le]
        refine Real.sqrt_le_sqrt ?_
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * y)]; nlinarith
      · rw [hb_def, ← Real.sqrt_sq ht0.le]
        refine Real.sqrt_le_sqrt ?_
        rw [le_div_iff₀ hy]; linarith
    · rintro ⟨hta, htb⟩
      have ht0 : (0 : ℝ) < t := ha0.trans_le hta
      refine ⟨ht0, ?_, ?_⟩
      · have h1 : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ha0.le hta 2
        rw [ha2] at h1
        have : (1 : ℝ) ≤ t ^ 2 * (2 * y) := (div_le_iff₀ (by positivity)).mp h1
        nlinarith
      · have h2 : t ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ht0.le htb 2
        rw [hb2] at h2
        exact (le_div_iff₀ hy).mp h2
  rw [hset]

  have hcont : ContinuousOn (fun t : ℝ => t) (Icc a b) := continuous_id.continuousOn
  have hint : IntegrableOn (fun t : ℝ => t) (Icc a b) := hcont.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_iff' measurableSet_Icc |>.mpr
      (Filter.Eventually.of_forall fun t ht => (ha0.le.trans ht.1)))]

  congr 1
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, integral_id, ha2, hb2]
  field_simp; ring

private theorem finGLHaar_coset_pos_finite (L : Ideal (𝓞 ℚ)) (hL : L ≠ ⊥)
    (h : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ)) :
    letI := finGLBorel
    0 < finGLHaar ({hf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
        hf ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ ∧
        (AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ hf
          ∈ levelOne (𝓞 ℚ) ℚ L ⊓ MonoidHom.ker (glArch (𝓞 ℚ) ℚ)}) ∧
    finGLHaar ({hf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
        hf ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ ∧
        (AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ hf
          ∈ levelOne (𝓞 ℚ) ℚ L ⊓ MonoidHom.ker (glArch (𝓞 ℚ) ℚ)}) < ⊤ := by
  letI := finGLBorel
  haveI := borelSpace_finGLBorel
  haveI := isHaarMeasure_finGLHaar
  set S := {hf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
    hf ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ ∧
    (AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ hf
      ∈ levelOne (𝓞 ℚ) ℚ L ⊓ MonoidHom.ker (glArch (𝓞 ℚ) ℚ)} with hS_def

  have hSeq : S = (finiteIntegralGL2 (𝓞 ℚ) ℚ : Set _)
      ∩ {hf | ((↑h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))⁻¹ * hf
        ∈ finiteLevelOne (𝓞 ℚ) ℚ L} := by
    ext hf
    simp only [hS_def, mem_setOf_eq, mem_inter_iff, SetLike.mem_coe, Subgroup.mem_inf,
      MonoidHom.mem_ker]
    refine and_congr_right fun _ => ?_
    rw [← map_inv, ← map_mul, AdelicDock.finEmbed_mem_levelOne_iff,
      AdelicDock.glArch_finEmbed]
    exact and_iff_left rfl
  have hOpen : IsOpen S := by
    rw [hSeq]
    refine (isOpen_finiteLevelZero (𝓞 ℚ) ℚ (by exact top_ne_bot)).inter ?_
    exact (isOpen_finiteLevelOne (𝓞 ℚ) ℚ hL).preimage (continuous_const.mul continuous_id)
  have hMem : (↑h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ S := by
    rw [hSeq]
    exact ⟨h.2, by rw [mem_setOf_eq, inv_mul_cancel]; exact (finiteLevelOne (𝓞 ℚ) ℚ L).one_mem⟩
  have hSub : S ⊆ (finiteIntegralGL2 (𝓞 ℚ) ℚ : Set _) := by
    rw [hSeq]; exact inter_subset_left
  refine ⟨?_, ?_⟩
  ·
    exact hOpen.measure_pos finGLHaar ⟨↑h, hMem⟩
  ·
    calc finGLHaar S ≤ finGLHaar (finiteIntegralGL2 (𝓞 ℚ) ℚ : Set _) :=
          measure_mono hSub
      _ < ⊤ := (isCompact_finiteLevelZero (𝓞 ℚ) ℚ ⊤).measure_lt_top

end AssemblyHelpers
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

private theorem aemeasurable_of_comp_fst_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] (hν₀ : ν Set.univ ≠ 0) (hν₁ : ν Set.univ ≠ ⊤)
    {g : α → ENNReal} (h : AEMeasurable (fun z : α × β => g z.1) (μ.prod ν)) :
    AEMeasurable g μ := by
  refine (h.lintegral_prod_right'.mul_const (ν Set.univ)⁻¹).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show (∫⁻ _ : β, g x ∂ν) * (ν Set.univ)⁻¹ = g x
  rw [lintegral_const, mul_assoc, ENNReal.mul_inv_cancel hν₀ hν₁, mul_one]

private theorem adelicL2_dominates_lebesgueBox (w : InfinitePlace ℚ) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
        (centreCutSiegelSet ℚ (1/2:ℝ) 1 (1/2) 2)))
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * φ g)
    (L : Ideal (𝓞 ℚ)) (hL : L ≠ ⊥)
    (hlev : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∀ u ∈ levelOne (𝓞 ℚ) ℚ L ⊓ MonoidHom.ker (glArch (𝓞 ℚ) ℚ), φ (g * u) = φ g)
    (hKinf : ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
      (k : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ (g * adelicArchGLInclAt ℚ w k)‖ = ‖φ g‖)
    (h : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ)) :
    Integrable (fun p : ℝ × ℝ => ‖descentFn w hw φ h (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹)
      (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ))) := by

  letI := glBorel (Fin 2) (𝓞 ℚ) ℚ; haveI := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  letI := archGLBorel; haveI := borelSpace_archGLBorel
  letI := finGLBorel; haveI := borelSpace_finGLBorel
  letI := realGLBorel; haveI := borelSpace_realGLBorel
  letI := rowIsoBorel; haveI := borelSpace_rowIsoBorel
  haveI := sigmaFinite_archGLHaar; haveI := sigmaFinite_finGLHaar
  haveI := isHaarMeasure_finGLHaar

  set D : Set (AdelicGL2 (𝓞 ℚ) ℚ) := centreCutSiegelSet ℚ (1/2:ℝ) 1 (1/2) 2 with hD_def
  have hDmeas : MeasurableSet D := measurableSet_centreCutSiegelSet _ _ _ _
  have hJ : ∫⁻ g in D, ‖φ g‖ₑ ^ (2:ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) < ⊤ := by
    have h2 : ((2:ENNReal).toReal) = (2:ℝ) := by norm_num
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero
      ENNReal.ofNat_ne_top hφ.2
    rwa [h2] at this

  obtain ⟨c₁, hc₁, hG1⟩ := adelicGLHaar_eq_haarScalarFactor_smul_map_prod
  obtain ⟨c₂, hc₂, hG2⟩ := archGLHaar_eq_smul_map_realGLHaar w hw

  set Box : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ) with hBox_def
  set Fh : ℝ × ℝ → ℝ := fun p =>
    ‖descentFn w hw φ h (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹ with hFh_def
  have hFh_nonneg : ∀ p ∈ Box, 0 ≤ Fh p := fun p hp => by
    have hy2 : (0:ℝ) < p.2 := lt_of_lt_of_le (by norm_num) hp.2
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hy2.le)

  obtain ⟨hFh_meas, hI_lt⟩ : AEStronglyMeasurable Fh (volume.restrict Box)
      ∧ ∫⁻ p in Box, ENNReal.ofReal (Fh p) < ⊤ := by

    obtain ⟨c₃, hc₃, hbake⟩ := realGLHaar_eq_smul_iwasawaHaar
    haveI : SigmaFinite realGLHaar := by
      haveI := isHaarMeasure_realGLHaar; exact Measure.IsHaarMeasure.sigmaFinite _

    set E : ((ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ) × GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)
        → AdelicGL2 (𝓞 ℚ) ℚ :=
      fun p => adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          (ringEquivRealOfIsReal hw).symm.toRingHom (iwasawaParam p.1))
        * AdelicDock.finEmbed (𝓞 ℚ) ℚ p.2 with hE_def

    have hE_eq : E = (⇑(adelicGLProdEquiv.symm : _ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ))
        ∘ (Prod.map ((⇑((archCollapseEquiv w hw).symm : _ ≃ₜ* _)) ∘ iwasawaParam) id) := by
      funext p
      show adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          (ringEquivRealOfIsReal hw).symm.toRingHom (iwasawaParam p.1))
        * AdelicDock.finEmbed (𝓞 ℚ) ℚ p.2
        = adelicGLProdEquiv.symm ((archCollapseEquiv w hw).symm (iwasawaParam p.1), p.2)
      rw [adelicGLProdEquiv_symm_apply, archCollapseEquiv_symm_apply]
    have hE2Ψ_meas : Measurable
        ((⇑((archCollapseEquiv w hw).symm : _ ≃ₜ* _)) ∘ iwasawaParam) :=
      ((archCollapseEquiv w hw).symm.continuous.measurable).comp measurable_iwasawaParam
    set μ_P : Measure (((ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ)
        × GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
      (borelHaar₃.prod haarRowIso).prod finGLHaar with hμP_def

    have hE_meas : Measurable E := by
      rw [hE_eq]
      exact (adelicGLProdEquiv.symm.continuous.measurable).comp
        (hE2Ψ_meas.prodMap measurable_id)

    have hHaarEq : adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
        = (((c₁ : ENNReal) * c₂ * c₃) : ENNReal) • Measure.map E μ_P := by

      have hG1' : adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
          = (c₁ : ENNReal) • Measure.map
            (⇑(adelicGLProdEquiv.symm : _ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ))
            (archGLHaar.prod finGLHaar) := by
        rw [hG1, ENNReal.smul_def]
      have hG2' : archGLHaar = (c₂ : ENNReal) • Measure.map
          (⇑((archCollapseEquiv w hw).symm : _ ≃ₜ* _)) realGLHaar := by
        rw [hG2, ENNReal.smul_def]
      have hbake' : realGLHaar = (c₃ : ENNReal) • iwasawaHaar := by
        rw [hbake, ENNReal.smul_def]
      have hiw : iwasawaHaar = Measure.map iwasawaParam (borelHaar₃.prod haarRowIso) := rfl

      have haf : archGLHaar.prod finGLHaar
          = ((c₂:ENNReal) * c₃) • Measure.map
            (Prod.map ((⇑((archCollapseEquiv w hw).symm : _ ≃ₜ* _)) ∘ iwasawaParam) id)
            μ_P := by
        have step1 : Measure.map (⇑((archCollapseEquiv w hw).symm : _ ≃ₜ* _))
              (Measure.map iwasawaParam (borelHaar₃.prod haarRowIso))
            = Measure.map ((⇑((archCollapseEquiv w hw).symm : _ ≃ₜ* _)) ∘ iwasawaParam)
              (borelHaar₃.prod haarRowIso) := by
          refine Measure.map_map ?_ measurable_iwasawaParam
          exact (archCollapseEquiv w hw).symm.continuous.measurable
        rw [hG2', hbake', hiw, Measure.map_smul, smul_smul, step1, Measure.prod_smul_left]
        congr 1
        conv_lhs => rw [show finGLHaar = Measure.map id finGLHaar from (Measure.map_id).symm]
        rw [Measure.map_prod_map _ _ hE2Ψ_meas measurable_id]
      have step2 : Measure.map (⇑(adelicGLProdEquiv.symm : _ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ))
            (Measure.map (Prod.map ((⇑((archCollapseEquiv w hw).symm : _ ≃ₜ* _)) ∘ iwasawaParam)
              id) μ_P)
          = Measure.map E μ_P := by
        refine (Measure.map_map ?_ (hE2Ψ_meas.prodMap measurable_id)).trans ?_
        · exact adelicGLProdEquiv.symm.continuous.measurable
        · rw [← hE_eq]
      rw [hG1', haf, Measure.map_smul, smul_smul, step2, ← mul_assoc]

    set Sxyt : Set (ℝ × ℝ × ℝ) :=
      {q | q.1 ∈ Icc (0:ℝ) 1 ∧ q.2.1 ∈ Ici (1/2:ℝ) ∧ 0 < q.2.2
        ∧ q.2.2 ^ 2 * q.2.1 ∈ Icc (1/2:ℝ) 2} with hSxyt_def
    set Sk : Set (rowIsometrySubgroup ℝ) :=
      {k | ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1} with hSk_def
    set Sgf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
      {gf | gf ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ ∧
        (AdelicDock.finEmbed (𝓞 ℚ) ℚ ↑h)⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ gf
          ∈ levelOne (𝓞 ℚ) ℚ L ⊓ MonoidHom.ker (glArch (𝓞 ℚ) ℚ)} with hSgf_def

    have hSxyt_meas : MeasurableSet Sxyt := by
      have : Sxyt = (Icc (0:ℝ) 1 ×ˢ (Ici (1/2:ℝ) ×ˢ Ioi (0:ℝ)))
          ∩ {q : ℝ × ℝ × ℝ | q.2.2 ^ 2 * q.2.1 ∈ Icc (1/2:ℝ) 2} := by
        ext q
        simp only [hSxyt_def, mem_setOf_eq, mem_inter_iff, mem_prod, mem_Ici, mem_Ioi]
        tauto
      rw [this]
      refine (measurableSet_Icc.prod (measurableSet_Ici.prod measurableSet_Ioi)).inter ?_
      exact measurableSet_preimage
        (((measurable_snd.comp measurable_snd).pow_const 2).mul
          (measurable_fst.comp measurable_snd)) measurableSet_Icc
    have hSk_meas : MeasurableSet Sk := by
      have hdcont : Continuous (fun k : rowIsometrySubgroup ℝ =>
          (((k : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).det) := by fun_prop
      exact hdcont.measurable (measurableSet_singleton 1)
    have hSgf_meas : MeasurableSet Sgf := by

      have hOpen : IsOpen Sgf := by
        have hSeq : Sgf = (finiteIntegralGL2 (𝓞 ℚ) ℚ : Set _)
            ∩ {hf | ((↑h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))⁻¹ * hf
              ∈ finiteLevelOne (𝓞 ℚ) ℚ L} := by
          ext hf
          simp only [hSgf_def, mem_setOf_eq, mem_inter_iff, SetLike.mem_coe, Subgroup.mem_inf,
            MonoidHom.mem_ker]
          refine and_congr_right fun _ => ?_
          rw [← map_inv, ← map_mul, AdelicDock.finEmbed_mem_levelOne_iff,
            AdelicDock.glArch_finEmbed]
          exact and_iff_left rfl
        rw [hSeq]
        exact (isOpen_finiteLevelZero (𝓞 ℚ) ℚ (by exact top_ne_bot)).inter
          ((isOpen_finiteLevelOne (𝓞 ℚ) ℚ hL).preimage (continuous_const.mul continuous_id))
      exact hOpen.measurableSet
    have hSB_meas : MeasurableSet ((Sxyt ×ˢ Sk) ×ˢ Sgf) :=
      (hSxyt_meas.prod hSk_meas).prod hSgf_meas

    have hSB_sub : (Sxyt ×ˢ Sk) ×ˢ Sgf ⊆ E ⁻¹' D := by
      rintro ⟨⟨q, k⟩, gf⟩ ⟨⟨hq, _hk⟩, hgf⟩
      have hy12 : (1/2:ℝ) ≤ q.2.1 := hq.2.1
      have ht : 0 < q.2.2 := hq.2.2.1
      have hy : 0 < q.2.1 := lt_of_lt_of_le (by norm_num) hy12
      show E ((q, k), gf) ∈ D
      simp only [hE_def]

      have hψ : iwasawaParam (q, k) = borelCoordGL q.1 q.2.1 q.2.2 hy ht * ↑k := by
        unfold iwasawaParam; rw [dif_pos ⟨hy, ht⟩]
      rw [hψ, hD_def]
      exact assemblyImage_mem_centreCutSiegelSet w hw hq.1 hy12 ht hq.2.2.2
        ↑k (mem_rowIsometrySubgroup_iff.mp k.2) ⟨gf, hgf.1⟩

    have hcgf := finGLHaar_coset_pos_finite L hL h

    have hck_pos : 0 < haarRowIso Sk := by
      have hSk_eq : Sk = {k : rowIsometrySubgroup ℝ |
          0 < ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det} := by
        ext k
        simp only [hSk_def, mem_setOf_eq]
        rcases det_eq_one_or_neg_one_of_isRowIsometry_real
            (mem_rowIsometrySubgroup_iff.mp k.2) with h1 | hn1
        · rw [h1]; norm_num
        · rw [hn1]; norm_num
      have hSk_open : IsOpen Sk := by
        rw [hSk_eq]
        refine isOpen_lt continuous_const ?_

        fun_prop
      have h1 : (1 : rowIsometrySubgroup ℝ) ∈ Sk := by
        simp only [hSk_def, mem_setOf_eq, OneMemClass.coe_one, Units.val_one, Matrix.det_one]
      haveI : (haarRowIso).IsHaarMeasure := by
        show (Measure.haar : Measure (rowIsometrySubgroup ℝ)).IsHaarMeasure; infer_instance
      exact hSk_open.measure_pos haarRowIso ⟨1, h1⟩
    have hck_fin : haarRowIso Sk < ⊤ := by
      haveI : IsFiniteMeasure haarRowIso := by
        show IsFiniteMeasure (Measure.haar : Measure (rowIsometrySubgroup ℝ)); infer_instance
      exact measure_lt_top haarRowIso Sk

    set C : ENNReal := ((c₁ : ENNReal) * c₂ * c₃) * (finGLHaar Sgf * haarRowIso Sk
        * ENNReal.ofReal (3/4)) with hC_def
    have hCI : AEStronglyMeasurable Fh (volume.restrict Box)
        ∧ C * (∫⁻ p in Box, ENNReal.ofReal (Fh p))
          ≤ ∫⁻ g in D, ‖φ g‖ₑ ^ (2:ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by

      have hφAE_restrict : AEMeasurable (fun g => ‖φ g‖ₑ ^ (2:ℝ))
          ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict D) := by
        simp_rw [ENNReal.rpow_two]
        exact hφ.1.enorm.pow_const 2
      have hφAE_ind : AEMeasurable (D.indicator fun g => ‖φ g‖ₑ ^ (2:ℝ))
          (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
        (aemeasurable_indicator_iff hDmeas).mpr hφAE_restrict
      have hac : Measure.map E μ_P ≪ adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ := by
        have hc : ((c₁ : ENNReal) * c₂ * c₃) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by exact_mod_cast hc₁.ne')
            (by exact_mod_cast hc₂.ne')) (by exact_mod_cast hc₃.ne')
        exact hHaarEq ▸ Measure.absolutelyContinuous_smul hc
      have hφAE : AEMeasurable (D.indicator fun g => ‖φ g‖ₑ ^ (2:ℝ)) (Measure.map E μ_P) :=
        hφAE_ind.mono_ac hac

      have hRHS : ∫⁻ g in D, ‖φ g‖ₑ ^ (2:ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)
          = ((c₁:ENNReal) * c₂ * c₃)
            * ∫⁻ p, D.indicator (fun g => ‖φ g‖ₑ ^ (2:ℝ)) (E p) ∂μ_P := by
        rw [← lintegral_indicator hDmeas, hHaarEq, lintegral_smul_measure,
          lintegral_map' hφAE hE_meas.aemeasurable]
        rfl

      have hMono : ((c₁:ENNReal) * c₂ * c₃)
            * ∫⁻ p in (Sxyt ×ˢ Sk) ×ˢ Sgf, ‖φ (E p)‖ₑ ^ (2:ℝ) ∂μ_P
          ≤ ∫⁻ g in D, ‖φ g‖ₑ ^ (2:ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
        rw [hRHS]
        refine mul_le_mul_right ?_ _
        calc ∫⁻ p in (Sxyt ×ˢ Sk) ×ˢ Sgf, ‖φ (E p)‖ₑ ^ (2:ℝ) ∂μ_P
            = ∫⁻ p in (Sxyt ×ˢ Sk) ×ˢ Sgf,
                D.indicator (fun g => ‖φ g‖ₑ ^ (2:ℝ)) (E p) ∂μ_P := by
              refine setLIntegral_congr_fun hSB_meas ?_
              intro p hp
              exact (indicator_of_mem (show E p ∈ D from hSB_sub hp)
                (fun g => ‖φ g‖ₑ ^ (2:ℝ))).symm
          _ ≤ ∫⁻ p, D.indicator (fun g => ‖φ g‖ₑ ^ (2:ℝ)) (E p) ∂μ_P :=
              setLIntegral_le_lintegral _ _

      have hF1eq : ∀ p ∈ (Sxyt ×ˢ Sk) ×ˢ Sgf,
          ‖φ (E p)‖ₑ ^ (2:ℝ)
            = ENNReal.ofReal ((p.1.1.2.2 * p.1.1.2.1
              * ‖descentFn w hw φ h (↑p.1.1.1 + ↑p.1.1.2.1 * Complex.I)‖) ^ 2) := by
        rintro ⟨⟨q, k⟩, gf⟩ ⟨⟨hq, hk⟩, hgf⟩
        have hy12 : (1/2:ℝ) ≤ q.2.1 := hq.2.1
        have ht : 0 < q.2.2 := hq.2.2.1
        have hy : 0 < q.2.1 := lt_of_lt_of_le (by norm_num) hy12
        have hψ : iwasawaParam (q, k) = borelCoordGL q.1 q.2.1 q.2.2 hy ht * ↑k := by
          unfold iwasawaParam; rw [dif_pos ⟨hy, ht⟩]

        have hF1 := enorm_phi_assemblyImage_eq w hw φ homega L hlev hKinf h
          (x := q.1) hy ht (↑k) (mem_rowIsometrySubgroup_iff.mp k.2) hk ⟨gf, hgf.1⟩ hgf.2
        have hφeq : ‖φ (E ((q, k), gf))‖
            = q.2.2 * q.2.1 * ‖descentFn w hw φ h (↑q.1 + ↑q.2.1 * Complex.I)‖ := by
          simp only [hE_def]; rw [hψ]; exact hF1
        rw [← ofReal_norm (φ _), hφeq, ENNReal.rpow_two]
        exact (ENNReal.ofReal_pow (mul_nonneg (mul_nonneg ht.le hy.le) (norm_nonneg _)) 2).symm

      set G : ℝ × ℝ × ℝ → ENNReal := fun q => ENNReal.ofReal ((q.2.2 * q.2.1
          * ‖descentFn w hw φ h (↑q.1 + ↑q.2.1 * Complex.I)‖) ^ 2) with hG_def

      have hGp : AEMeasurable (fun p : ((ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ)
            × GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => G p.1.1)
          (((borelHaar₃.prod haarRowIso).prod finGLHaar).restrict ((Sxyt ×ˢ Sk) ×ˢ Sgf)) := by
        rw [← hμP_def]
        refine ((hφAE.comp_aemeasurable hE_meas.aemeasurable).restrict).congr ?_
        refine ae_restrict_of_forall_mem hSB_meas fun p hp => ?_
        show D.indicator (fun g => ‖φ g‖ₑ ^ (2:ℝ)) (E p) = G p.1.1
        rw [indicator_of_mem (show E p ∈ D from hSB_sub hp)]
        exact hF1eq p hp
      have hGqk : AEMeasurable (fun qk : (ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ => G qk.1)
          ((borelHaar₃.prod haarRowIso).restrict (Sxyt ×ˢ Sk)) := by
        refine aemeasurable_of_comp_fst_prod (ν := finGLHaar.restrict Sgf) ?_ ?_ ?_
        · rw [Measure.restrict_apply_univ]; exact hcgf.1.ne'
        · rw [Measure.restrict_apply_univ]; exact hcgf.2.ne
        · rw [Measure.prod_restrict]; exact hGp
      have hGq : AEMeasurable G (borelHaar₃.restrict Sxyt) := by
        refine aemeasurable_of_comp_fst_prod (ν := haarRowIso.restrict Sk) ?_ ?_ ?_
        · rw [Measure.restrict_apply_univ]; exact hck_pos.ne'
        · rw [Measure.restrict_apply_univ]; exact hck_fin.ne
        · rw [Measure.prod_restrict]; exact hGqk
      have hTonelli : ∫⁻ p in (Sxyt ×ˢ Sk) ×ˢ Sgf, ‖φ (E p)‖ₑ ^ (2:ℝ) ∂μ_P
          = finGLHaar Sgf * haarRowIso Sk
            * ∫⁻ q in Sxyt, G q ∂borelHaar₃ := by
        rw [setLIntegral_congr_fun hSB_meas hF1eq]

        rw [hμP_def, setLIntegral_prod _ hGp]
        simp only [setLIntegral_const]

        rw [lintegral_mul_const' _ _ hcgf.2.ne, setLIntegral_prod _ hGqk]
        simp only [setLIntegral_const]
        rw [lintegral_mul_const' _ _ hck_fin.ne]
        ring

      set ρ : ℝ × ℝ × ℝ → ENNReal := fun q => ENNReal.ofReal ((q.2.1 ^ 2)⁻¹ * q.2.2⁻¹) with hρ_def
      set cF : ℝ × ℝ → ENNReal := fun xy =>
        ENNReal.ofReal (‖descentFn w hw φ h (↑xy.1 + ↑xy.2 * Complex.I)‖ ^ 2) with hcF_def
      set K : ℝ × ℝ × ℝ → ENNReal := fun q => ENNReal.ofReal q.2.2
        * ENNReal.ofReal (‖descentFn w hw φ h (↑q.1 + ↑q.2.1 * Complex.I)‖ ^ 2) with hK_def
      have hρm : Measurable ρ := by
        rw [hρ_def]; fun_prop
      have hBox_meas : MeasurableSet Box := hBox_def ▸ measurableSet_Icc.prod measurableSet_Ici

      have hbH : borelHaar₃.restrict Sxyt = (volume.restrict Sxyt).withDensity ρ := by
        have hsub : Sxyt ⊆ Set.univ ×ˢ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) := by
          intro q hq
          simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and]
          exact ⟨lt_of_lt_of_le (by norm_num) hq.2.1, hq.2.2.1⟩
        rw [show borelHaar₃
              = (volume.restrict (Set.univ ×ˢ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ))).withDensity ρ
            from rfl,
          restrict_withDensity hSxyt_meas, Measure.restrict_restrict hSxyt_meas,
          Set.inter_eq_self_of_subset_left hsub]
      have hGq' : AEMeasurable G ((volume.restrict Sxyt).withDensity ρ) := by
        rw [← hbH]; exact hGq

      have hpt : ∀ q ∈ Sxyt, (ρ * G) q = K q := by
        intro q hq
        have ht : 0 < q.2.2 := hq.2.2.1
        have hy : 0 < q.2.1 := lt_of_lt_of_le (by norm_num) hq.2.1
        have hρnn : (0:ℝ) ≤ (q.2.1 ^ 2)⁻¹ * q.2.2⁻¹ := by positivity
        have key : ∀ n : ℝ, (q.2.1 ^ 2)⁻¹ * q.2.2⁻¹ * (q.2.2 * q.2.1 * n) ^ 2 = q.2.2 * n ^ 2 := by
          intro n
          have hy2 : (q.2.1 ^ 2)⁻¹ * q.2.1 ^ 2 = 1 := inv_mul_cancel₀ (pow_pos hy 2).ne'
          have ht1 : q.2.2⁻¹ * q.2.2 = 1 := inv_mul_cancel₀ ht.ne'
          calc (q.2.1 ^ 2)⁻¹ * q.2.2⁻¹ * (q.2.2 * q.2.1 * n) ^ 2
              = ((q.2.1 ^ 2)⁻¹ * q.2.1 ^ 2) * (q.2.2⁻¹ * q.2.2) * (q.2.2 * n ^ 2) := by ring
            _ = q.2.2 * n ^ 2 := by simp only [hy2, ht1, one_mul]
        simp only [Pi.mul_apply, hρ_def, hG_def, hK_def]
        rw [← ENNReal.ofReal_mul hρnn, ← ENNReal.ofReal_mul ht.le, key]
      have hGvol : AEMeasurable G (volume.restrict Sxyt) := by
        refine hGq'.mono_ac (withDensity_absolutelyContinuous' hρm.aemeasurable ?_)
        refine ae_restrict_of_forall_mem hSxyt_meas fun q hq => ?_
        have ht : 0 < q.2.2 := hq.2.2.1
        have hy : 0 < q.2.1 := lt_of_lt_of_le (by norm_num) hq.2.1
        simp only [hρ_def]
        exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      have hK : AEMeasurable K (volume.restrict Sxyt) :=
        (hρm.aemeasurable.mul hGvol).congr (ae_restrict_of_forall_mem hSxyt_meas hpt)

      set I : (ℝ × ℝ) × ℝ → ENNReal := fun r => Sxyt.indicator K (MeasurableEquiv.prodAssoc r)
        with hI_def
      have hI : AEMeasurable I ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) :=
        ((aemeasurable_indicator_iff hSxyt_meas).mpr hK).comp_quasiMeasurePreserving
          (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)).quasiMeasurePreserving

      have hinner : ∀ xy : ℝ × ℝ, ∫⁻ t, I (xy, t) ∂volume
          = Box.indicator (fun xy : ℝ × ℝ => ENNReal.ofReal (3 / (4 * xy.2)) * cF xy) xy := by
        intro xy
        by_cases hxy : xy ∈ Box
        · have hy : (0:ℝ) < xy.2 := lt_of_lt_of_le (by norm_num) hxy.2
          have hT_meas : MeasurableSet {t : ℝ | 0 < t ∧ t ^ 2 * xy.2 ∈ Icc (1/2:ℝ) 2} := by
            rw [show {t : ℝ | 0 < t ∧ t ^ 2 * xy.2 ∈ Icc (1/2:ℝ) 2}
                = Ioi (0:ℝ) ∩ (fun t : ℝ => t ^ 2 * xy.2) ⁻¹' Icc (1/2:ℝ) 2 from rfl]
            exact measurableSet_Ioi.inter
              ((by fun_prop : Measurable fun t : ℝ => t ^ 2 * xy.2) measurableSet_Icc)
          have hslice : (fun t : ℝ => I (xy, t))
              = fun t : ℝ => {t : ℝ | 0 < t ∧ t ^ 2 * xy.2 ∈ Icc (1/2:ℝ) 2}.indicator
                  (fun t => ENNReal.ofReal t * cF xy) t := by
            funext t
            show Sxyt.indicator K (xy.1, (xy.2, t)) = _
            by_cases ht : 0 < t ∧ t ^ 2 * xy.2 ∈ Icc (1/2:ℝ) 2
            · have hmem : (xy.1, (xy.2, t)) ∈ Sxyt := by
                simp only [hSxyt_def, Set.mem_setOf_eq]
                exact ⟨hxy.1, hxy.2, ht.1, ht.2⟩
              simp only [indicator_of_mem hmem,
                indicator_of_mem (show t ∈ {t : ℝ | 0 < t ∧ t ^ 2 * xy.2 ∈ Icc (1/2:ℝ) 2} from ht),
                hK_def, hcF_def]
            · have hmem : (xy.1, (xy.2, t)) ∉ Sxyt := by
                intro hm
                simp only [hSxyt_def, Set.mem_setOf_eq] at hm
                exact ht ⟨hm.2.2.1, hm.2.2.2⟩
              simp only [indicator_of_notMem hmem,
                indicator_of_notMem
                  (show t ∉ {t : ℝ | 0 < t ∧ t ^ 2 * xy.2 ∈ Icc (1/2:ℝ) 2} from ht)]
          rw [indicator_of_mem hxy, hslice, lintegral_indicator hT_meas,
            lintegral_mul_const _ ENNReal.measurable_ofReal, lintegral_tWindow_eq hy]
        · rw [indicator_of_notMem hxy]
          have hzero : ∀ t : ℝ, I (xy, t) = 0 := by
            intro t
            have hnot : (xy.1, (xy.2, t)) ∉ Sxyt := by
              intro hm
              simp only [hSxyt_def, Set.mem_setOf_eq] at hm
              exact hxy ⟨hm.1, hm.2.1⟩
            show Sxyt.indicator K (xy.1, (xy.2, t)) = 0
            exact indicator_of_notMem hnot K
          simp only [hzero, lintegral_zero]

      have hpt2 : ∀ xy ∈ Box, ENNReal.ofReal (3 / (4 * xy.2)) * cF xy
          = ENNReal.ofReal (3/4) * ENNReal.ofReal (Fh xy) := by
        intro xy hxy
        have hy : (0:ℝ) < xy.2 := lt_of_lt_of_le (by norm_num) hxy.2
        have h1 : (0:ℝ) ≤ 3 / (4 * xy.2) := by positivity
        have h2 : (0:ℝ) ≤ 3/4 := by norm_num
        simp only [hcF_def, hFh_def]
        rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2]
        congr 1
        ring
      have hCore : ∫⁻ q in Sxyt, G q ∂borelHaar₃
          = ENNReal.ofReal (3/4) * ∫⁻ p in Box, ENNReal.ofReal (Fh p) := by
        rw [hbH, lintegral_withDensity_eq_lintegral_mul₀' hρm.aemeasurable hGq',
          setLIntegral_congr_fun hSxyt_meas hpt, ← lintegral_indicator hSxyt_meas K,
          ← (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)).lintegral_comp_emb
            MeasurableEquiv.prodAssoc.measurableEmbedding (Sxyt.indicator K)]
        change ∫⁻ r, I r ∂((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) = _
        rw [lintegral_prod I hI, lintegral_congr hinner, lintegral_indicator hBox_meas,
          setLIntegral_congr_fun hBox_meas hpt2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

      have hFmeas : AEStronglyMeasurable Fh (volume.restrict Box) := by
        have h1 : AEMeasurable (fun xy : ℝ × ℝ => ∫⁻ t, I (xy, t) ∂volume)
            (volume : Measure (ℝ × ℝ)) := hI.lintegral_prod_right'
        have h2 : AEMeasurable (Box.indicator fun xy : ℝ × ℝ =>
            ENNReal.ofReal (3 / (4 * xy.2)) * cF xy) (volume : Measure (ℝ × ℝ)) :=
          h1.congr (Filter.Eventually.of_forall fun xy => hinner xy)
        have h3 : AEMeasurable (fun xy : ℝ × ℝ => ENNReal.ofReal (3 / (4 * xy.2)) * cF xy)
            (volume.restrict Box) := (aemeasurable_indicator_iff hBox_meas).mp h2
        have h4 : AEMeasurable cF (volume.restrict Box) := by
          have hm : Measurable fun xy : ℝ × ℝ => (ENNReal.ofReal (3 / (4 * xy.2)))⁻¹ := by
            fun_prop
          refine (hm.aemeasurable.mul h3).congr
            (ae_restrict_of_forall_mem hBox_meas fun xy hxy => ?_)
          have hy : (0:ℝ) < xy.2 := lt_of_lt_of_le (by norm_num) hxy.2
          have hc0 : ENNReal.ofReal (3 / (4 * xy.2)) ≠ 0 :=
            (ENNReal.ofReal_pos.mpr (by positivity)).ne'
          show (ENNReal.ofReal (3 / (4 * xy.2)))⁻¹
              * (ENNReal.ofReal (3 / (4 * xy.2)) * cF xy) = cF xy
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
        have h5 : AEMeasurable (fun xy : ℝ × ℝ =>
            ‖descentFn w hw φ h (↑xy.1 + ↑xy.2 * Complex.I)‖ ^ 2) (volume.restrict Box) := by
          refine (ENNReal.measurable_toReal.comp_aemeasurable h4).congr
            (Filter.Eventually.of_forall fun xy => ?_)
          show (cF xy).toReal = _
          simp only [hcF_def]
          exact ENNReal.toReal_ofReal (sq_nonneg _)
        have hinv : Measurable fun xy : ℝ × ℝ => xy.2⁻¹ := by fun_prop
        exact (h5.mul hinv.aemeasurable).aestronglyMeasurable
      refine ⟨hFmeas, ?_⟩

      calc C * (∫⁻ p in Box, ENNReal.ofReal (Fh p))
          = ((c₁:ENNReal) * c₂ * c₃) * (finGLHaar Sgf * haarRowIso Sk
              * (ENNReal.ofReal (3/4) * ∫⁻ p in Box, ENNReal.ofReal (Fh p))) := by
            rw [hC_def]; ring
        _ = ((c₁:ENNReal) * c₂ * c₃) * (finGLHaar Sgf * haarRowIso Sk
              * ∫⁻ q in Sxyt, G q ∂borelHaar₃) := by
            rw [hCore]
        _ = ((c₁:ENNReal) * c₂ * c₃)
              * ∫⁻ p in (Sxyt ×ˢ Sk) ×ˢ Sgf, ‖φ (E p)‖ₑ ^ (2:ℝ) ∂μ_P := by
            rw [hTonelli]
        _ ≤ ∫⁻ g in D, ‖φ g‖ₑ ^ (2:ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := hMono

    have hC_pos : C ≠ 0 := by
      rw [hC_def]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
        (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
      · exact_mod_cast hc₁.ne'
      · exact_mod_cast hc₂.ne'
      · exact_mod_cast hc₃.ne'
      · exact hcgf.1.ne'
      · exact hck_pos.ne'
      · exact (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 3/4)).ne'
    rcases ENNReal.mul_lt_top_iff.mp (lt_of_le_of_lt hCI.2 hJ) with ⟨-, hI⟩ | hC0 | hI0
    · exact ⟨hCI.1, hI⟩
    · exact absurd hC0 hC_pos
    · exact ⟨hCI.1, hI0 ▸ ENNReal.zero_lt_top⟩

  refine ⟨hFh_meas, ?_⟩

  have heq : ∀ᵐ p ∂(volume.restrict Box), ‖Fh p‖ₑ = ENNReal.ofReal (Fh p) := by
    refine (ae_restrict_iff' (hBox_def ▸ measurableSet_Icc.prod measurableSet_Ici)).mpr ?_
    exact Filter.Eventually.of_forall fun p hp => by
      rw [Real.enorm_eq_ofReal (hFh_nonneg p hp)]
  calc ∫⁻ p, ‖Fh p‖ₑ ∂(volume.restrict Box)
      = ∫⁻ p, ENNReal.ofReal (Fh p) ∂(volume.restrict Box) := lintegral_congr_ae heq
    _ < ⊤ := hI_lt

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part02
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part03

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm

open AutomorphicForm.WindowedSiegel UpperHalfPlane

noncomputable section

namespace HeckeDictionary

private def iwasawaSec (z : UpperHalfPlane) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by
    simp [Matrix.det_fin_two_of]
    exact z.im_ne_zero)

@[scoped simp] private theorem coe_iwasawaSec (z : UpperHalfPlane) :
    (iwasawaSec z : Matrix (Fin 2) (Fin 2) ℝ) = !![(z.im : ℝ), (z.re : ℝ); 0, 1] := rfl

private theorem det_iwasawaSec (z : UpperHalfPlane) :
    ((iwasawaSec z : Matrix (Fin 2) (Fin 2) ℝ)).det = z.im := by
  simp [Matrix.det_fin_two_of]

private theorem denom_iwasawaSec (z : UpperHalfPlane) (w : ℂ) :
    denom (iwasawaSec z) w = 1 := by
  simp [denom]

private theorem num_iwasawaSec (z : UpperHalfPlane) (w : ℂ) :
    num (iwasawaSec z) w = (z.im : ℂ) * w + (z.re : ℂ) := by
  simp [num]

private theorem σ_iwasawaSec_apply (z : UpperHalfPlane) (w : ℂ) :
    σ (iwasawaSec z) w = w := by
  unfold σ
  split
  · rfl
  · rename_i h
    exact absurd (show (0 : ℝ) < (!![(z.im : ℝ), (z.re : ℝ); 0, 1]).det by
      simp [Matrix.det_fin_two_of]; exact z.im_pos) h

private theorem iwasawaSec_smul_I (z : UpperHalfPlane) : iwasawaSec z • I = z := by
  apply UpperHalfPlane.ext
  rw [coe_smul, num_iwasawaSec, denom_iwasawaSec, σ_iwasawaSec_apply, div_one,
    UpperHalfPlane.coe_I]
  apply Complex.ext <;> simp

private def kappa (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane) : GL (Fin 2) ℝ :=
  (iwasawaSec (γ • z))⁻¹ * γ * iwasawaSec z

private theorem mul_iwasawaSec_eq (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane) :
    γ * iwasawaSec z = iwasawaSec (γ • z) * kappa γ z := by
  rw [kappa]
  group

private theorem kappa_smul_I (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane) :
    kappa γ z • I = I := by
  rw [kappa, mul_smul, mul_smul, iwasawaSec_smul_I, inv_smul_eq_iff, iwasawaSec_smul_I]

private theorem denom_inv_iwasawaSec (z : UpperHalfPlane) (w : ℂ) :
    denom (iwasawaSec z)⁻¹ w = 1 := by
  have hdet : (!![(z.im : ℝ), (z.re : ℝ); 0, 1]).det = z.im := by
    simp [Matrix.det_fin_two_of]
  have k10 : (!![(z.im : ℝ), (z.re : ℝ); 0, 1])⁻¹ 1 0 = 0 := by
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, hdet]
    simp
  have k11 : (!![(z.im : ℝ), (z.re : ℝ); 0, 1])⁻¹ 1 1 = 1 := by
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, hdet]
    simp [Ring.inverse_eq_inv, inv_mul_cancel₀ z.im_ne_zero]
  simp [denom, k10, k11]

private theorem num_div_denom_iwasawaSec_I (z : UpperHalfPlane) :
    num (iwasawaSec z) Complex.I / denom (iwasawaSec z) Complex.I = (z : ℂ) := by
  rw [num_iwasawaSec, denom_iwasawaSec, div_one]
  apply Complex.ext <;> simp

private theorem denom_kappa (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane) :
    denom (kappa γ z) Complex.I = denom γ (z : ℂ) := by
  have h1 : denom (kappa γ z) Complex.I
      = denom ((iwasawaSec (γ • z))⁻¹ * γ) ((z : ℂ)) * 1 := by
    rw [kappa, denom_cocycle ((iwasawaSec (γ • z))⁻¹ * γ) (iwasawaSec z)
      (by simp : (Complex.I).im ≠ 0), num_div_denom_iwasawaSec_I, denom_iwasawaSec]
  rw [h1, mul_one, denom_cocycle (iwasawaSec (γ • z))⁻¹ γ
    (by exact_mod_cast z.im_ne_zero : (z : ℂ).im ≠ 0), denom_inv_iwasawaSec, one_mul]

private theorem det_kappa (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane)
    (hγ : (0 : ℝ) < ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det) :
    ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)).det = Complex.normSq (denom γ (z : ℂ)) := by
  have him : (γ • z).im = |(Matrix.GeneralLinearGroup.det γ : ℝ)| * z.im
      / Complex.normSq (denom γ (z : ℂ)) := im_smul_eq_div_normSq γ z
  have hdetcoe : (Matrix.GeneralLinearGroup.det γ : ℝ)
      = ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det := rfl
  have hns : Complex.normSq (denom γ (z : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.mpr (denom_ne_zero γ z)).ne'
  have hd : ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)).det
      = ((γ • z).im)⁻¹ * ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det * z.im := by
    rw [kappa]
    simp only [Units.val_mul, Matrix.det_mul, Matrix.coe_units_inv,
      Matrix.det_nonsing_inv, det_iwasawaSec, Ring.inverse_eq_inv]
  rw [hd, him, hdetcoe, abs_of_pos hγ]
  have h0 : z.im ≠ 0 := z.im_ne_zero
  have h1 : ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := ne_of_gt hγ
  field_simp

private theorem kappa_entries (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane)
    (hγ : (0 : ℝ) < ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det) :
    ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)) 1 1
    ∧ ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)) 0 1
      = -((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 := by
  have hdet : (0 : ℝ) < ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)).det := by
    rw [det_kappa γ z hγ]
    exact Complex.normSq_pos.mpr (denom_ne_zero γ z)
  have hI := kappa_smul_I γ z
  have hcoe : (UpperHalfPlane.σ (kappa γ z))
      (num (kappa γ z) (Complex.I) / denom (kappa γ z) (Complex.I)) = Complex.I := by
    have := congrArg (UpperHalfPlane.coe) hI
    rwa [coe_smul, UpperHalfPlane.coe_I] at this
  have hσ : ∀ w : ℂ, σ (kappa γ z) w = w := by
    intro w
    unfold σ
    split
    · rfl
    · rename_i h; exact absurd hdet h
  rw [hσ] at hcoe
  have hden : denom (kappa γ z) Complex.I ≠ 0 :=
    UpperHalfPlane.coe_I ▸ denom_ne_zero (kappa γ z) UpperHalfPlane.I
  have hmul : num (kappa γ z) Complex.I = Complex.I * denom (kappa γ z) Complex.I := by
    rwa [div_eq_iff hden] at hcoe
  simp only [num, denom] at hmul
  have hre := congrArg Complex.re hmul
  have him2 := congrArg Complex.im hmul
  simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im] at hre him2
  constructor
  · linarith [him2]
  · linarith [hre]

private theorem stabilizer_entries (κ : GL (Fin 2) ℝ)
    (hI : κ • I = I) (hdet : (0 : ℝ) < ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det) :
    ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 1
    ∧ ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = -((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 := by
  have hcoe : (UpperHalfPlane.σ κ)
      (num κ (Complex.I) / denom κ (Complex.I)) = Complex.I := by
    have := congrArg (UpperHalfPlane.coe) hI
    rwa [coe_smul, UpperHalfPlane.coe_I] at this
  have hσ : ∀ w : ℂ, σ κ w = w := by
    intro w
    unfold σ
    split
    · rfl
    · rename_i h; exact absurd hdet h
  rw [hσ] at hcoe
  have hden : denom κ Complex.I ≠ 0 :=
    UpperHalfPlane.coe_I ▸ denom_ne_zero κ UpperHalfPlane.I
  have hmul : num κ Complex.I = Complex.I * denom κ Complex.I := by
    rwa [div_eq_iff hden] at hcoe
  simp only [num, denom] at hmul
  have hre := congrArg Complex.re hmul
  have him2 := congrArg Complex.im hmul
  simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im] at hre him2
  constructor
  · linarith [him2]
  · linarith [hre]

private theorem det_stabilizer (κ : GL (Fin 2) ℝ)
    (hI : κ • I = I) (hdet : (0 : ℝ) < ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det) :
    ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det
      = ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 ^ 2 + ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 ^ 2 := by
  obtain ⟨h1, h2⟩ := stabilizer_entries κ hI hdet
  rw [Matrix.det_fin_two, h1, h2]
  ring

private def Hset : Set ℂ := {z : ℂ | 0 < z.im}

private theorem isOpen_Hset : IsOpen Hset := isOpen_lt continuous_const Complex.continuous_im

private theorem isPreconnected_Hset : IsPreconnected Hset :=
  (convex_halfSpace_im_gt 0).isPreconnected

private def arcPt (c d r θ : ℝ) : ℂ :=
  (↑(-(d / c)) : ℂ) + (↑(r / |c|) : ℂ) * Complex.exp (↑θ * Complex.I)

private theorem im_arcPt (c d r θ : ℝ) : (arcPt c d r θ).im = (r / |c|) * Real.sin θ := by
  simp [arcPt, Complex.exp_ofReal_mul_I_im, Complex.add_im, Complex.mul_im]

private theorem arcPt_mem_Hset (c d r θ : ℝ) (hc : c ≠ 0) (hr : 0 < r)
    (h0 : 0 < θ) (hπ : θ < Real.pi) : arcPt c d r θ ∈ Hset := by
  have : (0 : ℝ) < (r / |c|) * Real.sin θ :=
    mul_pos (div_pos hr (abs_pos.mpr hc)) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
  simpa [Hset, im_arcPt] using this

private theorem norm_arcPt (c d r θ : ℝ) (hc : c ≠ 0) (hr : 0 < r) :
    ‖(↑c : ℂ) * arcPt c d r θ + ↑d‖ = r := by
  have hne : (↑c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have key : (↑c : ℂ) * arcPt c d r θ + ↑d
      = (↑(r / |c|) : ℂ) * ↑c * Complex.exp (↑θ * Complex.I) := by
    rw [arcPt]
    push_cast [mul_comm]
    field_simp
    ring
  rw [key]
  rw [norm_mul, norm_mul, Complex.norm_exp]
  simp [abs_of_pos hr, mul_comm]
  rw [mul_comm]
  exact div_mul_cancel₀ r (abs_ne_zero.mpr hc)

private theorem arcPt_injOn (c d r : ℝ) (hc : c ≠ 0) (hr : 0 < r) {θ₁ θ₂ : ℝ}
    (h1 : θ₁ ∈ Set.Ioo 0 Real.pi) (h2 : θ₂ ∈ Set.Ioo 0 Real.pi)
    (he : arcPt c d r θ₁ = arcPt c d r θ₂) : θ₁ = θ₂ := by
  have hscale : (↑(r / |c|) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos hr (abs_pos.mpr hc)).ne'
  have hexp : Complex.exp (↑θ₁ * Complex.I) = Complex.exp (↑θ₂ * Complex.I) := by
    have := he
    rw [arcPt, arcPt, add_right_inj] at this
    exact mul_left_cancel₀ hscale this
  rcases Complex.exp_eq_exp_iff_exists_int.mp hexp with ⟨n, hn⟩
  have hreal : θ₁ = θ₂ + n * (2 * Real.pi) := by
    have h2' : (↑θ₁ : ℂ) * Complex.I = (↑(θ₂ + n * (2 * Real.pi)) : ℂ) * Complex.I := by
      rw [hn]; push_cast; ring
    have := mul_right_cancel₀ Complex.I_ne_zero h2'
    exact_mod_cast this
  have hbound : |θ₁ - θ₂| < 2 * Real.pi := by
    rw [abs_sub_lt_iff]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, Real.pi_pos]
  have hn0 : n = 0 := by
    by_contra hn0
    have h1abs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs (by exact_mod_cast hn0)
    have : 2 * Real.pi ≤ |θ₁ - θ₂| := by
      have : θ₁ - θ₂ = n * (2 * Real.pi) := by linarith [hreal]
      rw [this, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    linarith
  rw [hn0] at hreal
  simpa using hreal

private theorem eqOn_Hset_of_eqOn_arc (c d r : ℝ) (hc : c ≠ 0) (hr : 0 < r)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hset) (hg : DifferentiableOn ℂ g Hset)
    (harc : ∀ z ∈ Hset, ‖(↑c : ℂ) * z + ↑d‖ = r → f z = g z) :
    Set.EqOn f g Hset := by
  set θ₀ : ℝ := Real.pi / 2 with hθ₀
  have hθ₀mem : θ₀ ∈ Set.Ioo 0 Real.pi := by
    constructor <;> [positivity; linarith [Real.pi_pos]]
  set z₀ := arcPt c d r θ₀ with hz₀
  have hz₀H : z₀ ∈ Hset := arcPt_mem_Hset c d r θ₀ hc hr hθ₀mem.1 hθ₀mem.2

  set u : ℕ → ℝ := fun n => θ₀ + Real.pi / (4 * (n + 1)) with hu
  have humem : ∀ n, u n ∈ Set.Ioo 0 Real.pi := by
    intro n
    have h1 : (0 : ℝ) < Real.pi / (4 * (n + 1)) := by positivity
    have h2 : Real.pi / (4 * (n + 1)) ≤ Real.pi / 4 := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
      have h15 : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith
    constructor
    · have := Real.pi_pos; simp only [hu]; positivity
    · simp only [hu, hθ₀]; nlinarith [Real.pi_pos]
  have hune : ∀ n, u n ≠ θ₀ := by
    intro n
    simp only [hu]
    have : (0 : ℝ) < Real.pi / (4 * (n + 1)) := by positivity
    linarith
  have hulim : Filter.Tendsto u Filter.atTop (nhds θ₀) := by
    have : Filter.Tendsto (fun n : ℕ => Real.pi / (4 * ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      apply Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 4)
      exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h := this.const_add θ₀
    simpa using h
  have harcont : Continuous fun θ : ℝ => arcPt c d r θ := by
    unfold arcPt
    fun_prop
  have hzlim : Filter.Tendsto (fun n => arcPt c d r (u n)) Filter.atTop
      (nhdsWithin z₀ {z₀}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (harcont.tendsto θ₀).comp hulim
    · filter_upwards with n
      intro hmem
      exact hune n (arcPt_injOn c d r hc hr (humem n) hθ₀mem hmem)
  have hfreq : ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = g z := by
    apply hzlim.frequently
    apply Filter.Frequently.of_forall
    intro n
    exact harc _ (arcPt_mem_Hset c d r (u n) hc hr (humem n).1 (humem n).2)
      (norm_arcPt c d r (u n) hc hr)
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (hf.analyticOnNhd isOpen_Hset) (hg.analyticOnNhd isOpen_Hset)
    isPreconnected_Hset hz₀H hfreq

private theorem exists_mem_Hset_norm_eq (c d : ℝ) (hc : c ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∃ z ∈ Hset, ‖(↑c : ℂ) * z + ↑d‖ = t :=
  ⟨arcPt c d t (Real.pi / 2),
    arcPt_mem_Hset c d t _ hc ht (by positivity) (by linarith [Real.pi_pos]),
    norm_arcPt c d t _ hc ht⟩

private theorem exists_on_arc_ne_zero (c d t : ℝ) (hc : c ≠ 0) (ht : 0 < t)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Hset)
    (hne : ¬ Set.EqOn g (fun _ => (0 : ℂ)) Hset) :
    ∃ z ∈ Hset, ‖(↑c : ℂ) * z + ↑d‖ = t ∧ g z ≠ 0 := by
  by_contra h
  push Not at h
  exact hne (eqOn_Hset_of_eqOn_arc c d t hc ht hg (by fun_prop) fun z hz hn => h z hz hn)

private theorem eta_eq_of_radial_ratio (η : ℝ → ℂ) (F G : ℂ → ℂ) (c d : ℝ) (hc : c ≠ 0)
    (hF : DifferentiableOn ℂ F Hset) (hG : DifferentiableOn ℂ G Hset)
    (hGne : ¬ Set.EqOn G (fun _ => (0 : ℂ)) Hset)
    (hrel : ∀ z ∈ Hset, F z = η ‖(↑c : ℂ) * z + ↑d‖ * G z) :
    ∀ t : ℝ, 0 < t → η t = η 1 := by
  have hglob : Set.EqOn F (fun z => η 1 * G z) Hset := by
    apply eqOn_Hset_of_eqOn_arc c d 1 hc one_pos hF (by fun_prop)
    intro z hz hnorm
    rw [hrel z hz, hnorm]
  intro t ht
  obtain ⟨z, hzH, hznorm, hzne⟩ := exists_on_arc_ne_zero c d t hc ht hG hGne
  have h1 : F z = η t * G z := by rw [hrel z hzH, hznorm]
  have h2 : F z = η 1 * G z := hglob hzH
  have := h1.symm.trans h2
  exact mul_right_cancel₀ hzne this

section OmegaInfra

private abbrev H4Ad := AdeleRing (𝓞 ℚ) ℚ

private abbrev h4pins : CarrierPins ℚ := productionPinsCompact ℚ

variable {Ψ : HeckeEigensystem ℚ ℂ}

private def omegaUnit (R : SmoothCuspRealizationAt ℚ h4pins Ψ) : H4Adˣ →* ℂˣ where
  toFun z := R.centralChar ⟨z, by rw [productionPinsCompact_Z]; trivial⟩
  map_one' := by
    have h : (⟨1, by rw [productionPinsCompact_Z]; trivial⟩ : h4pins.Z) = 1 := rfl
    rw [h, map_one]
  map_mul' z w := by
    have h : (⟨z * w, by rw [productionPinsCompact_Z]; trivial⟩ : h4pins.Z)
        = ⟨z, by rw [productionPinsCompact_Z]; trivial⟩
          * ⟨w, by rw [productionPinsCompact_Z]; trivial⟩ := rfl
    rw [h, map_mul]

private theorem omega_spec (R : SmoothCuspRealizationAt ℚ h4pins Ψ) (z : H4Adˣ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    R.toFun (centralScalar (𝓞 ℚ) ℚ z * g) = ((omegaUnit R z : ℂˣ) : ℂ) * R.toFun g := by
  letI := h4pins.mS
  exact (((lsXiMemberAt_iff (𝓞 ℚ) ℚ h4pins.μ h4pins.Z R.centralChar h4pins.D R.toFun).mp
    R.smoothCusp.1.1).1).central_transform ⟨z, by rw [productionPinsCompact_Z]; trivial⟩ g

private theorem centralScalar_mul_comm (z : H4Adˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    centralScalar (𝓞 ℚ) ℚ z * g = g * centralScalar (𝓞 ℚ) ℚ z := by
  ext : 1
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.scalar_commute (z : H4Ad) (fun r' => mul_comm _ _)
    ((g : Matrix (Fin 2) (Fin 2) H4Ad))

private local instance instDecEqInfinitePlaceRat : DecidableEq (InfinitePlace ℚ) :=
  fun a b => Decidable.isTrue (Subsingleton.elim a b)

private noncomputable def archIdeleUnit (w : InfinitePlace ℚ) (hw : w.IsReal) (t : ℝˣ) :
    (AdeleRing (𝓞 ℚ) ℚ)ˣ where
  val := (Function.update (1 : InfiniteAdeleRing ℚ) w
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm ((t : ℝ))), 1)
  inv := (Function.update (1 : InfiniteAdeleRing ℚ) w
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (((t⁻¹ : ℝˣ) : ℝ))), 1)
  val_inv := by
    refine Prod.ext ?_ (one_mul 1)
    funext w'
    rcases Subsingleton.elim w w' with rfl
    show (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm ((t : ℝ))
        * (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (((t⁻¹ : ℝˣ) : ℝ))
      = 1
    rw [← map_mul]
    simp
  inv_val := by
    refine Prod.ext ?_ (one_mul 1)
    funext w'
    rcases Subsingleton.elim w w' with rfl
    show (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (((t⁻¹ : ℝˣ) : ℝ))
        * (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm ((t : ℝ))
      = 1
    rw [← map_mul]
    simp

private theorem archIdeleUnit_val_fst_self (w : InfinitePlace ℚ) (hw : w.IsReal) (t : ℝˣ) :
    (((archIdeleUnit w hw t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)).1 w
      = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm ((t : ℝ)) := rfl

private theorem archIdeleUnit_val_snd (w : InfinitePlace ℚ) (hw : w.IsReal) (t : ℝˣ) :
    (((archIdeleUnit w hw t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 := rfl

private theorem centralScalar_archIdeleUnit (w : InfinitePlace ℚ) (hw : w.IsReal) (t : ℝˣ) :
    centralScalar (𝓞 ℚ) ℚ (archIdeleUnit w hw t)
      = adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) := by
  ext i j
  refine Prod.ext ?_ ?_
  · show (Matrix.diagonal (fun _ => ((archIdeleUnit w hw t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ)) i j).1
      = archMatrixUpdate ℚ w
        ((Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t) :
            GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
    funext w'
    rcases Subsingleton.elim w w' with rfl
    rw [archMatrixUpdate_apply_self]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, archIdeleUnit_val_fst_self]
      show _ = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
          ((Matrix.scalar (Fin 2) ((t : ℝ))) i i)
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      rfl
    · rw [Matrix.diagonal_apply_ne _ h]
      show (0 : AdeleRing (𝓞 ℚ) ℚ).1 w
        = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
          ((Matrix.scalar (Fin 2) ((t : ℝ))) i j)
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, map_zero]
      rfl
  · show (Matrix.diagonal (fun _ => ((archIdeleUnit w hw t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ)) i j).2
      = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl

end OmegaInfra
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

private theorem archIncl_finEmbed_comm (k : GL (Fin 2) (InfiniteAdeleRing ℚ))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    adelicArchGLIncl ℚ k * AdelicDock.finEmbed (𝓞 ℚ) ℚ h
      = AdelicDock.finEmbed (𝓞 ℚ) ℚ h * adelicArchGLIncl ℚ k := by
  apply glpair_ext
  · rw [map_mul, map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one, one_mul]
  · rw [map_mul, map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, mul_one, one_mul]

private theorem adeleFin_comp_algebraMap :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  apply RingHom.ext_rat

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := by
  show AdelicLevel.adeleFin (𝓞 ℚ) ℚ
      ((globalPoints (𝓞 ℚ) ℚ γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) = _
  have h1 : ((globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := by
    simp only [globalPoints, Matrix.GeneralLinearGroup.map, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [h1, ← RingHom.comp_apply, adeleFin_comp_algebraMap]

private theorem intValuation_le_idealBound_of_mem {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {N : Ideal A} {r : A}
    (hr : r ∈ N) : v.intValuation r ≤ idealBound A N v := by
  classical
  by_cases hN : N = ⊥
  · subst hN
    rw [Ideal.mem_bot] at hr
    subst hr
    rw [map_zero, idealBound_bot]
  · by_cases hr0 : r = 0
    · subst hr0
      rw [map_zero]
      exact zero_le'
    · rw [v.intValuation_if_neg hr0, idealBound_of_ne_bot hN]
      have hdvd : Ideal.span {r} ≤ N := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hr)
      have hle := Associates.mk_le_mk_iff_dvd.mpr (Ideal.dvd_iff_le.mpr hdvd)
      have hb : Associates.mk (Ideal.span {r}) ≠ (0 : Associates (Ideal A)) := by
        rw [Ne, Associates.mk_eq_zero]
        exact fun h => hr0 (Ideal.span_singleton_eq_bot.mp h)
      have hcount := Associates.count_le_count_of_le hb v.associates_irreducible hle
      rw [WithZero.exp_le_exp]
      exact neg_le_neg (by exact_mod_cast hcount)

private theorem algebraMap_mem_integralFiniteAdeles (r : 𝓞 ℚ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ :=
  fun v => algebraMap_mem_adicCompletionIntegers v r

private theorem algebraMap_mem_idealBall_of_mem {L : Ideal (𝓞 ℚ)} {r : 𝓞 ℚ} (hr : r ∈ L) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r)
      ∈ idealBall (𝓞 ℚ) ℚ L := by
  intro v
  show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ r))
    ≤ idealBound (𝓞 ℚ) L v
  rw [valued_algebraMap]
  exact intValuation_le_idealBound_of_mem v hr

private theorem neg_mem_idealBall {L : Ideal (𝓞 ℚ)} {x : FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ idealBall (𝓞 ℚ) ℚ L) : -x ∈ idealBall (𝓞 ℚ) ℚ L := by
  intro v
  have h : ((-x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = -(x v) := rfl
  rw [h, Valuation.map_neg]
  exact hx v

private def gammaQ (n : ℕ) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; (n : ℚ), 1] (by
    norm_num [Matrix.det_fin_two_of])

private theorem gammaQ_coe (n : ℕ) :
    (gammaQ n : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; (n : ℚ), 1] := rfl

private theorem gammaQ_inv_coe (n : ℕ) :
    (((gammaQ n)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; -(n : ℚ), 1] := by
  have hu : (((gammaQ n)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = ((gammaQ n : Matrix (Fin 2) (Fin 2) ℚ))⁻¹ := by simp
  rw [hu, gammaQ_coe, Matrix.inv_def, Matrix.adjugate_fin_two]
  norm_num [Matrix.det_fin_two_of, Ring.inverse_eq_inv]

private theorem isLevelOneMatrix_glFin_gammaQ {L : Ideal (𝓞 ℚ)} {n : ℕ}
    (hn : ((n : ℕ) : 𝓞 ℚ) ∈ L) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L
      ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ n)))
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have e : ∀ i j, ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ n)))
      : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((!![1, 0; (n : ℚ), 1]) i j) := by
    intro i j; rw [glFin_globalPoints_apply, gammaQ_coe]
  have e00 : (!![1, 0; (n : ℚ), 1]) 0 0 = (1 : ℚ) := rfl
  have e01 : (!![1, 0; (n : ℚ), 1]) 0 1 = (0 : ℚ) := rfl
  have e10 : (!![1, 0; (n : ℚ), 1]) 1 0 = ((n : ℕ) : ℚ) := rfl
  have e11 : (!![1, 0; (n : ℚ), 1]) 1 1 = (1 : ℚ) := rfl
  have hcast : ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((n : ℕ) : 𝓞 ℚ) := by
    rw [map_natCast]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    intro i j
    rw [e i j]
    fin_cases i <;> fin_cases j
    · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (1 : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      rw [show (1:ℚ) = algebraMap (𝓞 ℚ) ℚ 1 from (map_one _).symm]
      exact algebraMap_mem_integralFiniteAdeles 1
    · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (0 : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      rw [show (0:ℚ) = algebraMap (𝓞 ℚ) ℚ 0 from (map_zero _).symm]
      exact algebraMap_mem_integralFiniteAdeles 0
    · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℕ) : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      rw [hcast]
      exact algebraMap_mem_integralFiniteAdeles _
    · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (1 : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      rw [show (1:ℚ) = algebraMap (𝓞 ℚ) ℚ 1 from (map_one _).symm]
      exact algebraMap_mem_integralFiniteAdeles 1
  ·
    rw [e 1 0, e10, hcast]
    exact algebraMap_mem_idealBall_of_mem hn
  ·
    rw [e 1 1, e11, map_one, sub_self]
    exact zero_mem_idealBall L

private theorem rot_mem_rowIsometrySubgroup₀ (a c r : ℝ) (hr : 0 < r) (h : a ^ 2 + c ^ 2 = r ^ 2) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![a / r, -(c / r); c / r, a / r]
      (by
        have : (a / r) * (a / r) - (-(c / r)) * (c / r) = 1 := by
          field_simp
          nlinarith [h]
        simp [Matrix.det_fin_two_of]
        nlinarith [this])
      ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  constructor
  · show (!![a / r, -(c / r); c / r, a / r]).det = 1
    rw [Matrix.det_fin_two_of]
    field_simp
    nlinarith [h]
  · constructor
    · show ‖(!![a / r, -(c / r); c / r, a / r]).det‖ = 1
      rw [Matrix.det_fin_two_of]
      have hd : a / r * (a / r) - -(c / r) * (c / r) = 1 := by
        field_simp; nlinarith [h]
      rw [hd, norm_one]
    · intro x y
      have f00 : (!![a / r, -(c / r); c / r, a / r]) 0 0 = a / r := rfl
      have f01 : (!![a / r, -(c / r); c / r, a / r]) 0 1 = -(c / r) := rfl
      have f10 : (!![a / r, -(c / r); c / r, a / r]) 1 0 = c / r := rfl
      have f11 : (!![a / r, -(c / r); c / r, a / r]) 1 1 = a / r := rfl
      show ‖x * (!![a / r, -(c / r); c / r, a / r]) 0 0 + y * (!![a / r, -(c / r); c / r, a / r]) 1 0‖ ^ 2
          + ‖x * (!![a / r, -(c / r); c / r, a / r]) 0 1 + y * (!![a / r, -(c / r); c / r, a / r]) 1 1‖ ^ 2
          = ‖x‖ ^ 2 + ‖y‖ ^ 2
      rw [f00, f01, f10, f11, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, sq_abs, sq_abs, sq_abs, sq_abs]
      have hr2 : r ^ 2 ≠ 0 := by positivity
      field_simp
      nlinarith [h]

private theorem norm_ringEquivRealOfIsReal_symm {w : InfinitePlace ℚ} (hw : w.IsReal) (x : ℝ) :
    ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have h := norm_ringEquivRealOfIsReal hw
    ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

private theorem rowIsometrySubgroup₀Map_round {w : InfinitePlace ℚ} (hw : w.IsReal)
    (k : rowIsometrySubgroup₀ ℝ) :
    rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw)
      (rowIsometrySubgroup₀Map
        (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
        (norm_ringEquivRealOfIsReal_symm hw) k) = k := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [rowIsometrySubgroup₀Map, glEquivOfRingEquiv_apply_entry]

private theorem archWeightOneAt_transported {w : InfinitePlace ℚ} (hw : w.IsReal)
    (k : rowIsometrySubgroup₀ ℝ) :
    archWeightOneAt hw (rowIsometrySubgroup₀Map
        (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
        (norm_ringEquivRealOfIsReal_symm hw) k)
      = archWeightOneℝ k := by
  unfold archWeightOneAt
  rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_round]

section KappaRelation

variable {Ψ : HeckeEigensystem ℚ ℂ}

private def archAt (w : InfinitePlace ℚ) (hw : w.IsReal) : GL (Fin 2) ℝ →* AdelicGL2 (𝓞 ℚ) ℚ :=
  (adelicArchGLInclAt ℚ w).comp
    (Matrix.GeneralLinearGroup.map
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom))

private def gammaR (n : ℕ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (gammaQ n)

private theorem gammaR_coe (n : ℕ) :
    (gammaR n : Matrix (Fin 2) (Fin 2) ℝ) = !![(1:ℝ), 0; (n : ℝ), 1] := by
  have h : (gammaR n : Matrix (Fin 2) (Fin 2) ℝ)
      = ((gammaQ n : Matrix (Fin 2) (Fin 2) ℚ)).map (algebraMap ℚ ℝ) := rfl
  rw [h, gammaQ_coe]
  ext i j
  fin_cases i <;> fin_cases j
  · show algebraMap ℚ ℝ 1 = 1; exact map_one _
  · show algebraMap ℚ ℝ 0 = 0; exact map_zero _
  · show algebraMap ℚ ℝ ((n : ℕ) : ℚ) = ((n : ℕ) : ℝ); exact map_natCast _ n
  · show algebraMap ℚ ℝ 1 = 1; exact map_one _

private theorem det_gammaR (n : ℕ) : ((gammaR n : Matrix (Fin 2) (Fin 2) ℝ)).det = 1 := by
  rw [gammaR_coe, Matrix.det_fin_two_of]
  ring

private theorem det_gammaR_pos (n : ℕ) : (0:ℝ) < ((gammaR n : Matrix (Fin 2) (Fin 2) ℝ)).det := by
  rw [det_gammaR]; norm_num

private theorem denom_gammaR (n : ℕ) (z : ℂ) :
    denom (gammaR n) z = ((n : ℝ) : ℂ) * z + 1 := by
  simp [denom, gammaR_coe]

private theorem isLevelOneMatrix_glFin_gammaQ_inv {L : Ideal (𝓞 ℚ)} {n : ℕ}
    (hn : ((n : ℕ) : 𝓞 ℚ) ∈ L) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L
      ((((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ n)))⁻¹ :
          GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hinv : (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ n)))⁻¹
      = glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ ((gammaQ n)⁻¹)) := by
    rw [map_inv, map_inv]
  rw [hinv]
  have e : ∀ i j, ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ ((gammaQ n)⁻¹)))
      : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((!![1, 0; -(n : ℚ), 1]) i j) := by
    intro i j; rw [glFin_globalPoints_apply, gammaQ_inv_coe]
  have f10 : (!![1, 0; -(n : ℚ), 1]) 1 0 = -((n : ℕ) : ℚ) := rfl
  have f11 : (!![1, 0; -(n : ℚ), 1]) 1 1 = (1 : ℚ) := rfl
  have hnegcast : -((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (-((n : ℕ) : 𝓞 ℚ)) := by
    rw [map_neg, map_natCast]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j
    rw [e i j]
    fin_cases i <;> fin_cases j
    · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (1 : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      rw [show (1:ℚ) = algebraMap (𝓞 ℚ) ℚ 1 from (map_one _).symm]
      exact algebraMap_mem_integralFiniteAdeles 1
    · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (0 : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      rw [show (0:ℚ) = algebraMap (𝓞 ℚ) ℚ 0 from (map_zero _).symm]
      exact algebraMap_mem_integralFiniteAdeles 0
    · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (-((n : ℕ) : ℚ))
        ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      rw [hnegcast]
      exact algebraMap_mem_integralFiniteAdeles _
    · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (1 : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      rw [show (1:ℚ) = algebraMap (𝓞 ℚ) ℚ 1 from (map_one _).symm]
      exact algebraMap_mem_integralFiniteAdeles 1
  · rw [e 1 0, f10, hnegcast]
    exact algebraMap_mem_idealBall_of_mem (neg_mem hn)
  · rw [e 1 1, f11, map_one, sub_self]
    exact zero_mem_idealBall L

private theorem glFin_globalPoints_gammaQ_mem {L : Ideal (𝓞 ℚ)} {n : ℕ}
    (hn : ((n : ℕ) : 𝓞 ℚ) ∈ L) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ n)) ∈ finiteLevelOne (𝓞 ℚ) ℚ L :=
  mem_finiteLevelOne_iff.mpr
    ⟨isLevelOneMatrix_glFin_gammaQ hn, isLevelOneMatrix_glFin_gammaQ_inv hn⟩

private theorem finEmbed_glFin_gammaQ_inv_mem_U {n : ℕ}
    (hn : ((n : ℕ) : 𝓞 ℚ) ∈ Ψ.level) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ n)))⁻¹)
      ∈ h4pins.U Ψ.level := by
  rw [productionPinsCompact_U]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (AdelicDock.finEmbed_mem_levelOne_iff (𝓞 ℚ) ℚ _).mpr
      (inv_mem (glFin_globalPoints_gammaQ_mem hn))
  · exact (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _)

private theorem globalPoints_gammaQ_decomp (w : InfinitePlace ℚ) (hw : w.IsReal) (n : ℕ) :
    globalPoints (𝓞 ℚ) ℚ (gammaQ n)
      = archAt w hw (gammaR n)
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ n))) := by
  apply glpair_ext
  · rw [map_mul, AdelicDock.glArch_finEmbed, mul_one,
      show archAt w hw (gammaR n) = (adelicArchGLIncl ℚ) (archGLIncl ℚ w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (gammaR n))) from rfl,
      glArch_adelicArchGLIncl]
    ext i j
    funext w'
    rcases Subsingleton.elim w w' with rfl
    show AdelicLevel.adeleArch (𝓞 ℚ) ℚ
        ((globalPoints (𝓞 ℚ) ℚ (gammaQ n) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) w
      = (archMatrixUpdate ℚ w
          ((Matrix.GeneralLinearGroup.map
            ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
            (gammaR n) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) i j w
    rw [archMatrixUpdate_apply_self]
    have h1 : ((globalPoints (𝓞 ℚ) ℚ (gammaQ n)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j
        = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((gammaQ n : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl
    have h2 : ((Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (gammaR n) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
        = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (algebraMap ℚ ℝ ((gammaQ n : Matrix (Fin 2) (Fin 2) ℚ) i j)) := rfl
    rw [h1, h2]
    exact congrArg (fun f : ℚ →+* w.Completion => f ((gammaQ n : Matrix (Fin 2) (Fin 2) ℚ) i j))
      (by apply RingHom.ext_rat :
        ((Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) w).comp
          ((RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
            (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))))
        = ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom).comp
            (algebraMap ℚ ℝ))
  · rw [map_mul, AdelicDock.glFin_finEmbed,
      show archAt w hw (gammaR n) = (adelicArchGLIncl ℚ) (archGLIncl ℚ w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (gammaR n))) from rfl,
      glFin_adelicArchGLIncl, one_mul]

private theorem toFun_archAt_gammaR_mul (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) (s : GL (Fin 2) ℝ) :
    R.toFun (archAt w hw (gammaR (Ideal.absNorm Ψ.level)) * archAt w hw s)
      = R.toFun (archAt w hw s) := by
  have hmem : ((Ideal.absNorm Ψ.level : ℕ) : 𝓞 ℚ) ∈ Ψ.level := by
    exact_mod_cast Ideal.absNorm_mem Ψ.level
  have harch : archAt w hw (gammaR (Ideal.absNorm Ψ.level))
      = globalPoints (𝓞 ℚ) ℚ (gammaQ (Ideal.absNorm Ψ.level))
          * (AdelicDock.finEmbed (𝓞 ℚ) ℚ
              (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ (Ideal.absNorm Ψ.level)))))⁻¹ :=
    eq_mul_inv_of_mul_eq (globalPoints_gammaQ_decomp w hw (Ideal.absNorm Ψ.level)).symm
  have hfi : (AdelicDock.finEmbed (𝓞 ℚ) ℚ
        (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ (Ideal.absNorm Ψ.level)))))⁻¹
      = AdelicDock.finEmbed (𝓞 ℚ) ℚ
          (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ (Ideal.absNorm Ψ.level))))⁻¹ :=
    (map_inv _ _).symm
  have hcomm : AdelicDock.finEmbed (𝓞 ℚ) ℚ
        (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ (Ideal.absNorm Ψ.level))))⁻¹
          * archAt w hw s
      = archAt w hw s * AdelicDock.finEmbed (𝓞 ℚ) ℚ
          (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (gammaQ (Ideal.absNorm Ψ.level))))⁻¹ := by
    rw [show archAt w hw s = (adelicArchGLIncl ℚ) (archGLIncl ℚ w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom) s)) from rfl,
      ← archIncl_finEmbed_comm]
  rw [harch, hfi, mul_assoc, hcomm, R.left_invariant]
  exact R.level_invariant _ _ (finEmbed_glFin_gammaQ_inv_mem_U hmem)

private noncomputable def omegaPos (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) : ℝ → ℂ := fun t =>
  if ht : 0 < t then ((omegaUnit R (archIdeleUnit w hw (Units.mk0 t ht.ne')) : ℂˣ) : ℂ) else 0

private theorem omegaPos_of_pos (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) {t : ℝ} (ht : 0 < t) :
    omegaPos R w hw t
      = ((omegaUnit R (archIdeleUnit w hw (Units.mk0 t ht.ne')) : ℂˣ) : ℂ) := dif_pos ht

private theorem omegaPos_ne_zero (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) {t : ℝ} (ht : 0 < t) :
    omegaPos R w hw t ≠ 0 := by
  rw [omegaPos_of_pos R w hw ht]
  exact Units.ne_zero _

private theorem coe_rowIsometrySubgroup₀Map_symm {w : InfinitePlace ℚ} (hw : w.IsReal)
    (k : rowIsometrySubgroup₀ ℝ) :
    ((rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
        (norm_ringEquivRealOfIsReal_symm hw) k : rowIsometrySubgroup₀ w.Completion)
      : GL (Fin 2) w.Completion)
      = Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (k : GL (Fin 2) ℝ) := by
  ext i j
  simp [rowIsometrySubgroup₀Map, glEquivOfRingEquiv_apply_entry]

private theorem descent_kappa_relation (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun) (z : UpperHalfPlane) :
    R.toFun (archAt w hw (iwasawaSec z))
      = omegaPos R w hw ‖denom (gammaR (Ideal.absNorm Ψ.level)) (z : ℂ)‖
          * (starRingEnd ℂ (denom (gammaR (Ideal.absNorm Ψ.level)) (z : ℂ))
              / (‖denom (gammaR (Ideal.absNorm Ψ.level)) (z : ℂ)‖ : ℂ))
          * R.toFun (archAt w hw (iwasawaSec (gammaR (Ideal.absNorm Ψ.level) • z))) := by
  set γ := gammaR (Ideal.absNorm Ψ.level) with hγdef
  have hγpos : (0:ℝ) < ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det := det_gammaR_pos _

  have hI := kappa_smul_I γ z
  have hκdet : (0:ℝ) < ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)).det := by
    rw [det_kappa γ z hγpos]
    exact Complex.normSq_pos.mpr (denom_ne_zero γ z)
  obtain ⟨h1, h2⟩ := stabilizer_entries (kappa γ z) hI hκdet
  have hdet2 := det_stabilizer (kappa γ z) hI hκdet
  set a := ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 with ha
  set c := ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 with hc

  set d := denom γ (z : ℂ) with hd
  have hdne : d ≠ 0 := denom_ne_zero γ z
  set r := ‖d‖ with hr
  have hrpos : (0:ℝ) < r := by rw [hr]; exact norm_pos_iff.mpr hdne
  have hrne : r ≠ 0 := hrpos.ne'

  have hdac : d = (a : ℂ) + (c : ℂ) * Complex.I := by
    rw [hd, ← denom_kappa γ z]
    show ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * Complex.I
        + ((kappa γ z : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) = (a : ℂ) + (c : ℂ) * Complex.I
    rw [← hc, ← h1]
    ring
  have hr2 : a ^ 2 + c ^ 2 = r ^ 2 := by
    have h3 : Complex.normSq d = a ^ 2 + c ^ 2 := by
      rw [hdac]
      simp [Complex.normSq_apply]
      ring
    rw [← h3, hr]
    exact Complex.normSq_eq_norm_sq d

  have hrotdet : (!![a / r, -(c / r); c / r, a / r]).det ≠ 0 := by
    have : (a / r) * (a / r) - (-(c / r)) * (c / r) = 1 := by
      field_simp
      nlinarith [hr2]
    simp [Matrix.det_fin_two_of]
    nlinarith [this]
  set rot := Matrix.GeneralLinearGroup.mkOfDetNeZero !![a / r, -(c / r); c / r, a / r] hrotdet
    with hrot
  have hrotmem : rot ∈ rowIsometrySubgroup₀ ℝ := rot_mem_rowIsometrySubgroup₀ a c r hrpos hr2

  have hscalarlit : (Matrix.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) ℝ)
      * !![a / r, -(c / r); c / r, a / r]
      = !![r * (a / r), r * (-(c / r)); r * (c / r), r * (a / r)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hκdecomp : kappa γ z
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne) * rot := by
    apply Units.ext
    rw [Units.val_mul,
      show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne) : GL (Fin 2) ℝ)
          : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) r from rfl,
      show ((rot : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          = !![a / r, -(c / r); c / r, a / r] from rfl,
      hscalarlit]
    have e1 : r * (a / r) = a := by field_simp
    have e2 : r * (-(c / r)) = -c := by field_simp
    have e3 : r * (c / r) = c := by field_simp
    rw [e1, e2, e3]
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha.symm
    · exact h2
    · exact hc.symm
    · exact h1.symm

  have hsplit : archAt w hw γ * archAt w hw (iwasawaSec z)
      = archAt w hw (iwasawaSec (γ • z)) * archAt w hw (kappa γ z) := by
    rw [← map_mul, ← map_mul, mul_iwasawaSec_eq γ z]

  have hscalar : archAt w hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne))
      = centralScalar (𝓞 ℚ) ℚ (archIdeleUnit w hw (Units.mk0 r hrne)) :=
    (centralScalar_archIdeleUnit w hw (Units.mk0 r hrne)).symm

  have hrotarch : archAt w hw rot
      = adelicArchGLInclAt ℚ w
          ((rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
            (norm_ringEquivRealOfIsReal_symm hw) ⟨rot, hrotmem⟩ : rowIsometrySubgroup₀ w.Completion)
            : GL (Fin 2) w.Completion) := by
    rw [coe_rowIsometrySubgroup₀Map_symm]
    rfl

  have hχ : ((archWeightOneAt hw
        (rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
          (norm_ringEquivRealOfIsReal_symm hw) ⟨rot, hrotmem⟩) : ℂˣ) : ℂ)
      = starRingEnd ℂ d / (r : ℂ) := by
    rw [archWeightOneAt_transported hw ⟨rot, hrotmem⟩]
    show firstRowℂ (rot : GL (Fin 2) ℝ) = starRingEnd ℂ d / (r : ℂ)
    have hrot00 : ((rot : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = a / r := rfl
    have hrot01 : ((rot : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(c / r) := rfl
    rw [eq_div_iff (by exact_mod_cast hrne : ((r : ℝ) : ℂ) ≠ 0)]
    apply Complex.ext
    · simp [firstRowℂ, hdac, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.mul_im]
      simp only [hrot00, hrot01]
      field_simp
    · simp [firstRowℂ, hdac, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.mul_im]
      simp only [hrot00, hrot01]
      field_simp

  have hω : R.toFun (archAt w hw (iwasawaSec z))
      = ((omegaUnit R (archIdeleUnit w hw (Units.mk0 r hrne)) : ℂˣ) : ℂ)
        * (((archWeightOneAt hw
            (rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
              (norm_ringEquivRealOfIsReal_symm hw) ⟨rot, hrotmem⟩) : ℂˣ) : ℂ)
          * R.toFun (archAt w hw (iwasawaSec (γ • z)))) := by
    calc R.toFun (archAt w hw (iwasawaSec z))
        = R.toFun (archAt w hw γ * archAt w hw (iwasawaSec z)) :=
          (toFun_archAt_gammaR_mul R w hw (iwasawaSec z)).symm
      _ = R.toFun (archAt w hw (iwasawaSec (γ • z)) * archAt w hw (kappa γ z)) := by
          rw [hsplit]
      _ = R.toFun (archAt w hw (iwasawaSec (γ • z))
            * (archAt w hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne))
              * archAt w hw rot)) := by
          rw [← map_mul (archAt w hw)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne)) rot, ← hκdecomp]
      _ = R.toFun (centralScalar (𝓞 ℚ) ℚ (archIdeleUnit w hw (Units.mk0 r hrne))
            * (archAt w hw (iwasawaSec (γ • z)) * archAt w hw rot)) := by
          rw [hscalar, ← mul_assoc,
            ← centralScalar_mul_comm (archIdeleUnit w hw (Units.mk0 r hrne))
              (archAt w hw (iwasawaSec (γ • z))), mul_assoc]
      _ = ((omegaUnit R (archIdeleUnit w hw (Units.mk0 r hrne)) : ℂˣ) : ℂ)
            * R.toFun (archAt w hw (iwasawaSec (γ • z)) * archAt w hw rot) :=
          omega_spec R _ _
      _ = _ := by
          rw [hrotarch, harch _ (archAt w hw (iwasawaSec (γ • z)))]
  rw [hω, hχ, omegaPos_of_pos R w hw hrpos]
  ring

end KappaRelation
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Stage3Furniture

variable {Ψ : HeckeEigensystem ℚ ℂ}

private theorem iwasawaSec_I : iwasawaSec I = 1 := by
  apply Units.ext
  rw [coe_iwasawaSec, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.I]

private theorem archIdeleUnit_one (w : InfinitePlace ℚ) (hw : w.IsReal) :
    archIdeleUnit w hw 1 = 1 := by
  apply Units.ext
  refine Prod.ext ?_ rfl
  show Function.update (1 : InfiniteAdeleRing ℚ) w
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (((1:ℝˣ) : ℝ))) = 1
  rw [Units.val_one, map_one]
  exact Function.update_eq_self w 1

private theorem finEmbed_mem_U {L : Ideal (𝓞 ℚ)} {h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hh : h ∈ finiteLevelOne (𝓞 ℚ) ℚ L) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ h ∈ h4pins.U L := by
  rw [productionPinsCompact_U]
  exact Subgroup.mem_inf.mpr ⟨(AdelicDock.finEmbed_mem_levelOne_iff (𝓞 ℚ) ℚ h).mpr hh,
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ h)⟩

private theorem archGLIncl_archComponent_g5 (w : InfinitePlace ℚ)
    (A : GL (Fin 2) (InfiniteAdeleRing ℚ)) :
    archGLIncl ℚ w (archComponent ℚ w A) = A := by
  ext i j
  funext w'
  rcases Subsingleton.elim w w' with rfl
  show archMatrixUpdate ℚ w
      ((archComponent ℚ w A : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j w
    = (A : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j w
  rw [archMatrixUpdate_apply_self]
  rfl

private theorem map_symm_map {w : InfinitePlace ℚ} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom) k) = k := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw) ((k : Matrix _ _ _) i j))
    = (k : Matrix _ _ _) i j
  rw [RingEquiv.symm_apply_apply]

private theorem coe_ofComplex {zc : ℂ} (h : 0 < zc.im) :
    ((UpperHalfPlane.ofComplex zc : UpperHalfPlane) : ℂ) = zc := by
  have h1 : UpperHalfPlane.ofComplex ((⟨zc, h⟩ : UpperHalfPlane) : ℂ)
      = (⟨zc, h⟩ : UpperHalfPlane) := UpperHalfPlane.ofComplex_apply ⟨zc, h⟩
  exact congrArg UpperHalfPlane.coe h1

private theorem im_ofComplex {zc : ℂ} (h : 0 < zc.im) :
    (UpperHalfPlane.ofComplex zc).im = zc.im := by
  have := coe_ofComplex h
  rw [UpperHalfPlane.im, this]

private theorem toFun_mul_archAt_stabilizer (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    {κ : GL (Fin 2) ℝ} (hI : κ • I = I)
    (hdet : (0:ℝ) < ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det)
    (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ u : ℂ, u ≠ 0 ∧ R.toFun (X * archAt w hw κ) = u * R.toFun X := by
  obtain ⟨h1, h2⟩ := stabilizer_entries κ hI hdet
  have hdet2 := det_stabilizer κ hI hdet
  set a := ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 with ha
  set c := ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 with hc
  set r := Real.sqrt (a ^ 2 + c ^ 2) with hr
  have hsumpos : (0:ℝ) < a ^ 2 + c ^ 2 := by
    rw [← hdet2]; exact hdet
  have hrpos : (0:ℝ) < r := Real.sqrt_pos.mpr hsumpos
  have hrne : r ≠ 0 := hrpos.ne'
  have hr2 : a ^ 2 + c ^ 2 = r ^ 2 := (Real.sq_sqrt hsumpos.le).symm
  have hrotdet : (!![a / r, -(c / r); c / r, a / r]).det ≠ 0 := by
    have hd1 : (a / r) * (a / r) - (-(c / r)) * (c / r) = 1 := by
      field_simp
      nlinarith [hr2]
    simp [Matrix.det_fin_two_of]
    nlinarith [hd1]
  set rot := Matrix.GeneralLinearGroup.mkOfDetNeZero !![a / r, -(c / r); c / r, a / r] hrotdet
    with hrot
  have hrotmem : rot ∈ rowIsometrySubgroup₀ ℝ := rot_mem_rowIsometrySubgroup₀ a c r hrpos hr2
  have hscalarlit : (Matrix.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) ℝ)
      * !![a / r, -(c / r); c / r, a / r]
      = !![r * (a / r), r * (-(c / r)); r * (c / r), r * (a / r)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hκdecomp : κ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne) * rot := by
    apply Units.ext
    rw [Units.val_mul,
      show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne) : GL (Fin 2) ℝ)
          : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) r from rfl,
      show ((rot : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          = !![a / r, -(c / r); c / r, a / r] from rfl,
      hscalarlit]
    have e1 : r * (a / r) = a := by field_simp
    have e2 : r * (-(c / r)) = -c := by field_simp
    have e3 : r * (c / r) = c := by field_simp
    rw [e1, e2, e3]
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha.symm
    · exact h2
    · exact hc.symm
    · exact h1.symm
  refine ⟨((omegaUnit R (archIdeleUnit w hw (Units.mk0 r hrne)) : ℂˣ) : ℂ)
      * ((archWeightOneAt hw
          (rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
            (norm_ringEquivRealOfIsReal_symm hw) ⟨rot, hrotmem⟩) : ℂˣ) : ℂ),
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _), ?_⟩
  have hrotarch : archAt w hw rot
      = adelicArchGLInclAt ℚ w
          ((rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
            (norm_ringEquivRealOfIsReal_symm hw) ⟨rot, hrotmem⟩ : rowIsometrySubgroup₀ w.Completion)
            : GL (Fin 2) w.Completion) := by
    rw [coe_rowIsometrySubgroup₀Map_symm]
    rfl
  calc R.toFun (X * archAt w hw κ)
      = R.toFun (X * (archAt w hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne))
          * archAt w hw rot)) := by
        rw [← map_mul (archAt w hw)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne)) rot, ← hκdecomp]
    _ = R.toFun (centralScalar (𝓞 ℚ) ℚ (archIdeleUnit w hw (Units.mk0 r hrne))
          * (X * archAt w hw rot)) := by
        have hscalar : archAt w hw
              (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne))
            = centralScalar (𝓞 ℚ) ℚ (archIdeleUnit w hw (Units.mk0 r hrne)) :=
          (centralScalar_archIdeleUnit w hw (Units.mk0 r hrne)).symm
        rw [hscalar, ← mul_assoc,
          ← centralScalar_mul_comm (archIdeleUnit w hw (Units.mk0 r hrne)) X, mul_assoc]
    _ = ((omegaUnit R (archIdeleUnit w hw (Units.mk0 r hrne)) : ℂˣ) : ℂ)
          * R.toFun (X * archAt w hw rot) := omega_spec R _ _
    _ = _ := by
        rw [hrotarch, harch _ X, mul_assoc]

private theorem sigma_eq_of_det_pos (γ : GL (Fin 2) ℝ)
    (hγ : 0 < ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det) (wc : ℂ) :
    σ γ wc = wc := by
  unfold σ
  split
  · rfl
  · rename_i h
    exact absurd hγ h

private theorem coe_smul_of_det_pos (γ : GL (Fin 2) ℝ)
    (hγ : 0 < ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det) (z : UpperHalfPlane) :
    ((γ • z : UpperHalfPlane) : ℂ) = num γ (z : ℂ) / denom γ (z : ℂ) := by
  rw [coe_smul]
  exact sigma_eq_of_det_pos γ hγ _

private theorem mobius_differentiableOn (γ : GL (Fin 2) ℝ) :
    DifferentiableOn ℂ (fun zc : ℂ => num γ zc / denom γ zc) {zc : ℂ | 0 < zc.im} := by
  apply DifferentiableOn.div
  · intro zc _
    exact (Differentiable.differentiableAt (by unfold num; fun_prop)).differentiableWithinAt
  · intro zc _
    exact (Differentiable.differentiableAt (by unfold denom; fun_prop)).differentiableWithinAt
  · intro zc hzc
    exact denom_ne_zero γ ⟨zc, hzc⟩

private theorem exists_descent_ne_zero (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) (hN : Ψ.level ≠ ⊥)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun) :
    ∃ z : UpperHalfPlane, R.toFun (archAt w hw (iwasawaSec z)) ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  obtain ⟨γ', hlev, hpos⟩ :=
    NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat hN g₀
  set u : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ' * g₀ with hu
  have hfu : R.toFun u = R.toFun g₀ := R.left_invariant γ' g₀

  have hufin : glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ Ψ.level :=
    (mem_levelOne_iff).mp hlev
  have hsplitu : u = adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ u)
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u) := eq_archIncl_mul_finEmbed u
  have hfarch : R.toFun u = R.toFun (adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ u)) := by
    conv_lhs => rw [hsplitu]
    exact R.level_invariant _ _ (finEmbed_mem_U hufin)

  set B : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.map
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom)
      (archComponent ℚ w (glArch (𝓞 ℚ) ℚ u)) with hB
  have hBpos : (0:ℝ) < ((B : Matrix (Fin 2) (Fin 2) ℝ)).det := by
    have h1 := hpos w hw
    rw [Matrix.mem_glpos] at h1
    calc (0:ℝ) < (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom)
          (archComponent ℚ w (glArch (𝓞 ℚ) ℚ
            (globalPoints (𝓞 ℚ) ℚ γ' * g₀)))) : ℝ) := h1
      _ = ((B : Matrix (Fin 2) (Fin 2) ℝ)).det := rfl

  have harchB : adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ u) = archAt w hw B := by
    have h1 : archComponent ℚ w (glArch (𝓞 ℚ) ℚ u)
        = Matrix.GeneralLinearGroup.map
            ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom) B :=
      (map_symm_map hw (archComponent ℚ w (glArch (𝓞 ℚ) ℚ u))).symm
    rw [show archAt w hw B = adelicArchGLIncl ℚ (archGLIncl ℚ w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom) B)) from rfl,
      ← h1, archGLIncl_archComponent_g5]

  have hBfact : B = iwasawaSec (B • I) * kappa B I := by
    have h1 := mul_iwasawaSec_eq B I
    rwa [iwasawaSec_I, mul_one] at h1
  have hκI : kappa B I • I = I := kappa_smul_I B I
  have hκdet : (0:ℝ) < ((kappa B I : Matrix (Fin 2) (Fin 2) ℝ)).det := by
    rw [det_kappa B I hBpos]
    exact Complex.normSq_pos.mpr (denom_ne_zero B I)
  obtain ⟨v, hvne, hv⟩ := toFun_mul_archAt_stabilizer R w hw harch hκI hκdet
    (archAt w hw (iwasawaSec (B • I)))
  refine ⟨B • I, fun hzero => hg₀ ?_⟩
  have h2 : R.toFun (archAt w hw B) = v * R.toFun (archAt w hw (iwasawaSec (B • I))) := by
    conv_lhs => rw [hBfact, map_mul]
    exact hv
  rw [← hfu, hfarch, harchB, h2, hzero, mul_zero]

end Stage3Furniture
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section G5Main

variable {Ψ : HeckeEigensystem ℚ ℂ}

private theorem omegaUnit_archIdele_eq_self (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) (hN : Ψ.level ≠ ⊥)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    (hhol : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, MDifferentiable (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
        ((z.im : ℝ) : ℂ)⁻¹ * R.toFun (g * archAt w hw (iwasawaSec z)))
    (t : ℝˣ) (ht : (0 : ℝ) < (t : ℝ)) :
    ((omegaUnit R (archIdeleUnit w hw t) : ℂˣ) : ℂ) = ((t : ℝ) : ℂ) := by
  set N₀ := Ideal.absNorm Ψ.level with hN₀def
  have hcN : ((N₀ : ℝ)) ≠ 0 := by
    have h1 : N₀ ≠ 0 := by
      rw [hN₀def]
      exact fun h => hN (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast h1
  set γ := gammaR N₀ with hγdef
  have hγpos : (0:ℝ) < ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det := det_gammaR_pos N₀
  have hdetγ : ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det = 1 := by
    rw [hγdef]; exact det_gammaR N₀
  have hdenγ : ∀ wc : ℂ, denom γ wc = ((N₀ : ℝ) : ℂ) * wc + 1 := by
    intro wc; rw [hγdef]; exact denom_gammaR N₀ wc
  set G : UpperHalfPlane → ℂ := fun z => R.toFun (archAt w hw (iwasawaSec z)) with hGdef
  set F : ℂ → ℂ := fun zc =>
    (((UpperHalfPlane.ofComplex zc).im : ℝ) : ℂ)⁻¹ * G (UpperHalfPlane.ofComplex zc)
    with hFdef
  set m : ℂ → ℂ := fun zc => num γ zc / denom γ zc with hmdef
  set η : ℝ → ℂ := fun s => omegaPos R w hw s / ((s : ℝ) : ℂ) with hηdef

  have hF : DifferentiableOn ℂ F Hset := by
    have h1 := UpperHalfPlane.mdifferentiable_iff.mp (hhol 1)
    have h2 : F = (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹
        * R.toFun (1 * archAt w hw (iwasawaSec z))) ∘ UpperHalfPlane.ofComplex := by
      funext zc
      simp only [Function.comp_apply, one_mul]
      rfl
    rw [h2]
    exact h1

  have hmapsTo : Set.MapsTo m Hset Hset := by
    intro zc hzc
    have h1 : m zc = ((γ • UpperHalfPlane.ofComplex zc : UpperHalfPlane) : ℂ) := by
      show num γ zc / denom γ zc = _
      rw [coe_smul_of_det_pos γ hγpos (UpperHalfPlane.ofComplex zc), coe_ofComplex hzc]
    show (0:ℝ) < (m zc).im
    rw [h1]
    exact (γ • UpperHalfPlane.ofComplex zc).2
  have hG2 : DifferentiableOn ℂ (F ∘ m) Hset :=
    DifferentiableOn.comp hF (mobius_differentiableOn γ) hmapsTo
  have hFb : DifferentiableOn ℂ (fun zc => denom γ zc * F zc) Hset := by
    refine DifferentiableOn.mul ?_ hF
    intro zc _
    exact (Differentiable.differentiableAt (by unfold denom; fun_prop)).differentiableWithinAt

  have hGne : ¬ Set.EqOn (F ∘ m) (fun _ => (0:ℂ)) Hset := by
    obtain ⟨z₀, hz₀⟩ := exists_descent_ne_zero R w hw hN harch
    intro hEq
    apply hz₀
    have hmem : ((γ⁻¹ • z₀ : UpperHalfPlane) : ℂ) ∈ Hset := (γ⁻¹ • z₀).2
    have h3 := hEq hmem
    have h4 : m ((γ⁻¹ • z₀ : UpperHalfPlane) : ℂ) = (z₀ : ℂ) := by
      show num γ _ / denom γ _ = _
      rw [← coe_smul_of_det_pos γ hγpos (γ⁻¹ • z₀), smul_inv_smul]
    have h5 : (F ∘ m) ((γ⁻¹ • z₀ : UpperHalfPlane) : ℂ)
        = ((z₀.im : ℝ) : ℂ)⁻¹ * G z₀ := by
      rw [Function.comp_apply, h4]
      show (((UpperHalfPlane.ofComplex (z₀ : ℂ)).im : ℝ) : ℂ)⁻¹
          * G (UpperHalfPlane.ofComplex (z₀ : ℂ)) = _
      rw [UpperHalfPlane.ofComplex_apply z₀]
    rw [h5] at h3
    rcases mul_eq_zero.mp h3 with h6 | h6
    · exact absurd h6 (inv_ne_zero (Complex.ofReal_ne_zero.mpr z₀.im_pos.ne'))
    · exact h6

  have hrel : ∀ zc ∈ Hset,
      denom γ zc * F zc
        = η ‖((N₀ : ℝ) : ℂ) * zc + ((1:ℝ) : ℂ)‖ * (F ∘ m) zc := by
    intro zc hzc
    have hcz : ((UpperHalfPlane.ofComplex zc : UpperHalfPlane) : ℂ) = zc :=
      coe_ofComplex hzc
    set z := UpperHalfPlane.ofComplex zc with hzdef
    have hmz : m zc = ((γ • z : UpperHalfPlane) : ℂ) := by
      show num γ zc / denom γ zc = _
      rw [coe_smul_of_det_pos γ hγpos z, hcz]
    have hFz : F zc = ((z.im : ℝ) : ℂ)⁻¹ * G z := rfl
    have hFmz : (F ∘ m) zc = (((γ • z).im : ℝ) : ℂ)⁻¹ * G (γ • z) := by
      rw [Function.comp_apply, hmz]
      show (((UpperHalfPlane.ofComplex ((γ • z : UpperHalfPlane) : ℂ)).im : ℝ) : ℂ)⁻¹
          * G (UpperHalfPlane.ofComplex ((γ • z : UpperHalfPlane) : ℂ)) = _
      rw [UpperHalfPlane.ofComplex_apply (γ • z)]
    have hdz : denom γ zc = denom γ (z : ℂ) := by rw [hcz]
    have hnorm : ‖((N₀ : ℝ) : ℂ) * zc + ((1:ℝ) : ℂ)‖ = ‖denom γ (z : ℂ)‖ := by
      rw [Complex.ofReal_one, ← hdenγ zc, hdz]
    have him2 : ((γ • z).im : ℝ) = z.im / Complex.normSq (denom γ (z : ℂ)) := by
      have ha1 : |(Matrix.GeneralLinearGroup.det γ : ℝ)| = 1 := by
        rw [show (Matrix.GeneralLinearGroup.det γ : ℝ)
            = ((γ : Matrix (Fin 2) (Fin 2) ℝ)).det from rfl, hdetγ]
        norm_num
      rw [im_smul_eq_div_normSq γ z, ha1, one_mul]
    have hdne : denom γ (z : ℂ) ≠ 0 := denom_ne_zero γ z
    have hrne : ‖denom γ (z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hdne
    have hzim : z.im ≠ 0 := z.im_pos.ne'
    have hnsne : Complex.normSq (denom γ (z : ℂ)) ≠ 0 :=
      (Complex.normSq_pos.mpr hdne).ne'
    have hconj : starRingEnd ℂ (denom γ (z : ℂ))
        = ((‖denom γ (z : ℂ)‖ : ℝ) : ℂ) ^ 2 / denom γ (z : ℂ) := by
      rw [eq_div_iff hdne, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have hK2 : G z = omegaPos R w hw ‖denom γ (z : ℂ)‖
        * (starRingEnd ℂ (denom γ (z : ℂ)) / ((‖denom γ (z : ℂ)‖ : ℝ) : ℂ))
        * G (γ • z) := descent_kappa_relation R w hw harch z
    rw [hdz, hnorm, hFz, hFmz, hK2, him2]
    show denom γ (z : ℂ)
        * (((z.im : ℝ) : ℂ)⁻¹ * (omegaPos R w hw ‖denom γ (z : ℂ)‖
            * (starRingEnd ℂ (denom γ (z : ℂ)) / ((‖denom γ (z : ℂ)‖ : ℝ) : ℂ))
            * G (γ • z)))
      = omegaPos R w hw ‖denom γ (z : ℂ)‖ / ((‖denom γ (z : ℂ)‖ : ℝ) : ℂ)
          * ((((z.im / Complex.normSq (denom γ (z : ℂ))) : ℝ) : ℂ)⁻¹ * G (γ • z))
    rw [hconj, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp

  have key := eta_eq_of_radial_ratio η (fun zc => denom γ zc * F zc) (F ∘ m)
    (N₀ : ℝ) 1 hcN hFb hG2 hGne hrel
  have hη1 : η 1 = 1 := by
    show omegaPos R w hw 1 / ((1:ℝ) : ℂ) = 1
    rw [omegaPos_of_pos R w hw one_pos,
      show Units.mk0 (1:ℝ) one_pos.ne' = 1 from Units.ext rfl,
      archIdeleUnit_one w hw, map_one]
    norm_num
  have hkey := key (t : ℝ) ht
  rw [hη1] at hkey
  have h8 : omegaPos R w hw (t : ℝ) / (((t : ℝ)) : ℂ) = 1 := hkey
  rw [div_eq_one_iff_eq (Complex.ofReal_ne_zero.mpr ht.ne')] at h8
  rw [omegaPos_of_pos R w hw ht,
    show Units.mk0 ((t : ℝ)) ht.ne' = t from Units.ext rfl] at h8
  exact h8

private theorem homega_of_archType (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) (hN : Ψ.level ≠ ⊥)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    (hhol : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, MDifferentiable (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
        ((z.im : ℝ) : ℂ)⁻¹ * R.toFun (g * archAt w hw (iwasawaSec z))) :
    ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g := by
  intro t ht g
  rw [← centralScalar_archIdeleUnit w hw t, omega_spec R (archIdeleUnit w hw t) g,
    omegaUnit_archIdele_eq_self R w hw hN harch hhol t ht]

end G5Main
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section AuditG5

end AuditG5
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part03
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part04

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel

open AutomorphicForm MeasureTheory

noncomputable section

namespace HeckeDictionary

section OmegaInfra

variable {Ψ : HeckeEigensystem ℚ ℂ}

private def principalUnit (m : ℚˣ) : H4Adˣ := Units.map (algebraMap ℚ H4Ad).toMonoidHom m

private theorem globalPoints_scalar (m : ℚˣ) :
    globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) m)
      = centralScalar (𝓞 ℚ) ℚ (principalUnit m) := by
  ext i j
  simp only [globalPoints, centralScalar, principalUnit, Matrix.GeneralLinearGroup.map,
    Units.coe_map, Matrix.GeneralLinearGroup.scalar]
  by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply]

private theorem omegaUnit_eq_one_of_centralScalar_mem (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    {z : H4Adˣ} (hz : centralScalar (𝓞 ℚ) ℚ z ∈ h4pins.U Ψ.level) :
    omegaUnit R z = 1 := by
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have h1 := omega_spec R z g₀
  have h2 : R.toFun (centralScalar (𝓞 ℚ) ℚ z * g₀) = R.toFun g₀ := by
    rw [centralScalar_mul_comm]
    exact R.level_invariant g₀ _ hz
  have h3 : ((omegaUnit R z : ℂˣ) : ℂ) * R.toFun g₀ = 1 * R.toFun g₀ := by
    rw [one_mul]
    exact h1.symm.trans h2
  exact Units.ext (mul_right_cancel₀ hg₀ h3)

private theorem omegaUnit_principal (R : SmoothCuspRealizationAt ℚ h4pins Ψ) (m : ℚˣ) :
    omegaUnit R (principalUnit m) = 1 := by
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have hL := R.left_invariant (Matrix.GeneralLinearGroup.scalar (Fin 2) m) g₀
  rw [globalPoints_scalar] at hL
  have h3 : ((omegaUnit R (principalUnit m) : ℂˣ) : ℂ) * R.toFun g₀ = 1 * R.toFun g₀ := by
    rw [one_mul]
    exact (omega_spec R (principalUnit m) g₀).symm.trans hL
  exact Units.ext (mul_right_cancel₀ hg₀ h3)

end OmegaInfra
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Bridge

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

private theorem intValuation_le_idealBound_of_mem_H4 (v : HeightOneSpectrum A) {N : Ideal A} {r : A}
    (hr : r ∈ N) : v.intValuation r ≤ idealBound A N v := by
  classical
  by_cases hN : N = ⊥
  · subst hN
    rw [Ideal.mem_bot] at hr
    subst hr
    rw [map_zero, idealBound_bot]
  · by_cases hr0 : r = 0
    · subst hr0
      rw [map_zero]
      exact zero_le'
    · rw [v.intValuation_if_neg hr0, idealBound_of_ne_bot hN]
      have hdvd : Ideal.span {r} ≤ N := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hr)
      have hle := Associates.mk_le_mk_iff_dvd.mpr (Ideal.dvd_iff_le.mpr hdvd)
      have hb : Associates.mk (Ideal.span {r}) ≠ (0 : Associates (Ideal A)) := by
        rw [Ne, Associates.mk_eq_zero]
        exact fun h => hr0 (Ideal.span_singleton_eq_bot.mp h)
      have hcount := Associates.count_le_count_of_le hb v.associates_irreducible hle
      rw [WithZero.exp_le_exp]
      exact neg_le_neg (by exact_mod_cast hcount)

end Bridge
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section PrincipalMembership

end PrincipalMembership
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section KillAssembler

private theorem isLevelOneMatrix_scalar {L : Ideal (𝓞 ℚ)} {x : FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) (hb : x - 1 ∈ idealBall (𝓞 ℚ) ℚ L) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L (Matrix.scalar (Fin 2) x) where
  integral i j := by
    by_cases h : i = j
    · subst h
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      exact hx
    · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]
      exact zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    exact zero_mem_idealBall L
  lowerRight := by
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact hb

private theorem glFin_centralScalar_entry (w : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (i j : Fin 2) :
    ((glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) w)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
      = Matrix.diagonal (fun _ => (w : FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := by
  rw [glFin_apply]
  show adeleFin (𝓞 ℚ) ℚ (Matrix.diagonal
    (fun _ => (finIncl (𝓞 ℚ) ℚ (w : FiniteAdeleRing (𝓞 ℚ) ℚ) : H4Ad)) i j) = _
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]

private theorem isLevelOneMatrix_glFin_centralScalar {L : Ideal (𝓞 ℚ)}
    (w : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hint : (w : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hball : (w : FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ idealBall (𝓞 ℚ) ℚ L) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L
      ((glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) w)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) _) where
  integral i j := by
    rw [glFin_centralScalar_entry]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
      exact hint
    · rw [Matrix.diagonal_apply_ne _ h]
      exact zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [glFin_centralScalar_entry,
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    exact zero_mem_idealBall L
  lowerRight := by
    rw [glFin_centralScalar_entry, Matrix.diagonal_apply_eq]
    exact hball

private theorem units_inv_sub_one {α : Type*} [CommRing α] (u : αˣ) :
    ((u⁻¹ : αˣ) : α) - 1 = (-1 : α) * (((u⁻¹ : αˣ) : α) * ((u : α) - 1)) := by
  have hui : ((u⁻¹ : αˣ) : α) * (u : α) = 1 := Units.inv_mul u
  linear_combination hui

set_option maxHeartbeats 1600000 in
private theorem inv_sub_one_mem_idealBall {L : Ideal (𝓞 ℚ)} (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hinv : ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hb : (u : FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ idealBall (𝓞 ℚ) ℚ L) :
    ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) - 1
      ∈ idealBall (𝓞 ℚ) ℚ L := by
  have hneg1 : (-1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    have h := sub_mem_integralFiniteAdeles
      (zero_mem_integralFiniteAdeles (R := 𝓞 ℚ) (K := ℚ)) one_mem_integralFiniteAdeles
    rwa [zero_sub] at h
  rw [units_inv_sub_one u]
  exact mul_mem_idealBall_left hneg1 (mul_mem_idealBall_left hinv hb)

private theorem centralScalar_finIncl_mem_U {L : Ideal (𝓞 ℚ)} (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hint : (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hinv : ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hball : (u : FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ idealBall (𝓞 ℚ) ℚ L) :
    centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) u) ∈ h4pins.U L := by
  rw [productionPinsCompact_U]
  constructor
  · show glFin (𝓞 ℚ) ℚ _ ∈ finiteLevelOne (𝓞 ℚ) ℚ L
    rw [mem_finiteLevelOne_iff]
    refine ⟨isLevelOneMatrix_glFin_centralScalar u hint hball, ?_⟩
    have hrw : (glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) u)))⁻¹
        = glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) u⁻¹)) := by
      rw [← map_inv, ← map_inv, ← map_inv]
    rw [hrw]
    exact isLevelOneMatrix_glFin_centralScalar u⁻¹ hinv
      (inv_sub_one_mem_idealBall u hinv hball)
  · show glArch (𝓞 ℚ) ℚ _ = 1
    ext i j
    rw [glArch_apply]
    show adeleArch (𝓞 ℚ) ℚ (Matrix.diagonal
      (fun _ => (finIncl (𝓞 ℚ) ℚ (u : FiniteAdeleRing (𝓞 ℚ) ℚ) : H4Ad)) i j)
      = ((1 : GL (Fin 2) (InfiniteAdeleRing ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
      have h1 : adeleArch (𝓞 ℚ) ℚ (finIncl (𝓞 ℚ) ℚ (u : FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 := rfl
      rw [h1, Units.val_one, Matrix.one_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero, Units.val_one, Matrix.one_apply_ne h]

end KillAssembler
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section RatPrimeFacts

private theorem natGenerator_ratPrime (p : Nat.Primes) :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (ratPrime p) = (p : ℕ) :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

private theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((n : ℤ)) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : 𝓞 ℚ)) from
      (map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n).symm,
    Ideal.apply_mem_of_equiv_iff]

private theorem natCast_not_mem_asIdeal_of_coprime {L : Ideal (𝓞 ℚ)} (hL : L ≠ ⊥)
    {w : HeightOneSpectrum (𝓞 ℚ)} (hwL : idealBound (𝓞 ℚ) L w ≠ 1) {m : ℕ}
    (hcop : m.Coprime (Ideal.absNorm L)) : (m : 𝓞 ℚ) ∉ w.asIdeal := by
  intro hmem
  have hdvd : w.asIdeal ∣ L := by
    by_contra h
    exact hwL (idealBound_eq_one_of_not_dvd hL h)
  have hNmem : ((Ideal.absNorm L : ℕ) : 𝓞 ℚ) ∈ w.asIdeal :=
    Ideal.dvd_iff_le.mp hdvd (Ideal.absNorm_mem L)
  have h1 : Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w ∣ Ideal.absNorm L :=
    (natCast_mem_asIdeal_iff w _).mp hNmem
  have h2 : Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w ∣ m :=
    (natCast_mem_asIdeal_iff w m).mp hmem
  have h3 : Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w ∣ 1 :=
    Nat.dvd_gcd h2 h1 |>.trans (dvd_of_eq hcop)
  exact (Rat.HeightOneSpectrum.prime_natGenerator (R := 𝓞 ℚ) w).ne_one (Nat.dvd_one.mp h3)

end RatPrimeFacts
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section EpsilonCarrier

variable {L : Ideal (𝓞 ℚ)}

private noncomputable def levelPlaces (hL : L ≠ ⊥) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  (finite_setOf_idealBound_ne_one hL).toFinset

private theorem mem_levelPlaces {hL : L ≠ ⊥} {w : HeightOneSpectrum (𝓞 ℚ)} :
    w ∈ levelPlaces hL ↔ idealBound (𝓞 ℚ) L w ≠ 1 := by
  unfold levelPlaces
  exact Set.Finite.mem_toFinset _

private noncomputable def epsUnitHom (hL : L ≠ ⊥) : ℚˣ →* (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  ∏ w ∈ levelPlaces hL,
    (localUnit (𝓞 ℚ) ℚ w).comp (Units.map (algebraMap ℚ (w.adicCompletion ℚ)).toMonoidHom)

private theorem epsUnitHom_apply (hL : L ≠ ⊥) (q : ℚˣ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((epsUnitHom hL q : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w
      = if idealBound (𝓞 ℚ) L w ≠ 1
        then algebraMap ℚ (w.adicCompletion ℚ) (q : ℚ) else 1 := by
  classical
  rw [epsUnitHom, MonoidHom.finsetProd_apply,
    show ((∏ w' ∈ levelPlaces hL,
        ((localUnit (𝓞 ℚ) ℚ w').comp
          (Units.map (algebraMap ℚ (w'.adicCompletion ℚ)).toMonoidHom)) q :
        (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      = ∏ w' ∈ levelPlaces hL,
        ((((localUnit (𝓞 ℚ) ℚ w').comp
          (Units.map (algebraMap ℚ (w'.adicCompletion ℚ)).toMonoidHom)) q :
          (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      from map_prod (Units.coeHom _) _ _,
    ← finAdeleEval_apply, map_prod]
  simp only [finAdeleEval_apply, MonoidHom.coe_comp, Function.comp_apply]
  by_cases hw : idealBound (𝓞 ℚ) L w ≠ 1
  · rw [if_pos hw]
    rw [Finset.prod_eq_single_of_mem w (mem_levelPlaces.mpr hw)
      (fun w' _ hne => localUnit_apply_of_ne (𝓞 ℚ) ℚ w' _ hne.symm)]
    exact localUnit_apply_self (𝓞 ℚ) ℚ w _
  · rw [if_neg hw]
    refine Finset.prod_eq_one fun w' hw' => ?_
    refine localUnit_apply_of_ne (𝓞 ℚ) ℚ w' _ ?_
    intro h
    exact hw (by rw [h]; exact mem_levelPlaces.mp hw')

private def ratUnit (m : ℕ) (hm : 0 < m) : ℚˣ :=
  Units.mk0 (m : ℚ) (by exact_mod_cast hm.ne')

@[scoped simp] private theorem ratUnit_val (m : ℕ) (hm : 0 < m) : ((ratUnit m hm : ℚˣ) : ℚ) = (m : ℚ) := rfl

private theorem valued_natCast_eq_one (hL : L ≠ ⊥) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hwL : idealBound (𝓞 ℚ) L w ≠ 1) {m : ℕ} (hcop : m.Coprime (Ideal.absNorm L)) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (m : ℚ)) = 1 := by
  rw [show ((m : ℚ)) = algebraMap (𝓞 ℚ) ℚ ((m : 𝓞 ℚ)) by simp, valued_algebraMap]
  exact intValuation_eq_one_iff.mpr (natCast_not_mem_asIdeal_of_coprime hL hwL hcop)

private theorem epsUnitHom_div_conditions (hL : L ≠ ⊥) {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hcop : m.Coprime (Ideal.absNorm L)) (hcop' : m'.Coprime (Ideal.absNorm L))
    (hdvd : ((Ideal.absNorm L : ℕ) : ℤ) ∣ (m : ℤ) - (m' : ℤ)) :
    (((epsUnitHom hL (ratUnit m hm / ratUnit m' hm') :
        (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    ∧ ((((epsUnitHom hL (ratUnit m hm / ratUnit m' hm'))⁻¹ :
        (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    ∧ (((epsUnitHom hL (ratUnit m hm / ratUnit m' hm') :
        (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) - 1
      ∈ idealBall (𝓞 ℚ) ℚ L) := by
  classical
  have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have hq : ((ratUnit m hm / ratUnit m' hm' : ℚˣ) : ℚ) = (m : ℚ) / (m' : ℚ) := by
    rw [Units.val_div_eq_div_val]; rfl
  have hqi : (((ratUnit m hm / ratUnit m' hm')⁻¹ : ℚˣ) : ℚ) = (m' : ℚ) / (m : ℚ) := by
    rw [Units.val_inv_eq_inv_val, Units.val_div_eq_div_val, inv_div]; rfl
  have hint : ∀ (a b : ℕ), a.Coprime (Ideal.absNorm L) → b.Coprime (Ideal.absNorm L) →
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
        (if idealBound (𝓞 ℚ) L w ≠ 1
          then algebraMap ℚ (w.adicCompletion ℚ) ((a : ℚ) / (b : ℚ)) else 1)
          ∈ w.adicCompletionIntegers ℚ := by
    intro a b ha hb w
    by_cases hw : idealBound (𝓞 ℚ) L w ≠ 1
    · rw [if_pos hw, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, map_div₀,
        valued_natCast_eq_one hL hw ha, valued_natCast_eq_one hL hw hb]
      simp
    · rw [if_neg hw]
      exact one_mem _
  refine ⟨?_, ?_, ?_⟩
  · intro w
    rw [epsUnitHom_apply, hq]
    exact hint m m' hcop hcop' w
  · intro w
    rw [← map_inv, epsUnitHom_apply, hqi]
    exact hint m' m hcop' hcop w
  · intro w
    rw [← finAdeleEval_apply, map_sub, map_one, finAdeleEval_apply, epsUnitHom_apply, hq]
    by_cases hw : idealBound (𝓞 ℚ) L w ≠ 1
    · rw [if_pos hw]
      have hQ : (m : ℚ) / (m' : ℚ) - 1 = ((m : ℚ) - (m' : ℚ)) / (m' : ℚ) := by
        field_simp
      rw [show algebraMap ℚ (w.adicCompletion ℚ) ((m : ℚ) / (m' : ℚ)) - 1
            = algebraMap ℚ (w.adicCompletion ℚ) (((m : ℚ) - (m' : ℚ)) / (m' : ℚ)) by
          rw [← hQ, map_sub, map_one]]
      rw [map_div₀, map_div₀, valued_natCast_eq_one hL hw hcop', div_one,
        show (m : ℚ) - (m' : ℚ) = algebraMap (𝓞 ℚ) ℚ ((m : 𝓞 ℚ) - (m' : 𝓞 ℚ)) by
          rw [map_sub]; simp,
        valued_algebraMap]
      refine intValuation_le_idealBound_of_mem_H4 w ?_
      obtain ⟨c, hc⟩ := hdvd
      have hδ : (m : 𝓞 ℚ) - (m' : 𝓞 ℚ) = ((Ideal.absNorm L : ℕ) : 𝓞 ℚ) * (c : 𝓞 ℚ) := by
        have h2 := congrArg (fun z : ℤ => (z : 𝓞 ℚ)) hc
        push_cast at h2
        exact h2
      rw [hδ]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem L)
    · rw [if_neg hw, sub_self, map_zero]
      exact zero_le'

private theorem omegaUnit_epsUnitHom_div {Ψ : HeckeEigensystem ℚ ℂ}
    (R : SmoothCuspRealizationAt ℚ h4pins Ψ) {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hcop : m.Coprime (Ideal.absNorm Ψ.level)) (hcop' : m'.Coprime (Ideal.absNorm Ψ.level))
    (hdvd : ((Ideal.absNorm Ψ.level : ℕ) : ℤ) ∣ (m : ℤ) - (m' : ℤ)) :
    omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
      (epsUnitHom Ψ.level_ne_bot (ratUnit m hm / ratUnit m' hm'))) = 1 := by
  obtain ⟨h1, h2, h3⟩ := epsUnitHom_div_conditions Ψ.level_ne_bot hm hm' hcop hcop' hdvd
  exact omegaUnit_eq_one_of_centralScalar_mem R (centralScalar_finIncl_mem_U _ h1 h2 h3)

end EpsilonCarrier
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section RatPrimeNorm

private theorem intEquiv_dvd_iff (x y : 𝓞 ℚ) :
    x ∣ y ↔ Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x ∣ Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) y := by
  constructor
  · exact fun h => map_dvd (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h
  · intro h
    have h2 := map_dvd (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm h
    simpa only [RingEquiv.symm_apply_apply] using h2

private theorem ratPrime_asIdeal_eq_span (p : Nat.Primes) :
    (ratPrime p).asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := by
  ext x
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    have h1 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x
        ∈ (ratPrime p).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) :=
      Ideal.apply_mem_of_equiv_iff.mpr hx
    rw [← Rat.HeightOneSpectrum.span_natGenerator, natGenerator_ratPrime,
      Ideal.mem_span_singleton] at h1
    rw [intEquiv_dvd_iff]
    simpa using h1
  · intro hx
    have h1 : ((p : ℕ) : ℤ) ∣ Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x := by
      have h2 := (intEquiv_dvd_iff _ x).mp hx
      simpa using h2
    have h2 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x
        ∈ (ratPrime p).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
      rw [← Rat.HeightOneSpectrum.span_natGenerator, natGenerator_ratPrime,
        Ideal.mem_span_singleton]
      exact h1
    exact Ideal.apply_mem_of_equiv_iff.mp h2

private theorem absNorm_ratPrime (p : Nat.Primes) :
    Ideal.absNorm (ratPrime p).asIdeal = (p : ℕ) := by
  rw [ratPrime_asIdeal_eq_span, Ideal.absNorm_span_singleton,
    show (((p : ℕ) : 𝓞 ℚ)) = algebraMap ℤ (𝓞 ℚ) ((p : ℕ) : ℤ) by simp,
    Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  simp

private theorem cNorm_ratPrime (p : Nat.Primes) :
    HeckeEigensystem.cNorm (ratPrime p) = ((p : ℕ) : ℂ) := by
  rw [HeckeEigensystem.cNorm, absNorm_ratPrime]

private theorem idealBound_ratPrime_eq_one {L : Ideal (𝓞 ℚ)} (hL : L ≠ ⊥) (p : Nat.Primes)
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm L) : idealBound (𝓞 ℚ) L (ratPrime p) = 1 := by
  refine idealBound_eq_one_of_not_dvd hL fun hdvd => hpN ?_
  have hmem : ((Ideal.absNorm L : ℕ) : 𝓞 ℚ) ∈ (ratPrime p).asIdeal :=
    Ideal.dvd_iff_le.mp hdvd (Ideal.absNorm_mem L)
  have h1 := (natCast_mem_asIdeal_iff (ratPrime p) _).mp hmem
  rwa [natGenerator_ratPrime] at h1

end RatPrimeNorm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section ChiSupply

open EisensteinWeightOne

private theorem chiNegThree_mul (a b : ℕ) :
    chiNegThree (a * b) = chiNegThree a * chiNegThree b := by
  unfold chiNegThree
  rw [Nat.mul_mod]
  have ha : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hb : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h1 : a % 3 <;> interval_cases h2 : b % 3 <;> norm_num

private theorem chiNegThree_eq_one_or_neg_one {n : ℕ} (h3 : ¬ 3 ∣ n) :
    chiNegThree n = 1 ∨ chiNegThree n = -1 := by
  unfold chiNegThree
  have hn : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h0 : n % 3 ≠ 0 := fun h => h3 (Nat.dvd_of_mod_eq_zero h)
  interval_cases h1 : n % 3
  · exact absurd rfl h0
  · left; norm_num
  · right; norm_num

private theorem chiNegThree_complex_self_inv {n : ℕ} (h3 : ¬ 3 ∣ n) :
    ((chiNegThree n : ℤ) : ℂ)⁻¹ = ((chiNegThree n : ℤ) : ℂ) := by
  rcases chiNegThree_eq_one_or_neg_one h3 with h | h <;> rw [h] <;> norm_num

end ChiSupply
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section DetPlumbing

private theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = (a : A)
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

private theorem det_heckeGenAt (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 ℚ) ℚ v t)
      = Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t) := by
  rw [show heckeGenAt (𝓞 ℚ) ℚ v t
      = diagOne (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) from rfl]
  exact det_diagOne _

end DetPlumbing
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section PrimeSplit

variable {Ψ : HeckeEigensystem ℚ ℂ}

private noncomputable def pUnit (p : Nat.Primes) : ((ratPrime p).adicCompletion ℚ)ˣ :=
  Units.mk0 (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((p : ℕ) : ℚ))
    (by
      refine (map_ne_zero _).mpr ?_
      exact_mod_cast p.2.pos.ne')

private theorem valued_pUnit (p : Nat.Primes) :
    Valued.v ((pUnit p : ((ratPrime p).adicCompletion ℚ))) = WithZero.exp (-1 : ℤ) := by
  show Valued.v (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((p : ℕ) : ℚ))
    = WithZero.exp (-1 : ℤ)
  rw [show (((p : ℕ) : ℚ)) = algebraMap (𝓞 ℚ) ℚ (((p : ℕ) : 𝓞 ℚ)) by simp,
    valued_algebraMap]
  exact intValuation_singleton _ (by exact_mod_cast p.2.pos.ne')
    (ratPrime_asIdeal_eq_span p)

private theorem omegaUnit_finIncl_localUnit_of_valued_one
    (R : SmoothCuspRealizationAt ℚ h4pins Ψ) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : idealBound (𝓞 ℚ) Ψ.level v = 1) {u : (v.adicCompletion ℚ)ˣ}
    (hu : Valued.v ((u : v.adicCompletion ℚ)) = 1) :
    omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v u)) = 1 := by
  have huinv : Valued.v (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = 1 := by
    have h : Valued.v ((u : v.adicCompletion ℚ))
        * Valued.v (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = 1 := by
      rw [← map_mul]
      simp
    rw [hu, one_mul] at h
    exact h
  refine omegaUnit_eq_one_of_centralScalar_mem R (centralScalar_finIncl_mem_U _ ?_ ?_ ?_)
  · intro w
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v u hw]
      exact one_mem _
  · intro w
    rw [← map_inv]
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr huinv.le
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hw]
      exact one_mem _
  · intro w
    rw [← finAdeleEval_apply, map_sub, map_one, finAdeleEval_apply]
    by_cases hw : w = v
    · subst hw
      calc Valued.v (((localUnit (𝓞 ℚ) ℚ w u : _ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w - 1)
          ≤ max (Valued.v (((localUnit (𝓞 ℚ) ℚ w u : _ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w))
            (Valued.v (1 : w.adicCompletion ℚ)) := Valuation.map_sub _ _ _
        _ ≤ 1 := by
            rw [localUnit_apply_self, hu, map_one]
            simp
        _ = idealBound (𝓞 ℚ) Ψ.level w := hv.symm
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v u hw, sub_self, map_zero]
      exact zero_le'

private theorem omegaUnit_finIncl_localUnit_pUnit (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm Ψ.level)
    (hpex : ratPrime p ∉ R.exceptionalSet) :
    ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))) : ℂˣ) : ℂ) = Ψ.b (ratPrime p) := by
  have hval_u : Valued.v ((((uniformizerUnit ℚ (ratPrime p))⁻¹ * pUnit p :
      ((ratPrime p).adicCompletion ℚ)ˣ) : (ratPrime p).adicCompletion ℚ)) = 1 := by
    rw [Units.val_mul, map_mul,
      show ((((uniformizerUnit ℚ (ratPrime p))⁻¹ :
          ((ratPrime p).adicCompletion ℚ)ˣ) : (ratPrime p).adicCompletion ℚ))
        = ((uniformizerUnit ℚ (ratPrime p) : (ratPrime p).adicCompletion ℚ))⁻¹ from rfl,
      map_inv₀, valued_uniformizerUnit, valued_pUnit, ← WithZero.exp_neg, ← WithZero.exp_add]
    norm_num
  have hsplit : localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
      = localUnit (𝓞 ℚ) ℚ (ratPrime p) (uniformizerUnit ℚ (ratPrime p))
        * localUnit (𝓞 ℚ) ℚ (ratPrime p) ((uniformizerUnit ℚ (ratPrime p))⁻¹ * pUnit p) := by
    rw [← map_mul]
    congr 1
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hsplit, map_mul, map_mul,
    show Units.map (finIncl (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ (ratPrime p) (uniformizerUnit ℚ (ratPrime p)))
      = Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ (ratPrime p)) from
      (det_heckeGenAt (ratPrime p) _).symm,
    omegaUnit_finIncl_localUnit_of_valued_one R
      (idealBound_ratPrime_eq_one Ψ.level_ne_bot p hpN) hval_u, mul_one]
  exact R.centralChar_det_gen_eq_b hpex _ (by rw [productionPinsCompact_gen])

end PrimeSplit
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section ArchBridge

attribute [local instance] instDecEqInfinitePlaceRat

variable {Ψ : HeckeEigensystem ℚ ℂ}

private theorem omegaUnit_archIdeleUnit (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (t : ℝˣ) (ht : (0 : ℝ) < (t : ℝ)) :
    ((omegaUnit R (archIdeleUnit w hw t) : ℂˣ) : ℂ) = ((t : ℝ) : ℂ) := by
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have h1 := omega_spec R (archIdeleUnit w hw t) g₀
  have h2 := homega t ht g₀
  rw [← centralScalar_archIdeleUnit w hw t, h1] at h2
  exact mul_right_cancel₀ hg₀ h2

private noncomputable def finRatUnit : ℚˣ →* (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom

@[scoped simp] private theorem finRatUnit_val (q : ℚˣ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((finRatUnit q : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w
      = algebraMap ℚ (w.adicCompletion ℚ) (q : ℚ) := rfl

private theorem principalUnit_eq_arch_mul_fin (w : InfinitePlace ℚ) (hw : w.IsReal)
    (m : ℕ) (hm : 0 < m) :
    principalUnit (ratUnit m hm)
      = archIdeleUnit w hw (Units.mk0 ((m : ℝ)) (by exact_mod_cast hm.ne'))
        * Units.map (finIncl (𝓞 ℚ) ℚ) (finRatUnit (ratUnit m hm)) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · funext w'
    rcases Subsingleton.elim w w' with rfl
    show algebraMap ℚ w.Completion ((m : ℚ))
      = ((archIdeleUnit w hw (Units.mk0 ((m : ℝ)) _) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
          AdeleRing (𝓞 ℚ) ℚ).1 w
        * ((Units.map (finIncl (𝓞 ℚ) ℚ) (finRatUnit (ratUnit m hm)) :
            (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 w
    rw [archIdeleUnit_val_fst_self,
      show ((Units.map (finIncl (𝓞 ℚ) ℚ) (finRatUnit (ratUnit m hm)) :
          (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 from rfl,
      show ((1 : InfiniteAdeleRing ℚ)) w = 1 from rfl, mul_one,
      map_natCast (algebraMap ℚ w.Completion)]
    show ((m : ℕ) : w.Completion)
      = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm ((m : ℝ))
    rw [map_natCast (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm]
  · show (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((m : ℚ))).2
      = (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)
        * ((finRatUnit (ratUnit m hm) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [one_mul]
    rfl

end ArchBridge
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section RestKill

variable {Ψ : HeckeEigensystem ℚ ℂ}

private theorem eq_ratPrime_of_natCast_mem (p : Nat.Primes) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hmem : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : w = ratPrime p := by
  have h1 : Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w ∣ (p : ℕ) :=
    (natCast_mem_asIdeal_iff w _).mp hmem
  have h2 : Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w = (p : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq
      (Rat.HeightOneSpectrum.prime_natGenerator (R := 𝓞 ℚ) w) p.2).mp h1
  have h3 : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w = p := Subtype.ext h2
  have h4 := congrArg (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm h3
  rwa [Equiv.symm_apply_apply] at h4

private theorem valued_natCast_prime_eq_one (p : Nat.Primes) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ ratPrime p) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (((p : ℕ) : ℚ))) = 1 := by
  rw [show ((((p : ℕ) : ℚ))) = algebraMap (𝓞 ℚ) ℚ (((p : ℕ) : 𝓞 ℚ)) by simp,
    valued_algebraMap]
  exact intValuation_eq_one_iff.mpr fun hmem => hw (eq_ratPrime_of_natCast_mem p hmem)

private theorem omegaUnit_eq_one_of_components (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (h1 : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (((u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w) = 1)
    (h2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), idealBound (𝓞 ℚ) Ψ.level w ≠ 1 →
      ((u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1) :
    omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ) u) = 1 := by
  have hinv : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Valued.v ((((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ)) w) = 1 := by
    intro w
    have hmul : Valued.v (((u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w)
        * Valued.v ((((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ)) w) = 1 := by
      rw [← map_mul, ← finAdeleEval_apply, ← finAdeleEval_apply, ← map_mul,
        show (((u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * (((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)))
          = 1 from Units.mul_inv u, map_one, map_one]
    rw [h1, one_mul] at hmul
    exact hmul
  refine omegaUnit_eq_one_of_centralScalar_mem R (centralScalar_finIncl_mem_U _ ?_ ?_ ?_)
  · intro w
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h1 w).le
  · intro w
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hinv w).le
  · intro w
    rw [← finAdeleEval_apply, map_sub, map_one, finAdeleEval_apply]
    by_cases hw : idealBound (𝓞 ℚ) Ψ.level w ≠ 1
    · rw [h2 w hw, sub_self, map_zero]
      exact zero_le'
    · rw [not_not.mp hw]
      calc Valued.v (((u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w - 1)
          ≤ max (Valued.v (((u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
              FiniteAdeleRing (𝓞 ℚ) ℚ) w)) (Valued.v (1 : w.adicCompletion ℚ)) :=
            Valuation.map_sub _ _ _
        _ ≤ 1 := by rw [h1, map_one]; simp

private theorem omegaUnit_rest (R : SmoothCuspRealizationAt ℚ h4pins Ψ) (p : Nat.Primes)
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm Ψ.level) :
    omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
      ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
          * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos))⁻¹
        * finRatUnit (ratUnit p p.2.pos))) = 1 := by
  have hpQ : (((p : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast p.2.pos.ne'
  have hboundp : idealBound (𝓞 ℚ) Ψ.level (ratPrime p) = 1 :=
    idealBound_ratPrime_eq_one Ψ.level_ne_bot p hpN

  have hcomp : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      (((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
            * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos))⁻¹
          * finRatUnit (ratUnit p p.2.pos) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          FiniteAdeleRing (𝓞 ℚ) ℚ) w
        = ((((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) :
              (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w)
            * (((epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos) :
              (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w))⁻¹
          * algebraMap ℚ (w.adicCompletion ℚ) (((p : ℕ) : ℚ)) := by
    intro w
    have hmul1 : (((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
          * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos) :
          (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) w
        * ((((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
          * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos))⁻¹ :
          (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) w = 1 := by
      rw [show (((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
            * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos) :
            (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) w
          * ((((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
            * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos))⁻¹ :
            (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) w
          = finAdeleEval (𝓞 ℚ) ℚ w
            ((((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
              * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos) :
              (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ))
            * ((((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
              * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos))⁻¹ :
              (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ))) from by
        rw [map_mul, finAdeleEval_apply, finAdeleEval_apply],
        Units.mul_inv, map_one]
    have ha := left_ne_zero_of_mul_eq_one hmul1
    have hinv_comp : ((((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
          * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos))⁻¹ :
          (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) w
        = ((((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
            * epsUnitHom Ψ.level_ne_bot (ratUnit p p.2.pos) :
            (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) w)⁻¹ :=
      mul_left_cancel₀ ha (by rw [hmul1, mul_inv_cancel₀ ha])
    rw [Units.val_mul, ← finAdeleEval_apply, map_mul, finAdeleEval_apply, finAdeleEval_apply,
      finRatUnit_val]
    congr 1

  refine omegaUnit_eq_one_of_components R _ ?_ ?_
  · intro w
    rw [hcomp w]
    by_cases hwp : w = ratPrime p
    · subst hwp
      rw [localUnit_apply_self, epsUnitHom_apply, if_neg (by rw [hboundp]; simp),
        mul_one]
      rw [show ((pUnit p : ((ratPrime p).adicCompletion ℚ)))
          = algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (((p : ℕ) : ℚ)) from rfl,
        inv_mul_cancel₀ ((map_ne_zero _).mpr hpQ)]
      exact map_one _
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) hwp, one_mul,
        epsUnitHom_apply]
      by_cases hw : idealBound (𝓞 ℚ) Ψ.level w ≠ 1
      · rw [if_pos hw, ratUnit_val, inv_mul_cancel₀ ((map_ne_zero _).mpr hpQ)]
        exact map_one _
      · rw [if_neg hw, inv_one, one_mul]
        exact valued_natCast_prime_eq_one p hwp
  · intro w hw
    have hwp : w ≠ ratPrime p := fun h => hw (h ▸ hboundp)
    rw [hcomp w, localUnit_apply_of_ne (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) hwp, one_mul,
      epsUnitHom_apply, if_pos hw, ratUnit_val, inv_mul_cancel₀ ((map_ne_zero _).mpr hpQ)]

end RestKill
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section ProductFormula

open EisensteinWeightOne

variable {Ψ : HeckeEigensystem ℚ ℂ}

private theorem omegaUnit_finIncl_finRat (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (m : ℕ) (hm : 0 < m) :
    ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ) (finRatUnit (ratUnit m hm))) : ℂˣ) : ℂ)
      = (((m : ℕ) : ℂ))⁻¹ := by
  have hm0 : (((m : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hm.ne'
  have hmR : (0 : ℝ) < ((Units.mk0 ((m : ℝ)) (by exact_mod_cast hm.ne') : ℝˣ) : ℝ) := by
    show (0 : ℝ) < ((m : ℕ) : ℝ)
    exact_mod_cast hm
  have h0 := omegaUnit_principal R (ratUnit m hm)
  rw [principalUnit_eq_arch_mul_fin w hw m hm, map_mul] at h0
  have h2 := congrArg (fun z : ℂˣ => (z : ℂ)) h0
  simp only [Units.val_mul, Units.val_one] at h2
  rw [omegaUnit_archIdeleUnit R w hw homega _ hmR] at h2
  have h3 : (((m : ℕ) : ℂ)) * ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
      (finRatUnit (ratUnit m hm))) : ℂˣ) : ℂ) = 1 := by
    rw [← h2]
    congr 1
  exact mul_left_cancel₀ hm0 (h3.trans (mul_inv_cancel₀ hm0).symm)

private theorem omegaEps_prime (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm Ψ.level)
    (hp3 : (p : ℕ) ≠ 3) (hpex : ratPrime p ∉ R.exceptionalSet)
    (hb : Ψ.b (ratPrime p) = ((chiNegThree (p : ℕ) : ℤ) : ℂ) * (((p : ℕ) : ℂ))⁻¹) :
    ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
        (epsUnitHom Ψ.level_ne_bot (ratUnit (p : ℕ) p.2.pos))) : ℂˣ) : ℂ)
      = ((chiNegThree (p : ℕ) : ℤ) : ℂ) := by
  have hp0 : (((p : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast p.2.pos.ne'
  have h3p : ¬ (3 : ℕ) ∣ (p : ℕ) := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) p.2).mp h).symm
  have hchi0 : ((chiNegThree (p : ℕ) : ℤ) : ℂ) ≠ 0 := by
    rcases chiNegThree_eq_one_or_neg_one h3p with h | h <;> rw [h] <;> norm_num
  have hdec : finRatUnit (ratUnit (p : ℕ) p.2.pos)
      = (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
          * epsUnitHom Ψ.level_ne_bot (ratUnit (p : ℕ) p.2.pos))
        * ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
            * epsUnitHom Ψ.level_ne_bot (ratUnit (p : ℕ) p.2.pos))⁻¹
          * finRatUnit (ratUnit (p : ℕ) p.2.pos)) := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hfr := omegaUnit_finIncl_finRat R w hw homega (p : ℕ) p.2.pos
  rw [hdec, map_mul, map_mul, map_mul, map_mul] at hfr
  have hco := congrArg (fun z : ℂˣ => (z : ℂ)) (omegaUnit_rest R p hpN)
  simp only [Units.val_one] at hco
  rw [Units.val_mul, Units.val_mul, hco, mul_one] at hfr
  rw [omegaUnit_finIncl_localUnit_pUnit R p hpN hpex, hb] at hfr

  have hsq : ((chiNegThree (p : ℕ) : ℤ) : ℂ) * ((chiNegThree (p : ℕ) : ℤ) : ℂ) = 1 := by
    rcases chiNegThree_eq_one_or_neg_one h3p with h | h <;> rw [h] <;> norm_num
  have hcp0 : ((chiNegThree (p : ℕ) : ℤ) : ℂ) * ((((p : ℕ) : ℂ)))⁻¹ ≠ 0 :=
    mul_ne_zero hchi0 (inv_ne_zero hp0)
  have key : ((chiNegThree (p : ℕ) : ℤ) : ℂ) * ((((p : ℕ) : ℂ)))⁻¹
      * ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit (p : ℕ) p.2.pos))) : ℂˣ) : ℂ)
      = ((chiNegThree (p : ℕ) : ℤ) : ℂ) * ((((p : ℕ) : ℂ)))⁻¹
        * ((chiNegThree (p : ℕ) : ℤ) : ℂ) := by
    rw [hfr, show ((chiNegThree (p : ℕ) : ℤ) : ℂ) * ((((p : ℕ) : ℂ)))⁻¹
        * ((chiNegThree (p : ℕ) : ℤ) : ℂ)
      = ((chiNegThree (p : ℕ) : ℤ) : ℂ) * ((chiNegThree (p : ℕ) : ℤ) : ℂ)
        * ((((p : ℕ) : ℂ)))⁻¹ from by ring, hsq, one_mul]
  exact mul_left_cancel₀ hcp0 key

private theorem omegaEps_eq_chi (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (m : ℕ) (hm : 0 < m)
    (hgood : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
      ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
        ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
        ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) :
    ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
        (epsUnitHom Ψ.level_ne_bot (ratUnit m hm))) : ℂˣ) : ℂ)
      = ((chiNegThree m : ℤ) : ℂ) := by
  suffices H : ∀ n : ℕ, ∀ m' : ℕ, m' ≤ n → ∀ hm' : 0 < m',
      (∀ q : ℕ, ∀ hq : q.Prime, q ∣ m' →
        ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
          ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
          ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) →
      ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit m' hm'))) : ℂˣ) : ℂ)
        = ((chiNegThree m' : ℤ) : ℂ) by
    exact H m m le_rfl hm hgood
  intro n
  induction n with
  | zero => intro m' hle hpos _; omega
  | succ n ih =>
    intro m' hle hpos hgood'
    by_cases h1 : m' = 1
    · subst h1
      rw [show ratUnit 1 hpos = 1 from Units.ext (by simp), map_one, map_one, map_one,
        Units.val_one]
      show (1 : ℂ) = ((chiNegThree 1 : ℤ) : ℂ)
      rw [show chiNegThree 1 = 1 from by unfold chiNegThree; norm_num]
      norm_num
    · set q := m'.minFac with hq_def
      have hq : q.Prime := Nat.minFac_prime h1
      have hqdvd : q ∣ m' := Nat.minFac_dvd m'
      have hqpos : 0 < q := hq.pos
      have hdiv_pos : 0 < m' / q := Nat.div_pos (Nat.le_of_dvd hpos hqdvd) hqpos
      have hrec : q * (m' / q) = m' := Nat.mul_div_cancel' hqdvd
      have hdiv_le : m' / q ≤ n := by
        have hlt : m' / q < m' := Nat.div_lt_self hpos hq.one_lt
        omega
      have hsplit : ratUnit m' hpos = ratUnit q hqpos * ratUnit (m' / q) hdiv_pos := by
        refine Units.ext ?_
        show ((m' : ℕ) : ℚ) = ((q : ℕ) : ℚ) * (((m' / q : ℕ) : ℚ))
        rw [← Nat.cast_mul, hrec]
      have hgood_div : ∀ r : ℕ, ∀ hr : r.Prime, r ∣ m' / q →
          ¬ r ∣ Ideal.absNorm Ψ.level ∧ r ≠ 3
            ∧ ratPrime ⟨r, hr⟩ ∉ R.exceptionalSet
            ∧ Ψ.b (ratPrime ⟨r, hr⟩) = ((chiNegThree r : ℤ) : ℂ) * ((r : ℂ))⁻¹ :=
        fun r hr hrdvd => hgood' r hr (hrdvd.trans (Nat.div_dvd_of_dvd hqdvd))
      obtain ⟨hqN, hq3, hqex, hqb⟩ := hgood' q hq hqdvd
      have hprime := omegaEps_prime R w hw homega ⟨q, hq⟩ hqN hq3 hqex hqb
      have hih := ih (m' / q) hdiv_le hdiv_pos hgood_div
      rw [hsplit, map_mul, map_mul, map_mul, Units.val_mul, hprime, hih,
        ← Int.cast_mul, ← chiNegThree_mul, hrec]

private theorem exists_pos_rep_one_two_mod_three (N S : ℕ) (hN : N ≠ 0) (hS : S ≠ 0)
    (h3N : ¬ 3 ∣ N) (h3S : ¬ 3 ∣ S) (hco : N.Coprime S) :
    ∃ m : ℕ, 0 < m ∧ (m : ZMod N) = 1 ∧ m % 3 = 2 ∧ m.Coprime S := by
  have h3 : Nat.Prime 3 := by norm_num
  have c3S : Nat.Coprime 3 S := (Nat.Prime.coprime_iff_not_dvd h3).mpr h3S
  have cN3 : Nat.Coprime N 3 := ((Nat.Prime.coprime_iff_not_dvd h3).mpr h3N).symm
  have cN3S : N.Coprime (3 * S) := Nat.Coprime.mul_right cN3 hco
  obtain ⟨k₁, hk11, hk12⟩ := Nat.chineseRemainder c3S 2 1
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder cN3S 1 k₁
  have hpos : 0 < N * (3 * S) := by positivity
  refine ⟨k + N * (3 * S), by positivity, ?_, ?_, ?_⟩
  · have h1 : ((k + N * (3 * S) : ℕ) : ZMod N) = (k : ZMod N) := by
      push_cast; simp
    rw [h1, ZMod.natCast_eq_natCast_iff _ _ _ |>.mpr hk1]
    norm_num
  · have hd3 : (3 : ℕ) ∣ 3 * S := ⟨S, rfl⟩
    have hm3 : (k + N * (3 * S)) ≡ 2 [MOD 3] := by
      have ha : k ≡ k₁ [MOD 3] := (Nat.ModEq.of_dvd hd3) hk2
      have hb : N * (3 * S) ≡ 0 [MOD 3] := (Nat.modEq_zero_iff_dvd).mpr ⟨N * S, by ring⟩
      have hsum := ha.add hb
      simpa using hsum.trans hk11
    simpa [Nat.ModEq] using hm3
  · have hdS : S ∣ 3 * S := ⟨3, mul_comm 3 S⟩
    have hmS : (k + N * (3 * S)) ≡ 1 [MOD S] := by
      have ha : k ≡ k₁ [MOD S] := (Nat.ModEq.of_dvd hdS) hk2
      have hb : N * (3 * S) ≡ 0 [MOD S] := (Nat.modEq_zero_iff_dvd).mpr ⟨N * 3, by ring⟩
      have hsum := ha.add hb
      simpa using hsum.trans hk12
    rw [← ZMod.isUnit_iff_coprime]
    rw [ZMod.natCast_eq_natCast_iff _ _ _ |>.mpr hmS]
    simp

private theorem three_dvd_absNorm (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (hdet : ∀ q : ℕ, ∀ hq : q.Prime, ¬ q ∣ Ideal.absNorm Ψ.level → q ≠ 3 →
      ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet →
      Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) :
    3 ∣ Ideal.absNorm Ψ.level := by
  by_contra h3N
  classical
  have hN0 : Ideal.absNorm Ψ.level ≠ 0 := fun h =>
    Ψ.level_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  set Sset := ((R.exceptionalSet.image
      (fun v => Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) v)).erase 3).filter
      (fun q => ¬ q ∣ Ideal.absNorm Ψ.level) with hSset_def
  have hSfac : ∀ q ∈ Sset, Nat.Prime q := by
    intro q hqmem
    have h1 := (Finset.mem_filter.mp hqmem).1
    have h2 := (Finset.mem_erase.mp h1).2
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp h2
    exact Rat.HeightOneSpectrum.prime_natGenerator (R := 𝓞 ℚ) v
  set S := ∏ q ∈ Sset, q with hS_def
  have hS0 : S ≠ 0 := (Finset.prod_pos fun q hq => (hSfac q hq).pos).ne'
  have h3S : ¬ 3 ∣ S := by
    have h3p : Nat.Prime 3 := by norm_num
    have hco3 : Nat.Coprime 3 S :=
      Nat.Coprime.prod_right fun q hqmem =>
        (Nat.coprime_primes h3p (hSfac q hqmem)).mpr
          (fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp hqmem).1).1 h.symm)
    exact (Nat.Prime.coprime_iff_not_dvd h3p).mp hco3
  have hcoNS : (Ideal.absNorm Ψ.level).Coprime S :=
    Nat.Coprime.prod_right fun q hqmem =>
      ((Nat.Prime.coprime_iff_not_dvd (hSfac q hqmem)).mpr
        ((Finset.mem_filter.mp hqmem).2)).symm
  obtain ⟨m, hmpos, hmN, hm3, hmS⟩ :=
    exists_pos_rep_one_two_mod_three (Ideal.absNorm Ψ.level) S hN0 hS0 h3N h3S hcoNS
  have hmNco : m.Coprime (Ideal.absNorm Ψ.level) := by
    have hu : IsUnit ((m : ℕ) : ZMod (Ideal.absNorm Ψ.level)) := hmN ▸ isUnit_one
    exact (ZMod.isUnit_iff_coprime m _).mp hu
  have h3m : ¬ 3 ∣ m := by omega
  have hgood : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
      ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
        ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
        ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹ := by
    intro q hq hqm
    have hqN : ¬ q ∣ Ideal.absNorm Ψ.level := by
      intro hdvd
      have hgcd : q ∣ Nat.gcd m (Ideal.absNorm Ψ.level) := Nat.dvd_gcd hqm hdvd
      rw [hmNco] at hgcd
      exact hq.ne_one (Nat.dvd_one.mp hgcd)
    have hq3 : q ≠ 3 := fun h => h3m (h ▸ hqm)
    have hqex : ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet := by
      intro hmem
      have himg : q ∈ R.exceptionalSet.image
          (fun v => Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) v) :=
        Finset.mem_image.mpr ⟨_, hmem, by
          rw [natGenerator_ratPrime]⟩
      have hfilt : q ∈ Sset :=
        Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hq3, himg⟩, hqN⟩
      have hdvdS : q ∣ S := Finset.dvd_prod_of_mem _ hfilt
      have hgcd : q ∣ Nat.gcd m S := Nat.dvd_gcd hqm hdvdS
      rw [hmS] at hgcd
      exact hq.ne_one (Nat.dvd_one.mp hgcd)
    exact ⟨hqN, hq3, hqex, hdet q hq hqN hq3 hqex⟩
  have hchi := omegaEps_eq_chi R w hw homega m hmpos hgood
  have hval : chiNegThree m = -1 := by
    unfold chiNegThree
    rw [hm3]
    norm_num
  have hdvdZ : ((Ideal.absNorm Ψ.level : ℕ) : ℤ) ∣ (m : ℤ) - ((1 : ℕ) : ℤ) := by
    have hmod : m ≡ 1 [MOD Ideal.absNorm Ψ.level] :=
      (ZMod.natCast_eq_natCast_iff m 1 _).mp (by rw [Nat.cast_one]; exact hmN)
    exact (dvd_sub_comm).mp hmod.dvd
  have hK1 := omegaUnit_epsUnitHom_div R hmpos Nat.one_pos hmNco
    (Nat.coprime_one_left _) hdvdZ
  rw [show ratUnit 1 Nat.one_pos = 1 from Units.ext (by simp), div_one] at hK1
  have hK1c := congrArg (fun z : ℂˣ => (z : ℂ)) hK1
  simp only [Units.val_one] at hK1c
  rw [hchi, hval] at hK1c
  norm_num at hK1c

end ProductFormula
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section AuditH4

end AuditH4
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part04
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part05

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

open UpperHalfPlane CongruenceSubgroup ModularForm EisensteinWeightOne

open scoped MatrixGroups ModularForm

noncomputable section

namespace HeckeDictionary

section OmegaInfraSplice

variable {Ψ : HeckeEigensystem ℚ ℂ}

attribute [local instance] instDecEqInfinitePlaceRat

end OmegaInfraSplice
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section EpsCarrierSplice

variable {L : Ideal (𝓞 ℚ)}

end EpsCarrierSplice
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section SupplySplice

end SupplySplice
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section KappaSupplySplice

end KappaSupplySplice
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Head8Supply

private theorem denom_inv_stabilizer (κ : GL (Fin 2) ℝ)
    (hI : κ • I = I) (hdet : (0 : ℝ) < ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det) :
    denom κ⁻¹ Complex.I = (denom κ Complex.I)⁻¹ := by
  obtain ⟨h1, h2⟩ := stabilizer_entries κ hI hdet
  have hdet2 := det_stabilizer κ hI hdet
  have hu : ((κ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((κ : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ := by
    simp
  have hdetne : ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := ne_of_gt hdet
  have hinv10 : ((κ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0
      = -(((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 / ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det) := by
    rw [hu, Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [Ring.inverse_eq_inv]
    ring
  have hinv11 : ((κ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1
      = ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 / ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det := by
    rw [hu, Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [Ring.inverse_eq_inv]
    ring
  have hdne : denom κ Complex.I ≠ 0 :=
    UpperHalfPlane.coe_I ▸ denom_ne_zero κ UpperHalfPlane.I
  apply eq_inv_of_mul_eq_one_right
  simp only [denom, hinv10, hinv11]
  rw [h1]
  push_cast [hdet2]
  have hI2 : (Complex.I) ^ 2 = -1 := Complex.I_sq
  have hne : (((κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 : ℂ) ^ 2
      + (((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 : ℂ) ^ 2 ≠ 0 := by
    have h := hdet2 ▸ hdetne
    exact_mod_cast h
  have hc1 : ((((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 : ℝ) : ℂ)
      = ((((κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h1.symm
  field_simp
  linear_combination (-((((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 : ℝ) : ℂ) ^ 2) * hI2
    + (((((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 : ℝ) : ℂ)
      + ((((κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 : ℝ) : ℂ)) * hc1

private def realOf (γ : GL (Fin 2) ℚ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) γ

private theorem globalPoints_decomp (w : InfinitePlace ℚ) (hw : w.IsReal) (γ : GL (Fin 2) ℚ) :
    globalPoints (𝓞 ℚ) ℚ γ
      = archAt w hw (realOf γ)
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) := by
  apply glpair_ext
  · rw [map_mul, AdelicDock.glArch_finEmbed, mul_one,
      show archAt w hw (realOf γ) = (adelicArchGLIncl ℚ) (archGLIncl ℚ w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (realOf γ))) from rfl,
      glArch_adelicArchGLIncl]
    ext i j
    funext w'
    rcases Subsingleton.elim w w' with rfl
    show AdelicLevel.adeleArch (𝓞 ℚ) ℚ
        ((globalPoints (𝓞 ℚ) ℚ γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) w
      = (archMatrixUpdate ℚ w
          ((Matrix.GeneralLinearGroup.map
            ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
            (realOf γ) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) i j w
    rw [archMatrixUpdate_apply_self]
    have h1 : ((globalPoints (𝓞 ℚ) ℚ γ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j
        = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl
    have h2 : ((Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (realOf γ) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
        = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (algebraMap ℚ ℝ ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)) := rfl
    rw [h1, h2]
    exact congrArg (fun f : ℚ →+* w.Completion => f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j))
      (by apply RingHom.ext_rat :
        ((Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) w).comp
          ((RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
            (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))))
        = ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom).comp
            (algebraMap ℚ ℝ))
  · rw [map_mul, AdelicDock.glFin_finEmbed,
      show archAt w hw (realOf γ) = (adelicArchGLIncl ℚ) (archGLIncl ℚ w
        (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (realOf γ))) from rfl,
      glFin_adelicArchGLIncl, one_mul]

private theorem iwasawaSec_eq_iwasawaSectionGL (z : UpperHalfPlane) :
    iwasawaSec z = iwasawaSectionGL z := rfl

private theorem archAt_finEmbed_comm (w : InfinitePlace ℚ) (hw : w.IsReal) (M : GL (Fin 2) ℝ)
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    archAt w hw M * AdelicDock.finEmbed (𝓞 ℚ) ℚ h
      = AdelicDock.finEmbed (𝓞 ℚ) ℚ h * archAt w hw M := by
  rw [show archAt w hw M = (adelicArchGLIncl ℚ) (archGLIncl ℚ w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom) M)) from rfl]
  exact archIncl_finEmbed_comm _ _

end Head8Supply
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section PeelSupply

variable {L : Ideal (𝓞 ℚ)}

variable {L : Ideal (𝓞 ℚ)}

private theorem diagOne_coe (a : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((diagOne a : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.diagonal ![(a : FiniteAdeleRing (𝓞 ℚ) ℚ), 1] :=
  Matrix.ext fun i j => diagOne_coe_apply a i j

private theorem scalar_inv_mul_diagOne_coe (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) e⁻¹ * diagOne e :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.diagonal ![1, ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)] := by
  rw [Units.val_mul, diagOne_coe,
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2) e⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.scalar (Fin 2) ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      from rfl]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Units.inv_mul,
      Units.mul_inv]

private theorem scalar_mul_diagOne_inv_coe (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) e * diagOne e⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.diagonal ![1, ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)] := by
  rw [Units.val_mul, diagOne_coe,
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2) e :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.scalar (Fin 2) ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      from rfl]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Units.inv_mul,
      Units.mul_inv]

private theorem peel_inv_coe (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 2) e⁻¹ * diagOne e)⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.diagonal ![1, ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)] := by
  rw [mul_inv_rev, ← map_inv, ← map_inv, inv_inv, Units.val_mul, diagOne_coe,
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2) e :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.scalar (Fin 2) ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      from rfl]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Units.inv_mul,
      Units.mul_inv]

private theorem peel_identity (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (γf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    γf = (Matrix.GeneralLinearGroup.scalar (Fin 2) e * diagOne e⁻¹)
          * ((Matrix.GeneralLinearGroup.scalar (Fin 2) e⁻¹ * diagOne e) * γf) := by
  have hone : (Matrix.GeneralLinearGroup.scalar (Fin 2) e * diagOne e⁻¹)
      * (Matrix.GeneralLinearGroup.scalar (Fin 2) e⁻¹ * diagOne e) = 1 := by
    apply Units.ext
    rw [Units.val_mul, scalar_mul_diagOne_inv_coe e, scalar_inv_mul_diagOne_coe e,
      Matrix.diagonal_mul_diagonal, Units.val_one]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Units.mul_inv]
  rw [← mul_assoc, hone, one_mul]

private theorem diagOne_mem_finiteLevelOne (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (he : ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hei : ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    diagOne e ∈ finiteLevelOne (𝓞 ℚ) ℚ L := by
  rw [mem_finiteLevelOne_iff]
  constructor
  · rw [diagOne_coe]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, if_true, if_false, Fin.zero_eta, Fin.mk_one, ne_eq,
          reduceCtorEq, ite_true, ite_false] <;>
        first
          | exact he
          | exact one_mem_integralFiniteAdeles
          | exact zero_mem_integralFiniteAdeles
          | simp_all
    · simpa [Matrix.diagonal_apply] using zero_mem_idealBall L
    · simpa [Matrix.diagonal_apply] using zero_mem_idealBall L
  · rw [← map_inv, diagOne_coe]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, if_true, if_false, Fin.zero_eta, Fin.mk_one, ne_eq,
          reduceCtorEq, ite_true, ite_false] <;>
        first
          | exact hei
          | exact one_mem_integralFiniteAdeles
          | exact zero_mem_integralFiniteAdeles
          | simp_all
    · simpa [Matrix.diagonal_apply] using zero_mem_idealBall L
    · simpa [Matrix.diagonal_apply] using zero_mem_idealBall L

private theorem peel_mem_finiteLevelOne (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (u γf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (hcoe : ((u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.diagonal ![1, ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)]
        * ((γf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (hcoeinv : ((u⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = ((γf⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        * Matrix.diagonal ![1, ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)])
    (hint : ∀ i j, ((γf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hintinv : ∀ i j, ((γf⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hei : ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (he : ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hc : ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
        * ((γf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 ∈ idealBall (𝓞 ℚ) ℚ L)
    (hd : ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
        * ((γf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1 ∈ idealBall (𝓞 ℚ) ℚ L)
    (hcinv : ((γf⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 ∈ idealBall (𝓞 ℚ) ℚ L)
    (ha : ((γf⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        * ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) - 1
        ∈ idealBall (𝓞 ℚ) ℚ L) :
    u ∈ finiteLevelOne (𝓞 ℚ) ℚ L := by
  rw [mem_finiteLevelOne_iff]
  constructor
  · rw [hcoe]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j
      · rw [Matrix.diagonal_mul]
        simpa only [Matrix.cons_val_zero, Fin.zero_eta, one_mul] using hint 0 0
      · rw [Matrix.diagonal_mul]
        simp only [Matrix.cons_val_zero, Fin.zero_eta, one_mul]
        exact hint 0 1
      · rw [Matrix.diagonal_mul]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Fin.mk_one]
        exact mul_mem_integralFiniteAdeles hei (hint 1 0)
      · rw [Matrix.diagonal_mul]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Fin.mk_one]
        exact mul_mem_integralFiniteAdeles hei (hint 1 1)
    · rw [Matrix.diagonal_mul]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
      exact hc
    · rw [Matrix.diagonal_mul]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
      exact hd
  · rw [hcoeinv]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j
      · rw [Matrix.mul_diagonal]
        simpa only [Matrix.cons_val_zero, Fin.zero_eta, mul_one] using hintinv 0 0
      · rw [Matrix.mul_diagonal]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Fin.mk_one]
        exact mul_mem_integralFiniteAdeles (hintinv 0 1) he
      · rw [Matrix.mul_diagonal]
        simp only [Matrix.cons_val_zero, Fin.zero_eta, mul_one]
        exact hintinv 1 0
      · rw [Matrix.mul_diagonal]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Fin.mk_one]
        exact mul_mem_integralFiniteAdeles (hintinv 1 1) he
    · rw [Matrix.mul_diagonal]
      simpa only [Matrix.cons_val_zero, Fin.zero_eta, mul_one] using hcinv
    · rw [Matrix.mul_diagonal]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Fin.mk_one]
      exact ha

private theorem finEmbed_scalar_eq_centralScalar (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) e)
      = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) e) := by
  apply glpair_ext
  · rw [AdelicDock.glArch_finEmbed]
    symm
    ext i j
    rw [glArch_apply]
    show adeleArch (𝓞 ℚ) ℚ (Matrix.diagonal
      (fun _ => (finIncl (𝓞 ℚ) ℚ (e : FiniteAdeleRing (𝓞 ℚ) ℚ) : H4Ad)) i j)
      = ((1 : GL (Fin 2) (InfiniteAdeleRing ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
      have h1 : adeleArch (𝓞 ℚ) ℚ (finIncl (𝓞 ℚ) ℚ (e : FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 := rfl
      rw [h1, Units.val_one, Matrix.one_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero, Units.val_one, Matrix.one_apply_ne h]
  · rw [AdelicDock.glFin_finEmbed]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [glFin_centralScalar_entry,
      show ((Matrix.GeneralLinearGroup.scalar (Fin 2) e :
          GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        = Matrix.scalar (Fin 2) ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ) from rfl]
    by_cases h : i = j
    · subst h
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, h]

private theorem epsUnitHom_ratUnit_mem_integral {L : Ideal (𝓞 ℚ)} (hL : L ≠ ⊥) {m : ℕ}
    (hm : 0 < m) (hcop : m.Coprime (Ideal.absNorm L)) :
    ((epsUnitHom hL (ratUnit m hm) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro v
  show ((epsUnitHom hL (ratUnit m hm) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    FiniteAdeleRing (𝓞 ℚ) ℚ) v ∈ v.adicCompletionIntegers ℚ
  rw [epsUnitHom_apply]
  split_ifs with h
  · rw [ratUnit_val]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [valued_natCast_eq_one hL h hcop]
  · exact one_mem _

private theorem epsUnitHom_ratUnit_inv_mem_integral {L : Ideal (𝓞 ℚ)} (hL : L ≠ ⊥) {m : ℕ}
    (hm : 0 < m) (hcop : m.Coprime (Ideal.absNorm L)) :
    (((epsUnitHom hL (ratUnit m hm))⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  rw [← map_inv]
  intro v
  show ((epsUnitHom hL ((ratUnit m hm)⁻¹) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    FiniteAdeleRing (𝓞 ℚ) ℚ) v ∈ v.adicCompletionIntegers ℚ
  rw [epsUnitHom_apply]
  split_ifs with h
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (((ratUnit m hm)⁻¹ : ℚˣ) : ℚ) = ((m : ℚ))⁻¹ from by
        rw [← ratUnit_val m hm]; rfl,
      map_inv₀, map_inv₀, valued_natCast_eq_one hL h hcop]
    norm_num
  · exact one_mem _

private theorem epsUnitHom_ratUnit_sub_natCast_mem_idealBall {L : Ideal (𝓞 ℚ)} (hL : L ≠ ⊥)
    {m : ℕ} (hm : 0 < m) :
    ((epsUnitHom hL (ratUnit m hm) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ)
      - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((m : ℚ))
      ∈ idealBall (𝓞 ℚ) ℚ L := by
  intro v
  show Valued.v (((epsUnitHom hL (ratUnit m hm) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v
      - algebraMap ℚ (v.adicCompletion ℚ) ((m : ℚ))) ≤ idealBound (𝓞 ℚ) L v
  rw [epsUnitHom_apply]
  split_ifs with h
  · rw [ratUnit_val, sub_self, map_zero]
    exact zero_le'
  · rw [not_not] at h
    rw [h]
    have h1 : (1 : v.adicCompletion ℚ) - algebraMap ℚ (v.adicCompletion ℚ) ((m : ℚ))
        = algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ ((1 : 𝓞 ℚ) - (m : 𝓞 ℚ))) := by
      rw [map_sub, map_sub, map_one, map_one]
      norm_num
    rw [h1, valued_algebraMap]
    exact (v.intValuation_le_one _)

end PeelSupply
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section TransportHeads

variable {Ψ : HeckeEigensystem ℚ ℂ}

private theorem glFin_globalPoints_mapGL_integral (δ : SL(2, ℤ)) (i j : Fin 2) :
    ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ))) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    rw [glFin_globalPoints_apply]
    have h1 : ((Matrix.SpecialLinearGroup.mapGL ℚ δ : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ) i j
        = algebraMap ℤ ℚ ((δ : Matrix (Fin 2) (Fin 2) ℤ) i j) := by
      rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
      rfl
    have h2 : algebraMap ℤ ℚ ((δ : Matrix (Fin 2) (Fin 2) ℤ) i j)
        = algebraMap (𝓞 ℚ) ℚ ((((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : 𝓞 ℚ)) := by
      simp only [map_intCast, eq_intCast]
    rw [h1, h2]
    exact algebraMap_mem_integralFiniteAdeles _

private theorem glFin_globalPoints_mapGL_inv (δ : SL(2, ℤ)) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ)))⁻¹
      = glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ⁻¹)) := by
  rw [← map_inv, ← map_inv, ← map_inv]

private theorem slGammaFinLift_mem (γ : SL(2, ℤ)) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ))
      ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨glFin_globalPoints_mapGL_integral γ, ?_⟩
  intro i j
  rw [glFin_globalPoints_mapGL_inv]
  exact glFin_globalPoints_mapGL_integral γ⁻¹ i j

private noncomputable def slGammaFinLift (γ : SL(2, ℤ)) : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ) :=
  ⟨glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)),
   slGammaFinLift_mem γ⟩

@[scoped simp] private theorem slGammaFinLift_coe (γ : SL(2, ℤ)) :
    ((slGammaFinLift γ : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)) := rfl

private noncomputable def descentF (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) : ℍ → ℂ :=
  fun z => descentFn w hw R.toFun 1 (z : ℂ)

private theorem exists_pos_rep_mod_coprime (N B : ℕ) (hN : N ≠ 0) (h3N : 3 ∣ N) (hB : B ≠ 0)
    (d : ℤ) (hd : IsUnit (d : ZMod N)) :
    ∃ m : ℕ, 0 < m ∧ ((m : ℤ) : ZMod N) = (d : ZMod N) ∧ m.Coprime B ∧
      ((m : ℤ) : ZMod 3) = (d : ZMod 3) := by
  classical
  haveI : NeZero N := ⟨hN⟩

  set B₀ : ℕ := ∏ p ∈ B.primeFactors.filter (fun p => ¬ p ∣ N), p with hB₀_def
  have hB₀_pos : 0 < B₀ := Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hco : N.Coprime B₀ := Nat.Coprime.prod_right fun p hp =>
    (((Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).coprime_iff_not_dvd).mpr
      (Finset.mem_filter.mp hp).2).symm

  set d₀ : ℕ := (d : ZMod N).val with hd₀_def
  have hd₀_cast : ((d₀ : ℕ) : ZMod N) = (d : ZMod N) := ZMod.natCast_rightInverse (d : ZMod N)

  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hco d₀ 1
  set m : ℕ := k + N * B₀ with hm_def
  have hmN : m ≡ d₀ [MOD N] := by
    rw [hm_def]
    have hb : (N * B₀) ≡ 0 [MOD N] := (Nat.modEq_zero_iff_dvd).mpr ⟨B₀, rfl⟩
    simpa using (hk1.add hb)

  have hmodN : ((m : ℤ) : ZMod N) = (d : ZMod N) := by
    have h2 : ((m : ℕ) : ZMod N) = ((d₀ : ℕ) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmN
    push_cast at h2 ⊢
    rw [h2, hd₀_cast]

  have hmod3 : ((m : ℤ) : ZMod 3) = (d : ZMod 3) := by
    have hz : (m : ℤ) ≡ d [ZMOD (N : ℤ)] := (ZMod.intCast_eq_intCast_iff _ _ _).mp hmodN
    have h3 : (m : ℤ) ≡ d [ZMOD ((3 : ℕ) : ℤ)] :=
      hz.of_dvd (Int.natCast_dvd_natCast.mpr h3N)
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (by exact_mod_cast h3)

  have hcop : m.Coprime B := by
    by_contra hcop
    obtain ⟨p, hp, hpm, hpB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    by_cases hpN : p ∣ N
    ·
      have hmd : m ≡ d₀ [MOD p] := Nat.ModEq.of_dvd hpN hmN
      have hpd₀ : p ∣ d₀ := by
        have h0 : (0 : ℕ) ≡ d₀ [MOD p] :=
          ((Nat.modEq_zero_iff_dvd).mpr hpm).symm.trans hmd
        have := (Nat.modEq_zero_iff_dvd).mp h0.symm
        exact this
      have hunit : d₀.Coprime N := by
        rw [← ZMod.isUnit_iff_coprime, hd₀_cast]
        exact hd
      have hg : p ∣ Nat.gcd d₀ N := Nat.dvd_gcd hpd₀ hpN
      rw [Nat.Coprime] at hunit
      rw [hunit] at hg
      exact hp.one_lt.ne' (Nat.dvd_one.mp hg)
    ·
      have hpB₀ : p ∣ B₀ := Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hp, hpB, hB⟩, hpN⟩)
      have hm1 : m ≡ 1 [MOD p] := by
        have ha : k ≡ 1 [MOD p] := Nat.ModEq.of_dvd hpB₀ hk2
        have hb : (N * B₀) ≡ 0 [MOD p] :=
          (Nat.modEq_zero_iff_dvd).mpr (Dvd.dvd.mul_left hpB₀ N)
        simpa using (ha.add hb)
      have h01 : (0 : ℕ) ≡ 1 [MOD p] :=
        ((Nat.modEq_zero_iff_dvd).mpr hpm).symm.trans hm1
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.modEq_zero_iff_dvd).mp h01.symm))
  exact ⟨m, by positivity, hmodN, hcop, hmod3⟩

private theorem toFun_mul_archAt_stabilizer_exact (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    {κ : GL (Fin 2) ℝ} (hI : κ • I = I)
    (hdet : (0 : ℝ) < ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det)
    (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    R.toFun (X * archAt w hw κ)
      = (starRingEnd ℂ) (denom κ Complex.I) * R.toFun X := by
  obtain ⟨h1, h2⟩ := stabilizer_entries κ hI hdet
  have hdet2 := det_stabilizer κ hI hdet
  set a := ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 with ha
  set c := ((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 with hc
  set r := Real.sqrt (a ^ 2 + c ^ 2) with hr
  have hsumpos : (0:ℝ) < a ^ 2 + c ^ 2 := by
    rw [← hdet2]; exact hdet
  have hrpos : (0:ℝ) < r := Real.sqrt_pos.mpr hsumpos
  have hrne : r ≠ 0 := hrpos.ne'
  have hr2 : a ^ 2 + c ^ 2 = r ^ 2 := (Real.sq_sqrt hsumpos.le).symm
  have hrotdet : (!![a / r, -(c / r); c / r, a / r]).det ≠ 0 := by
    have hd1 : (a / r) * (a / r) - (-(c / r)) * (c / r) = 1 := by
      field_simp
      nlinarith [hr2]
    simp [Matrix.det_fin_two_of]
    nlinarith [hd1]
  set rot := Matrix.GeneralLinearGroup.mkOfDetNeZero !![a / r, -(c / r); c / r, a / r] hrotdet
    with hrot
  have hrotmem : rot ∈ rowIsometrySubgroup₀ ℝ := rot_mem_rowIsometrySubgroup₀ a c r hrpos hr2
  have hscalarlit : (Matrix.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) ℝ)
      * !![a / r, -(c / r); c / r, a / r]
      = !![r * (a / r), r * (-(c / r)); r * (c / r), r * (a / r)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hκdecomp : κ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne) * rot := by
    apply Units.ext
    rw [Units.val_mul,
      show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne) : GL (Fin 2) ℝ)
          : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) r from rfl,
      show ((rot : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          = !![a / r, -(c / r); c / r, a / r] from rfl,
      hscalarlit]
    have e1 : r * (a / r) = a := by field_simp
    have e2 : r * (-(c / r)) = -c := by field_simp
    have e3 : r * (c / r) = c := by field_simp
    rw [e1, e2, e3]
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha.symm
    · exact h2
    · exact hc.symm
    · exact h1.symm
  have hrotarch : archAt w hw rot
      = adelicArchGLInclAt ℚ w
          ((rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
            (norm_ringEquivRealOfIsReal_symm hw) ⟨rot, hrotmem⟩ : rowIsometrySubgroup₀ w.Completion)
            : GL (Fin 2) w.Completion) := by
    rw [coe_rowIsometrySubgroup₀Map_symm]
    rfl
  have hval : ((r : ℝ) : ℂ)
      * ((archWeightOneAt hw
          (rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
            (norm_ringEquivRealOfIsReal_symm hw) ⟨rot, hrotmem⟩) : ℂˣ) : ℂ)
      = (starRingEnd ℂ) (denom κ Complex.I) := by
    rw [archWeightOneAt_transported]
    have hχ : ((archWeightOneℝ ⟨rot, hrotmem⟩ : ℂˣ) : ℂ)
        = ⟨a / r, -(c / r)⟩ := rfl
    rw [hχ]
    have hd : denom κ Complex.I = (c : ℂ) * Complex.I + (a : ℂ) := by
      show (((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 : ℂ) * Complex.I
          + (((κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 : ℂ) = _
      rw [← hc, ← h1]
    rw [hd]
    apply Complex.ext <;>
      simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      field_simp
  calc R.toFun (X * archAt w hw κ)
      = R.toFun (X * (archAt w hw (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne))
          * archAt w hw rot)) := by
        rw [← map_mul (archAt w hw)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne)) rot, ← hκdecomp]
    _ = R.toFun (centralScalar (𝓞 ℚ) ℚ (archIdeleUnit w hw (Units.mk0 r hrne))
          * (X * archAt w hw rot)) := by
        have hscalar : archAt w hw
              (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrne))
            = centralScalar (𝓞 ℚ) ℚ (archIdeleUnit w hw (Units.mk0 r hrne)) :=
          (centralScalar_archIdeleUnit w hw (Units.mk0 r hrne)).symm
        rw [hscalar, ← mul_assoc,
          ← centralScalar_mul_comm (archIdeleUnit w hw (Units.mk0 r hrne)) X, mul_assoc]
    _ = ((r : ℝ) : ℂ) * R.toFun (X * archAt w hw rot) := by
        rw [centralScalar_archIdeleUnit]
        exact homega (Units.mk0 r hrne) hrpos (X * archAt w hw rot)
    _ = ((r : ℝ) : ℂ) * ((((archWeightOneAt hw
          (rowIsometrySubgroup₀Map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
            (norm_ringEquivRealOfIsReal_symm hw) ⟨rot, hrotmem⟩) : ℂˣ) : ℂ)) * R.toFun X) := by
        rw [hrotarch, harch _ X]
    _ = (starRingEnd ℂ) (denom κ Complex.I) * R.toFun X := by
        rw [← mul_assoc, hval]

private theorem descentFn_smul (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    descentFn w hw R.toFun 1 ((((γ : GL (Fin 2) ℝ)) • z : UpperHalfPlane) : ℂ)
      = UpperHalfPlane.denom ((γ : GL (Fin 2) ℝ)) (z : ℂ)
        * descentFn w hw R.toFun (slGammaFinLift γ⁻¹) (z : ℂ) := by
  set γQ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hγQ
  set γR : GL (Fin 2) ℝ := (γ : GL (Fin 2) ℝ) with hγR
  set d : ℂ := UpperHalfPlane.denom γR (z : ℂ) with hddef

  have hγRreal : realOf γQ = γR := by
    rw [hγQ, hγR]
    show Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ γ)
        = (γ : GL (Fin 2) ℝ)
    exact Matrix.SpecialLinearGroup.map_mapGL γ

  have hdetγ : ((γR : Matrix (Fin 2) (Fin 2) ℝ)).det = 1 := by
    rw [hγR, show (γ : GL (Fin 2) ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ γ from rfl,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    exact Matrix.SpecialLinearGroup.det_coe _
  have hdetγpos : (0 : ℝ) < ((γR : Matrix (Fin 2) (Fin 2) ℝ)).det := by
    rw [hdetγ]; norm_num
  have hdne : d ≠ 0 := denom_ne_zero _ z

  set κ : GL (Fin 2) ℝ := kappa γR z with hκdef
  have hκI : κ • I = I := kappa_smul_I _ z
  have hκdet : (0 : ℝ) < ((κ : Matrix (Fin 2) (Fin 2) ℝ)).det := by
    rw [hκdef, det_kappa _ z hdetγpos]
    exact Complex.normSq_pos.mpr hdne
  have hκinvI : κ⁻¹ • I = I := by rw [inv_smul_eq_iff, hκI]
  have hκinvdet : (0 : ℝ) < (((κ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det := by
    have hu : ((κ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = ((κ : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ := by simp
    rw [hu, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_pos.mpr hκdet

  have hsec : iwasawaSec (γR • z) = γR * iwasawaSec z * κ⁻¹ := by
    rw [hκdef]
    exact eq_mul_inv_iff_mul_eq.mpr (mul_iwasawaSec_eq γR z).symm

  have hlift : ((slGammaFinLift γ⁻¹ : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ)) :
      GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γQ))⁻¹ := by
    rw [slGammaFinLift_coe, hγQ, ← map_inv, ← map_inv, ← map_inv]
  have hone : AdelicDock.finEmbed (𝓞 ℚ) ℚ
      ((1 : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    rw [OneMemClass.coe_one, map_one]

  have hofc : UpperHalfPlane.ofComplex (((γR • z : UpperHalfPlane)) : ℂ) = γR • z :=
    UpperHalfPlane.ofComplex_apply _
  have hofz : UpperHalfPlane.ofComplex ((z : UpperHalfPlane) : ℂ) = z :=
    UpperHalfPlane.ofComplex_apply _
  have harg : adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL (UpperHalfPlane.ofComplex (((γR • z : UpperHalfPlane)) : ℂ))))
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ
          ((1 : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = globalPoints (𝓞 ℚ) ℚ γQ
        * ((archAt w hw (iwasawaSec z)
            * AdelicDock.finEmbed (𝓞 ℚ) ℚ ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γQ))⁻¹))
          * archAt w hw κ⁻¹) := by
    rw [hone, mul_one, hofc,
      show adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (iwasawaSectionGL (γR • z))) = archAt w hw (iwasawaSectionGL (γR • z)) from rfl,
      ← iwasawaSec_eq_iwasawaSectionGL, hsec, map_mul, map_mul]
    rw [← hγRreal,
      show archAt w hw (realOf γQ)
          = globalPoints (𝓞 ℚ) ℚ γQ
            * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γQ)))⁻¹ from by
        rw [eq_mul_inv_iff_mul_eq]
        exact (globalPoints_decomp w hw γQ).symm,
      ← map_inv]
    rw [show archAt w hw (iwasawaSec z)
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γQ))⁻¹)
        = AdelicDock.finEmbed (𝓞 ℚ) ℚ ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γQ))⁻¹)
          * archAt w hw (iwasawaSec z) from
      archAt_finEmbed_comm w hw (iwasawaSec z) _]
    group

  simp only [descentFn]
  rw [harg]
  rw [R.left_invariant γQ]
  rw [toFun_mul_archAt_stabilizer_exact R w hw harch homega hκinvI hκinvdet]
  rw [hκdef, denom_inv_stabilizer _ (kappa_smul_I _ z) hκdet, denom_kappa]
  rw [hofz, ← iwasawaSec_eq_iwasawaSectionGL,
    show adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSec z)) = archAt w hw (iwasawaSec z) from rfl,
    hlift]

  have him : ((γR • z : UpperHalfPlane) : ℂ).im = z.im / Complex.normSq d := by
    rw [UpperHalfPlane.coe_im, im_smul_eq_div_normSq,
      show (↑(Matrix.GeneralLinearGroup.det γR) : ℝ)
          = ((γR : Matrix (Fin 2) (Fin 2) ℝ)).det from rfl,
      hdetγ, hddef]
    simp
  have hnsq : ((Complex.normSq d : ℝ) : ℂ) = d * (starRingEnd ℂ) d := by
    rw [Complex.normSq_eq_conj_mul_self]; ring
  have hcdne : (starRingEnd ℂ) d ≠ 0 := by
    simpa using hdne
  have himcne : ((z.im : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast z.im_ne_zero
  rw [him, map_inv₀, Complex.ofReal_div, hnsq]
  simp only [UpperHalfPlane.coe_im]
  field_simp
  ring

private theorem slash_descentF_eq (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (γ : SL(2, ℤ)) :
    (descentF R w hw) ∣[(1 : ℤ)] γ
      = fun z : ℍ => descentFn w hw R.toFun (slGammaFinLift γ⁻¹) (z : ℂ) := by
  have hsmul := descentFn_smul R w hw harch homega γ
  funext z
  rw [ModularForm.SL_slash_apply, zpow_neg, zpow_one]
  have hact : (γ • z : UpperHalfPlane) = (γ : GL (Fin 2) ℝ) • z := rfl
  have hdne : UpperHalfPlane.denom ((γ : GL (Fin 2) ℝ)) (z : ℂ) ≠ 0 := denom_ne_zero _ z
  rw [show descentF R w hw (γ • z)
      = descentFn w hw R.toFun 1 ((((γ : GL (Fin 2) ℝ)) • z : UpperHalfPlane) : ℂ) from by
    rw [descentF, hact],
    hsmul z]
  field_simp

private theorem descentFn_slGammaFinLift_inv_eq (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hepsval : ∀ (m : ℕ) (hm : 0 < m),
      (∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
        ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
          ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
          ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) →
      ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit m hm))) : ℂˣ) : ℂ)
        = ((chiNegThree m : ℤ) : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (Ideal.absNorm Ψ.level))
    (m : ℕ) (hm : 0 < m)
    (hgood : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
      ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
        ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
        ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹)
    (hmd : ((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) ≡ (m : ℤ) [ZMOD (Ideal.absNorm Ψ.level)]) :
    descentFn w hw R.toFun (slGammaFinLift γ⁻¹)
      = fun z => ((chiNegThree m : ℤ) : ℂ) * descentFn w hw R.toFun 1 z := by
  classical
  funext zc
  set δ : SL(2, ℤ) := γ⁻¹ with hδdef
  set e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := epsUnitHom Ψ.level_ne_bot (ratUnit m hm) with hedef
  set γf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ)) with hγfdef

  have hcop : m.Coprime (Ideal.absNorm Ψ.level) := by
    by_contra hc
    obtain ⟨p, hp, hpm, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact (hgood p hp hpm).1 hpN

  have hδmem : δ ∈ Gamma0 (Ideal.absNorm Ψ.level) := by
    rw [hδdef]
    exact (Gamma0 (Ideal.absNorm Ψ.level)).inv_mem hγ
  have hγc : ((Ideal.absNorm Ψ.level : ℕ) : ℤ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    have h := CongruenceSubgroup.Gamma0_mem.mp hγ
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast h)
  have hδc : ((Ideal.absNorm Ψ.level : ℕ) : ℤ) ∣ ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    have h := CongruenceSubgroup.Gamma0_mem.mp hδmem
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast h)
  have hδd : ((Ideal.absNorm Ψ.level : ℕ) : ℤ)
      ∣ ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - (m : ℤ)) := by
    have h := (Int.modEq_iff_dvd.mp hmd)
    have h2 := dvd_neg.mpr h
    rw [neg_sub] at h2
    exact_mod_cast h2
  have hδ01 : ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) = -((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
    rw [hδdef]
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hδ11 : ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) := by
    rw [hδdef]
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hdet1 : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
      + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = 1 := by
    rw [hδ01, hδ11]
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet
  have hγdm : ((Ideal.absNorm Ψ.level : ℕ) : ℤ)
      ∣ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * (m : ℤ) - 1) := by
    have hsplit : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * (m : ℤ) - 1
        = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)
            * ((m : ℤ) - ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1))
          - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
      linear_combination hdet1
    rw [hsplit]
    refine dvd_sub (Dvd.dvd.mul_left ?_ _) (Dvd.dvd.mul_right hγc _)
    have h2 := dvd_neg.mpr hδd
    rwa [neg_sub] at h2

  have hentry : ∀ (σ : SL(2, ℤ)) (i j : Fin 2),
      ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ σ))) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
          ((((σ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℚ)) := by
    intro σ i j
    rw [glFin_globalPoints_apply]
    congr 1

  have hball_of_dvd : ∀ x : ℤ, (((Ideal.absNorm Ψ.level : ℕ) : ℤ)) ∣ x →
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((x : ℚ)) ∈ idealBall (𝓞 ℚ) ℚ Ψ.level := by
    intro x hx
    have hmem : ((x : ℤ) : 𝓞 ℚ) ∈ Ψ.level := by
      obtain ⟨k, hk⟩ := hx
      rw [hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (by exact_mod_cast Ideal.absNorm_mem Ψ.level)
    have h := algebraMap_mem_idealBall_of_mem hmem
    rwa [show algebraMap (𝓞 ℚ) ℚ ((x : ℤ) : 𝓞 ℚ) = ((x : ℤ) : ℚ) from map_intCast _ x] at h

  have hint : ∀ i j, (γf : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro i j
    rw [hγfdef]
    exact glFin_globalPoints_mapGL_integral δ i j
  have hγfinv : γf⁻¹
      = glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ⁻¹)) := by
    rw [hγfdef]
    exact glFin_globalPoints_mapGL_inv δ
  have hintinv : ∀ i j, ((γf⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro i j
    rw [hγfinv]
    exact glFin_globalPoints_mapGL_integral δ⁻¹ i j
  have he : ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    rw [hedef]
    exact epsUnitHom_ratUnit_mem_integral Ψ.level_ne_bot hm hcop
  have hei : ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    rw [hedef]
    exact epsUnitHom_ratUnit_inv_mem_integral Ψ.level_ne_bot hm hcop
  have hesub : ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((m : ℚ)) ∈ idealBall (𝓞 ℚ) ℚ Ψ.level := by
    rw [hedef]
    exact epsUnitHom_ratUnit_sub_natCast_mem_idealBall Ψ.level_ne_bot hm
  have hee : ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      * ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := Units.inv_mul e
  have hc : ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      * ((γf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 ∈ idealBall (𝓞 ℚ) ℚ Ψ.level := by
    rw [hγfdef, hentry δ 1 0]
    exact mul_mem_idealBall_left hei (hball_of_dvd _ hδc)
  have hd : ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
      * ((γf : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1
      ∈ idealBall (𝓞 ℚ) ℚ Ψ.level := by
    rw [hγfdef, hentry δ 1 1]
    have hsplit : ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
        * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
            ((((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ)) - 1
        = ((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
                ((((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ))
              - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((m : ℚ)))
          + (-(((e⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
              * (((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
                - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((m : ℚ))))) := by
      linear_combination hee
    rw [hsplit]
    refine add_mem_idealBall (mul_mem_idealBall_left hei ?_) (neg_mem_idealBall
      (mul_mem_idealBall_left hei hesub))
    rw [← map_sub,
      show ((((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ)) - ((m : ℚ))
        = (((((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) - (m : ℤ)) : ℤ) : ℚ) from by push_cast; ring]
    exact hball_of_dvd _ hδd
  have hcinv : ((γf⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 ∈ idealBall (𝓞 ℚ) ℚ Ψ.level := by
    rw [hγfinv, hentry δ⁻¹ 1 0]
    refine hball_of_dvd _ ?_
    rw [hδdef, inv_inv]
    exact hγc
  have ha : ((γf⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      * ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) - 1
      ∈ idealBall (𝓞 ℚ) ℚ Ψ.level := by
    rw [hγfinv, hentry δ⁻¹ 1 1]
    have hδinv : (δ⁻¹ : SL(2, ℤ)) = γ := by rw [hδdef, inv_inv]
    rw [hδinv]
    have hsplit2 : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
          ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ))
          * ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) - 1
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
            ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ))
            * (((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
              - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((m : ℚ)))
          + (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
              (((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * (m : ℤ) : ℤ) : ℚ)) - 1) := by
      rw [show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
            (((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * (m : ℤ) : ℤ) : ℚ))
          = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
              ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ))
            * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((m : ℚ)) from by
        rw [← map_mul]
        congr 1
        push_cast
        ring]
      ring
    rw [hsplit2]
    refine add_mem_idealBall (mul_mem_idealBall_left ?_ hesub) ?_
    · rw [show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
            ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ))
          = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
              (algebraMap (𝓞 ℚ) ℚ ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : 𝓞 ℚ))) from by
        rw [map_intCast (algebraMap (𝓞 ℚ) ℚ)]]
      exact algebraMap_mem_integralFiniteAdeles _
    · rw [show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)
          = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((1 : ℚ)) from (map_one _).symm,
        ← map_sub,
        show (((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * (m : ℤ) : ℤ) : ℚ)) - ((1 : ℚ))
          = ((((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * (m : ℤ) - 1) : ℤ) : ℚ)) from by
        push_cast; ring]
      exact hball_of_dvd _ hγdm

  have hu_mem : (Matrix.GeneralLinearGroup.scalar (Fin 2) e⁻¹ * diagOne e) * γf
      ∈ finiteLevelOne (𝓞 ℚ) ℚ Ψ.level := by
    refine peel_mem_finiteLevelOne e _ γf ?_ ?_ hint hintinv hei he hc hd hcinv ha
    · rw [Units.val_mul, scalar_inv_mul_diagOne_coe]
    · rw [mul_inv_rev, Units.val_mul, peel_inv_coe]
  have hdiag_mem : diagOne e⁻¹ ∈ finiteLevelOne (𝓞 ℚ) ℚ Ψ.level := by
    refine diagOne_mem_finiteLevelOne e⁻¹ hei ?_
    rw [inv_inv]
    exact he

  show descentFn w hw R.toFun (slGammaFinLift γ⁻¹) zc
      = ((chiNegThree m : ℤ) : ℂ) * descentFn w hw R.toFun 1 zc
  simp only [descentFn]
  rw [show ((slGammaFinLift γ⁻¹ : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ)) :
      GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = γf from by
    rw [slGammaFinLift_coe, hγfdef, hδdef],
    OneMemClass.coe_one, map_one, mul_one]
  have hpeel := peel_identity e γf
  rw [show AdelicDock.finEmbed (𝓞 ℚ) ℚ γf
      = AdelicDock.finEmbed (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) e)
        * AdelicDock.finEmbed (𝓞 ℚ) ℚ (diagOne e⁻¹)
        * AdelicDock.finEmbed (𝓞 ℚ) ℚ
            ((Matrix.GeneralLinearGroup.scalar (Fin 2) e⁻¹ * diagOne e) * γf) from by
    rw [← map_mul, ← map_mul]
    exact congrArg (AdelicDock.finEmbed (𝓞 ℚ) ℚ) hpeel]
  rw [show ∀ A B C D : AdelicGL2 (𝓞 ℚ) ℚ, A * (B * C * D) = ((A * B) * C) * D from by
    intro A B C D; group]
  rw [R.level_invariant _ _ (finEmbed_mem_U hu_mem)]
  rw [R.level_invariant _ _ (finEmbed_mem_U hdiag_mem)]
  rw [finEmbed_scalar_eq_centralScalar, ← centralScalar_mul_comm, omega_spec]
  rw [hedef, hepsval m hm hgood]
  ring

section Gamma0Supply

section ChiSupply

open EisensteinWeightOne

end ChiSupply
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

open EisensteinWeightOne in
private theorem chiNegThree_congr {a b : ℕ} (h : ((a : ℤ) : ZMod 3) = ((b : ℤ) : ZMod 3)) :
    chiNegThree a = chiNegThree b := by
  unfold chiNegThree
  have hab : a % 3 = b % 3 := by
    have h2 : ((a : ZMod 3)) = ((b : ZMod 3)) := by exact_mod_cast h
    have := congrArg ZMod.val h2
    rwa [ZMod.val_natCast, ZMod.val_natCast] at this
  rw [hab]

end Gamma0Supply
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

private theorem descent_slash_gamma0 (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (hepsval : ∀ (m : ℕ) (hm : 0 < m),
      (∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
        ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
          ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
          ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) →
      ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit m hm))) : ℂˣ) : ℂ)
        = ((chiNegThree m : ℤ) : ℂ))
    (hdet : ∀ q : ℕ, ∀ hq : q.Prime, ¬ q ∣ Ideal.absNorm Ψ.level → q ≠ 3 →
      ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet →
      Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹)
    (hN3 : 3 ∣ Ideal.absNorm Ψ.level)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (Ideal.absNorm Ψ.level)) :
    (descentF R w hw) ∣[(1 : ℤ)] γ
      = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (descentF R w hw) := by
  classical
  set N₀ : ℕ := Ideal.absNorm Ψ.level with hN₀def
  have hN0 : N₀ ≠ 0 := by
    rw [hN₀def]
    simpa [Ideal.absNorm_eq_zero_iff] using Ψ.level_ne_bot

  set δ : SL(2, ℤ) := γ⁻¹ with hδdef
  have hδmem : δ ∈ Gamma0 N₀ := (Gamma0 N₀).inv_mem hγ
  have hδ11 : ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) := by
    rw [hδdef]
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

  have hδdet : ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N₀)
      * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N₀) = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe δ
    rw [Matrix.det_fin_two] at hdet
    have hc : ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N₀) = 0 := by
      exact_mod_cast CongruenceSubgroup.Gamma0_mem.mp hδmem
    have := congrArg (fun x : ℤ => (x : ZMod N₀)) hdet
    push_cast at this
    rw [hc] at this
    linear_combination this
  have hdunit : IsUnit (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N₀) :=
    isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans hδdet⟩

  set B : ℕ := ∏ v ∈ R.exceptionalSet, Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) v
    with hBdef
  have hB : B ≠ 0 := by
    rw [hBdef]
    refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
    exact (Rat.HeightOneSpectrum.prime_natGenerator (R := 𝓞 ℚ) v).ne_zero

  obtain ⟨m, hm, hmN, hmB, hm3⟩ := exists_pos_rep_mod_coprime N₀ B hN0 hN3 hB
    ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) hdunit

  have hmcop : m.Coprime N₀ := by
    have hu : IsUnit ((m : ℤ) : ZMod N₀) := by
      rw [hmN]
      exact hdunit
    rwa [Int.cast_natCast, ZMod.isUnit_iff_coprime] at hu
  have hgood : ∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
      ¬ q ∣ N₀ ∧ q ≠ 3
        ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
        ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹ := by
    intro q hq hqm
    have hqN : ¬ q ∣ N₀ := fun hqN =>
      hq.ne_one ((Nat.Coprime.coprime_dvd_left hqm hmcop).eq_one_of_dvd hqN)
    have hq3 : q ≠ 3 := by
      intro hq3
      subst hq3
      have hδc3 : ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 3) = 0 := by
        have hcN : ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N₀) = 0 := by
          exact_mod_cast CongruenceSubgroup.Gamma0_mem.mp hδmem
        have hdvdN : ((N₀ : ℕ) : ℤ) ∣ ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
          (dvd_trans (by exact_mod_cast (show (3 : ℕ) ∣ N₀ from by rwa [hN₀def] at hN3))
            hdvdN)
      have hδdet3 : ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 3)
          * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3) = 1 := by
        have hdet := Matrix.SpecialLinearGroup.det_coe δ
        rw [Matrix.det_fin_two] at hdet
        have := congrArg (fun x : ℤ => (x : ZMod 3)) hdet
        push_cast at this
        rw [hδc3] at this
        linear_combination this
      have hu3 : IsUnit ((m : ℤ) : ZMod 3) := by
        rw [hm3]
        exact isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans hδdet3⟩
      have hcop3 : m.Coprime 3 := by
        rwa [Int.cast_natCast, ZMod.isUnit_iff_coprime] at hu3
      have h1 := (Nat.Coprime.coprime_dvd_left hqm hcop3).eq_one_of_dvd (dvd_refl 3)
      norm_num at h1
    have hexc : ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet := by
      intro hmem
      have hqB : q ∣ B := by
        rw [hBdef,
          show q = Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (ratPrime ⟨q, hq⟩) from
            (natGenerator_ratPrime ⟨q, hq⟩).symm]
        exact Finset.dvd_prod_of_mem _ hmem
      exact hq.ne_one ((Nat.Coprime.coprime_dvd_left hqm hmB).eq_one_of_dvd hqB)
    exact ⟨hqN, hq3, hexc, hdet q hq hqN hq3 hexc⟩

  have hmd : ((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) ≡ (m : ℤ) [ZMOD N₀] := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mp
      (show (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N₀) = ((m : ℤ) : ZMod N₀) from
        hmN.symm)
    rw [hδdef] at this
    exact this

  rw [slash_descentF_eq R w hw harch homega γ,
    descentFn_slGammaFinLift_inv_eq R w hw hepsval γ hγ m hm hgood hmd]

  have h3dvd : (3 : ℕ) ∣ N₀ := by rwa [hN₀def] at hN3
  have hval : chiNegThree m
      = chiNegThree (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3).val) := by

    have hγdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 3)
        * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3) = 1 := by
      have hdet := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at hdet
      have hc3 : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 3) = 0 := by
        have hcN : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N₀) = 0 := by
          exact_mod_cast CongruenceSubgroup.Gamma0_mem.mp hγ
        have hdvdN : ((N₀ : ℕ) : ℤ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
        have hdvd3 : ((3 : ℕ) : ℤ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :=
          dvd_trans (by exact_mod_cast h3dvd) hdvdN
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd3
      have := congrArg (fun x : ℤ => (x : ZMod 3)) hdet
      push_cast at this
      rw [hc3] at this
      linear_combination this

    have hm00 : ((m : ℤ) : ZMod 3) = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 3) := by
      rw [hm3, hδ11]

    have h11unit : IsUnit ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3) :=
      isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans hγdet⟩
    have h11val : ¬ (3 : ℕ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3).val := by
      intro hdvd
      have hv3 : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3).val < 3 := ZMod.val_lt _
      interval_cases h : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3).val
      · have h0 : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3) = 0 := by
          have := congrArg (fun n : ℕ => (n : ZMod 3)) h
          simpa [ZMod.natCast_val, ZMod.cast_id] using this
        rw [h0] at h11unit
        simpa using h11unit
      · simp at hdvd
      · omega
    have h3m : ¬ (3 : ℕ) ∣ m := by
      intro h3m
      have h0 : ((m : ℤ) : ZMod 3) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) 3).mpr (by exact_mod_cast h3m)
      rw [hm00] at h0
      have : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3)
          * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 3) = 1 := (mul_comm _ _).trans hγdet
      rw [h0] at this
      simp at this

    have hmul1 : chiNegThree m
        * chiNegThree (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3).val) = 1 := by
      rw [← chiNegThree_mul]
      rw [show chiNegThree (m * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3).val)
          = chiNegThree 1 from chiNegThree_congr (by
        push_cast [ZMod.natCast_val, ZMod.cast_id]
        have hm00' : ((m : ℕ) : ZMod 3) = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 3) := by
          exact_mod_cast hm00
        rw [hm00']
        linear_combination hγdet)]
      decide
    rcases chiNegThree_eq_one_or_neg_one h3m with h | h <;>
      rcases chiNegThree_eq_one_or_neg_one h11val with h' | h'
    · rw [h, h']
    · rw [h, h'] at hmul1
      norm_num at hmul1
    · rw [h, h'] at hmul1
      norm_num at hmul1
    · rw [h, h']
  rw [hval]
  funext z
  simp [descentF, Pi.smul_apply, smul_eq_mul]

private theorem descent_slash_gamma1 (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (hepsval : ∀ (m : ℕ) (hm : 0 < m),
      (∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
        ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
          ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
          ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) →
      ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit m hm))) : ℂˣ) : ℂ)
        = ((chiNegThree m : ℤ) : ℂ))
    (hdet : ∀ q : ℕ, ∀ hq : q.Prime, ¬ q ∣ Ideal.absNorm Ψ.level → q ≠ 3 →
      ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet →
      Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹)
    (hN3 : 3 ∣ Ideal.absNorm Ψ.level)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 (Ideal.absNorm Ψ.level)) :
    (descentF R w hw) ∣[(1 : ℤ)] γ = descentF R w hw := by
  obtain ⟨h00, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem _ _).mp hγ
  have hγ0 : γ ∈ Gamma0 (Ideal.absNorm Ψ.level) := CongruenceSubgroup.Gamma0_mem.mpr h10
  rw [descent_slash_gamma0 R w hw harch homega hepsval hdet hN3 γ hγ0]

  have h113 : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3) = 1 := by
    have hdvdN : ((Ideal.absNorm Ψ.level : ℕ) : ℤ)
        ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1) := by
      have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr
        (show ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) ≡ 1 [ZMOD (Ideal.absNorm Ψ.level)] from ?_)
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
          push_cast at this ⊢
          linear_combination this)
      · rw [Int.ModEq]
        have h1 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (Ideal.absNorm Ψ.level))
            = 1 := by exact_mod_cast h11
        have := (ZMod.intCast_eq_intCast_iff _ _ _).mp
          (show (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (Ideal.absNorm Ψ.level))
            = ((1 : ℤ) : ZMod (Ideal.absNorm Ψ.level)) from by rw [h1]; norm_num)
        exact this
    have hdvd3 : ((3 : ℕ) : ℤ) ∣ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1) :=
      dvd_trans (by exact_mod_cast hN3) hdvdN
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd3
    push_cast at this
    linear_combination this
  rw [show (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3)).val = 1 from by
    rw [h113]; rfl]
  rw [show chiNegThree 1 = 1 from by decide]
  norm_num

end TransportHeads
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section MinusIdentityTest

variable {Ψ : HeckeEigensystem ℚ ℂ}

private theorem neg_one_mem_Gamma0 (N : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem]

example (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (hepsval : ∀ (m : ℕ) (hm : 0 < m),
      (∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
        ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
          ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
          ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) →
      ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit m hm))) : ℂˣ) : ℂ)
        = ((chiNegThree m : ℤ) : ℂ))
    (hdet : ∀ q : ℕ, ∀ hq : q.Prime, ¬ q ∣ Ideal.absNorm Ψ.level → q ≠ 3 →
      ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet →
      Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹)
    (hN3 : 3 ∣ Ideal.absNorm Ψ.level) :
    (descentF R w hw) ∣[(1 : ℤ)] (-1 : SL(2, ℤ))
      = ((chiNegThree ((((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3).val :
          ℕ) : ℤ) : ℂ) • (descentF R w hw) :=
  descent_slash_gamma0 R w hw harch homega hepsval hdet hN3 (-1)
    (neg_one_mem_Gamma0 _)

example : ((((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 3).val : ℕ) = 2
    ∧ EisensteinWeightOne.chiNegThree 2 = -1 := by
  constructor
  · decide
  · decide

end MinusIdentityTest
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part05
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part06

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

open UpperHalfPlane CongruenceSubgroup ModularForm EisensteinWeightOne

open scoped MatrixGroups ModularForm

noncomputable section

namespace HeckeDictionary

section OmegaInfraSplice

variable {Ψ : HeckeEigensystem ℚ ℂ}

attribute [local instance] instDecEqInfinitePlaceRat

end OmegaInfraSplice
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section EpsCarrierSplice

variable {L : Ideal (𝓞 ℚ)}

end EpsCarrierSplice
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

variable {Ψ : HeckeEigensystem ℚ ℂ}

section KappaSupplySplice

end KappaSupplySplice
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Head8Supply

end Head8Supply
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

private def upperTriQ (a b d : ℚ) (ha : a ≠ 0) (hd : d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d] (by
    simp only [Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_ne_zero ha hd)

private noncomputable def heckeReps (p : ℕ) (hp : p.Prime) :
    Fin (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ :=
  fun i =>
    if (i : ℕ) < p then
      AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
        * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
    else
      centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
          (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
        * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹

section S2Supply

private theorem coe_realOf_upperTriQ (a b d : ℚ) (ha : a ≠ 0) (hd : d ≠ 0) :
    (realOf (upperTriQ a b d ha hd) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(a : ℝ), (b : ℝ); 0, (d : ℝ)] := by
  ext i j
  show algebraMap ℚ ℝ ((!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℚ) i j)
    = (!![(a : ℝ), (b : ℝ); 0, (d : ℝ)]) i j
  fin_cases i <;> fin_cases j <;> simp [eq_ratCast]

private theorem det_realOf_upperTriQ_pos (a b d : ℚ) (ha : 0 < a) (hd : 0 < d) :
    (0 : ℝ) < ((realOf (upperTriQ a b d ha.ne' hd.ne') :
        Matrix (Fin 2) (Fin 2) ℝ)).det := by
  rw [coe_realOf_upperTriQ, Matrix.det_fin_two_of]
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  nlinarith

private theorem coe_smul_realOf_upperTriQ_mul (a b d : ℚ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    ((realOf (upperTriQ a b d ha.ne' hd.ne') • τ : ℍ) : ℂ) * ((d : ℝ) : ℂ)
      = ((a : ℝ) : ℂ) * (τ : ℂ) + ((b : ℝ) : ℂ) := by
  have hdc : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [coe_smul_of_det_pos _ (det_realOf_upperTriQ_pos a b d ha hd),
    show num (realOf (upperTriQ a b d ha.ne' hd.ne')) ((τ : ℂ))
        = ((a : ℝ) : ℂ) * (τ : ℂ) + ((b : ℝ) : ℂ) by
      simp [num, coe_realOf_upperTriQ],
    show denom (realOf (upperTriQ a b d ha.ne' hd.ne')) ((τ : ℂ)) = ((d : ℝ) : ℂ) by
      simp [denom, coe_realOf_upperTriQ],
    div_mul_cancel₀ _ hdc]

private theorem im_smul_realOf_upperTriQ (a b d : ℚ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    ((realOf (upperTriQ a b d ha.ne' hd.ne') • τ : ℍ)).im * (d : ℝ)
      = (a : ℝ) * τ.im := by
  have h := congrArg Complex.im (coe_smul_realOf_upperTriQ_mul a b d ha hd τ)
  simpa [Complex.add_im, Complex.mul_im] using h

private theorem re_smul_realOf_upperTriQ (a b d : ℚ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    ((realOf (upperTriQ a b d ha.ne' hd.ne') • τ : ℍ)).re * (d : ℝ)
      = (a : ℝ) * τ.re + (b : ℝ) := by
  have h := congrArg Complex.re (coe_smul_realOf_upperTriQ_mul a b d ha hd τ)
  simpa [Complex.add_re, Complex.mul_re] using h

private theorem realOf_upperTriQ_mul_iwasawaSec (a b d : ℚ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    realOf (upperTriQ a b d ha.ne' hd.ne') * iwasawaSec τ
      = iwasawaSec (realOf (upperTriQ a b d ha.ne' hd.ne') • τ)
        * Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.mk0 ((d : ℝ)) (by exact_mod_cast hd.ne')) := by
  have him := im_smul_realOf_upperTriQ a b d ha hd τ
  have hre := re_smul_realOf_upperTriQ a b d ha hd τ
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_realOf_upperTriQ, coe_iwasawaSec, coe_iwasawaSec,
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.mk0 ((d : ℝ)) (by exact_mod_cast hd.ne' : ((d : ℝ)) ≠ 0)) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.scalar (Fin 2) ((d : ℝ)) from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply]
      try linarith [him, hre]

private theorem mul_mul_mul_inv_cancel_of_comm {G : Type*} [Group G] {F S : G} (A : G)
    (h : F * S = S * F) : A * F * (S * F⁻¹) = A * S := by
  rw [mul_assoc, ← mul_assoc F S, h, mul_assoc S, mul_inv_cancel, mul_one]

end S2Supply
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section S5SupplyVal

private theorem withZero_exp_le_exp {a b : ℤ} : WithZero.exp a ≤ WithZero.exp b ↔ a ≤ b := by
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, WithZero.coe_le_coe]
  exact Multiplicative.ofAdd_le

private theorem withZero_exp_lt_exp {a b : ℤ} : WithZero.exp a < WithZero.exp b ↔ a < b := by
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, WithZero.coe_lt_coe]
  exact Multiplicative.ofAdd_lt

private theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx0 : x ≠ 0)
    (hx1 : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.exp_log hx0] at hx1 ⊢
  rw [← WithZero.exp_zero, withZero_exp_lt_exp] at hx1
  exact withZero_exp_le_exp.mpr (by omega)

private theorem valued_adicInt_le_one {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    (x : v.adicCompletionIntegers ℚ) :
    Valued.v (x : v.adicCompletion ℚ) ≤ 1 := by
  have h := x.2
  rwa [mem_adicCompletionIntegers] at h

private theorem isUnit_adicInt_of_valued_eq_one {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    {x : v.adicCompletionIntegers ℚ} (hx : Valued.v (x : v.adicCompletion ℚ) = 1) :
    IsUnit x := by
  have hx0 : (x : v.adicCompletion ℚ) ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  have hmem : (x : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [mem_adicCompletionIntegers, map_inv₀, hx, inv_one]
  exact ⟨⟨x, ⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

private theorem valued_eq_one_of_isUnit {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    {x : v.adicCompletionIntegers ℚ} (hx : IsUnit x) :
    Valued.v (x : v.adicCompletion ℚ) = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 : ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
      * (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
          : v.adicCompletion ℚ) = 1 := by
    exact_mod_cast congrArg Subtype.val u.mul_inv
  have h2 := congrArg Valued.v h1
  rw [map_mul, map_one] at h2
  refine le_antisymm (valued_adicInt_le_one _) ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
        * Valued.v (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
            : v.adicCompletion ℚ) := h2.symm
    _ ≤ Valued.v ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) * 1 :=
        mul_le_mul' le_rfl (valued_adicInt_le_one _)
    _ = Valued.v ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := mul_one _

private theorem adicInt_dvd_of_valued_le {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    {x y : v.adicCompletionIntegers ℚ} (hx0 : (x : v.adicCompletion ℚ) ≠ 0)
    (h : Valued.v (y : v.adicCompletion ℚ) ≤ Valued.v (x : v.adicCompletion ℚ)) :
    x ∣ y := by
  have hvx : Valued.v (x : v.adicCompletion ℚ) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hx0
  have hmem : (y : v.adicCompletion ℚ) / (x : v.adicCompletion ℚ)
      ∈ v.adicCompletionIntegers ℚ := by
    rw [mem_adicCompletionIntegers, map_div₀, div_eq_mul_inv]
    calc Valued.v (y : v.adicCompletion ℚ) * (Valued.v (x : v.adicCompletion ℚ))⁻¹
        ≤ Valued.v (x : v.adicCompletion ℚ) * (Valued.v (x : v.adicCompletion ℚ))⁻¹ :=
          mul_le_mul' h le_rfl
      _ = 1 := mul_inv_cancel₀ hvx
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  show (y : v.adicCompletion ℚ)
      = (x : v.adicCompletion ℚ) * ((y : v.adicCompletion ℚ) / (x : v.adicCompletion ℚ))
  rw [mul_comm]
  exact (div_mul_cancel₀ _ hx0).symm

private noncomputable def natInt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    v.adicCompletionIntegers ℚ :=
  ⟨algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ), by
    rw [mem_adicCompletionIntegers,
      show (((n : ℕ) : ℚ)) = algebraMap (𝓞 ℚ) ℚ (((n : ℕ) : 𝓞 ℚ)) by simp,
      valued_algebraMap]
    exact v.intValuation_le_one _⟩

@[scoped simp] private theorem coe_natInt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((natInt v n : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
      = algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ) := rfl

private theorem valued_natInt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v ((natInt v n : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
      = v.intValuation (((n : ℕ) : 𝓞 ℚ)) := by
  show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ)) = _
  rw [show (((n : ℕ) : ℚ)) = algebraMap (𝓞 ℚ) ℚ (((n : ℕ) : 𝓞 ℚ)) by simp, valued_algebraMap]

private noncomputable def pInt (p : Nat.Primes) : (ratPrime p).adicCompletionIntegers ℚ :=
  natInt (ratPrime p) (p : ℕ)

private theorem valued_pInt (p : Nat.Primes) :
    Valued.v ((pInt p : (ratPrime p).adicCompletionIntegers ℚ)
        : (ratPrime p).adicCompletion ℚ)
      = WithZero.exp (-1 : ℤ) := valued_pUnit p

private theorem irreducible_pInt (p : Nat.Primes) : Irreducible (pInt p) := by
  constructor
  · intro hu
    have h1 := valued_eq_one_of_isUnit hu
    rw [valued_pInt, ← WithZero.exp_zero] at h1
    have h2 := WithZero.exp_inj.mp h1
    omega
  · intro a b hab
    by_contra hcon
    push Not at hcon
    have ha1 : Valued.v ((a : (ratPrime p).adicCompletion ℚ)) < 1 :=
      lt_of_le_of_ne (valued_adicInt_le_one _)
        (fun h => hcon.1 (isUnit_adicInt_of_valued_eq_one h))
    have hb1 : Valued.v ((b : (ratPrime p).adicCompletion ℚ)) < 1 :=
      lt_of_le_of_ne (valued_adicInt_le_one _)
        (fun h => hcon.2 (isUnit_adicInt_of_valued_eq_one h))
    have hco : ((pInt p : (ratPrime p).adicCompletionIntegers ℚ)
          : (ratPrime p).adicCompletion ℚ)
        = (a : (ratPrime p).adicCompletion ℚ) * (b : (ratPrime p).adicCompletion ℚ) := by
      exact_mod_cast congrArg Subtype.val hab
    have hv : WithZero.exp (-1 : ℤ)
        = Valued.v ((a : (ratPrime p).adicCompletion ℚ))
          * Valued.v ((b : (ratPrime p).adicCompletion ℚ)) := by
      rw [← map_mul, ← hco, valued_pInt]
    have ha0 : Valued.v ((a : (ratPrime p).adicCompletion ℚ)) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hv
      exact WithZero.exp_ne_zero hv
    have hb0 : Valued.v ((b : (ratPrime p).adicCompletion ℚ)) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hv
      exact WithZero.exp_ne_zero hv
    have hle : Valued.v ((a : (ratPrime p).adicCompletion ℚ))
          * Valued.v ((b : (ratPrime p).adicCompletion ℚ))
        ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (-1 : ℤ) :=
      mul_le_mul' (le_exp_neg_one_of_lt_one ha0 ha1) (le_exp_neg_one_of_lt_one hb0 hb1)
    rw [← hv, ← WithZero.exp_add] at hle
    have h3 := withZero_exp_le_exp.mp hle
    omega

private theorem isUnit_natInt_of_not_dvd (p : Nat.Primes) {n : ℕ} (hnp : ¬ (p : ℕ) ∣ n) :
    IsUnit (natInt (ratPrime p) n) := by
  apply isUnit_adicInt_of_valued_eq_one
  rw [valued_natInt]
  have hmem : ((n : ℕ) : 𝓞 ℚ) ∉ (ratPrime p).asIdeal := by
    rw [ratPrime_asIdeal_eq_span p, Ideal.mem_span_singleton]
    intro hdvd
    apply hnp
    have h2 := (intEquiv_dvd_iff _ _).mp hdvd
    rw [map_natCast, map_natCast] at h2
    exact_mod_cast h2
  refine le_antisymm ((ratPrime p).intValuation_le_one _) (not_lt.mp ?_)
  intro hcon
  exact hmem (((ratPrime p).intValuation_lt_one_iff_mem _).mp hcon)

end S5SupplyVal
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section S5SupplyRes

private theorem valued_ball_one_mem_nhds {R : Type*} {Γ₀ : Type*} [Ring R]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀] (b : R) :
    { y : R | Valued.v (y - b) < (1 : Γ₀) } ∈ nhds b := by
  rw [Valued.mem_nhds]
  refine ⟨1, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_one] at hy
  have h1 : Valued.v.restrict (y - b) < Valued.v.restrict 1 := by rwa [map_one]
  rw [Valuation.restrict_lt_iff] at h1
  simpa using h1

private theorem exists_rat_valued_sub_lt_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (b : v.adicCompletion ℚ) :
    ∃ q : ℚ, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q - b)
      < (1 : WithZero (Multiplicative ℤ)) :=
  (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap ℚ v).mem_nhds
    (valued_ball_one_mem_nhds b)

private theorem exists_intRing_valued_sub_lt_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (b : v.adicCompletionIntegers ℚ) :
    ∃ a : 𝓞 ℚ, Valued.v ((b : v.adicCompletion ℚ)
        - algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)) < 1 := by
  obtain ⟨q, hq⟩ := exists_rat_valued_sub_lt_one v (b : v.adicCompletion ℚ)
  have hswap : Valued.v ((b : v.adicCompletion ℚ)
      - algebraMap ℚ (v.adicCompletion ℚ) q) < 1 := by
    rwa [Valued.v.map_sub_swap]
  have hq1 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 := by
    have h1 : algebraMap ℚ (v.adicCompletion ℚ) q
        = (b : v.adicCompletion ℚ)
          - ((b : v.adicCompletion ℚ) - algebraMap ℚ (v.adicCompletion ℚ) q) := by ring
    rw [h1]
    exact Valued.v.map_sub_le (valued_adicInt_le_one b) hswap.le
  have hqK : v.valuation ℚ q ≤ 1 := by
    calc v.valuation ℚ q
        = Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) :=
          (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q).symm
      _ ≤ 1 := hq1
  obtain ⟨a, ha⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hqK 1
  refine ⟨a, ?_⟩
  have haC : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
      - algebraMap ℚ (v.adicCompletion ℚ) q) < 1 := by
    rw [← map_sub]
    calc Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a - q))
        = v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ a - q) :=
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
      _ < 1 := by simpa using ha
  have hfinal : (b : v.adicCompletion ℚ)
      - algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
      = ((b : v.adicCompletion ℚ) - algebraMap ℚ (v.adicCompletion ℚ) q)
        - (algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
            - algebraMap ℚ (v.adicCompletion ℚ) q) := by ring
  rw [hfinal]
  exact Valued.v.map_sub_lt hswap haC

private theorem exists_nat_sub_mem_ratPrime (p : Nat.Primes) (a : 𝓞 ℚ) :
    ∃ n : ℕ, n < (p : ℕ) ∧ a - ((n : ℕ) : 𝓞 ℚ) ∈ (ratPrime p).asIdeal := by
  haveI : NeZero (p : ℕ) := ⟨p.2.pos.ne'⟩
  set z : ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) a with hz
  refine ⟨(z : ZMod (p : ℕ)).val, ZMod.val_lt _, ?_⟩
  rw [ratPrime_asIdeal_eq_span, Ideal.mem_span_singleton, intEquiv_dvd_iff,
    map_natCast, map_sub, map_natCast, ← hz]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sub_self]

private theorem valued_le_exp_neg_one_of_mem (p : Nat.Primes) {x : 𝓞 ℚ}
    (hx : x ∈ (ratPrime p).asIdeal) :
    Valued.v (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ x))
      ≤ WithZero.exp (-1 : ℤ) := by
  rw [valued_algebraMap]
  rcases eq_or_ne ((ratPrime p).intValuation x) 0 with h0 | h0
  · rw [h0]; exact zero_le'
  · exact le_exp_neg_one_of_lt_one h0
      (((ratPrime p).intValuation_lt_one_iff_mem _).mpr hx)

private theorem exists_natInt_dvd_sub (p : Nat.Primes)
    (b : (ratPrime p).adicCompletionIntegers ℚ) :
    ∃ n : ℕ, n < (p : ℕ) ∧ pInt p ∣ (b - natInt (ratPrime p) n) := by
  obtain ⟨a, ha⟩ := exists_intRing_valued_sub_lt_one (ratPrime p) b
  obtain ⟨n, hn, hmem⟩ := exists_nat_sub_mem_ratPrime p a
  refine ⟨n, hn, ?_⟩
  have hban : Valued.v ((b : (ratPrime p).adicCompletion ℚ)
      - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
          : (ratPrime p).adicCompletion ℚ)) ≤ WithZero.exp (-1 : ℤ) := by
    have hsplit : (b : (ratPrime p).adicCompletion ℚ)
        - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
            : (ratPrime p).adicCompletion ℚ)
        = ((b : (ratPrime p).adicCompletion ℚ)
            - algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a))
          + (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
              - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
                  : (ratPrime p).adicCompletion ℚ)) := by ring
    rw [hsplit]
    refine Valued.v.map_add_le ?_ ?_
    · rcases eq_or_ne (Valued.v ((b : (ratPrime p).adicCompletion ℚ)
          - algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a))) 0
        with h0 | h0
      · rw [h0]; exact zero_le'
      · exact le_exp_neg_one_of_lt_one h0 ha
    · have hcoe : algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
          - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
              : (ratPrime p).adicCompletion ℚ)
          = algebraMap ℚ ((ratPrime p).adicCompletion ℚ)
              (algebraMap (𝓞 ℚ) ℚ (a - ((n : ℕ) : 𝓞 ℚ))) := by
        rw [coe_natInt, map_sub, map_sub]
        congr 1
      rw [hcoe]
      exact valued_le_exp_neg_one_of_mem p hmem
  have hpne : ((pInt p : (ratPrime p).adicCompletionIntegers ℚ)
      : (ratPrime p).adicCompletion ℚ) ≠ 0 := by
    intro h
    have h2 := valued_pInt p
    rw [h, map_zero] at h2
    exact WithZero.exp_ne_zero h2.symm
  apply adicInt_dvd_of_valued_le hpne
  rw [valued_pInt]
  calc Valued.v (((b - natInt (ratPrime p) n) : (ratPrime p).adicCompletionIntegers ℚ)
        : (ratPrime p).adicCompletion ℚ)
      = Valued.v ((b : (ratPrime p).adicCompletion ℚ)
          - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
              : (ratPrime p).adicCompletion ℚ)) := by norm_cast
    _ ≤ WithZero.exp (-1 : ℤ) := hban

end S5SupplyRes
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section S5SupplyW

open scoped Classical in
private noncomputable def finDelta (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    FiniteAdeleRing (𝓞 ℚ) ℚ :=
  ⟨Function.update (0 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 1,
    Filter.Eventually.of_forall fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact one_mem _
      · rw [Function.update_of_ne hw]; exact zero_mem _⟩

open scoped Classical in
private noncomputable def finCoDelta (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    FiniteAdeleRing (𝓞 ℚ) ℚ :=
  ⟨Function.update (1 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 0,
    Filter.Eventually.of_forall fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact zero_mem _
      · rw [Function.update_of_ne hw]; exact one_mem _⟩

open scoped Classical in
private theorem finDelta_apply_self (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finDelta v v = 1 := by
  show Function.update (0 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 1 v = 1
  rw [Function.update_self]

open scoped Classical in
private theorem finDelta_apply_of_ne {v w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ v) : finDelta v w = 0 := by
  show Function.update (0 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 1 w = 0
  rw [Function.update_of_ne hw]
  rfl

open scoped Classical in
private theorem finCoDelta_apply_self (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finCoDelta v v = 0 := by
  show Function.update (1 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 0 v = 0
  rw [Function.update_self]

open scoped Classical in
private theorem finCoDelta_apply_of_ne {v w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ v) : finCoDelta v w = 1 := by
  show Function.update (1 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 0 w = 1
  rw [Function.update_of_ne hw]
  rfl

private theorem finDelta_mem_integral (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finDelta v ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun w => by
  by_cases hw : w = v
  · subst hw; rw [finDelta_apply_self]; exact one_mem _
  · rw [finDelta_apply_of_ne hw]; exact zero_mem _

private theorem finCoDelta_mem_integral (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finCoDelta v ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun w => by
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self]; exact zero_mem _
  · rw [finCoDelta_apply_of_ne hw]; exact one_mem _

private theorem finCoDelta_sq_add_finDelta_sq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finCoDelta v * finCoDelta v + finDelta v * finDelta v = 1 := by
  refine Subtype.ext (funext fun w => ?_)
  show (finCoDelta v * finCoDelta v + finDelta v * finDelta v) w
      = (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply, coe_one_apply]
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self, finDelta_apply_self]; ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]; ring

private theorem finCoDelta_mul_finDelta_add_finDelta_mul_finCoDelta
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finCoDelta v * finDelta v + finDelta v * finCoDelta v = 0 := by
  refine Subtype.ext (funext fun w => ?_)
  show (finCoDelta v * finDelta v + finDelta v * finCoDelta v) w
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply, coe_zero_apply]
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self, finDelta_apply_self]; ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]; ring

private theorem finDelta_mul_finCoDelta_add_finCoDelta_mul_finDelta
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finDelta v * finCoDelta v + finCoDelta v * finDelta v = 0 := by
  refine Subtype.ext (funext fun w => ?_)
  show (finDelta v * finCoDelta v + finCoDelta v * finDelta v) w
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply, coe_zero_apply]
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self, finDelta_apply_self]; ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]; ring

private theorem finDelta_sq_add_finCoDelta_sq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finDelta v * finDelta v + finCoDelta v * finCoDelta v = 1 := by
  refine Subtype.ext (funext fun w => ?_)
  show (finDelta v * finDelta v + finCoDelta v * finCoDelta v) w
      = (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply, coe_one_apply]
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self, finDelta_apply_self]; ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]; ring

private theorem weylMat_mul_self (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    (!![finCoDelta v, finDelta v; finDelta v, finCoDelta v]
        * !![finCoDelta v, finDelta v; finDelta v, finCoDelta v])
      = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two,
    finCoDelta_sq_add_finDelta_sq,
    finCoDelta_mul_finDelta_add_finDelta_mul_finCoDelta,
    finDelta_mul_finCoDelta_add_finCoDelta_mul_finDelta,
    finDelta_sq_add_finCoDelta_sq]

private noncomputable def weylFin (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) where
  val := !![finCoDelta v, finDelta v; finDelta v, finCoDelta v]
  inv := !![finCoDelta v, finDelta v; finDelta v, finCoDelta v]
  val_inv := weylMat_mul_self v
  inv_val := weylMat_mul_self v

private theorem ratPrime_not_dvd_of_not_dvd_absNorm (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm L) :
    ¬ (ratPrime p).asIdeal ∣ L ∧ L ≠ ⊥ := by
  have key : (ratPrime p).asIdeal ∣ L → False := by
    intro h
    apply hpN
    have h2 := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h)
    rwa [absNorm_ratPrime] at h2
  refine ⟨key, fun hbot => key ?_⟩
  rw [hbot, ← Ideal.zero_eq_bot]
  exact dvd_zero _

private theorem finDelta_mem_idealBall (p : Nat.Primes) {L : Ideal (𝓞 ℚ)} (hL : L ≠ ⊥)
    (hdvd : ¬ (ratPrime p).asIdeal ∣ L) :
    finDelta (ratPrime p) ∈ idealBall (𝓞 ℚ) ℚ L := fun w => by
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finDelta_apply_self, map_one, idealBound_eq_one_of_not_dvd hL hdvd]
  · rw [finDelta_apply_of_ne hw, map_zero]; exact zero_le'

private theorem finCoDelta_sub_one_mem_idealBall (p : Nat.Primes) {L : Ideal (𝓞 ℚ)} (hL : L ≠ ⊥)
    (hdvd : ¬ (ratPrime p).asIdeal ∣ L) :
    finCoDelta (ratPrime p) - 1 ∈ idealBall (𝓞 ℚ) ℚ L := fun w => by
  rw [coe_sub_apply, coe_one_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, zero_sub, Valuation.map_neg, map_one,
      idealBound_eq_one_of_not_dvd hL hdvd]
  · rw [finCoDelta_apply_of_ne hw, sub_self, map_zero]; exact zero_le'

private theorem weylFin_isLevelOneMatrix (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm L) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L
      ((weylFin (ratPrime p) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  obtain ⟨hdvd, hbot⟩ := ratPrime_not_dvd_of_not_dvd_absNorm p hpN
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j
    · show finCoDelta (ratPrime p) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      exact finCoDelta_mem_integral _
    · show finDelta (ratPrime p) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      exact finDelta_mem_integral _
    · show finDelta (ratPrime p) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      exact finDelta_mem_integral _
    · show finCoDelta (ratPrime p) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      exact finCoDelta_mem_integral _
  · show finDelta (ratPrime p) ∈ idealBall (𝓞 ℚ) ℚ L
    exact finDelta_mem_idealBall p hbot hdvd
  · show finCoDelta (ratPrime p) - 1 ∈ idealBall (𝓞 ℚ) ℚ L
    exact finCoDelta_sub_one_mem_idealBall p hbot hdvd

private theorem weylFin_mem_finiteLevelOne (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm L) :
    weylFin (ratPrime p) ∈ finiteLevelOne (𝓞 ℚ) ℚ L := by
  rw [mem_finiteLevelOne_iff]
  exact ⟨weylFin_isLevelOneMatrix p hpN, weylFin_isLevelOneMatrix p hpN⟩

private theorem weylV_mem_U (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm L) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (weylFin (ratPrime p)) ∈ h4pins.U L := by
  rw [productionPinsCompact_U, Subgroup.mem_inf]
  exact ⟨(AdelicDock.finEmbed_mem_levelOne_iff _ _ _).mpr (weylFin_mem_finiteLevelOne p hpN),
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _)⟩

end S5SupplyW
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section S5SupplyKey

private theorem glArch_heckeGenAt (p : Nat.Primes) :
    glArch (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one]
  exact heckeGenAt_fst (pUnit p) i j

private noncomputable def piAdele (p : Nat.Primes) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    FiniteAdeleRing (𝓞 ℚ) ℚ)

private theorem piAdele_apply_of_ne {p : Nat.Primes} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ ratPrime p) : piAdele p w = 1 :=
  localUnit_apply_of_ne (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) hw

private theorem glFin_heckeGenAt_val (p : Nat.Primes) :
    ((glFin (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = !![piAdele p, 0; 0, 1] := by
  rw [Matrix.eta_fin_two ((glFin (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) :
      GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
  rfl

private theorem weylGen_entry_LA (p : Nat.Primes) :
    (finCoDelta (ratPrime p) * piAdele p) * (finCoDelta (ratPrime p) * piAdele p)
        + finDelta (ratPrime p) * (finDelta (ratPrime p) * piAdele p)
      = piAdele p := by
  refine Subtype.ext (funext fun w => ?_)
  show ((finCoDelta (ratPrime p) * piAdele p) * (finCoDelta (ratPrime p) * piAdele p)
      + finDelta (ratPrime p) * (finDelta (ratPrime p) * piAdele p)) w = piAdele p w
  simp only [coe_add_apply, coe_mul_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, finDelta_apply_self]
    ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw, piAdele_apply_of_ne hw]
    ring

private theorem weylGen_entry_LB (p : Nat.Primes) :
    (finCoDelta (ratPrime p) * piAdele p) * finDelta (ratPrime p)
        + finDelta (ratPrime p) * finCoDelta (ratPrime p)
      = 0 := by
  refine Subtype.ext (funext fun w => ?_)
  show ((finCoDelta (ratPrime p) * piAdele p) * finDelta (ratPrime p)
      + finDelta (ratPrime p) * finCoDelta (ratPrime p)) w
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  simp only [coe_add_apply, coe_mul_apply, coe_zero_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, finDelta_apply_self]
    ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]
    ring

private theorem weylGen_entry_LC (p : Nat.Primes) :
    (finDelta (ratPrime p) * piAdele p) * (finCoDelta (ratPrime p) * piAdele p)
        + finCoDelta (ratPrime p) * (finDelta (ratPrime p) * piAdele p)
      = 0 := by
  refine Subtype.ext (funext fun w => ?_)
  show ((finDelta (ratPrime p) * piAdele p) * (finCoDelta (ratPrime p) * piAdele p)
      + finCoDelta (ratPrime p) * (finDelta (ratPrime p) * piAdele p)) w
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  simp only [coe_add_apply, coe_mul_apply, coe_zero_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, finDelta_apply_self]
    ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]
    ring

private theorem weylGen_entry_LD (p : Nat.Primes) :
    (finDelta (ratPrime p) * piAdele p) * finDelta (ratPrime p)
        + finCoDelta (ratPrime p) * finCoDelta (ratPrime p)
      = piAdele p := by
  refine Subtype.ext (funext fun w => ?_)
  show ((finDelta (ratPrime p) * piAdele p) * finDelta (ratPrime p)
      + finCoDelta (ratPrime p) * finCoDelta (ratPrime p)) w = piAdele p w
  simp only [coe_add_apply, coe_mul_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, finDelta_apply_self]
    ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw, piAdele_apply_of_ne hw]
    ring

private theorem weylGen_sq (p : Nat.Primes) :
    (weylFin (ratPrime p) * glFin (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
        * (weylFin (ratPrime p) * glFin (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      = Matrix.GeneralLinearGroup.scalar (Fin 2)
          (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rw [glFin_heckeGenAt_val,
    show ((weylFin (ratPrime p) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = !![finCoDelta (ratPrime p), finDelta (ratPrime p);
          finDelta (ratPrime p), finCoDelta (ratPrime p)] from rfl,
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2)
          (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.scalar (Fin 2) (piAdele p) from rfl]
  rw [Matrix.mul_fin_two]
  simp only [mul_zero, add_zero, zero_add, mul_one]
  rw [Matrix.mul_fin_two, weylGen_entry_LA p, weylGen_entry_LB p, weylGen_entry_LC p,
    weylGen_entry_LD p,
    show Matrix.scalar (Fin 2) (piAdele p) = !![piAdele p, 0; 0, piAdele p] from by
      rw [Matrix.eta_fin_two (Matrix.scalar (Fin 2) (piAdele p))]
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]]

private theorem central_mul_heckeGenAt_inv_eq_weyl_sandwich (p : Nat.Primes) :
    centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))⁻¹
    = AdelicDock.finEmbed (𝓞 ℚ) ℚ (weylFin (ratPrime p))
      * heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ (weylFin (ratPrime p)) := by
  rw [← finEmbed_scalar_eq_centralScalar]
  refine glpair_ext ?_ ?_
  · rw [map_mul, map_mul, map_mul, map_inv, AdelicDock.glArch_finEmbed,
      AdelicDock.glArch_finEmbed, glArch_heckeGenAt]
    simp
  · rw [map_mul, map_mul, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      AdelicDock.glFin_finEmbed]
    rw [mul_inv_eq_iff_eq_mul, mul_assoc]
    exact (weylGen_sq p).symm

end S5SupplyKey
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section S5F4Supply

private theorem glArch_heckeGenAt_unit (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (t : ((v.adicCompletion ℚ))ˣ) :
    glArch (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ v t) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one]
  exact heckeGenAt_fst t i j

private theorem finComponent_glFin_mem_integralSubgroup
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) {L : Ideal (𝓞 ℚ)}
    {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hg : g ∈ levelOne (𝓞 ℚ) ℚ L) :
    finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ g)
      ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) := by
  have h := mem_levelOne_iff.mp hg
  have h1 := (mem_finiteLevelOne_iff.mp h).1.integral
  have h2 := (mem_finiteLevelOne_iff.mp h).2.integral
  rw [FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem
    (IsFractionRing.injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))]
  refine ⟨fun i j => ⟨⟨_, h1 i j v⟩, rfl⟩, fun i j => ?_⟩
  rw [← map_inv]
  exact ⟨⟨_, h2 i j v⟩, rfl⟩

private theorem finComponent_glFin_heckeGenAt_of_ne (p : Nat.Primes)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime p) :
    finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ
      (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one]
  exact heckeGenAt_snd_apply_of_ne (pUnit p) hw i j

private theorem hpInt_ne (p : Nat.Primes) :
    algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
      (pInt p) ≠ 0 :=
  (pUnit p).ne_zero

private theorem finComponent_glFin_heckeGenAt_self (p : Nat.Primes) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
        (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      = LocalGL2.diagPi (pInt p) (hpInt_ne p) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hL : (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
        (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))) :
        Matrix (Fin 2) (Fin 2) ((ratPrime p).adicCompletion ℚ)) i j
      = ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 (ratPrime p) := rfl
  rw [hL, heckeGenAt_snd_apply_self (pUnit p) i j, LocalGL2.coe_diagPi]
  fin_cases i <;> fin_cases j <;> rfl

private theorem finComponent_mul_gen_mem_heckeMulSet (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ levelOne (𝓞 ℚ) ℚ L) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
        (u * heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      ∈ LocalGL2.heckeMulSet (pInt p) (hpInt_ne p) := by
  rw [map_mul, map_mul]
  exact (LocalGL2.mem_heckeMulSet_iff _ _).mpr
    ⟨finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ u),
      finComponent_glFin_mem_integralSubgroup (ratPrime p) hu,
      by rw [finComponent_glFin_heckeGenAt_self]⟩

private theorem glFin_globalPoints_apply_place (γ : GL (Fin 2) ℚ) (i j : Fin 2)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
      = algebraMap ℚ (w.adicCompletion ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) :=
  congrArg (fun f : ℚ →+* w.adicCompletion ℚ => f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j))
    (by apply RingHom.ext_rat :
      ((finAdeleEval (𝓞 ℚ) ℚ w).comp
          ((RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
            (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))))
        = algebraMap ℚ (w.adicCompletion ℚ))

private theorem upperTriQ_uni_mul (b c : ℚ) :
    upperTriQ 1 b 1 one_ne_zero one_ne_zero * upperTriQ 1 c 1 one_ne_zero one_ne_zero
      = upperTriQ 1 (b + c) 1 one_ne_zero one_ne_zero := by
  refine Units.ext ?_
  rw [Units.val_mul]
  show (!![(1 : ℚ), b; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) * !![(1 : ℚ), c; 0, 1]
      = !![(1 : ℚ), b + c; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperTriQ_uni_inv (b : ℚ) :
    (upperTriQ 1 b 1 one_ne_zero one_ne_zero)⁻¹
      = upperTriQ 1 (-b) 1 one_ne_zero one_ne_zero := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [upperTriQ_uni_mul, add_neg_cancel]
  refine Units.ext ?_
  show (!![(1 : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem isLevelOneMatrix_glFin_globalPoints_uniQ (b : ℚ)
    (hb : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      algebraMap ℚ (w.adicCompletion ℚ) b ∈ w.adicCompletionIntegers ℚ)
    {L : Ideal (𝓞 ℚ)} :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L
      ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
  · rw [glFin_globalPoints_apply_place]
    fin_cases i <;> fin_cases j
    · show algebraMap ℚ (w.adicCompletion ℚ) (1 : ℚ) ∈ w.adicCompletionIntegers ℚ
      rw [map_one]
      exact one_mem _
    · exact hb w
    · show algebraMap ℚ (w.adicCompletion ℚ) (0 : ℚ) ∈ w.adicCompletionIntegers ℚ
      rw [map_zero]
      exact zero_mem _
    · show algebraMap ℚ (w.adicCompletion ℚ) (1 : ℚ) ∈ w.adicCompletionIntegers ℚ
      rw [map_one]
      exact one_mem _
  · rw [show (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w
      = ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 w from rfl,
      glFin_globalPoints_apply_place,
      show ((upperTriQ 1 b 1 one_ne_zero one_ne_zero : Matrix (Fin 2) (Fin 2) ℚ) 1 0)
        = (0 : ℚ) from rfl, map_zero, map_zero]
    exact zero_le'
  · rw [show (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) w
      = finAdeleEval (𝓞 ℚ) ℚ w (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
      map_sub, map_one, finAdeleEval_apply, glFin_globalPoints_apply_place,
      show ((upperTriQ 1 b 1 one_ne_zero one_ne_zero : Matrix (Fin 2) (Fin 2) ℚ) 1 1)
        = (1 : ℚ) from rfl, map_one, sub_self, map_zero]
    exact zero_le'

private theorem glFin_globalPoints_uniQ_mem_finiteLevelOne (b : ℚ)
    (hb : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      algebraMap ℚ (w.adicCompletion ℚ) b ∈ w.adicCompletionIntegers ℚ)
    {L : Ideal (𝓞 ℚ)} :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ 1 b 1 one_ne_zero one_ne_zero))
      ∈ finiteLevelOne (𝓞 ℚ) ℚ L := by
  refine mem_finiteLevelOne_iff.mpr ⟨isLevelOneMatrix_glFin_globalPoints_uniQ b hb, ?_⟩
  rw [← map_inv, ← map_inv, upperTriQ_uni_inv]
  exact isLevelOneMatrix_glFin_globalPoints_uniQ (-b)
    (fun w => by rw [map_neg]; exact neg_mem (hb w))

private theorem uniQ_mem_U (n : ℕ) {L : Ideal (𝓞 ℚ)} :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero))) ∈ h4pins.U L := by
  rw [productionPinsCompact_U, Subgroup.mem_inf]
  exact ⟨(AdelicDock.finEmbed_mem_levelOne_iff _ _ _).mpr
      (glFin_globalPoints_uniQ_mem_finiteLevelOne _
        (fun w => by rw [map_neg]; exact neg_mem (natInt w n).2)),
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _)⟩

private theorem finComponent_glFin_globalPoints_uniQ_self (p : Nat.Primes) (n : ℕ) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
      = LocalGL2.unipotentInt ((ratPrime p).adicCompletion ℚ)
          (-(natInt (ratPrime p) n)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [show ((finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero))) :
      Matrix (Fin 2) (Fin 2) ((ratPrime p).adicCompletion ℚ)) i j)
      = ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ 1 (-((n : ℕ) : ℚ)) 1
          one_ne_zero one_ne_zero)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j)
        (ratPrime p) from rfl,
    glFin_globalPoints_apply_place]
  fin_cases i <;> fin_cases j
  · show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (1 : ℚ)
      = algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
          (1 : (ratPrime p).adicCompletionIntegers ℚ)
    rw [map_one, map_one]
  · show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (-((n : ℕ) : ℚ))
      = algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
          (-(natInt (ratPrime p) n))
    rw [map_neg, map_neg]
    rfl
  · show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (0 : ℚ)
      = algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
          (0 : (ratPrime p).adicCompletionIntegers ℚ)
    rw [map_zero, map_zero]
  · show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (1 : ℚ)
      = algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
          (1 : (ratPrime p).adicCompletionIntegers ℚ)
    rw [map_one, map_one]

private theorem finComponent_glFin_repsFin_self (p : Nat.Primes) (n : ℕ) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
        * heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      = LocalGL2.localRepSome (pInt p) (hpInt_ne p) (-(natInt (ratPrime p) n)) := by
  rw [map_mul, map_mul, AdelicDock.glFin_finEmbed, finComponent_glFin_heckeGenAt_self,
    finComponent_glFin_globalPoints_uniQ_self]
  rfl

private theorem isLevelOneMatrix_of_eq_off_of_integral_at
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) {L : Ideal (𝓞 ℚ)}
    (hLbot : L ≠ ⊥) (hvL : ¬ v.asIdeal ∣ L)
    {Z Y : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hY : IsLevelOneMatrix (𝓞 ℚ) ℚ L (Y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (hoff : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      finComponent (𝓞 ℚ) ℚ w Z = finComponent (𝓞 ℚ) ℚ w Y)
    (hat : finComponent (𝓞 ℚ) ℚ v Z
      ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L (Z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hent : ∀ (i j : Fin 2) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)), w ≠ v →
      ((Z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((Y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w :=
    fun i j w hw => congrArg (fun u : GL (Fin 2) (w.adicCompletion ℚ) =>
      (u : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) (hoff w hw)
  have hatv : ∀ i j : Fin 2,
      ((Z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) v
        ∈ v.adicCompletionIntegers ℚ := by
    intro i j
    obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup hat i j
    rw [show ((Z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) v
        = (finComponent (𝓞 ℚ) ℚ v Z :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j from rfl, ← hr]
    exact r.2
  have hsub : ∀ (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
      ((M 1 1 - 1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) w = (M 1 1) w - 1 := fun M w => by
    rw [show ((M 1 1 - 1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) w
        = finAdeleEval (𝓞 ℚ) ℚ w (M 1 1 - 1) from rfl, map_sub, map_one, finAdeleEval_apply]
  refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
  · by_cases hw : w = v
    · subst hw; exact hatv i j
    · rw [hent i j w hw]; exact hY.integral i j w
  · by_cases hw : w = v
    · subst hw
      rw [idealBound_eq_one_of_not_dvd hLbot hvL]
      exact (mem_adicCompletionIntegers _ _ _).mp (hatv 1 0)
    · rw [hent 1 0 w hw]; exact hY.lowerLeft w
  · by_cases hw : w = v
    · subst hw
      rw [hsub, idealBound_eq_one_of_not_dvd hLbot hvL]
      exact (mem_adicCompletionIntegers _ _ _).mp (sub_mem (hatv 1 1) (one_mem _))
    · rw [hsub, hent 1 1 w hw, ← hsub]; exact hY.lowerRight w

private theorem finComponent_glFin_central_of_ne (p : Nat.Primes)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime p) :
    finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ
      (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))))) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one]
  show ((Matrix.scalar (Fin 2) (((Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ)) i j).2) w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    show ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1
    exact localUnit_apply_of_ne (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) hw
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    show ((0 : AdeleRing (𝓞 ℚ) ℚ).2) w = 0
    rfl

private theorem finComponent_glFin_central_self_val (p : Nat.Primes) :
    (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ
        (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))))) :
        Matrix (Fin 2) (Fin 2) ((ratPrime p).adicCompletion ℚ))
      = !![(pUnit p : (ratPrime p).adicCompletion ℚ), 0;
          0, (pUnit p : (ratPrime p).adicCompletion ℚ)] := by
  ext i j : 1
  show ((Matrix.scalar (Fin 2) (((Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ)) i j).2) (ratPrime p) = _
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    have : ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) (ratPrime p) = (pUnit p : (ratPrime p).adicCompletion ℚ) :=
      localUnit_apply_self (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
    rw [show ((((Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) :
        (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ) from rfl, this]
    fin_cases i <;> rfl
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
    have h0 : ((0 : AdeleRing (𝓞 ℚ) ℚ).2) (ratPrime p)
        = (0 : (ratPrime p).adicCompletion ℚ) := rfl
    rw [h0]
    fin_cases i <;> fin_cases j <;> simp_all

private theorem glArch_central (p : Nat.Primes) :
    glArch (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one]
  show ((Matrix.scalar (Fin 2) (((Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ)) i j).1) = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact finIncl_apply_fst (𝓞 ℚ) ℚ _
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rfl

private theorem finComponent_glFin_repsLast_self (p : Nat.Primes) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
      (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
          (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
        * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))⁻¹))
      = LocalGL2.localRepInf (pInt p) (hpInt_ne p) := by
  rw [map_mul, map_mul, map_inv, map_inv, finComponent_glFin_heckeGenAt_self]
  refine Units.ext ?_
  rw [Units.val_mul, finComponent_glFin_central_self_val, LocalGL2.coe_diagPi_inv,
    LocalGL2.coe_localRepInf,
    show (algebraMap ((ratPrime p).adicCompletionIntegers ℚ)
        ((ratPrime p).adicCompletion ℚ) (pInt p))
      = (pUnit p : (ratPrime p).adicCompletion ℚ) from rfl,
    Matrix.mul_fin_two]
  simp only [mul_zero, zero_mul, mul_one, add_zero, zero_add,
    mul_inv_cancel₀ (pUnit p).ne_zero]

private theorem mem_U_of_arch_off_at (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hLbot : L ≠ ⊥) (hvL : ¬ (ratPrime p).asIdeal ∣ L)
    {T y : AdelicGL2 (𝓞 ℚ) ℚ} (hy : y ∈ h4pins.U L)
    (harch : glArch (𝓞 ℚ) ℚ T = 1)
    (hoff : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w ≠ ratPrime p →
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T) = finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ y))
    (hat : finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ T)
      ∈ LocalGL2.integralSubgroup ((ratPrime p).adicCompletionIntegers ℚ)
          ((ratPrime p).adicCompletion ℚ)) :
    T ∈ h4pins.U L := by
  have hyL : glFin (𝓞 ℚ) ℚ y ∈ finiteLevelOne (𝓞 ℚ) ℚ L := by
    rw [productionPinsCompact_U, Subgroup.mem_inf] at hy
    exact mem_levelOne_iff.mp hy.1
  rw [productionPinsCompact_U, Subgroup.mem_inf]
  refine ⟨mem_levelOne_iff.mpr (mem_finiteLevelOne_iff.mpr ⟨?_, ?_⟩),
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr harch⟩
  · exact isLevelOneMatrix_of_eq_off_of_integral_at (ratPrime p) hLbot hvL
      (mem_finiteLevelOne_iff.mp hyL).1 hoff hat
  · refine isLevelOneMatrix_of_eq_off_of_integral_at (ratPrime p) hLbot hvL
      (mem_finiteLevelOne_iff.mp hyL).2 (fun w hw => ?_) ?_
    · simp only [map_inv]
      rw [hoff w hw]
    · rw [map_inv]
      exact inv_mem hat

private theorem mk_eq_mk_of_transfer (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hLbot : L ≠ ⊥) (hvL : ¬ (ratPrime p).asIdeal ∣ L)
    {z r y : AdelicGL2 (𝓞 ℚ) ℚ} (hy : y ∈ h4pins.U L)
    (harch : glArch (𝓞 ℚ) ℚ (z⁻¹ * r) = 1)
    (hoff : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w ≠ ratPrime p →
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (z⁻¹ * r))
        = finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ y))
    (hat : (QuotientGroup.mk (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ z)) :
          _ ⧸ LocalGL2.integralSubgroup ((ratPrime p).adicCompletionIntegers ℚ)
            ((ratPrime p).adicCompletion ℚ))
        = QuotientGroup.mk (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ r))) :
    (QuotientGroup.mk z : _ ⧸ h4pins.U L) = QuotientGroup.mk r := by
  refine QuotientGroup.eq.mpr (mem_U_of_arch_off_at p hLbot hvL hy harch hoff ?_)
  have h2 := QuotientGroup.eq.mp hat
  have he : finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (z⁻¹ * r))
      = (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ z))⁻¹
        * finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ r) := by
    rw [map_mul, map_mul, map_inv, map_inv]
  rw [he]
  exact h2

private theorem mk_loc_eq_of_mk_eq (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    {a b : AdelicGL2 (𝓞 ℚ) ℚ}
    (h : (QuotientGroup.mk a : _ ⧸ h4pins.U L) = QuotientGroup.mk b) :
    (QuotientGroup.mk (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ a)) :
        _ ⧸ LocalGL2.integralSubgroup ((ratPrime p).adicCompletionIntegers ℚ)
          ((ratPrime p).adicCompletion ℚ))
      = QuotientGroup.mk (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ b)) := by
  have hmem := QuotientGroup.eq.mp h
  have hL : a⁻¹ * b ∈ levelOne (𝓞 ℚ) ℚ L := by
    rw [productionPinsCompact_U, Subgroup.mem_inf] at hmem
    exact hmem.1
  have hint := finComponent_glFin_mem_integralSubgroup (ratPrime p) hL
  refine QuotientGroup.eq.mpr ?_
  have he : finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (a⁻¹ * b))
      = (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ a))⁻¹
        * finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ b) := by
    rw [map_mul, map_mul, map_inv, map_inv]
  rw [← he]
  exact hint

private theorem pInt_not_dvd_natInt_sub (p : Nat.Primes) {a b : ℕ}
    (ha : a < (p : ℕ)) (hba : b < a) :
    ¬ pInt p ∣ (natInt (ratPrime p) a - natInt (ratPrime p) b) := by
  intro hdvd
  have hsub : natInt (ratPrime p) a - natInt (ratPrime p) b
      = natInt (ratPrime p) (a - b) := by
    refine Subtype.ext ?_
    show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((a : ℕ) : ℚ)
        - algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((b : ℕ) : ℚ)
      = algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (((a - b : ℕ) : ℚ))
    rw [← map_sub]
    congr 1
    rw [Nat.cast_sub hba.le]
  rw [hsub] at hdvd
  have hunit := isUnit_natInt_of_not_dvd p
    (n := a - b) (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  have h1 := valued_eq_one_of_isUnit hunit
  obtain ⟨c, hc⟩ := hdvd
  rw [hc] at h1
  have h2 : Valued.v (((pInt p * c : (ratPrime p).adicCompletionIntegers ℚ))
      : (ratPrime p).adicCompletion ℚ) ≤ WithZero.exp (-1 : ℤ) := by
    rw [show (((pInt p * c : (ratPrime p).adicCompletionIntegers ℚ))
        : (ratPrime p).adicCompletion ℚ)
        = ((pInt p : (ratPrime p).adicCompletionIntegers ℚ)
            : (ratPrime p).adicCompletion ℚ)
          * ((c : (ratPrime p).adicCompletionIntegers ℚ)
            : (ratPrime p).adicCompletion ℚ) from rfl,
      Valuation.map_mul, valued_pInt]
    calc WithZero.exp (-1 : ℤ) * Valued.v ((c : (ratPrime p).adicCompletionIntegers ℚ)
          : (ratPrime p).adicCompletion ℚ)
        ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul' le_rfl (valued_adicInt_le_one c)
      _ = WithZero.exp (-1 : ℤ) := mul_one _
  rw [h1, ← WithZero.exp_zero] at h2
  have := withZero_exp_le_exp.mp h2
  omega

end S5F4Supply
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section S7Supply

private theorem upperTriQ_one_j_inv_eq (j p : ℕ) (hp : 0 < p) :
    (upperTriQ 1 (j : ℚ) (p : ℚ) one_ne_zero (by exact_mod_cast hp.ne'))⁻¹
      = (Matrix.GeneralLinearGroup.scalar (Fin 2) (ratUnit p hp))⁻¹
        * upperTriQ 1 (-(j : ℚ)) 1 one_ne_zero one_ne_zero
        * upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.ne') one_ne_zero := by
  have key : upperTriQ 1 (-(j : ℚ)) 1 one_ne_zero one_ne_zero
      * upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.ne') one_ne_zero
      * upperTriQ 1 (j : ℚ) (p : ℚ) one_ne_zero (by exact_mod_cast hp.ne')
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (ratUnit p hp) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    show (!![(1 : ℚ), -(j : ℚ); 0, 1] * !![(p : ℚ), 0; 0, 1]) * !![(1 : ℚ), (j : ℚ); 0, (p : ℚ)]
      = ((Matrix.GeneralLinearGroup.scalar (Fin 2) (ratUnit p hp) :
          GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i jj => ?_
    rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (ratUnit p hp) :
        GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = Matrix.diagonal (fun _ => (p : ℚ)) from by
        rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (ratUnit p hp) :
            GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
          = Matrix.scalar (Fin 2) ((p : ℚ)) from rfl, Matrix.scalar_apply]]
    fin_cases i <;> fin_cases jj <;>
      (simp; try ring)
  rw [← key]
  group

private theorem isUnit_natInt_p_of_ne (p : ℕ) (hp : p.Prime)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime ⟨p, hp⟩) :
    IsUnit (natInt w p) := by
  obtain ⟨q, rfl⟩ : ∃ q : Nat.Primes, ratPrime q = w :=
    ⟨Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w,
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply w⟩
  refine isUnit_natInt_of_not_dvd q fun hdvd => hw ?_
  have hqp : (q : ℕ) = p :=
    (Nat.prime_dvd_prime_iff_eq q.2 hp).mp hdvd
  exact congrArg ratPrime (Subtype.ext hqp)

private theorem finComponent_glFin_globalPoints_diag_self (p : ℕ) (hp : p.Prime) :
    finComponent (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      = LocalGL2.diagPi (pInt ⟨p, hp⟩) (hpInt_ne ⟨p, hp⟩) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [show ((finComponent (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero))) :
      Matrix (Fin 2) (Fin 2) ((ratPrime ⟨p, hp⟩).adicCompletion ℚ)) i j)
      = ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ (p : ℚ) 0 1
          (by exact_mod_cast hp.pos.ne') one_ne_zero)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) (ratPrime ⟨p, hp⟩) from rfl,
    glFin_globalPoints_apply_place]
  fin_cases i <;> fin_cases j
  · show algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) ((p : ℚ))
      = algebraMap ((ratPrime ⟨p, hp⟩).adicCompletionIntegers ℚ)
          ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) (pInt ⟨p, hp⟩)
    rfl
  · show algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) (0 : ℚ)
      = algebraMap ((ratPrime ⟨p, hp⟩).adicCompletionIntegers ℚ)
          ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) 0
    rw [map_zero, map_zero]
  · show algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) (0 : ℚ)
      = algebraMap ((ratPrime ⟨p, hp⟩).adicCompletionIntegers ℚ)
          ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) 0
    rw [map_zero, map_zero]
  · show algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) (1 : ℚ)
      = algebraMap ((ratPrime ⟨p, hp⟩).adicCompletionIntegers ℚ)
          ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) 1
    rw [map_one, map_one]

private noncomputable def diagUnitAt (p : ℕ) (hp : p.Prime)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime ⟨p, hp⟩) :
    GL (Fin 2) (w.adicCompletion ℚ) :=
  ⟨!![algebraMap ℚ (w.adicCompletion ℚ) ((p : ℚ)), 0; 0, 1],
    !![((((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
        w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ), 0; 0, 1],
    by
      have h2 : (natInt w p)
          * (((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
            w.adicCompletionIntegers ℚ) = 1 :=
        (isUnit_natInt_p_of_ne p hp hw).mul_val_inv
      have h1 : algebraMap ℚ (w.adicCompletion ℚ) ((p : ℚ))
          * ((((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
              w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ) = 1 := by
        have h3 := congrArg
          (fun x : w.adicCompletionIntegers ℚ => (x : w.adicCompletion ℚ)) h2
        exact h3
      rw [Matrix.mul_fin_two]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp <;> simpa using h1
    , by
      have h2 : (((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
            w.adicCompletionIntegers ℚ) * (natInt w p) = 1 :=
        (isUnit_natInt_p_of_ne p hp hw).val_inv_mul
      have h1 : ((((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
              w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ)
          * algebraMap ℚ (w.adicCompletion ℚ) ((p : ℚ)) = 1 := by
        have h3 := congrArg
          (fun x : w.adicCompletionIntegers ℚ => (x : w.adicCompletion ℚ)) h2
        exact h3
      rw [Matrix.mul_fin_two]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp <;> simpa using h1⟩

private theorem finComponent_glFin_globalPoints_diag_of_ne (p : ℕ) (hp : p.Prime)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime ⟨p, hp⟩) :
    finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      = diagUnitAt p hp hw := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [show ((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero))) :
      Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j)
      = ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ (p : ℚ) 0 1
          (by exact_mod_cast hp.pos.ne') one_ne_zero)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w from rfl,
    glFin_globalPoints_apply_place]
  fin_cases i <;> fin_cases j
  · rfl
  · show algebraMap ℚ (w.adicCompletion ℚ) (0 : ℚ) = 0
    rw [map_zero]
  · show algebraMap ℚ (w.adicCompletion ℚ) (0 : ℚ) = 0
    rw [map_zero]
  · show algebraMap ℚ (w.adicCompletion ℚ) (1 : ℚ) = 1
    rw [map_one]

private theorem heckeGenAt_inv_mul_finEmbed_global_diag_mem_U (p : ℕ) (hp : p.Prime)
    (L : Ideal (𝓞 ℚ)) :
    (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      ∈ h4pins.U L := by

  have hcompv : finComponent (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (glFin (𝓞 ℚ) ℚ
      ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
        * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
            (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero))))) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      finComponent_glFin_heckeGenAt_self,
      finComponent_glFin_globalPoints_diag_self p hp]
    exact inv_mul_cancel _
  have hcompw : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      ∀ hw : w ≠ ratPrime ⟨p, hp⟩,
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ
        ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))))
        = diagUnitAt p hp hw := by
    intro w hw
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      finComponent_glFin_heckeGenAt_of_ne ⟨p, hp⟩ hw,
      finComponent_glFin_globalPoints_diag_of_ne p hp hw]
    rw [inv_one, one_mul]

  rw [productionPinsCompact_U, Subgroup.mem_inf]
  set T : AdelicGL2 (𝓞 ℚ) ℚ :=
    (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero))) with hT
  have hcomp : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ∀ i j : Fin 2,
      ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T) :
            Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) := fun w i j => rfl
  have hcompinv : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ∀ i j : Fin 2,
      ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T))⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) := fun w i j => by
    rw [show ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((finComponent (𝓞 ℚ) ℚ w ((glFin (𝓞 ℚ) ℚ T)⁻¹) :
            Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) from rfl, map_inv]
  constructor
  · refine mem_levelOne_iff.mpr (mem_finiteLevelOne_iff.mpr ⟨?_, ?_⟩)
    ·
      refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · rw [hcomp w i j]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          fin_cases i <;> fin_cases j <;>
            simp only [Units.val_one, Matrix.one_apply_eq, Matrix.one_apply] <;>
            first
            | exact one_mem _
            | exact zero_mem _
        · rw [hcompw w hw]
          fin_cases i <;> fin_cases j
          · exact (natInt w (p : ℕ)).2
          · exact zero_mem _
          · exact zero_mem _
          · exact one_mem _
      · rw [show (((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0)) w
          = ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w
          from rfl, hcomp w 1 0]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          simp only [Units.val_one, Matrix.one_apply_ne one_ne_zero, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v (0 : w.adicCompletion ℚ) ≤ _
          rw [map_zero]
          exact zero_le'
      · rw [show (((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1)) w
          = finAdeleEval (𝓞 ℚ) ℚ w ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
          map_sub, map_one, finAdeleEval_apply, hcomp w 1 1]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          simp only [Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v ((1 : w.adicCompletion ℚ) - 1) ≤ _
          rw [sub_self, map_zero]
          exact zero_le'
    ·
      refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · rw [hcompinv w i j]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          fin_cases i <;> fin_cases j <;>
            simp only [Units.val_one, Matrix.one_apply] <;>
            (split <;> first | exact one_mem _ | exact zero_mem _)
        · rw [hcompw w hw]
          fin_cases i <;> fin_cases j
          · exact (((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ :
              (w.adicCompletionIntegers ℚ)ˣ) : w.adicCompletionIntegers ℚ).2
          · exact zero_mem _
          · exact zero_mem _
          · exact one_mem _
      · rw [show (((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0)) w
          = ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w from rfl,
          hcompinv w 1 0]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          simp only [Units.val_one, Matrix.one_apply_ne one_ne_zero, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v (0 : w.adicCompletion ℚ) ≤ _
          rw [map_zero]
          exact zero_le'
      · rw [show (((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1)) w
          = finAdeleEval (𝓞 ℚ) ℚ w ((((glFin (𝓞 ℚ) ℚ T)⁻¹ :
              GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
          map_sub, map_one, finAdeleEval_apply, hcompinv w 1 1]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          simp only [Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v ((1 : w.adicCompletion ℚ) - 1) ≤ _
          rw [sub_self, map_zero]
          exact zero_le'
  ·
    refine (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr ?_
    rw [map_mul, map_inv, glArch_heckeGenAt_unit (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩),
      AdelicDock.glArch_finEmbed, inv_one, one_mul]

private theorem heckeGenAt_inv_mul_finEmbed_global_diag_mem_U_inst :
    (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨5, by norm_num⟩) (pUnit ⟨5, by norm_num⟩))⁻¹
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ (5 : ℚ) 0 1 (by norm_num) one_ne_zero)))
      ∈ h4pins.U (Ideal.span {(3 : 𝓞 ℚ)}) := by
  have h5 : ((5 : ℕ) : ℚ) = (5 : ℚ) := by norm_num
  have := heckeGenAt_inv_mul_finEmbed_global_diag_mem_U 5 (by norm_num)
    (Ideal.span {(3 : 𝓞 ℚ)})
  simpa [h5] using this

private theorem chiNegThree_mul_self_of_not_dvd {n : ℕ} (h : ¬ (3 : ℕ) ∣ n) :
    chiNegThree n * chiNegThree n = 1 := by
  unfold chiNegThree
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · exfalso; omega

private theorem centralScalar_finIncl_residue_mem_U (p : ℕ) (hp : p.Prime)
    (L : Ideal (𝓞 ℚ)) (hL : L ≠ ⊥) (hpN : ¬ p ∣ Ideal.absNorm L) :
    centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
      (finRatUnit (ratUnit p hp.pos)
        * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
        * (epsUnitHom hL (ratUnit p hp.pos))⁻¹))
      ∈ h4pins.U L := by
  classical
  obtain ⟨hvL, hLbot⟩ := ratPrime_not_dvd_of_not_dvd_absNorm ⟨p, hp⟩ hpN
  have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hbv : idealBound (𝓞 ℚ) L (ratPrime ⟨p, hp⟩) = 1 :=
    idealBound_eq_one_of_not_dvd hL hvL

  have hval : ∀ w' : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      (((finRatUnit (ratUnit p hp.pos)
          * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * (epsUnitHom hL (ratUnit p hp.pos))⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ)) w'
      = if w' = ratPrime ⟨p, hp⟩ then 1
        else if idealBound (𝓞 ℚ) L w' ≠ 1 then 1
        else algebraMap ℚ (w'.adicCompletion ℚ) ((p : ℚ)) := by
    intro w'
    rw [← map_inv (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩)) (pUnit ⟨p, hp⟩),
      ← map_inv (epsUnitHom hL) (ratUnit p hp.pos),
      Units.val_mul, Units.val_mul, coe_mul_apply, coe_mul_apply,
      finRatUnit_val, ratUnit_val, epsUnitHom_apply,
      Units.val_inv_eq_inv_val, ratUnit_val]
    by_cases hwv : w' = ratPrime ⟨p, hp⟩
    · subst hwv
      rw [if_pos rfl, localUnit_apply_self,
        if_neg (fun hcon => hcon hbv), mul_one, Units.val_inv_eq_inv_val,
        show ((pUnit ⟨p, hp⟩ : ((ratPrime ⟨p, hp⟩).adicCompletion ℚ)ˣ) :
            (ratPrime ⟨p, hp⟩).adicCompletion ℚ)
          = algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) ((p : ℚ)) from rfl]
      exact mul_inv_cancel₀ ((map_ne_zero _).mpr hp0)
    · rw [if_neg hwv,
        localUnit_apply_of_ne (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)⁻¹ hwv, mul_one]
      by_cases hb : idealBound (𝓞 ℚ) L w' ≠ 1
      · rw [if_pos hb, if_pos hb, ← map_mul, mul_inv_cancel₀ hp0, map_one]
      · rw [if_neg hb, if_neg hb, mul_one]

  have hvalinv : ∀ w' : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      ((((finRatUnit (ratUnit p hp.pos)
          * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * (epsUnitHom hL (ratUnit p hp.pos))⁻¹)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ)) w'
      = if w' = ratPrime ⟨p, hp⟩ then 1
        else if idealBound (𝓞 ℚ) L w' ≠ 1 then 1
        else algebraMap ℚ (w'.adicCompletion ℚ) (((p : ℚ))⁻¹) := by
    intro w'
    rw [show (finRatUnit (ratUnit p hp.pos)
          * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * (epsUnitHom hL (ratUnit p hp.pos))⁻¹)⁻¹
        = epsUnitHom hL (ratUnit p hp.pos)
          * localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
          * (finRatUnit (ratUnit p hp.pos))⁻¹ from by group,
      ← map_inv finRatUnit (ratUnit p hp.pos),
      Units.val_mul, Units.val_mul, coe_mul_apply, coe_mul_apply,
      epsUnitHom_apply, finRatUnit_val, Units.val_inv_eq_inv_val, ratUnit_val]
    by_cases hwv : w' = ratPrime ⟨p, hp⟩
    · subst hwv
      rw [if_pos rfl, if_neg (fun hcon => hcon hbv), localUnit_apply_self, one_mul,
        show ((pUnit ⟨p, hp⟩ : ((ratPrime ⟨p, hp⟩).adicCompletion ℚ)ˣ) :
            (ratPrime ⟨p, hp⟩).adicCompletion ℚ)
          = algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) ((p : ℚ)) from rfl,
        ← map_mul, mul_inv_cancel₀ hp0, map_one]
    · rw [if_neg hwv,
        localUnit_apply_of_ne (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) hwv]
      by_cases hb : idealBound (𝓞 ℚ) L w' ≠ 1
      · rw [if_pos hb, if_pos hb, mul_one, ← map_mul, mul_inv_cancel₀ hp0, map_one]
      · rw [if_neg hb, if_neg hb, one_mul, one_mul]

  have hbridge : ∀ (w'' : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
      (hw : w'' ≠ ratPrime ⟨p, hp⟩),
      algebraMap ℚ (w''.adicCompletion ℚ) (((p : ℚ))⁻¹)
        = ((((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w''.adicCompletionIntegers ℚ)ˣ) :
            w''.adicCompletionIntegers ℚ) : w''.adicCompletion ℚ) := by
    intro w'' hw
    have h2 : (natInt w'' p)
        * (((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w''.adicCompletionIntegers ℚ)ˣ) :
          w''.adicCompletionIntegers ℚ) = 1 :=
      (isUnit_natInt_p_of_ne p hp hw).mul_val_inv
    have h1 : algebraMap ℚ (w''.adicCompletion ℚ) ((p : ℚ))
        * ((((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w''.adicCompletionIntegers ℚ)ˣ) :
            w''.adicCompletionIntegers ℚ) : w''.adicCompletion ℚ) = 1 := by
      have h3 := congrArg
        (fun x : w''.adicCompletionIntegers ℚ => (x : w''.adicCompletion ℚ)) h2
      exact h3
    rw [map_inv₀]
    exact inv_eq_of_mul_eq_one_right h1

  have hruInt : (((finRatUnit (ratUnit p hp.pos)
      * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      * (epsUnitHom hL (ratUnit p hp.pos))⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro w''
    rw [hval w'']
    split_ifs
    · exact one_mem _
    · exact one_mem _
    · exact (natInt w'' p).2
  have hruInvInt : ((((finRatUnit (ratUnit p hp.pos)
      * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      * (epsUnitHom hL (ratUnit p hp.pos))⁻¹)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro w''
    rw [hvalinv w'']
    split_ifs with h1 h2
    · exact one_mem _
    · exact one_mem _
    · rw [hbridge w'' h1]
      exact ((((isUnit_natInt_p_of_ne p hp h1).unit⁻¹ : (w''.adicCompletionIntegers ℚ)ˣ) :
        w''.adicCompletionIntegers ℚ)).2

  have hzeroBall : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ idealBall (𝓞 ℚ) ℚ L := fun w'' => by
    show Valued.v ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w'') ≤ idealBound (𝓞 ℚ) L w''
    rw [show ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ)) w'' = (0 : w''.adicCompletion ℚ) from rfl,
      map_zero]
    exact zero_le'
  have hruBall : (((finRatUnit (ratUnit p hp.pos)
      * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      * (epsUnitHom hL (ratUnit p hp.pos))⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ)) - 1 ∈ idealBall (𝓞 ℚ) ℚ L := by
    intro w''
    rw [coe_sub_apply, show ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) w'' = 1 from rfl, hval w'']
    by_cases hwv : w'' = ratPrime ⟨p, hp⟩
    · rw [if_pos hwv, sub_self, map_zero]; exact zero_le'
    · rw [if_neg hwv]
      by_cases hb : idealBound (𝓞 ℚ) L w'' ≠ 1
      · rw [if_pos hb, sub_self, map_zero]; exact zero_le'
      · rw [if_neg hb, not_not.mp hb]
        have hint : algebraMap ℚ (w''.adicCompletion ℚ) ((p : ℚ)) - 1
            ∈ w''.adicCompletionIntegers ℚ := sub_mem (natInt w'' p).2 (one_mem _)
        rw [mem_adicCompletionIntegers] at hint
        exact hint
  have hruInvBall : ((((finRatUnit (ratUnit p hp.pos)
      * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      * (epsUnitHom hL (ratUnit p hp.pos))⁻¹)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ)) - 1 ∈ idealBall (𝓞 ℚ) ℚ L := by
    intro w''
    rw [coe_sub_apply, show ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) w'' = 1 from rfl, hvalinv w'']
    by_cases hwv : w'' = ratPrime ⟨p, hp⟩
    · rw [if_pos hwv, sub_self, map_zero]; exact zero_le'
    · rw [if_neg hwv]
      by_cases hb : idealBound (𝓞 ℚ) L w'' ≠ 1
      · rw [if_pos hb, sub_self, map_zero]; exact zero_le'
      · rw [if_neg hb, not_not.mp hb, hbridge w'' hwv]
        have hint : ((((isUnit_natInt_p_of_ne p hp hwv).unit⁻¹ :
            (w''.adicCompletionIntegers ℚ)ˣ) : w''.adicCompletionIntegers ℚ) :
              w''.adicCompletion ℚ) - 1 ∈ w''.adicCompletionIntegers ℚ :=
          sub_mem (((isUnit_natInt_p_of_ne p hp hwv).unit⁻¹ :
            (w''.adicCompletionIntegers ℚ)ˣ) : w''.adicCompletionIntegers ℚ).2 (one_mem _)
        rw [mem_adicCompletionIntegers] at hint
        exact hint

  have hmat : ((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (finRatUnit (ratUnit p hp.pos)
        * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
        * (epsUnitHom hL (ratUnit p hp.pos))⁻¹) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.diagonal (fun _ => (((finRatUnit (ratUnit p hp.pos)
          * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * (epsUnitHom hL (ratUnit p hp.pos))⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2)
        (finRatUnit (ratUnit p hp.pos)
          * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * (epsUnitHom hL (ratUnit p hp.pos))⁻¹) :
          GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        = Matrix.scalar (Fin 2) (((finRatUnit (ratUnit p hp.pos)
            * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
            * (epsUnitHom hL (ratUnit p hp.pos))⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ)) from rfl, Matrix.scalar_apply]
  have hscinv : (Matrix.GeneralLinearGroup.scalar (Fin 2)
      (finRatUnit (ratUnit p hp.pos)
        * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
        * (epsUnitHom hL (ratUnit p hp.pos))⁻¹))⁻¹
      = Matrix.GeneralLinearGroup.scalar (Fin 2)
        ((finRatUnit (ratUnit p hp.pos)
          * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * (epsUnitHom hL (ratUnit p hp.pos))⁻¹)⁻¹) := (map_inv _ _).symm
  have hmatinv : (((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (finRatUnit (ratUnit p hp.pos)
        * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
        * (epsUnitHom hL (ratUnit p hp.pos))⁻¹))⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.diagonal (fun _ => ((((finRatUnit (ratUnit p hp.pos)
          * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * (epsUnitHom hL (ratUnit p hp.pos))⁻¹)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    rw [hscinv,
      show ((Matrix.GeneralLinearGroup.scalar (Fin 2)
        ((finRatUnit (ratUnit p hp.pos)
          * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * (epsUnitHom hL (ratUnit p hp.pos))⁻¹)⁻¹) :
          GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        = Matrix.scalar (Fin 2) ((((finRatUnit (ratUnit p hp.pos)
            * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
            * (epsUnitHom hL (ratUnit p hp.pos))⁻¹)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ)) from rfl, Matrix.scalar_apply]

  rw [← finEmbed_scalar_eq_centralScalar, productionPinsCompact_U, Subgroup.mem_inf]
  refine ⟨(AdelicDock.finEmbed_mem_levelOne_iff _ _ _).mpr ?_,
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _)⟩
  rw [mem_finiteLevelOne_iff]
  constructor
  · refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
    · rw [hmat]
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.diagonal_apply] <;>
        first
        | exact hruInt
        | exact zero_mem_integralFiniteAdeles
    · rw [hmat]
      simp only [Matrix.diagonal_apply]
      rw [if_neg (one_ne_zero : (1 : Fin 2) ≠ 0)]
      exact hzeroBall
    · rw [hmat]
      simp only [Matrix.diagonal_apply]
      rw [if_pos trivial]
      exact hruBall
  · refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
    · rw [hmatinv]
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.diagonal_apply] <;>
        first
        | exact hruInvInt
        | exact zero_mem_integralFiniteAdeles
    · rw [hmatinv]
      simp only [Matrix.diagonal_apply]
      rw [if_neg (one_ne_zero : (1 : Fin 2) ≠ 0)]
      exact hzeroBall
    · rw [hmatinv]
      simp only [Matrix.diagonal_apply]
      rw [if_pos trivial]
      exact hruInvBall

private theorem omegaUnit_finIncl_localUnit_pUnit_H7 (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (hepsval : ∀ (m : ℕ) (hm : 0 < m),
      (∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
        ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
          ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
          ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) →
      ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit m hm))) : ℂˣ) : ℂ)
        = ((chiNegThree m : ℤ) : ℂ))
    (hN3 : 3 ∣ Ideal.absNorm Ψ.level)
    (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ Ideal.absNorm Ψ.level)
    (hpB : ratPrime ⟨p, hp⟩ ∉ R.exceptionalSet)
    (hdet : Ψ.b (ratPrime ⟨p, hp⟩) = ((chiNegThree p : ℤ) : ℂ) * ((p : ℂ))⁻¹) :
    ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))) : ℂˣ) : ℂ)
      = ((p : ℂ))⁻¹ * ((chiNegThree p : ℤ) : ℂ) := by
  have hp3 : p ≠ 3 := fun h => hpN (by rw [h]; exact hN3)
  have h3p : ¬ (3 : ℕ) ∣ p := fun hdvd =>
    hp3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd).symm)
  have hchi2 : ((chiNegThree p : ℤ) : ℂ) * ((chiNegThree p : ℤ) : ℂ) = 1 := by
    exact_mod_cast chiNegThree_mul_self_of_not_dvd h3p

  have heps : ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
      (epsUnitHom Ψ.level_ne_bot (ratUnit p hp.pos))) : ℂˣ) : ℂ)
      = ((chiNegThree p : ℤ) : ℂ) := by
    refine hepsval p hp.pos fun q hq hqdvd => ?_
    obtain rfl : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqdvd
    exact ⟨hpN, hp3, hpB, hdet⟩

  have hres : omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
      (finRatUnit (ratUnit p hp.pos)
        * (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
        * (epsUnitHom Ψ.level_ne_bot (ratUnit p hp.pos))⁻¹)) = 1 :=
    omegaUnit_eq_one_of_centralScalar_mem R
      (centralScalar_finIncl_residue_mem_U p hp Ψ.level Ψ.level_ne_bot hpN)
  simp only [map_mul, map_inv] at hres
  have hFL : omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ) (finRatUnit (ratUnit p hp.pos)))
      = omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit p hp.pos)))
        * omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
            (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))) :=
    mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hres)
  have hFLc := congrArg (fun z : ℂˣ => (z : ℂ)) hFL
  simp only [Units.val_mul] at hFLc
  rw [omegaUnit_finIncl_finRat R w hw homega p hp.pos, heps] at hFLc

  calc ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))) : ℂˣ) : ℂ)
      = (((chiNegThree p : ℤ) : ℂ) * ((chiNegThree p : ℤ) : ℂ))
        * ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
            (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))) : ℂˣ) : ℂ) := by
        rw [hchi2, one_mul]
    _ = ((chiNegThree p : ℤ) : ℂ) * (((chiNegThree p : ℤ) : ℂ)
          * ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))) : ℂˣ) : ℂ)) := by
        rw [mul_assoc]
    _ = ((chiNegThree p : ℤ) : ℂ) * (((p : ℕ) : ℂ))⁻¹ := by rw [← hFLc]
    _ = ((p : ℂ))⁻¹ * ((chiNegThree p : ℤ) : ℂ) := mul_comm _ _

end S7Supply
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section H7Heads

private theorem toFun_arch_iwasawa_upperTriQ (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (a b d : ℚ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    R.toFun (archAt w hw (iwasawaSectionGL
        ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriQ a b d ha.ne' hd.ne')) • τ)))
      = (d : ℂ)⁻¹ * R.toFun (archAt w hw (iwasawaSectionGL τ)
          * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ a b d ha.ne' hd.ne'))))⁻¹) := by
  show R.toFun (archAt w hw (iwasawaSectionGL
        (realOf (upperTriQ a b d ha.ne' hd.ne') • τ)))
      = (d : ℂ)⁻¹ * R.toFun (archAt w hw (iwasawaSectionGL τ)
          * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ a b d ha.ne' hd.ne'))))⁻¹)
  simp only [← iwasawaSec_eq_iwasawaSectionGL]
  have hglob : globalPoints (𝓞 ℚ) ℚ (upperTriQ a b d ha.ne' hd.ne')
        * (archAt w hw (iwasawaSec τ)
          * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ a b d ha.ne' hd.ne'))))⁻¹)
      = adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
            ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
            (Matrix.GeneralLinearGroup.scalar (Fin 2)
              (Units.mk0 ((d : ℝ)) (by exact_mod_cast hd.ne'))))
          * archAt w hw (iwasawaSec (realOf (upperTriQ a b d ha.ne' hd.ne') • τ)) := by
    conv_lhs =>
      lhs
      rw [globalPoints_decomp w hw (upperTriQ a b d ha.ne' hd.ne')]
    rw [mul_mul_mul_inv_cancel_of_comm (archAt w hw (realOf (upperTriQ a b d ha.ne' hd.ne')))
        (archAt_finEmbed_comm w hw (iwasawaSec τ)
          (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ a b d ha.ne' hd.ne')))).symm,
      ← map_mul, realOf_upperTriQ_mul_iwasawaSec a b d ha hd τ, map_mul,
      show archAt w hw (Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.mk0 ((d : ℝ)) (by exact_mod_cast hd.ne' : ((d : ℝ)) ≠ 0)))
          = centralScalar (𝓞 ℚ) ℚ (archIdeleUnit w hw
              (Units.mk0 ((d : ℝ)) (by exact_mod_cast hd.ne')))
        from (centralScalar_archIdeleUnit w hw _).symm,
      ← centralScalar_mul_comm, centralScalar_archIdeleUnit]
  have h0 := SmoothCuspRealizationAt.left_invariant R (upperTriQ a b d ha.ne' hd.ne')
      (archAt w hw (iwasawaSec τ)
        * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
            (upperTriQ a b d ha.ne' hd.ne'))))⁻¹)
  rw [hglob, homega (Units.mk0 ((d : ℝ)) (by exact_mod_cast hd.ne'))
      (by rw [Units.val_mk0]; exact_mod_cast hd)
      (archAt w hw (iwasawaSec (realOf (upperTriQ a b d ha.ne' hd.ne') • τ))),
    show ((((Units.mk0 ((d : ℝ)) (by exact_mod_cast hd.ne' : ((d : ℝ)) ≠ 0)) : ℝˣ) : ℝ) : ℂ)
        = (d : ℂ) by rw [Units.val_mk0]; norm_cast] at h0
  rw [← h0, inv_mul_cancel_left₀ (by exact_mod_cast hd.ne' : ((d : ℂ)) ≠ 0)]

private theorem toFun_mul_finEmbed_scalar_inv (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (m : ℕ) (hm : 0 < m) (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    R.toFun (X * (AdelicDock.finEmbed (𝓞 ℚ) ℚ
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (finRatUnit (ratUnit m hm))))⁻¹)
      = (m : ℂ) * R.toFun X := by
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [finEmbed_scalar_eq_centralScalar]
  have h := omega_spec R (Units.map (finIncl (𝓞 ℚ) ℚ) (finRatUnit (ratUnit m hm)))
      (X * (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) (finRatUnit (ratUnit m hm))))⁻¹)
  rw [← mul_assoc, centralScalar_mul_comm, mul_assoc, mul_inv_cancel, mul_one] at h
  rw [omegaUnit_finIncl_finRat R w hw homega m hm] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]

private theorem isHeckeCosetSystem_heckeReps (p : ℕ) (hp : p.Prime)
    (L : Ideal (𝓞 ℚ)) (hpN : ¬ p ∣ Ideal.absNorm L) :
    HeckeIntegralSeam.IsHeckeCosetSystem (h4pins.U L)
      (h4pins.gen (ratPrime ⟨p, hp⟩)) (heckeReps p hp) := by
  obtain ⟨hvL, hLbot⟩ := ratPrime_not_dvd_of_not_dvd_absNorm ⟨p, hp⟩ hpN
  have hAN : Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal = p := by rw [absNorm_ratPrime]
  have hpc : ((⟨p, hp⟩ : Nat.Primes) : ℕ) = p := rfl
  have hseam : (h4pins.gen (ratPrime ⟨p, hp⟩))⁻¹
      * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) ∈ h4pins.U L := by
    rw [productionPinsCompact_U, productionPinsCompact_gen, Subgroup.mem_inf]
    have harch : glArch (𝓞 ℚ) ℚ (heckeGen (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩)) = 1 :=
      glArch_heckeGenAt_unit (ratPrime ⟨p, hp⟩) (uniformizerUnit ℚ (ratPrime ⟨p, hp⟩))
    refine ⟨heckeGen_inv_mul_heckeGenAt_mem_levelOne _ (valued_pUnit ⟨p, hp⟩) L, ?_⟩
    refine (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr ?_
    rw [map_mul, map_inv, harch, glArch_heckeGenAt_unit, inv_one, one_mul]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i
    by_cases hi : (i : ℕ) < p
    · rw [show heckeReps p hp i
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
        simp only [heckeReps]; rw [if_pos hi]]
      exact HeckePair.mem_doubleCoset_iff.mpr
        ⟨_, uniQ_mem_U (i : ℕ), _, hseam, by group⟩
    · rw [show heckeReps p hp i
          = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ from by
        simp only [heckeReps]; rw [if_neg hi],
        central_mul_heckeGenAt_inv_eq_weyl_sandwich ⟨p, hp⟩]
      exact HeckePair.mem_doubleCoset_iff.mpr
        ⟨_, weylV_mem_U ⟨p, hp⟩ hpN, _, mul_mem hseam (weylV_mem_U ⟨p, hp⟩ hpN), by group⟩
  ·
    intro x hx
    obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    have huL : u ∈ levelOne (𝓞 ℚ) ℚ L := by
      rw [productionPinsCompact_U, Subgroup.mem_inf] at hu
      exact hu.1
    have huA : glArch (𝓞 ℚ) ℚ u = 1 := by
      rw [productionPinsCompact_U, Subgroup.mem_inf] at hu
      exact (mem_finiteAdelicGL2Subgroup_iff ℚ _).mp hu.2
    have hg0 : u * h4pins.gen (ratPrime ⟨p, hp⟩)
          * ((h4pins.gen (ratPrime ⟨p, hp⟩))⁻¹
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))
        = u * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) := by group
    have hmkz : (QuotientGroup.mk (u * h4pins.gen (ratPrime ⟨p, hp⟩) * u')
          : _ ⧸ h4pins.U L)
        = QuotientGroup.mk (u * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)) := by
      rw [QuotientGroup.mk_mul_of_mem _ hu', ← hg0, QuotientGroup.mk_mul_of_mem _ hseam]
    have hmul := finComponent_mul_gen_mem_heckeMulSet ⟨p, hp⟩ huL
    rcases LocalGL2.exists_rep_of_mem_heckeMulSet (pInt ⟨p, hp⟩) (hpInt_ne ⟨p, hp⟩)
        (irreducible_pInt ⟨p, hp⟩) hmul with ⟨b, hb⟩ | hinf
    ·
      obtain ⟨n, hn, hdvd⟩ := exists_natInt_dvd_sub ⟨p, hp⟩ (-b)
      have hdvd' : pInt ⟨p, hp⟩ ∣ b - -(natInt (ratPrime ⟨p, hp⟩) n) := by
        have h2 : pInt ⟨p, hp⟩ ∣ -(-b - natInt (ratPrime ⟨p, hp⟩) n) := dvd_neg.mpr hdvd
        have h3 : -(-b - natInt (ratPrime ⟨p, hp⟩) n)
            = b - -(natInt (ratPrime ⟨p, hp⟩) n) := by ring
        rwa [h3] at h2
      refine ⟨⟨n, by omega⟩, ?_⟩
      rw [show heckeReps p hp ⟨n, by omega⟩
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
        simp only [heckeReps]; rw [if_pos (show ((⟨n, by omega⟩ :
          Fin (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal + 1)) : ℕ) < p from hn)]]
      refine hmkz.trans (mk_eq_mk_of_transfer ⟨p, hp⟩ hLbot hvL
        (y := u⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
            (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero))))
        (mul_mem (inv_mem hu) (uniQ_mem_U n)) ?_ ?_ ?_)
      · simp only [map_mul, map_inv, huA, AdelicDock.glArch_finEmbed,
          glArch_heckeGenAt_unit, inv_one, mul_one]
      · intro w hw
        simp only [map_mul, map_inv, finComponent_glFin_heckeGenAt_of_ne ⟨p, hp⟩ hw,
          mul_one]
      · rw [finComponent_glFin_repsFin_self]
        exact hb.symm.trans (LocalGL2.mk_localRepSome_eq_of_dvd_sub _ _ hdvd').symm
    ·
      refine ⟨⟨p, by omega⟩, ?_⟩
      rw [show heckeReps p hp ⟨p, by omega⟩
          = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ from by
        simp only [heckeReps]; rw [if_neg (lt_irrefl p)]]
      refine hmkz.trans (mk_eq_mk_of_transfer ⟨p, hp⟩ hLbot hvL
        (y := u⁻¹) (inv_mem hu) ?_ ?_ ?_)
      · simp only [map_mul, map_inv, huA, glArch_central ⟨p, hp⟩,
          glArch_heckeGenAt_unit, inv_one, mul_one]
      · intro w hw
        simp only [map_mul, map_inv, finComponent_glFin_heckeGenAt_of_ne ⟨p, hp⟩ hw,
          finComponent_glFin_central_of_ne ⟨p, hp⟩ hw, inv_one, mul_one]
      · rw [finComponent_glFin_repsLast_self]
        exact hinf.symm
  ·
    intro i j hij
    have hloc := mk_loc_eq_of_mk_eq ⟨p, hp⟩ hij
    by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p
    · rw [show heckeReps p hp i
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
          simp only [heckeReps]; rw [if_pos hi],
        show heckeReps p hp j
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((j : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
          simp only [heckeReps]; rw [if_pos hj],
        finComponent_glFin_repsFin_self, finComponent_glFin_repsFin_self] at hloc
      have hdvd := LocalGL2.dvd_sub_of_mk_localRepSome_eq _ _ hloc
      have hsub2 : (-(natInt (ratPrime ⟨p, hp⟩) (j : ℕ))
            - -(natInt (ratPrime ⟨p, hp⟩) (i : ℕ)))
          = natInt (ratPrime ⟨p, hp⟩) (i : ℕ) - natInt (ratPrime ⟨p, hp⟩) (j : ℕ) := by
        ring
      rw [hsub2] at hdvd
      by_contra hne
      have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne' with h | h
      · exact pInt_not_dvd_natInt_sub ⟨p, hp⟩ hj h (dvd_sub_comm.mp hdvd)
      · exact pInt_not_dvd_natInt_sub ⟨p, hp⟩ hi h hdvd
    · rw [show heckeReps p hp i
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
          simp only [heckeReps]; rw [if_pos hi],
        show heckeReps p hp j
          = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ from by
          simp only [heckeReps]; rw [if_neg hj],
        finComponent_glFin_repsFin_self, finComponent_glFin_repsLast_self] at hloc
      exact absurd hloc (LocalGL2.mk_localRepSome_ne_mk_localRepInf _ _
        (irreducible_pInt ⟨p, hp⟩).not_isUnit _)
    · rw [show heckeReps p hp i
          = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ from by
          simp only [heckeReps]; rw [if_neg hi],
        show heckeReps p hp j
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((j : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
          simp only [heckeReps]; rw [if_pos hj],
        finComponent_glFin_repsLast_self, finComponent_glFin_repsFin_self] at hloc
      exact absurd hloc.symm (LocalGL2.mk_localRepSome_ne_mk_localRepInf _ _
        (irreducible_pInt ⟨p, hp⟩).not_isUnit _)
    · have hi2 := i.isLt
      have hj2 := j.isLt
      exact Fin.ext (by omega)

private theorem heckeCosetSum_heckeReps_eq_smul (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ Ideal.absNorm Ψ.level)
    (hpB : ratPrime ⟨p, hp⟩ ∉ R.exceptionalSet)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    SmoothCusp.heckeCosetSum ℚ (heckeReps p hp) R.toFun g
      = Ψ.a (ratPrime ⟨p, hp⟩) * R.toFun g := by
  obtain ⟨reps', hsys', heig'⟩ := R.hecke_eigen (ratPrime ⟨p, hp⟩) hpB
  have h := HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys'
      (isHeckeCosetSystem_heckeReps p hp Ψ.level hpN) R.level_invariant g
  exact h.trans (heig' g)

section S7Value

private theorem descentF_apply (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) (τ : ℍ) :
    descentF R w hw τ
      = ((τ.im : ℝ) : ℂ)⁻¹ * R.toFun (archAt w hw (iwasawaSectionGL τ)) := by
  simp only [descentF, descentFn, UpperHalfPlane.ofComplex_apply, OneMemClass.coe_one,
    map_one, mul_one]
  rfl

private theorem heckeMatrix_eq_realOf_upperTriQ (p j : ℕ) (hp : p ≠ 0) :
    heckeMatrix p j
      = realOf (upperTriQ 1 (j : ℚ) (p : ℚ) one_ne_zero (by exact_mod_cast hp)) := by
  refine Units.ext ?_
  rw [val_heckeMatrix hp, coe_realOf_upperTriQ]
  refine Matrix.ext fun i jj => ?_
  fin_cases i <;> fin_cases jj <;> simp

private theorem heckeDiagMatrix_eq_realOf_upperTriQ (p : ℕ) (hp : p ≠ 0) :
    heckeDiagMatrix p
      = realOf (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp) one_ne_zero) := by
  refine Units.ext ?_
  rw [val_heckeDiagMatrix hp, coe_realOf_upperTriQ]
  refine Matrix.ext fun i jj => ?_
  fin_cases i <;> fin_cases jj <;> simp

private theorem glFin_globalPoints_scalar (u : ℚˣ) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) u))
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (finRatUnit u) := by
  have hkey : (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
      (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    apply RingHom.ext_rat
  have happ : ∀ q : ℚ, (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q).2
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q := fun q =>
    congrArg (fun f : ℚ →+* FiniteAdeleRing (𝓞 ℚ) ℚ => f q) hkey
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply]
  show (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)
      ((Matrix.scalar (Fin 2) ((u : ℚˣ) : ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j)).2
    = (Matrix.scalar (Fin 2) ((finRatUnit u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact happ _
  · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, map_zero]
    rfl

private theorem descentF_slash_heckeMatrix_eq (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (p : ℕ) (hp : p.Prime)
    (i : Fin (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal + 1)) (hi : (i : ℕ) < p)
    (τ : ℍ) :
    ((descentF R w hw) ∣[(1 : ℤ)] heckeMatrix p (i : ℕ)) τ
      = ((τ.im : ℝ) : ℂ)⁻¹
        * R.toFun (archAt w hw (iwasawaSectionGL τ) * heckeReps p hp i) := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  have hpq : (0 : ℚ) < ((p : ℕ) : ℚ) := by exact_mod_cast hp.pos
  have hpc : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp0

  rw [slash_heckeMatrix_apply (1 : ℤ) hp0, heckeMatrix_eq_realOf_upperTriQ p (i : ℕ) hp0,
    descentF_apply]

  have him2 : ((realOf (upperTriQ 1 ((i : ℕ) : ℚ) ((p : ℕ) : ℚ) one_pos.ne' hpq.ne')
      • τ : ℍ)).im * ((p : ℕ) : ℝ) = τ.im := by
    have him := im_smul_realOf_upperTriQ 1 ((i : ℕ) : ℚ) ((p : ℕ) : ℚ) one_pos hpq τ
    simpa using him
  have him3 : ((((realOf (upperTriQ 1 ((i : ℕ) : ℚ) ((p : ℕ) : ℚ) one_pos.ne' hpq.ne')
      • τ : ℍ)).im : ℝ) : ℂ) * ((p : ℕ) : ℂ) = ((τ.im : ℝ) : ℂ) := by
    exact_mod_cast congrArg Complex.ofReal him2
  have him' : ((((realOf (upperTriQ 1 ((i : ℕ) : ℚ) ((p : ℕ) : ℚ) one_pos.ne' hpq.ne')
      • τ : ℍ)).im : ℝ) : ℂ)
      = ((τ.im : ℝ) : ℂ) * (((p : ℕ) : ℂ))⁻¹ := by
    rw [← him3, mul_inv_cancel_right₀ hpc]
  rw [him']
  unfold realOf

  rw [toFun_arch_iwasawa_upperTriQ R w hw homega 1 ((i : ℕ) : ℚ) ((p : ℕ) : ℚ)
    one_pos hpq τ]

  rw [← map_inv, ← map_inv, ← map_inv, upperTriQ_one_j_inv_eq (i : ℕ) p hp.pos]
  simp only [map_mul, map_inv]

  rw [glFin_globalPoints_scalar, finEmbed_scalar_eq_centralScalar,
    show (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
        (finRatUnit (ratUnit p hp.pos))))⁻¹
      = centralScalar (𝓞 ℚ) ℚ ((Units.map (finIncl (𝓞 ℚ) ℚ)
        (finRatUnit (ratUnit p hp.pos)))⁻¹) from (map_inv _ _).symm]
  have hmove : ∀ (c : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x y z : AdelicGL2 (𝓞 ℚ) ℚ),
      x * (centralScalar (𝓞 ℚ) ℚ c * y * z)
        = centralScalar (𝓞 ℚ) ℚ c * (x * (y * z)) := by
    intro c x y z
    rw [← mul_assoc, ← mul_assoc, ← centralScalar_mul_comm, mul_assoc, mul_assoc]
  rw [hmove, omega_spec]
  have homval : ((omegaUnit R ((Units.map (finIncl (𝓞 ℚ) ℚ)
      (finRatUnit (ratUnit p hp.pos)))⁻¹) : ℂˣ) : ℂ) = ((p : ℕ) : ℂ) := by
    rw [map_inv, Units.val_inv_eq_inv_val,
      omegaUnit_finIncl_finRat R w hw homega p hp.pos, inv_inv]
  rw [homval]

  have h6a := heckeGenAt_inv_mul_finEmbed_global_diag_mem_U p hp Ψ.level
  rw [show AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero)))
      = heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
        * ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero))))
      from (mul_inv_cancel_left _ _).symm,
    show archAt w hw (iwasawaSectionGL τ)
        * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
            (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
          * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
            * ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
              * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
                  (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero))))))
      = (archAt w hw (iwasawaSectionGL τ)
          * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
        * ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero))))
      from by rw [mul_assoc, mul_assoc],
    R.level_invariant _ _ h6a,
    show AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
        * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
      = heckeReps p hp i from by
      simp only [heckeReps]
      rw [if_pos hi]]

  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  push_cast
  field_simp

private theorem finEmbed_global_diag_mul_heckeGenAt_inv_mem_U (p : ℕ) (hp : p.Prime)
    (L : Ideal (𝓞 ℚ)) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      ∈ h4pins.U L := by
  have hcompv : finComponent (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (glFin (𝓞 ℚ) ℚ
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
        * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      finComponent_glFin_globalPoints_diag_self p hp,
      finComponent_glFin_heckeGenAt_self]
    exact mul_inv_cancel _
  have hcompw : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      ∀ hw : w ≠ ratPrime ⟨p, hp⟩,
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ
        (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
            (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
          * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹))
        = diagUnitAt p hp hw := by
    intro w hw
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      finComponent_glFin_globalPoints_diag_of_ne p hp hw,
      finComponent_glFin_heckeGenAt_of_ne ⟨p, hp⟩ hw]
    rw [inv_one, mul_one]
  rw [productionPinsCompact_U, Subgroup.mem_inf]
  set T : AdelicGL2 (𝓞 ℚ) ℚ :=
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ with hT
  have hcomp : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ∀ i j : Fin 2,
      ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T) :
            Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) := fun w i j => rfl
  have hcompinv : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ∀ i j : Fin 2,
      ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T))⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) := fun w i j => by
    rw [show ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((finComponent (𝓞 ℚ) ℚ w ((glFin (𝓞 ℚ) ℚ T)⁻¹) :
            Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) from rfl, map_inv]
  constructor
  · refine mem_levelOne_iff.mpr (mem_finiteLevelOne_iff.mpr ⟨?_, ?_⟩)
    · refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · rw [hcomp w i j]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          fin_cases i <;> fin_cases j <;>
            simp only [Units.val_one, Matrix.one_apply_eq, Matrix.one_apply] <;>
            first
            | exact one_mem _
            | exact zero_mem _
        · rw [hcompw w hw]
          fin_cases i <;> fin_cases j
          · exact (natInt w (p : ℕ)).2
          · exact zero_mem _
          · exact zero_mem _
          · exact one_mem _
      · rw [show (((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0)) w
          = ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w
          from rfl, hcomp w 1 0]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          simp only [Units.val_one, Matrix.one_apply_ne one_ne_zero, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v (0 : w.adicCompletion ℚ) ≤ _
          rw [map_zero]
          exact zero_le'
      · rw [show (((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1)) w
          = finAdeleEval (𝓞 ℚ) ℚ w ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
          map_sub, map_one, finAdeleEval_apply, hcomp w 1 1]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          simp only [Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v ((1 : w.adicCompletion ℚ) - 1) ≤ _
          rw [sub_self, map_zero]
          exact zero_le'
    · refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · rw [hcompinv w i j]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          fin_cases i <;> fin_cases j <;>
            simp only [Units.val_one, Matrix.one_apply] <;>
            (split <;> first | exact one_mem _ | exact zero_mem _)
        · rw [hcompw w hw]
          fin_cases i <;> fin_cases j
          · exact (((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ :
              (w.adicCompletionIntegers ℚ)ˣ) : w.adicCompletionIntegers ℚ).2
          · exact zero_mem _
          · exact zero_mem _
          · exact one_mem _
      · rw [show (((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0)) w
          = ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w from rfl,
          hcompinv w 1 0]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          simp only [Units.val_one, Matrix.one_apply_ne one_ne_zero, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v (0 : w.adicCompletion ℚ) ≤ _
          rw [map_zero]
          exact zero_le'
      · rw [show (((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1)) w
          = finAdeleEval (𝓞 ℚ) ℚ w ((((glFin (𝓞 ℚ) ℚ T)⁻¹ :
              GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
          map_sub, map_one, finAdeleEval_apply, hcompinv w 1 1]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          simp only [Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v ((1 : w.adicCompletion ℚ) - 1) ≤ _
          rw [sub_self, map_zero]
          exact zero_le'
  · refine (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr ?_
    rw [map_mul, map_inv, AdelicDock.glArch_finEmbed,
      glArch_heckeGenAt_unit (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩), inv_one, mul_one]

private theorem chi_mul_descentF_slash_heckeDiagMatrix_eq (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (hepsval : ∀ (m : ℕ) (hm : 0 < m),
      (∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
        ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
          ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
          ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) →
      ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit m hm))) : ℂˣ) : ℂ)
        = ((chiNegThree m : ℤ) : ℂ))
    (hN3 : 3 ∣ Ideal.absNorm Ψ.level)
    (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ Ideal.absNorm Ψ.level)
    (hpB : ratPrime ⟨p, hp⟩ ∉ R.exceptionalSet)
    (hdet : Ψ.b (ratPrime ⟨p, hp⟩) = ((chiNegThree p : ℤ) : ℂ) * ((p : ℂ))⁻¹)
    (τ : ℍ) :
    ((chiNegThree p : ℤ) : ℂ) * ((descentF R w hw) ∣[(1 : ℤ)] heckeDiagMatrix p) τ
      = ((τ.im : ℝ) : ℂ)⁻¹
        * R.toFun (archAt w hw (iwasawaSectionGL τ)
            * heckeReps p hp (Fin.last (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal))) := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  have hpq : (0 : ℚ) < ((p : ℕ) : ℚ) := by exact_mod_cast hp.pos
  have hpc : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp0

  have hp3 : p ≠ 3 := fun h => hpN (by rw [h]; exact hN3)
  have h3p : ¬ (3 : ℕ) ∣ p := fun hdvd =>
    hp3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd).symm)
  have hchi2 : ((chiNegThree p : ℤ) : ℂ) * ((chiNegThree p : ℤ) : ℂ) = 1 := by
    exact_mod_cast chiNegThree_mul_self_of_not_dvd h3p

  rw [slash_heckeDiagMatrix_apply (1 : ℤ) hp0, sub_self, zpow_zero, one_mul,
    heckeDiagMatrix_eq_realOf_upperTriQ p hp0, descentF_apply]

  have him2 : ((realOf (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero) • τ : ℍ)).im
      = ((p : ℕ) : ℝ) * τ.im := by
    have him := im_smul_realOf_upperTriQ ((p : ℕ) : ℚ) 0 1 hpq one_pos τ
    simpa using him
  have him' : ((((realOf (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero)
      • τ : ℍ)).im : ℝ) : ℂ)
      = ((p : ℕ) : ℂ) * ((τ.im : ℝ) : ℂ) := by
    exact_mod_cast congrArg Complex.ofReal him2
  rw [him']
  unfold realOf

  rw [toFun_arch_iwasawa_upperTriQ R w hw homega ((p : ℕ) : ℚ) 0 1 hpq one_pos τ]

  have hmir := finEmbed_global_diag_mul_heckeGenAt_inv_mem_U p hp Ψ.level
  have hu' : heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
      * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero))))⁻¹
      ∈ h4pins.U Ψ.level := by
    have h := (h4pins.U Ψ.level).inv_mem hmir
    rwa [mul_inv_rev, inv_inv] at h
  rw [show (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero))))⁻¹
      = (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
        * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
          * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero))))⁻¹)
      from (inv_mul_cancel_left _ _).symm,
    show archAt w hw (iwasawaSectionGL τ)
        * ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
            * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
                (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero))))⁻¹))
      = (archAt w hw (iwasawaSectionGL τ)
          * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹)
        * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
          * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ ((p : ℕ) : ℚ) 0 1 hpq.ne' one_ne_zero))))⁻¹)
      from by rw [mul_assoc],
    R.level_invariant _ _ hu']

  rw [show (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      = (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
          (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))))⁻¹
        * (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
            (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
          * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹)
      from (inv_mul_cancel_left _ _).symm,
    show (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
          (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))))⁻¹
      = centralScalar (𝓞 ℚ) ℚ ((Units.map (finIncl (𝓞 ℚ) ℚ)
          (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))⁻¹)
      from (map_inv _ _).symm]
  rw [show archAt w hw (iwasawaSectionGL τ)
        * (centralScalar (𝓞 ℚ) ℚ ((Units.map (finIncl (𝓞 ℚ) ℚ)
            (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))⁻¹)
          * (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹))
      = centralScalar (𝓞 ℚ) ℚ ((Units.map (finIncl (𝓞 ℚ) ℚ)
          (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))⁻¹)
        * (archAt w hw (iwasawaSectionGL τ)
          * (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹))
      from by rw [← mul_assoc, ← centralScalar_mul_comm, mul_assoc],
    omega_spec,
    show centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
          (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
        * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      = heckeReps p hp (Fin.last (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal))
      from by
        simp only [heckeReps]
        rw [if_neg (by rw [Fin.val_last, absNorm_ratPrime]; exact lt_irrefl p)]]

  have h6bval := omegaUnit_finIncl_localUnit_pUnit_H7 R w hw homega hepsval hN3 p hp hpN hpB hdet
  have homvald : ((omegaUnit R ((Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))⁻¹) : ℂˣ) : ℂ)
      = ((p : ℕ) : ℂ) * ((chiNegThree p : ℤ) : ℂ) := by
    rw [map_inv, Units.val_inv_eq_inv_val, h6bval, mul_inv, inv_inv,
      inv_eq_of_mul_eq_one_right hchi2]
  rw [homvald]

  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  push_cast
  field_simp
  linear_combination (R.toFun (archAt w hw (iwasawaSectionGL τ)
      * heckeReps p hp (Fin.last (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal)))) * hchi2

end S7Value
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

private theorem descentF_heckeT_char_eigen (R : SmoothCuspRealizationAt ℚ h4pins Ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (hepsval : ∀ (m : ℕ) (hm : 0 < m),
      (∀ q : ℕ, ∀ hq : q.Prime, q ∣ m →
        ¬ q ∣ Ideal.absNorm Ψ.level ∧ q ≠ 3
          ∧ ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet
          ∧ Ψ.b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹) →
      ((omegaUnit R (Units.map (finIncl (𝓞 ℚ) ℚ)
          (epsUnitHom Ψ.level_ne_bot (ratUnit m hm))) : ℂˣ) : ℂ)
        = ((chiNegThree m : ℤ) : ℂ))
    (hN3 : 3 ∣ Ideal.absNorm Ψ.level)
    (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ Ideal.absNorm Ψ.level)
    (hpB : ratPrime ⟨p, hp⟩ ∉ R.exceptionalSet)
    (hdet : Ψ.b (ratPrime ⟨p, hp⟩) = ((chiNegThree p : ℤ) : ℂ) * ((p : ℂ))⁻¹)
    (τ : ℍ) :
    heckeU 1 p (descentF R w hw) τ
      + ((chiNegThree p : ℤ) : ℂ) * ((descentF R w hw) ∣[(1 : ℤ)] heckeDiagMatrix p) τ
      = Ψ.a (ratPrime ⟨p, hp⟩) * descentF R w hw τ := by
  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  have habs : Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal = p := absNorm_ratPrime ⟨p, hp⟩

  have hsum := heckeCosetSum_heckeReps_eq_smul R p hp hpN hpB
      (archAt w hw (iwasawaSectionGL τ))
  simp only [SmoothCusp.heckeCosetSum] at hsum
  rw [Fin.sum_univ_castSucc] at hsum

  have hjterm : ∀ i : Fin (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal),
      R.toFun (archAt w hw (iwasawaSectionGL τ) * heckeReps p hp (Fin.castSucc i))
        = ((τ.im : ℝ) : ℂ)
          * (((descentF R w hw) ∣[(1 : ℤ)] heckeMatrix p ((Fin.castSucc i : Fin _) : ℕ)) τ) := by
    intro i
    have hilt : ((Fin.castSucc i : Fin _) : ℕ) < p := by
      have h1 := i.isLt
      simp only [Fin.val_castSucc]
      omega
    rw [descentF_slash_heckeMatrix_eq R w hw homega p hp (Fin.castSucc i) hilt τ,
      ← mul_assoc, mul_inv_cancel₀ hy, one_mul]
  have hdterm :
      R.toFun (archAt w hw (iwasawaSectionGL τ)
        * heckeReps p hp (Fin.last (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal)))
      = ((τ.im : ℝ) : ℂ) * (((chiNegThree p : ℤ) : ℂ)
          * ((descentF R w hw) ∣[(1 : ℤ)] heckeDiagMatrix p) τ) := by
    rw [chi_mul_descentF_slash_heckeDiagMatrix_eq R w hw homega hepsval hN3
        p hp hpN hpB hdet τ,
      ← mul_assoc, mul_inv_cancel₀ hy, one_mul]
  simp only [hjterm, hdterm, Fin.val_castSucc] at hsum
  rw [← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range
      (fun j => ((descentF R w hw) ∣[(1 : ℤ)] heckeMatrix p j) τ),
    show Finset.range (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal) = Finset.range p
      from by rw [habs]] at hsum

  rw [show heckeU 1 p (descentF R w hw) τ
      = ∑ j ∈ Finset.range p, ((descentF R w hw) ∣[(1 : ℤ)] heckeMatrix p j) τ
      from by rw [heckeU_def]; exact Finset.sum_apply _ _ _,
    descentF_apply R w hw τ]

  field_simp
  linear_combination hsum

end H7Heads
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part06
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part07

noncomputable section

namespace ArchimedeanDescent

section SmoothRough

variable (𝔅 : Finset ℕ)

private def smoothPart (n : ℕ) : ℕ := ∏ p ∈ 𝔅, p ^ n.factorization p

private def roughPart (n : ℕ) : ℕ := n / smoothPart 𝔅 n

private theorem smoothPart_dvd (n : ℕ) (hn : n ≠ 0) : smoothPart 𝔅 n ∣ n := by
  have h1 : smoothPart 𝔅 n = ∏ p ∈ 𝔅 ∩ n.factorization.support, p ^ n.factorization p := by
    rw [smoothPart]
    symm
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hpB hps
    have : n.factorization p = 0 := by
      by_contra h0
      exact hps (Finset.mem_inter.mpr ⟨hpB, Finsupp.mem_support_iff.mpr h0⟩)
    simp [this]
  rw [h1]
  calc ∏ p ∈ 𝔅 ∩ n.factorization.support, p ^ n.factorization p
      ∣ ∏ p ∈ n.factorization.support, p ^ n.factorization p :=
        Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right
    _ = n := Nat.prod_factorization_pow_eq_self hn

private theorem smoothPart_ne_zero (n : ℕ) : smoothPart 𝔅 n ≠ 0 := by
  rw [smoothPart, Finset.prod_ne_zero_iff]
  intro p _
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [Nat.factorization_zero_right]
  · exact pow_ne_zero _ hp0

private theorem smoothPart_mul_roughPart (n : ℕ) (hn : n ≠ 0) :
    smoothPart 𝔅 n * roughPart 𝔅 n = n :=
  Nat.mul_div_cancel' (smoothPart_dvd 𝔅 n hn)

private theorem prime_mem_of_dvd_smoothPart (n : ℕ) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ smoothPart 𝔅 n) : q ∈ 𝔅 := by
  rw [smoothPart] at hdvd
  obtain ⟨p, hpB, hqp⟩ := hq.prime.exists_mem_finset_dvd hdvd
  have hfac : n.factorization p ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Nat.dvd_one] at hqp
    exact hq.one_lt.ne' hqp
  have hpprime : p.Prime := by
    have hsup : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hfac
    rw [Nat.support_factorization] at hsup
    exact Nat.prime_of_mem_primeFactors hsup
  have : q = p := (Nat.prime_dvd_prime_iff_eq hq hpprime).mp (hq.dvd_of_dvd_pow hqp)
  rwa [this]

private theorem roughPart_prime_not_mem {n : ℕ} (hn : n ≠ 0) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ roughPart 𝔅 n) : q ∉ 𝔅 := by
  intro hqB
  have h1 : smoothPart 𝔅 n * roughPart 𝔅 n = n := smoothPart_mul_roughPart 𝔅 n hn
  have hsp : q ^ n.factorization q ∣ smoothPart 𝔅 n := Finset.dvd_prod_of_mem _ hqB
  rcases hdvd with ⟨t, ht⟩
  rcases hsp with ⟨s, hs⟩
  have hn_eq : n = q ^ (n.factorization q + 1) * (s * t) := by
    calc n = smoothPart 𝔅 n * roughPart 𝔅 n := h1.symm
      _ = (q ^ n.factorization q * s) * (q * t) := by rw [hs, ht]
      _ = q ^ (n.factorization q + 1) * (s * t) := by ring
  exact Nat.pow_succ_factorization_not_dvd hn hq ⟨s * t, hn_eq⟩

private theorem coprime_smoothPart_roughPart (n : ℕ) (hn : n ≠ 0) :
    Nat.Coprime (smoothPart 𝔅 n) (roughPart 𝔅 n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h1
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd h1
  exact roughPart_prime_not_mem 𝔅 hn hq (hqdvd.trans (Nat.gcd_dvd_right _ _))
    (prime_mem_of_dvd_smoothPart 𝔅 n hq (hqdvd.trans (Nat.gcd_dvd_left _ _)))

end SmoothRough
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Induction

variable (𝔅 : Finset ℕ) (c a e w lam : ℕ → ℂ)

private theorem lam_peel
    (hlam_p : ∀ p, p.Prime → p ∉ 𝔅 → lam p = a p)
    (hlam_rec : ∀ p, p.Prime → p ∉ 𝔅 → ∀ r : ℕ,
      lam (p ^ (r + 2)) = a p * lam (p ^ (r + 1)) - e p * w p * lam (p ^ r))
    (hlam_mul : ∀ m n : ℕ, Nat.Coprime m n → lam (m * n) = lam m * lam n)
    (p : ℕ) (hp : p.Prime) (hpB : p ∉ 𝔅) (m : ℕ) (hm : m ≠ 0) :
    lam (p * m) = a p * lam m - e p * w p * (if p ∣ m then lam (m / p) else 0) := by
  set r := m.factorization p with hr
  set m₂ := m / p ^ r with hm₂def
  have hdvd : p ^ r ∣ m := by
    have h := smoothPart_dvd {p} m hm
    rwa [smoothPart, Finset.prod_singleton] at h
  have hm2 : m = p ^ r * m₂ := (Nat.mul_div_cancel' hdvd).symm
  have hpm2 : ¬ p ∣ m₂ := by
    intro hd
    rcases hd with ⟨t, ht⟩
    have hmeq : m = p ^ (r + 1) * t := by
      calc m = p ^ r * m₂ := hm2
        _ = p ^ r * (p * t) := by rw [ht]
        _ = p ^ (r + 1) * t := by ring
    exact Nat.pow_succ_factorization_not_dvd hm hp ⟨t, hmeq⟩
  have hcop : ∀ s : ℕ, Nat.Coprime (p ^ s) m₂ :=
    fun s => Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm2)
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  ·
    have hm2' : m = m₂ := by rw [hm2, hr0, pow_zero, one_mul]
    have hpm : ¬ p ∣ m := hm2' ▸ hpm2
    rw [if_neg hpm, mul_zero, sub_zero]
    calc lam (p * m) = lam p * lam m := by
          rw [hlam_mul p m (by
            rw [hm2']
            exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm2)]
      _ = a p * lam m := by rw [hlam_p p hp hpB]
  ·
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hrpos
    have hrs : r = s + 1 := by omega
    have hpm : p ∣ m := by
      rw [hm2, hrs]
      exact Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero s)) m₂
    rw [if_pos hpm]
    have hmp : m / p = p ^ s * m₂ := by
      rw [hm2, hrs, pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    calc lam (p * m) = lam (p ^ (s + 2) * m₂) := by
          rw [hm2, hrs]; ring_nf
      _ = lam (p ^ (s + 2)) * lam m₂ := hlam_mul _ _ (hcop _)
      _ = (a p * lam (p ^ (s + 1)) - e p * w p * lam (p ^ s)) * lam m₂ := by
          rw [hlam_rec p hp hpB s]
      _ = a p * (lam (p ^ (s + 1)) * lam m₂) - e p * w p * (lam (p ^ s) * lam m₂) := by
          ring
      _ = a p * lam m - e p * w p * lam (m / p) := by
          rw [← hlam_mul _ _ (hcop (s + 1)), ← hlam_mul _ _ (hcop s), ← hmp,
            hm2, hrs]

private theorem coeff_factorization
    (hrel : ∀ p, p.Prime → p ∉ 𝔅 → ∀ n : ℕ,
      c (p * n) + e p * w p * (if p ∣ n then c (n / p) else 0) = a p * c n)
    (hlam_1 : lam 1 = 1)
    (hlam_p : ∀ p, p.Prime → p ∉ 𝔅 → lam p = a p)
    (hlam_rec : ∀ p, p.Prime → p ∉ 𝔅 → ∀ r : ℕ,
      lam (p ^ (r + 2)) = a p * lam (p ^ (r + 1)) - e p * w p * lam (p ^ r))
    (hlam_mul : ∀ m n : ℕ, Nat.Coprime m n → lam (m * n) = lam m * lam n)
    (n₁ : ℕ) :
    ∀ m : ℕ, m ≠ 0 → (∀ q, q.Prime → q ∣ m → q ∉ 𝔅) → Nat.Coprime n₁ m →
      c (n₁ * m) = c n₁ * lam m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hgood hcop
    rcases eq_or_ne m 1 with rfl | h1
    · simp [hlam_1]
    set p := m.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime h1
    set m₁ := m / p with hm₁def
    have hpdvd : p ∣ m := Nat.minFac_dvd m
    have hm1 : m = p * m₁ := (Nat.mul_div_cancel' hpdvd).symm
    have hm₁0 : m₁ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hm1
      exact hm0 hm1
    have hm₁lt : m₁ < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hp.one_lt
    have hm₁dvd : m₁ ∣ m := ⟨p, by rw [hm1]; ring⟩
    have hpB : p ∉ 𝔅 := hgood p hp hpdvd
    have hgood₁ : ∀ q, q.Prime → q ∣ m₁ → q ∉ 𝔅 :=
      fun q hq hd => hgood q hq (hd.trans hm₁dvd)
    have hcop₁ : Nat.Coprime n₁ m₁ := Nat.Coprime.coprime_dvd_right hm₁dvd hcop
    have hpn₁ : ¬ p ∣ n₁ := by
      intro hd
      have : p ∣ Nat.gcd n₁ m := Nat.dvd_gcd hd hpdvd
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hIH₁ : c (n₁ * m₁) = c n₁ * lam m₁ := ih m₁ hm₁lt hm₁0 hgood₁ hcop₁
    have hkey := hrel p hp hpB (n₁ * m₁)
    have hmul : p * (n₁ * m₁) = n₁ * m := by rw [hm1]; ring
    rw [hmul] at hkey
    by_cases hpm₁ : p ∣ m₁
    · have hdvd' : p ∣ n₁ * m₁ := hpm₁.mul_left n₁
      have hquot : n₁ * m₁ / p = n₁ * (m₁ / p) := Nat.mul_div_assoc n₁ hpm₁
      have hq0 : m₁ / p ≠ 0 := by
        have hle : p ≤ m₁ := Nat.le_of_dvd (Nat.pos_of_ne_zero hm₁0) hpm₁
        have := Nat.div_pos hle hp.pos
        omega
      have hqlt : m₁ / p < m :=
        lt_trans (Nat.div_lt_self (Nat.pos_of_ne_zero hm₁0) hp.one_lt) hm₁lt
      have hqdvd : m₁ / p ∣ m := (Nat.div_dvd_of_dvd hpm₁).trans hm₁dvd
      have hIHq : c (n₁ * (m₁ / p)) = c n₁ * lam (m₁ / p) :=
        ih (m₁ / p) hqlt hq0 (fun q hq hd => hgood q hq (hd.trans hqdvd))
          (Nat.Coprime.coprime_dvd_right hqdvd hcop)
      have peel := lam_peel 𝔅 a e w lam hlam_p hlam_rec hlam_mul p hp hpB m₁ hm₁0
      rw [if_pos hpm₁] at peel
      rw [if_pos hdvd', hquot, hIHq, hIH₁] at hkey
      have hout : c (n₁ * m) = a p * (c n₁ * lam m₁) - e p * w p * (c n₁ * lam (m₁ / p)) := by
        linear_combination hkey
      rw [hout, hm1, peel]
      ring
    · have hdvd' : ¬ p ∣ n₁ * m₁ := by
        intro h
        exact ((Nat.Prime.dvd_mul hp).mp h).elim hpn₁ hpm₁
      have peel := lam_peel 𝔅 a e w lam hlam_p hlam_rec hlam_mul p hp hpB m₁ hm₁0
      rw [if_neg hpm₁] at peel
      rw [if_neg hdvd'] at hkey
      have hout : c (n₁ * m) = a p * (c n₁ * lam m₁) := by
        rw [← hIH₁]
        linear_combination hkey
      rw [hout, hm1, peel]
      ring

private theorem exists_smooth_index_ne_zero
    (hrel : ∀ p, p.Prime → p ∉ 𝔅 → ∀ n : ℕ,
      c (p * n) + e p * w p * (if p ∣ n then c (n / p) else 0) = a p * c n)
    (hlam_1 : lam 1 = 1)
    (hlam_p : ∀ p, p.Prime → p ∉ 𝔅 → lam p = a p)
    (hlam_rec : ∀ p, p.Prime → p ∉ 𝔅 → ∀ r : ℕ,
      lam (p ^ (r + 2)) = a p * lam (p ^ (r + 1)) - e p * w p * lam (p ^ r))
    (hlam_mul : ∀ m n : ℕ, Nat.Coprime m n → lam (m * n) = lam m * lam n)
    (hne : ∃ n, n ≠ 0 ∧ c n ≠ 0) :
    ∃ s, s ≠ 0 ∧ (∀ q, q.Prime → q ∣ s → q ∈ 𝔅) ∧ c s ≠ 0 := by
  obtain ⟨n, hn0, hcn⟩ := hne
  refine ⟨smoothPart 𝔅 n, smoothPart_ne_zero 𝔅 n,
    fun q hq hd => prime_mem_of_dvd_smoothPart 𝔅 n hq hd, ?_⟩
  have hsplit := smoothPart_mul_roughPart 𝔅 n hn0
  have hr0 : roughPart 𝔅 n ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsplit
    exact hn0 hsplit.symm
  have hfac := coeff_factorization 𝔅 c a e w lam hrel hlam_1 hlam_p hlam_rec hlam_mul
    (smoothPart 𝔅 n) (roughPart 𝔅 n) hr0
    (fun q hq hd => roughPart_prime_not_mem 𝔅 hn0 hq hd)
    (coprime_smoothPart_roughPart 𝔅 n hn0)
  intro hs0
  apply hcn
  calc c n = c (smoothPart 𝔅 n * roughPart 𝔅 n) := by rw [hsplit]
    _ = c (smoothPart 𝔅 n) * lam (roughPart 𝔅 n) := hfac
    _ = 0 := by rw [hs0, zero_mul]

end Induction
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end ArchimedeanDescent
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

open CongruenceSubgroup UpperHalfPlane Complex ModularForm EisensteinWeightOne

open scoped MatrixGroups ModularForm Pointwise Real

namespace HeckeDictionary

private def restrictCusp {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) {k : ℤ} (f : CuspForm Γ k) : CuspForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

@[scoped simp] private theorem coe_restrictCusp {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) {k : ℤ} (f : CuspForm Γ k) :
    ⇑(restrictCusp h f) = ⇑f := rfl

private theorem Gamma0_le_of_dvd {N M : ℕ} (h : N ∣ M) : Gamma0 M ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have := congrArg (ZMod.castHom h (ZMod N)) hA
  rwa [map_intCast, map_zero] at this

private theorem sum_slash {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ) :
    (∑ i ∈ s, F i) ∣[k] g = ∑ i ∈ s, F i ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

private theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι) (F : ι → CuspForm Γ k) :
    ⇑(∑ i ∈ s, F i) = ∑ i ∈ s, ⇑(F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add, ih]

private def zetaQ (q : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / q)

private theorem zetaQ_pow_eq_one_iff (q : ℕ) (hq : q ≠ 0) (n : ℕ) : zetaQ q ^ n = 1 ↔ q ∣ n :=
  (Complex.isPrimitiveRoot_exp q hq).pow_eq_one_iff_dvd n

private theorem sum_zetaQ_pow (q : ℕ) [NeZero q] (n : ℕ) :
    ∑ j : ZMod q, zetaQ q ^ (j.val * n) = if q ∣ n then (q : ℂ) else 0 := by
  have hq : q ≠ 0 := NeZero.ne q
  have hsum : ∑ j : ZMod q, zetaQ q ^ (j.val * n) = ∑ i ∈ Finset.range q, (zetaQ q ^ n) ^ i := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul, mul_comm]
    rfl
  rw [hsum]
  split_ifs with h
  · rw [(zetaQ_pow_eq_one_iff q hq n).mpr h]
    simp
  · have hne : zetaQ q ^ n ≠ 1 := fun h1 => h ((zetaQ_pow_eq_one_iff q hq n).mp h1)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, (zetaQ_pow_eq_one_iff q hq q).mpr dvd_rfl, one_pow,
      sub_self, zero_div]

private theorem Gamma1_le_of_dvd {N M : ℕ} (h : N ∣ M) : Gamma1 M ≤ Gamma1 N := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod N)) h1
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod N)) h2
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod N)) h3
    rwa [map_intCast, map_zero] at this

private theorem one_mem_strictPeriods_Gamma1' (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine Subgroup.mem_map.mpr ⟨ModularGroup.T, ?_, ?_⟩
  · rw [Gamma1_mem]
    simp [ModularGroup.coe_T]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.coe_T, Matrix.GeneralLinearGroup.upperRightHom_apply]

private theorem hasSum_qCoeff_Gamma1 {N : ℕ} {k : ℤ} (F : CuspForm (Gamma1 N) k) (τ : ℍ) :
    HasSum (fun n : ℕ => ModularFormClass.qCoeff (⇑F) n • Function.Periodic.qParam 1 (τ : ℂ) ^ n) (F τ) := by
  have hΓ := one_mem_strictPeriods_Gamma1' N
  have : Fact (IsCusp OnePoint.infty ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex F hΓ)
    (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ

private theorem heckeU_eq_sum_zmod (k : ℤ) (p : ℕ) [NeZero p] (f : ℍ → ℂ) :
    heckeU k p f = ∑ j : ZMod p, f ∣[k] heckeMatrix p j.val := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  subst hm
  rw [heckeU_def, ← Fin.sum_univ_eq_sum_range]
  rfl

private theorem heckeMatrix_mul_eq {p : ℕ} (hp : p ≠ 0) (j j' : ℕ) {γ : SL(2, ℤ)} (hc : (p : ℤ) ∣ γ 1 0)
    (hjj : (p : ℤ) ∣ γ 0 1 + (j : ℤ) * γ 1 1 - (j' : ℤ) * γ 0 0) :
    ∃ γ' : SL(2, ℤ), γ' 0 0 = γ 0 0 + j * γ 1 0 ∧ γ' 1 0 = p * γ 1 0 ∧ γ' 1 1 = γ 1 1 - j' * γ 1 0 ∧
      heckeMatrix p j * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeMatrix p j' := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨w, hw⟩ : (p : ℤ) ∣ γ 0 1 + (j : ℤ) * γ 1 1 - (j' : ℤ) * γ 0 0 - (j : ℤ) * j' * γ 1 0 := by
    refine dvd_sub hjj ?_
    rw [hu]
    exact ⟨j * j' * u, by ring⟩
  have hdet := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [γ.det_coe] at hdet
  have hdet' : (γ 0 0 + j * γ 1 0) * (γ 1 1 - j' * γ 1 0) - w * (p * γ 1 0 : ℤ) = 1 := by
    linear_combination -hdet + (γ 1 0 : ℤ) * hw
  refine ⟨⟨!![γ 0 0 + j * γ 1 0, w; p * γ 1 0, γ 1 1 - j' * γ 1 0],
      by rw [Matrix.det_fin_two_of]; exact hdet'⟩, rfl, rfl, rfl, ?_⟩
  have hwR : ((γ 0 1 : ℤ) : ℝ) + (j : ℝ) * ((γ 1 1 : ℤ) : ℝ) - (j' : ℝ) * ((γ 0 0 : ℤ) : ℝ)
      - (j : ℝ) * (j' : ℝ) * ((γ 1 0 : ℤ) : ℝ) = (p : ℝ) * (w : ℝ) := by exact_mod_cast hw
  refine (Matrix.GeneralLinearGroup.ext_iff _ _).mpr fun i i' => ?_
  rw [Units.val_mul, Units.val_mul]
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.mapGL,
      Matrix.SpecialLinearGroup.map_apply_coe, val_heckeMatrix hp] <;>
    first
    | ring1
    | linear_combination hwR

private theorem mem_Gamma1_of_entries {M p j j' : ℕ} {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M)
    (ha : γ' 0 0 = γ 0 0 + j * γ 1 0) (hc : γ' 1 0 = p * γ 1 0) (hd : γ' 1 1 = γ 1 1 - j' * γ 1 0) :
    γ' ∈ Gamma1 M := by
  rw [Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]; push_cast; rw [h1, h3]; ring
  · rw [hd]; push_cast; rw [h2, h3]; ring
  · rw [hc]; push_cast; rw [h3]; ring

private theorem mem_Gamma0_of_entries {M p j' : ℕ} {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (p * M))
    (hc : γ' 1 0 = p * γ 1 0) (hd : γ' 1 1 = γ 1 1 - j' * γ 1 0) :
    γ' ∈ Gamma0 M ∧ (M : ℤ) ∣ γ' 1 1 - γ 1 1 := by
  have hcpM : (((p * M : ℕ)) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  have hMc : (M : ℤ) ∣ γ 1 0 := dvd_trans ⟨p, by push_cast; ring⟩ hcpM
  refine ⟨?_, ?_⟩
  · rw [Gamma0_mem, hc, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_of_dvd_right hMc _
  · rw [hd, show (γ 1 1 : ℤ) - j' * γ 1 0 - γ 1 1 = (-(j' : ℤ)) * γ 1 0 by ring]
    exact dvd_mul_of_dvd_right hMc _

private theorem Gamma_le_conj_heckeMatrix (p M : ℕ) (hp : p ≠ 0) (j : ℕ) :
    ((Gamma (p * M) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (heckeMatrix p j)⁻¹ • ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct]
  have hγ' := Gamma_mem.mp hγ
  have hγ1 : γ ∈ Gamma1 (p * M) := by
    rw [Gamma1_mem]
    exact ⟨hγ'.1, hγ'.2.2.2, hγ'.2.2.1⟩
  have hpM : (p : ℤ) ∣ ((p * M : ℕ) : ℤ) := ⟨M, by push_cast; ring⟩
  have hc : (p : ℤ) ∣ γ 1 0 := dvd_trans hpM ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ'.2.2.1)
  have hb : (p : ℤ) ∣ γ 0 1 := dvd_trans hpM ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ'.2.1)
  have hda : (p : ℤ) ∣ γ 1 1 - γ 0 0 := by
    have h1 : ((γ 0 0 : ℤ) : ZMod (p * M)) = ((γ 1 1 : ℤ) : ZMod (p * M)) := by rw [hγ'.1, hγ'.2.2.2]
    exact dvd_trans hpM ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1)
  have hjj : (p : ℤ) ∣ γ 0 1 + (j : ℤ) * γ 1 1 - (j : ℤ) * γ 0 0 := by
    rw [show (γ 0 1 : ℤ) + (j : ℤ) * γ 1 1 - (j : ℤ) * γ 0 0 = γ 0 1 + (j : ℤ) * (γ 1 1 - γ 0 0) by ring]
    exact dvd_add hb (dvd_mul_of_dvd_right hda _)
  obtain ⟨γ', ha, hc', hd, hmul⟩ := heckeMatrix_mul_eq hp j j hc hjj
  rw [hmul, mul_inv_cancel_right]
  exact Subgroup.mem_map.mpr
    ⟨γ', mem_Gamma1_of_entries (Gamma1_le_of_dvd (dvd_mul_left M p) hγ1) ha hc' hd, rfl⟩

private def heckeUGamma (p : ℕ) [NeZero p] {M : ℕ} {k : ℤ} (f : CuspForm (Gamma1 M) k) : CuspForm (Gamma (p * M)) k :=
  ∑ j : ZMod p, restrictCusp (Gamma_le_conj_heckeMatrix p M (NeZero.ne p) j.val)
    (CuspForm.translate f (heckeMatrix p j.val))

private theorem coe_heckeUGamma (p : ℕ) [NeZero p] {M : ℕ} {k : ℤ} (f : CuspForm (Gamma1 M) k) :
    ⇑(heckeUGamma p f) = heckeU k p ⇑f := by
  rw [heckeUGamma, coe_finset_sum, heckeU_eq_sum_zmod]
  rfl

private theorem exists_reindex_hecke (p : ℕ) [NeZero p] {γ : SL(2, ℤ)} (hc : (p : ℤ) ∣ γ 1 0) :
    ∃ e : ZMod p ≃ ZMod p, ∀ j : ZMod p,
      (p : ℤ) ∣ γ 0 1 + (j.val : ℤ) * γ 1 1 - ((e j).val : ℤ) * γ 0 0 := by
  have hc0 : ((γ 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have had : ((γ 0 0 : ℤ) : ZMod p) * ((γ 1 1 : ℤ) : ZMod p) = 1 := by
    have hdet := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
    rw [γ.det_coe] at hdet
    have := congrArg (fun x : ℤ => (x : ZMod p)) hdet
    simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, hc0, mul_zero, sub_zero] at this
    exact this.symm
  set dq : ZMod p := ((γ 1 1 : ℤ) : ZMod p) with hdq
  set aq : ZMod p := ((γ 0 0 : ℤ) : ZMod p) with haq
  set bq : ZMod p := ((γ 0 1 : ℤ) : ZMod p) with hbq
  have hunit : IsUnit (dq ^ 2) := (IsUnit.of_mul_eq_one aq (by rw [mul_comm]; exact had)).pow 2
  refine ⟨(Units.mulLeft hunit.unit).trans (Equiv.addRight (dq * bq)), fun j => ?_⟩
  have he : ((Units.mulLeft hunit.unit).trans (Equiv.addRight (dq * bq)) : ZMod p ≃ ZMod p) j =
      dq ^ 2 * j + dq * bq := rfl
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, he, ← hdq, ← haq, ← hbq]
  linear_combination (-(bq + j * dq)) * had

private theorem heckeU_slash_Gamma1 (p : ℕ) [NeZero p] {M : ℕ} {k : ℤ} (f : CuspForm (Gamma1 M) k)
    (x : GL (Fin 2) ℝ) (hx : x ∈ ((Gamma1 (p * M) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeU k p ⇑f) ∣[k] x = heckeU k p ⇑f := by
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
  have hp : p ≠ 0 := NeZero.ne p
  have hγM : γ ∈ Gamma1 M := Gamma1_le_of_dvd (dvd_mul_left M p) hγ
  have hc : (p : ℤ) ∣ γ 1 0 :=
    dvd_trans ⟨M, by push_cast; ring⟩ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma1_mem _ _).mp hγ).2.2)
  obtain ⟨e, he⟩ := exists_reindex_hecke p hc
  rw [heckeU_eq_sum_zmod, sum_slash]
  have hterm : ∀ j : ZMod p,
      ((⇑f) ∣[k] heckeMatrix p j.val) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ =
      (⇑f) ∣[k] heckeMatrix p (e j).val := fun j => by
    obtain ⟨γ', ha, hc', hd, hmul⟩ := heckeMatrix_mul_eq hp j.val (e j).val hc (he j)
    have hγ'1 : γ' ∈ Gamma1 M := mem_Gamma1_of_entries hγM ha hc' hd
    have h := congrArg (fun g : GL (Fin 2) ℝ => (⇑f) ∣[k] g) hmul
    simp only [SlashAction.slash_mul] at h
    rw [SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map.mpr ⟨γ', hγ'1, rfl⟩)] at h
    exact h
  simp_rw [hterm]
  exact Equiv.sum_comp e (fun j : ZMod p => (⇑f) ∣[k] heckeMatrix p j.val)

private def heckeU₁ (p : ℕ) [NeZero p] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) :
    CuspForm (Gamma1 (p * M)) k where
  toFun := heckeU k p ⇑f
  slash_action_eq' x hx := heckeU_slash_Gamma1 p f x hx
  holo' := by
    have h := ModularFormClass.holo (heckeUGamma p f)
    rwa [coe_heckeUGamma] at h
  zero_at_cusps' {c} hc := by
    haveI : NeZero (p * M) := ⟨mul_ne_zero (NeZero.ne p) (NeZero.ne M)⟩
    have hc' : IsCusp c ((Gamma (p * M) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)
    have h := CuspFormClass.zero_at_cusps (heckeUGamma p f) hc'
    rwa [coe_heckeUGamma] at h

@[scoped simp] private theorem coe_heckeU₁ (p : ℕ) [NeZero p] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) :
    ⇑(heckeU₁ p f) = heckeU k p ⇑f := rfl

private theorem heckeU₁_apply (p : ℕ) [NeZero p] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) (τ : ℍ) :
    heckeU₁ p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) :=
  heckeU_apply k (NeZero.ne p) (⇑f) τ

private theorem heckeU₁_slash_Gamma0 (p : ℕ) [NeZero p] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k)
    (c : ℤ → ℂ) (hcM : ∀ d d' : ℤ, (M : ℤ) ∣ d' - d → c d' = c d)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → (⇑f) ∣[k] γ = c (γ 1 1) • (⇑f))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (p * M)) :
    (⇑(heckeU₁ p f)) ∣[k] γ = c (γ 1 1) • (⇑(heckeU₁ p f)) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hc : (p : ℤ) ∣ γ 1 0 :=
    dvd_trans ⟨M, by push_cast; ring⟩ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))
  obtain ⟨e, he⟩ := exists_reindex_hecke p hc
  show (⇑(heckeU₁ p f)) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ = _
  rw [coe_heckeU₁, heckeU_eq_sum_zmod, sum_slash, Finset.smul_sum]
  have hterm : ∀ j : ZMod p,
      ((⇑f) ∣[k] heckeMatrix p j.val) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ =
      c (γ 1 1) • (⇑f) ∣[k] heckeMatrix p (e j).val := fun j => by
    obtain ⟨γ', ha, hc', hd, hmul⟩ := heckeMatrix_mul_eq hp j.val (e j).val hc (he j)
    obtain ⟨hγ'0, hdd⟩ := mem_Gamma0_of_entries hγ hc' hd
    have h := congrArg (fun g : GL (Fin 2) ℝ => (⇑f) ∣[k] g) hmul
    simp only [SlashAction.slash_mul] at h
    have hf' : (⇑f) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ' = c (γ 1 1) • (⇑f) := by
      rw [← hcM (γ 1 1) (γ' 1 1) hdd]
      exact hf γ' hγ'0
    rw [hf', ModularForm.smul_slash, σ_heckeMatrix, ContinuousAlgEquiv.refl_apply] at h
    exact h
  simp_rw [hterm]
  exact Equiv.sum_comp e (fun j : ZMod p => c (γ 1 1) • (⇑f) ∣[k] heckeMatrix p j.val)

private theorem heckeU₁_slash_Gamma0_chiNegThree (p : ℕ) [NeZero p] {M : ℕ} [NeZero M] (hM : 3 ∣ M) {k : ℤ}
    (f : CuspForm (Gamma1 M) k)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑f) ∣[k] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑f))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (p * M)) :
    (⇑(heckeU₁ p f)) ∣[k] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑(heckeU₁ p f)) := by
  refine heckeU₁_slash_Gamma0 p f (fun d : ℤ => ((chiNegThree ((d : ZMod 3).val) : ℤ) : ℂ)) ?_ hf γ hγ
  intro d d' hdd
  have h3 : ((d' : ℤ) : ZMod 3) = ((d : ℤ) : ZMod 3) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by
      have := dvd_trans (Int.natCast_dvd_natCast.mpr hM) hdd
      simpa using this.neg_right)
  simp only [h3]

private theorem qParam_heckeMatrix_smul (p : ℕ) (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((heckeMatrix p j • τ : ℍ) : ℂ) =
      Function.Periodic.qParam p (τ : ℂ) * zetaQ p ^ j := by
  rw [coe_heckeMatrix_smul hp, Function.Periodic.qParam, Function.Periodic.qParam, zetaQ, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem qParam_pow_self (p : ℕ) (hp : p ≠ 0) (z : ℂ) :
    Function.Periodic.qParam p z ^ p = Function.Periodic.qParam 1 z := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  have : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  push_cast
  rw [div_one, mul_comm]
  exact div_mul_cancel₀ _ this

private theorem qParam_heckeDiagMatrix_smul (p : ℕ) (hp : p ≠ 0) (τ : ℍ) :
    Function.Periodic.qParam 1 ((heckeDiagMatrix p • τ : ℍ) : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ p := by
  rw [coe_heckeDiagMatrix_smul hp, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  ring

private theorem hasSum_heckeMatrix_smul (p : ℕ) (hp : p ≠ 0) {M : ℕ} {k : ℤ} (f : CuspForm (Gamma1 M) k) (j : ℕ)
    (τ : ℍ) :
    HasSum (fun n : ℕ => (ModularFormClass.qCoeff (⇑f) n * zetaQ p ^ (j * n)) •
      Function.Periodic.qParam p (τ : ℂ) ^ n) (f (heckeMatrix p j • τ)) := by
  have h := hasSum_qCoeff_Gamma1 f (heckeMatrix p j • τ)
  simp_rw [qParam_heckeMatrix_smul p hp] at h
  convert h using 1
  funext n
  simp only [smul_eq_mul, mul_pow, ← pow_mul]
  ring

private theorem hasSum_heckeU (p : ℕ) [NeZero p] {M : ℕ} {k : ℤ} (f : CuspForm (Gamma1 M) k) (τ : ℍ) :
    HasSum (fun m : ℕ => ModularFormClass.qCoeff (⇑f) (p * m) • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (heckeU k p (⇑f) τ) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hS : HasSum (fun n : ℕ => (∑ j : ZMod p, ModularFormClass.qCoeff (⇑f) n * zetaQ p ^ (j.val * n)) •
      Function.Periodic.qParam p (τ : ℂ) ^ n) (∑ j : ZMod p, f (heckeMatrix p j.val • τ)) := by
    have := hasSum_sum (s := (Finset.univ : Finset (ZMod p)))
      (f := fun (j : ZMod p) (n : ℕ) => (ModularFormClass.qCoeff (⇑f) n * zetaQ p ^ (j.val * n)) •
        Function.Periodic.qParam p (τ : ℂ) ^ n) (fun j _ => hasSum_heckeMatrix_smul p hp f j.val τ)
    simpa only [Finset.sum_smul] using this
  have hval : heckeU k p (⇑f) τ = (p : ℂ)⁻¹ * ∑ j : ZMod p, f (heckeMatrix p j.val • τ) := by
    rw [heckeU_eq_sum_zmod, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => slash_heckeMatrix_apply k hp j.val (⇑f) τ
  have h1 : HasSum (fun n : ℕ => (if p ∣ n then ModularFormClass.qCoeff (⇑f) n else 0) •
      Function.Periodic.qParam p (τ : ℂ) ^ n) (heckeU k p (⇑f) τ) := by
    rw [hval]
    convert hS.mul_left ((p : ℂ)⁻¹) using 1
    all_goals try rfl
    funext n
    rw [← Finset.mul_sum, sum_zetaQ_pow p n]
    split_ifs with hpn
    · simp only [smul_eq_mul]
      rw [show (p : ℂ)⁻¹ * (ModularFormClass.qCoeff (⇑f) n * p * Function.Periodic.qParam p (τ : ℂ) ^ n) =
          ((p : ℂ)⁻¹ * p) * (ModularFormClass.qCoeff (⇑f) n * Function.Periodic.qParam p (τ : ℂ) ^ n) by ring,
        inv_mul_cancel₀ hpC, one_mul]
    · simp
  have h2 := (Function.Injective.hasSum_iff (mul_right_injective₀ hp) (fun x hx => by
      show (if p ∣ x then ModularFormClass.qCoeff (⇑f) x else 0) • Function.Periodic.qParam p (τ : ℂ) ^ x = 0
      rw [if_neg, zero_smul]
      rintro ⟨m, rfl⟩
      exact hx ⟨m, rfl⟩)).mpr h1
  convert h2 using 1
  funext m
  simp only [Function.comp_apply, if_pos (dvd_mul_right p m), pow_mul, qParam_pow_self p hp]

private theorem qCoeff_heckeU₁ (p : ℕ) [NeZero p] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(heckeU₁ p f)) n = ModularFormClass.qCoeff (⇑f) (p * n) := by
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => ModularFormClass.qCoeff (⇑f) (p * m) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (heckeU₁ p f τ) := fun τ => hasSum_heckeU p f τ
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma1' (p * M)) hsum n).symm

private theorem exists_heckeU₁ (p : ℕ) [NeZero p] {M : ℕ} [NeZero M] (hM : 3 ∣ M) {k : ℤ} (g : CuspForm (Gamma1 M) k)
    (hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑g) ∣[k] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑g))
    (b : ℕ → ℤ√(-2))
    (hgq : ∀ n, ModularFormClass.qCoeff (⇑g) n = ((b n).re : ℂ) + ((b n).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I)) :
    ∃ g' : CuspForm (Gamma1 (p * M)) k,
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 (p * M) →
        (⇑g') ∣[k] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑g')) ∧
      ∀ n, ModularFormClass.qCoeff (⇑g') n =
        ((b (p * n)).re : ℂ) + ((b (p * n)).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I) :=
  ⟨heckeU₁ p g, heckeU₁_slash_Gamma0_chiNegThree p hM g hg, fun n => by rw [qCoeff_heckeU₁, hgq]⟩

private theorem hasSum_slash_heckeDiagMatrix (p : ℕ) (hp : p ≠ 0) {N : ℕ} {k : ℤ} (F : CuspForm (Gamma1 N) k) (τ : ℍ) :
    HasSum (fun n : ℕ => (if p ∣ n then (p : ℂ) ^ (k - 1) * ModularFormClass.qCoeff (⇑F) (n / p) else 0) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ n) (((⇑F) ∣[k] heckeDiagMatrix p) τ) := by
  rw [slash_heckeDiagMatrix_apply k hp]
  have h := (hasSum_qCoeff_Gamma1 F (heckeDiagMatrix p • τ)).mul_left ((p : ℂ) ^ (k - 1))
  simp_rw [qParam_heckeDiagMatrix_smul p hp] at h
  refine (Function.Injective.hasSum_iff (mul_right_injective₀ hp) (fun x hx => ?_)).mp ?_
  · show (if p ∣ x then (p : ℂ) ^ (k - 1) * ModularFormClass.qCoeff (⇑F) (x / p) else 0) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ x = 0
    rw [if_neg, zero_smul]
    rintro ⟨m, rfl⟩
    exact hx ⟨m, rfl⟩
  · convert h using 1
    all_goals try rfl
    funext m
    simp only [Function.comp_apply, if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp),
      smul_eq_mul, pow_mul]
    ring

private theorem hasSum_heckeT_char (p : ℕ) [NeZero p] {N : ℕ} {k : ℤ} (F : CuspForm (Gamma1 N) k) (ε : ℂ) (τ : ℍ) :
    HasSum (fun n : ℕ => (ModularFormClass.qCoeff (⇑F) (p * n) +
        ε * (if p ∣ n then (p : ℂ) ^ (k - 1) * ModularFormClass.qCoeff (⇑F) (n / p) else 0)) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (heckeU k p (⇑F) τ + ε * ((⇑F) ∣[k] heckeDiagMatrix p) τ) := by
  have h := (hasSum_heckeU p F τ).add ((hasSum_slash_heckeDiagMatrix p (NeZero.ne p) F τ).mul_left ε)
  convert h using 1
  funext n
  simp only [smul_eq_mul]
  ring

private theorem qCoeff_smul_Gamma1 {N : ℕ} {k : ℤ} (a : ℂ) (F : CuspForm (Gamma1 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(a • F)) n = a * ModularFormClass.qCoeff (⇑F) n := by
  simp only [ModularFormClass.qCoeff, CuspForm.IsGLPos.coe_smul]
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1' N) a F, map_smul, smul_eq_mul]

private theorem qCoeff_rel_of_heckeT_char_eq_mul (p : ℕ) [NeZero p] {N : ℕ} {k : ℤ} (F : CuspForm (Gamma1 N) k) (ε a : ℂ)
    (hT : ∀ τ : ℍ, heckeU k p (⇑F) τ + ε * ((⇑F) ∣[k] heckeDiagMatrix p) τ = a * F τ) (n : ℕ) :
    ModularFormClass.qCoeff (⇑F) (p * n) +
        ε * (if p ∣ n then (p : ℂ) ^ (k - 1) * ModularFormClass.qCoeff (⇑F) (n / p) else 0) =
      a * ModularFormClass.qCoeff (⇑F) n := by
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => (ModularFormClass.qCoeff (⇑F) (p * m) +
        ε * (if p ∣ m then (p : ℂ) ^ (k - 1) * ModularFormClass.qCoeff (⇑F) (m / p) else 0)) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) ((a • F) τ) := fun τ => by
    rw [CuspForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul, ← hT τ]
    exact hasSum_heckeT_char p F ε τ
  refine (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma1' N) hsum n).trans ?_
  exact qCoeff_smul_Gamma1 a F n

private theorem qCoeff_rel_of_heckeT_char_eq_mul_weightOne (p : ℕ) [NeZero p] {N : ℕ} (F : CuspForm (Gamma1 N) 1)
    (ε a : ℂ) (hT : ∀ τ : ℍ, heckeU 1 p (⇑F) τ + ε * ((⇑F) ∣[(1 : ℤ)] heckeDiagMatrix p) τ = a * F τ) (n : ℕ) :
    ModularFormClass.qCoeff (⇑F) (p * n) + ε * (if p ∣ n then ModularFormClass.qCoeff (⇑F) (n / p) else 0) =
      a * ModularFormClass.qCoeff (⇑F) n := by
  have h := qCoeff_rel_of_heckeT_char_eq_mul p F ε a hT n
  simpa only [sub_self, zpow_zero, one_mul] using h

private def transl (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.upperRightHom t

@[scoped simp] private theorem transl_apply_00 (t : ℝ) : (transl t : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by
  simp [transl, Matrix.GeneralLinearGroup.upperRightHom_apply]

@[scoped simp] private theorem transl_apply_01 (t : ℝ) : (transl t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = t := by
  simp [transl, Matrix.GeneralLinearGroup.upperRightHom_apply]

@[scoped simp] private theorem transl_apply_10 (t : ℝ) : (transl t : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  simp [transl, Matrix.GeneralLinearGroup.upperRightHom_apply]

@[scoped simp] private theorem transl_apply_11 (t : ℝ) : (transl t : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by
  simp [transl, Matrix.GeneralLinearGroup.upperRightHom_apply]

private theorem det_transl (t : ℝ) : (transl t).det.val = 1 := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

@[scoped simp] private theorem det_coe_transl (t : ℝ) : (transl t : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  simp [Matrix.det_fin_two]

private theorem σ_transl (t : ℝ) (z : ℂ) : σ (transl t) z = z := by
  have h : 0 < (transl t).det.val := by rw [det_transl]; norm_num
  rw [σ, if_pos h]
  rfl

private theorem coe_transl_smul (t : ℝ) (τ : ℍ) : ((transl t • τ : ℍ) : ℂ) = (τ : ℂ) + (t : ℂ) := by
  rw [UpperHalfPlane.coe_smul, σ_transl, num, denom]
  simp

private theorem slash_transl_apply {k : ℤ} (f : ℍ → ℂ) (t : ℝ) (τ : ℍ) : (f ∣[k] transl t) τ = f (transl t • τ) := by
  rw [ModularForm.slash_apply, σ_transl, det_transl, denom]
  simp

private theorem qParam_transl_smul (q j : ℕ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((transl ((j : ℝ) / q) • τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) * zetaQ q ^ j := by
  rw [coe_transl_smul, Function.Periodic.qParam, Function.Periodic.qParam, zetaQ, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem transl_mul_eq' (q M : ℕ) (hq : q ≠ 0) (j j' : ℕ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (q ^ 2 * M))
    (hjj : (q : ℤ) ∣ (j : ℤ) * γ 1 1 - (j' : ℤ) * γ 0 0) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 M ∧ (M : ℤ) ∣ γ' 0 0 - γ 0 0 ∧ (M : ℤ) ∣ γ' 1 1 - γ 1 1 ∧
      transl ((j : ℝ) / q) * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ γ' * transl ((j' : ℝ) / q) := by
  have hqM : (((q ^ 2 * M : ℕ)) : ℤ) ∣ (γ 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨u, hu⟩ : ((q : ℤ) ^ 2 * M) ∣ (γ 1 0 : ℤ) := by exact_mod_cast hqM
  obtain ⟨w, hw⟩ := hjj
  have hdet := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [γ.det_coe] at hdet
  have hc : (γ 1 0 : ℤ) = q ^ 2 * M * u := hu
  have hdet' : (γ 0 0 + j * q * M * u) * (γ 1 1 - j' * q * M * u)
      - (γ 0 1 + w - j * j' * M * u) * (γ 1 0 : ℤ) = 1 := by
    rw [hc] at hdet ⊢
    linear_combination -hdet + (q : ℤ) * M * u * hw
  refine ⟨⟨!![γ 0 0 + j * q * M * u, γ 0 1 + w - j * j' * M * u; γ 1 0, γ 1 1 - j' * q * M * u],
      by rw [Matrix.det_fin_two_of]; exact hdet'⟩, ?_, ?_, ?_, ?_⟩
  · rw [Gamma0_mem]
    show (((γ 1 0 : ℤ)) : ZMod M) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
    exact ⟨q ^ 2 * u, by ring⟩
  · show (M : ℤ) ∣ (γ 0 0 + j * q * M * u) - γ 0 0
    exact ⟨j * q * u, by ring⟩
  · show (M : ℤ) ∣ (γ 1 1 - j' * q * M * u) - γ 1 1
    exact ⟨-(j' * q * u), by ring⟩
  · have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    have hcR : ((γ 1 0 : ℤ) : ℝ) = (q : ℝ) ^ 2 * M * u := by exact_mod_cast hc
    have hwR : (j : ℝ) * ((γ 1 1 : ℤ) : ℝ) - (j' : ℝ) * ((γ 0 0 : ℤ) : ℝ) = q * w := by exact_mod_cast hw
    refine (Matrix.GeneralLinearGroup.ext_iff _ _).mpr fun i i' => ?_
    rw [Units.val_mul, Units.val_mul]
    fin_cases i <;> fin_cases i' <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.mapGL,
        Matrix.SpecialLinearGroup.map_apply_coe]
    · linear_combination (norm := (field_simp; ring)) ((j : ℝ) / q) * hcR
    · linear_combination (norm := (field_simp; ring)) (1 / (q : ℝ)) * hwR
    · linear_combination (norm := (field_simp; ring)) (-(j' : ℝ) / q) * hcR

private theorem mem_Gamma1_of_congr {M : ℕ} {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) (h0 : γ' ∈ Gamma0 M)
    (ha : (M : ℤ) ∣ γ' 0 0 - γ 0 0) (hd : (M : ℤ) ∣ γ' 1 1 - γ 1 1) : γ' ∈ Gamma1 M := by
  rw [Gamma1_mem] at hγ ⊢
  refine ⟨?_, ?_, Gamma0_mem.mp h0⟩
  · rw [← hγ.1]; exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by simpa using ha.neg_right)
  · rw [← hγ.2.1]; exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by simpa using hd.neg_right)

private theorem Gamma1_sq_mul_le_Gamma1 (q M : ℕ) : Gamma1 (q ^ 2 * M) ≤ Gamma1 M := Gamma1_le_of_dvd (dvd_mul_left M (q ^ 2))

private theorem Gamma_le_conj_transl₁ (q M : ℕ) (hq : q ≠ 0) (j : ℕ) :
    ((Gamma (q ^ 2 * M) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (transl ((j : ℝ) / q))⁻¹ •
        ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct]
  have hγ' := Gamma_mem.mp hγ
  have hγ0 : γ ∈ Gamma0 (q ^ 2 * M) := by
    rw [Gamma0_mem]
    exact hγ'.2.2.1
  have hγ1 : γ ∈ Gamma1 (q ^ 2 * M) := by
    rw [Gamma1_mem]
    exact ⟨hγ'.1, hγ'.2.2.2, hγ'.2.2.1⟩
  have hjj : (q : ℤ) ∣ (j : ℤ) * γ 1 1 - (j : ℤ) * γ 0 0 := by
    have h1 : ((γ 1 1 : ℤ) : ZMod (q ^ 2 * M)) = ((γ 0 0 : ℤ) : ZMod (q ^ 2 * M)) := by
      rw [hγ'.1, hγ'.2.2.2]
    have h2 : (((q ^ 2 * M : ℕ)) : ℤ) ∣ (γ 1 1 : ℤ) - γ 0 0 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1.symm
    rw [← mul_sub]
    exact dvd_mul_of_dvd_right (dvd_trans ⟨(q : ℤ) * M, by push_cast; ring⟩ h2) _
  obtain ⟨γ', hγ'0, ha, hd, hmul⟩ := transl_mul_eq' q M hq j j hγ0 hjj
  rw [hmul, mul_inv_cancel_right]
  exact Subgroup.mem_map.mpr ⟨γ', mem_Gamma1_of_congr (Gamma1_sq_mul_le_Gamma1 q M hγ1) hγ'0 ha hd, rfl⟩

private def sumTranslGamma₁ (q : ℕ) [NeZero q] {M : ℕ} {k : ℤ} (f : CuspForm (Gamma1 M) k) :
    CuspForm (Gamma (q ^ 2 * M)) k :=
  ∑ j : ZMod q, restrictCusp (Gamma_le_conj_transl₁ q M (NeZero.ne q) j.val)
    (CuspForm.translate f (transl ((j.val : ℝ) / q)))

private theorem coe_sumTranslGamma₁ (q : ℕ) [NeZero q] {M : ℕ} {k : ℤ} (f : CuspForm (Gamma1 M) k) :
    ⇑(sumTranslGamma₁ q f) = ∑ j : ZMod q, (⇑f) ∣[k] transl ((j.val : ℝ) / q) := by
  rw [sumTranslGamma₁, coe_finset_sum]
  rfl

private theorem exists_reindex (q : ℕ) [NeZero q] {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (q ^ 2 * M)) :
    ∃ e : ZMod q ≃ ZMod q, ∀ j : ZMod q, (q : ℤ) ∣ (j.val : ℤ) * γ 1 1 - ((e j).val : ℤ) * γ 0 0 := by
  have hq : q ≠ 0 := NeZero.ne q
  have hc0 : ((γ 1 0 : ℤ) : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hqM : (((q ^ 2 * M : ℕ)) : ℤ) ∣ (γ 1 0 : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    exact dvd_trans ⟨(q : ℤ) * M, by push_cast; ring⟩ hqM
  have had : ((γ 0 0 : ℤ) : ZMod q) * ((γ 1 1 : ℤ) : ZMod q) = 1 := by
    have hdet := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
    rw [γ.det_coe] at hdet
    have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
    simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, hc0, mul_zero, sub_zero] at this
    exact this.symm
  set dq : ZMod q := ((γ 1 1 : ℤ) : ZMod q) with hdq
  set aq : ZMod q := ((γ 0 0 : ℤ) : ZMod q) with haq
  have hunit : IsUnit (dq ^ 2) := (IsUnit.of_mul_eq_one aq (by rw [mul_comm]; exact had)).pow 2
  refine ⟨Units.mulLeft hunit.unit, fun j => ?_⟩
  have he : (Units.mulLeft hunit.unit : ZMod q ≃ ZMod q) j = dq ^ 2 * j := rfl
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, he, ← hdq, ← haq]
  linear_combination (-(j * dq)) * had

private theorem sumTransl_slash₁ (q : ℕ) [NeZero q] {M : ℕ} {k : ℤ} (f : CuspForm (Gamma1 M) k)
    (x : GL (Fin 2) ℝ) (hx : x ∈ ((Gamma1 (q ^ 2 * M) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (∑ j : ZMod q, (⇑f) ∣[k] transl ((j.val : ℝ) / q)) ∣[k] x =
      ∑ j : ZMod q, (⇑f) ∣[k] transl ((j.val : ℝ) / q) := by
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
  have hq : q ≠ 0 := NeZero.ne q
  have hγ0 : γ ∈ Gamma0 (q ^ 2 * M) := Gamma1_in_Gamma0 _ hγ
  obtain ⟨e, he⟩ := exists_reindex q hγ0
  rw [sum_slash]
  have hterm : ∀ j : ZMod q,
      ((⇑f) ∣[k] transl ((j.val : ℝ) / q)) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ =
      (⇑f) ∣[k] transl (((e j).val : ℝ) / q) := fun j => by
    obtain ⟨γ', hγ'0, ha, hd, hmul⟩ := transl_mul_eq' q M hq j.val (e j).val hγ0 (he j)
    have hγ'1 : γ' ∈ Gamma1 M := mem_Gamma1_of_congr (Gamma1_sq_mul_le_Gamma1 q M hγ) hγ'0 ha hd
    have h := congrArg (fun g : GL (Fin 2) ℝ => (⇑f) ∣[k] g) hmul
    simp only [SlashAction.slash_mul] at h
    rw [SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map.mpr ⟨γ', hγ'1, rfl⟩)] at h
    exact h
  simp_rw [hterm]
  exact Equiv.sum_comp e (fun j : ZMod q => (⇑f) ∣[k] transl ((j.val : ℝ) / q))

private def sumTransl₁ (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) :
    CuspForm (Gamma1 (q ^ 2 * M)) k where
  toFun := ∑ j : ZMod q, (⇑f) ∣[k] transl ((j.val : ℝ) / q)
  slash_action_eq' x hx := sumTransl_slash₁ q f x hx
  holo' := by
    have h := ModularFormClass.holo (sumTranslGamma₁ q f)
    rwa [coe_sumTranslGamma₁] at h
  zero_at_cusps' {c} hc := by
    haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero 2 (NeZero.ne q)) (NeZero.ne M)⟩
    have hc' : IsCusp c ((Gamma (q ^ 2 * M) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)
    have h := CuspFormClass.zero_at_cusps (sumTranslGamma₁ q f) hc'
    rwa [coe_sumTranslGamma₁] at h

@[scoped simp] private theorem coe_sumTransl₁ (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) :
    ⇑(sumTransl₁ q f) = ∑ j : ZMod q, (⇑f) ∣[k] transl ((j.val : ℝ) / q) := rfl

private theorem sumTransl₁_apply (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) (τ : ℍ) :
    sumTransl₁ q f τ = ∑ j : ZMod q, f (transl ((j.val : ℝ) / q) • τ) := by
  rw [coe_sumTransl₁, Finset.sum_apply]
  simp_rw [slash_transl_apply]

private theorem sumTransl₁_slash_Gamma0 (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k)
    (c : ℤ → ℂ) (hcM : ∀ d d' : ℤ, (M : ℤ) ∣ d' - d → c d' = c d)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → (⇑f) ∣[k] γ = c (γ 1 1) • (⇑f))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (q ^ 2 * M)) :
    (⇑(sumTransl₁ q f)) ∣[k] γ = c (γ 1 1) • (⇑(sumTransl₁ q f)) := by
  have hq : q ≠ 0 := NeZero.ne q
  obtain ⟨e, he⟩ := exists_reindex q hγ
  show (⇑(sumTransl₁ q f)) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ = _
  rw [coe_sumTransl₁, sum_slash, Finset.smul_sum]
  have hterm : ∀ j : ZMod q,
      ((⇑f) ∣[k] transl ((j.val : ℝ) / q)) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ =
      c (γ 1 1) • (⇑f) ∣[k] transl (((e j).val : ℝ) / q) := fun j => by
    obtain ⟨γ', hγ'0, ha, hd, hmul⟩ := transl_mul_eq' q M hq j.val (e j).val hγ (he j)
    have h := congrArg (fun g : GL (Fin 2) ℝ => (⇑f) ∣[k] g) hmul
    simp only [SlashAction.slash_mul] at h
    have hf' : (⇑f) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ' = c (γ 1 1) • (⇑f) := by
      rw [← hcM (γ 1 1) (γ' 1 1) hd]
      exact hf γ' hγ'0
    rw [hf', ModularForm.smul_slash, σ_transl] at h
    exact h
  simp_rw [hterm]
  exact Equiv.sum_comp e (fun j : ZMod q => c (γ 1 1) • (⇑f) ∣[k] transl ((j.val : ℝ) / q))

private theorem Gamma1_sq_mul_le (q M : ℕ) :
    ((Gamma1 (q ^ 2 * M) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma1_sq_mul_le_Gamma1 q M)

private def deprive₁ (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) :
    CuspForm (Gamma1 (q ^ 2 * M)) k :=
  restrictCusp (Gamma1_sq_mul_le q M) f - (q : ℂ)⁻¹ • sumTransl₁ q f

private theorem coe_deprive₁ (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) :
    ⇑(deprive₁ q f) = ⇑f - (q : ℂ)⁻¹ • ⇑(sumTransl₁ q f) := by
  rw [deprive₁, CuspForm.coe_sub, CuspForm.IsGLPos.coe_smul, coe_restrictCusp]

private theorem deprive₁_apply (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) (τ : ℍ) :
    deprive₁ q f τ = f τ - (q : ℂ)⁻¹ * ∑ j : ZMod q, f (transl ((j.val : ℝ) / q) • τ) := by
  rw [coe_deprive₁, Pi.sub_apply, Pi.smul_apply, sumTransl₁_apply, smul_eq_mul]

private theorem deprive₁_slash_Gamma0 (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k)
    (c : ℤ → ℂ) (hcM : ∀ d d' : ℤ, (M : ℤ) ∣ d' - d → c d' = c d)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → (⇑f) ∣[k] γ = c (γ 1 1) • (⇑f))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (q ^ 2 * M)) :
    (⇑(deprive₁ q f)) ∣[k] γ = c (γ 1 1) • (⇑(deprive₁ q f)) := by
  have h0 : γ ∈ Gamma0 M := Gamma0_le_of_dvd (dvd_mul_left M (q ^ 2)) hγ
  rw [coe_deprive₁, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.SL_smul_slash, hf γ h0,
    sumTransl₁_slash_Gamma0 q f c hcM hf γ hγ, smul_add, smul_neg, smul_comm (c (γ 1 1)) ((q : ℂ)⁻¹)]

private theorem deprive₁_slash_Gamma0_chiNegThree (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] (hM : 3 ∣ M) {k : ℤ}
    (f : CuspForm (Gamma1 M) k)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑f) ∣[k] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑f))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (q ^ 2 * M)) :
    (⇑(deprive₁ q f)) ∣[k] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑(deprive₁ q f)) := by
  refine deprive₁_slash_Gamma0 q f (fun d : ℤ => ((chiNegThree ((d : ZMod 3).val) : ℤ) : ℂ)) ?_ hf γ hγ
  intro d d' hdd
  have h3 : ((d' : ℤ) : ZMod 3) = ((d : ℤ) : ZMod 3) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by
      have := dvd_trans (Int.natCast_dvd_natCast.mpr hM) hdd
      simpa using this.neg_right)
  simp only [h3]

private theorem hasSum_transl₁ (q : ℕ) {M : ℕ} {k : ℤ} (f : CuspForm (Gamma1 M) k) (j : ℕ) (τ : ℍ) :
    HasSum (fun n : ℕ => (ModularFormClass.qCoeff (⇑f) n * zetaQ q ^ (j * n)) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ n) (f (transl ((j : ℝ) / q) • τ)) := by
  have h := hasSum_qCoeff_Gamma1 f (transl ((j : ℝ) / q) • τ)
  simp_rw [qParam_transl_smul] at h
  convert h using 1
  funext n
  simp only [smul_eq_mul, mul_pow, ← pow_mul]
  ring

private theorem qCoeff_deprive₁ (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] {k : ℤ} (f : CuspForm (Gamma1 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(deprive₁ q f)) n = if q ∣ n then 0 else ModularFormClass.qCoeff (⇑f) n := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => (if q ∣ m then 0 else ModularFormClass.qCoeff (⇑f) m) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (deprive₁ q f τ) := fun τ => by
    have hS : HasSum (fun m : ℕ => (∑ j : ZMod q, ModularFormClass.qCoeff (⇑f) m * zetaQ q ^ (j.val * m)) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (∑ j : ZMod q, f (transl ((j.val : ℝ) / q) • τ)) := by
      have := hasSum_sum (s := (Finset.univ : Finset (ZMod q)))
        (f := fun (j : ZMod q) (m : ℕ) => (ModularFormClass.qCoeff (⇑f) m * zetaQ q ^ (j.val * m)) •
          Function.Periodic.qParam 1 (τ : ℂ) ^ m) (fun j _ => hasSum_transl₁ q f j.val τ)
      simpa only [Finset.sum_smul] using this
    have h := (hasSum_qCoeff_Gamma1 f τ).sub (hS.mul_left (q : ℂ)⁻¹)
    rw [deprive₁_apply]
    convert h using 1
    all_goals try rfl
    funext m
    rw [← Finset.mul_sum, sum_zetaQ_pow q m]
    split_ifs with hqm
    · simp only [smul_eq_mul, zero_mul]
      field_simp
      ring
    · simp only [smul_eq_mul, mul_zero, zero_mul, sub_zero]
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma1' (q ^ 2 * M)) hsum n).symm

private theorem exists_deprive₁ (q : ℕ) [NeZero q] {M : ℕ} [NeZero M] (hM : 3 ∣ M) {k : ℤ} (g : CuspForm (Gamma1 M) k)
    (hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑g) ∣[k] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑g))
    (b : ℕ → ℤ√(-2))
    (hgq : ∀ n, ModularFormClass.qCoeff (⇑g) n = ((b n).re : ℂ) + ((b n).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I)) :
    ∃ g' : CuspForm (Gamma1 (q ^ 2 * M)) k,
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 (q ^ 2 * M) →
        (⇑g') ∣[k] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑g')) ∧
      ∀ n, ModularFormClass.qCoeff (⇑g') n =
        (((if q ∣ n then 0 else b n : ℤ√(-2))).re : ℂ) +
          (((if q ∣ n then 0 else b n : ℤ√(-2))).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I) :=
  ⟨deprive₁ q g, deprive₁_slash_Gamma0_chiNegThree q hM g hg, fun n => by
    rw [qCoeff_deprive₁, hgq n]; split_ifs <;> simp⟩

section FormalCore

variable {R : Type*} [CommRing R]

private def ppow (e c : ℕ → R) (ℓ : ℕ) : ℕ → R
  | 0 => 1
  | 1 => c ℓ
  | (k + 2) => c ℓ * ppow e c ℓ (k + 1) - e ℓ * ppow e c ℓ k

@[scoped simp] private theorem ppow_zero (e c : ℕ → R) (ℓ : ℕ) : ppow e c ℓ 0 = 1 := rfl

@[scoped simp] private theorem ppow_one (e c : ℕ → R) (ℓ : ℕ) : ppow e c ℓ 1 = c ℓ := rfl

private theorem ppow_add_two (e c : ℕ → R) (ℓ k : ℕ) :
    ppow e c ℓ (k + 2) = c ℓ * ppow e c ℓ (k + 1) - e ℓ * ppow e c ℓ k := rfl

private noncomputable def extend (e c : ℕ → R) (n : ℕ) : R :=
  if n = 0 then 0 else n.factorization.prod fun ℓ k => ppow e c ℓ k

@[scoped simp] private theorem extend_zero (e c : ℕ → R) : extend e c 0 = 0 := by
  simp [extend]

@[scoped simp] private theorem extend_one (e c : ℕ → R) : extend e c 1 = 1 := by
  simp [extend]

private theorem extend_prime_pow_mul (e c : ℕ → R) {ℓ m : ℕ} (hℓ : ℓ.Prime) (hm : m ≠ 0) (hℓm : ¬ ℓ ∣ m)
    (k : ℕ) : extend e c (ℓ ^ k * m) = ppow e c ℓ k * extend e c m := by
  have hℓk : ℓ ^ k ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have hd : Disjoint (Finsupp.single ℓ k).support m.factorization.support := by
    rw [Finset.disjoint_left]
    intro x hx hxm
    have hxℓ : x = ℓ := Finset.mem_singleton.mp (Finsupp.support_single_subset hx)
    rw [hxℓ, Nat.support_factorization, Nat.mem_primeFactors] at hxm
    exact hℓm hxm.2.1
  rw [extend, if_neg (mul_ne_zero hℓk hm), extend, if_neg hm, Nat.factorization_mul hℓk hm,
    hℓ.factorization_pow, Finsupp.prod_add_index_of_disjoint hd,
    Finsupp.prod_single_index (ppow_zero e c ℓ)]

private theorem extend_prime (e c : ℕ → R) {ℓ : ℕ} (hℓ : ℓ.Prime) : extend e c ℓ = c ℓ := by
  have h := extend_prime_pow_mul e c hℓ one_ne_zero hℓ.not_dvd_one 1
  simpa using h

private theorem isEigensystem_extend (e c : ℕ → R) : FormalHecke.IsEigensystem e (extend e c) := by
  refine ⟨extend_one e c, fun ℓ hℓ n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨k, m, hm0, hℓm, rfl⟩ : ∃ k m : ℕ, m ≠ 0 ∧ ¬ ℓ ∣ m ∧ n = ℓ ^ k * m :=
    ⟨n.factorization ℓ, n / ℓ ^ n.factorization ℓ, (Nat.ordCompl_pos ℓ hn.ne').ne',
      Nat.not_dvd_ordCompl hℓ hn.ne', (Nat.ordProj_mul_ordCompl_eq_self n ℓ).symm⟩
  rw [extend_prime e c hℓ, show ℓ * (ℓ ^ k * m) = ℓ ^ (k + 1) * m by ring,
    extend_prime_pow_mul e c hℓ hm0 hℓm, extend_prime_pow_mul e c hℓ hm0 hℓm]
  cases k with
  | zero =>
    have h0 : ¬ ℓ ∣ ℓ ^ 0 * m := by simpa using hℓm
    rw [if_neg h0]
    simp
  | succ j =>
    have hdvd : ℓ ∣ ℓ ^ (j + 1) * m := Dvd.dvd.mul_right (dvd_pow_self ℓ j.succ_ne_zero) m
    have hdiv : ℓ ^ (j + 1) * m / ℓ = ℓ ^ j * m := by
      rw [show ℓ ^ (j + 1) * m = ℓ * (ℓ ^ j * m) by ring, Nat.mul_div_cancel_left _ hℓ.pos]
    rw [if_pos hdvd, hdiv, extend_prime_pow_mul e c hℓ hm0 hℓm, ppow_add_two]
    ring

private theorem exists_isEigensystem_of_primeData (e c : ℕ → R) :
    ∃ a : ℕ → R, FormalHecke.IsEigensystem e a ∧ a 0 = 0 ∧ ∀ ℓ : ℕ, ℓ.Prime → a ℓ = c ℓ :=
  ⟨extend e c, isEigensystem_extend e c, extend_zero e c, fun _ hℓ => extend_prime e c hℓ⟩

end FormalCore
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

private def iotaW : ℤ√(-2) →+* ℂ :=
  Zsqrtd.lift ⟨(Real.sqrt 2 : ℂ) * Complex.I, by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    calc ((Real.sqrt 2 : ℂ) * Complex.I) * ((Real.sqrt 2 : ℂ) * Complex.I)
        = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) * (Complex.I * Complex.I) := by ring
      _ = ((-2 : ℤ) : ℂ) := by rw [h2, Complex.I_mul_I]; norm_num⟩

private theorem iotaW_apply (z : ℤ√(-2)) :
    iotaW z = (z.re : ℂ) + (z.im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I) := rfl

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

namespace HeckeDictionary

section Extract

variable {R : Type*} [CommRing R]

private theorem extend_mul_of_coprime (e c : ℕ → R) {m n : ℕ} (hmn : Nat.Coprime m n) :
    extend e c (m * n) = extend e c m * extend e c n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hd : Disjoint m.factorization.support n.factorization.support := by
    rw [Nat.support_factorization, Nat.support_factorization]
    exact hmn.disjoint_primeFactors
  rw [extend, if_neg (mul_ne_zero hm hn), extend, if_neg hm, extend, if_neg hn,
    Nat.factorization_mul_of_coprime hmn, Finsupp.prod_add_index_of_disjoint hd]

private theorem extend_prime_pow (e c : ℕ → R) {p : ℕ} (hp : p.Prime) (r : ℕ) :
    extend e c (p ^ r) = ppow e c p r := by
  have h := extend_prime_pow_mul e c hp one_ne_zero hp.not_dvd_one r
  rwa [mul_one, extend_one, mul_one] at h

private theorem ppow_succ_eq_zero (e c : ℕ → R) {q : ℕ} (he : e q = 0) (hc : c q = 0) : ∀ k : ℕ, ppow e c q (k + 1) = 0
  | 0 => by rw [ppow_one, hc]
  | k + 1 => by rw [ppow_add_two, hc, he, zero_mul, zero_mul, sub_zero]

private theorem extend_eq_zero_of_dvd (e c : ℕ → R) {q : ℕ} (hq : q.Prime) (he : e q = 0) (hc : c q = 0) {n : ℕ}
    (hqn : q ∣ n) : extend e c n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact extend_zero e c
  have hk : 1 ≤ n.factorization q := (hq.dvd_iff_one_le_factorization hn).mp hqn
  obtain ⟨k, hk'⟩ := Nat.exists_eq_add_of_le' hk
  rw [← Nat.ordProj_mul_ordCompl_eq_self n q, extend_prime_pow_mul e c hq (Nat.ordCompl_pos q hn).ne'
    (Nat.not_dvd_ordCompl hq hn), hk', ppow_succ_eq_zero e c he hc k, zero_mul]

private def depLevel : List ℕ → ℕ → ℕ
  | [], M => M
  | q :: l, M => q ^ 2 * depLevel l M

private theorem depLevel_ne_zero : ∀ (l : List ℕ) {M : ℕ}, (∀ q ∈ l, q ≠ 0) → M ≠ 0 → depLevel l M ≠ 0
  | [], _, _, hM => hM
  | q :: l, _, hl, hM =>
      mul_ne_zero (pow_ne_zero 2 (hl q List.mem_cons_self))
        (depLevel_ne_zero l (fun r hr => hl r (List.mem_cons_of_mem q hr)) hM)

private theorem dvd_depLevel : ∀ (l : List ℕ) (M : ℕ), M ∣ depLevel l M
  | [], _ => dvd_rfl
  | _ :: l, M => (dvd_depLevel l M).trans (dvd_mul_left _ _)

private theorem dvd_depLevel_of_mem : ∀ (l : List ℕ) (M : ℕ) {q : ℕ}, q ∈ l → q ∣ depLevel l M
  | [], _, _, h => absurd h List.not_mem_nil
  | r :: l, M, q, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) _
      · exact (dvd_depLevel_of_mem l M h).trans (dvd_mul_left _ _)

private theorem prime_dvd_depLevel : ∀ (l : List ℕ) (M : ℕ), (∀ q ∈ l, q.Prime) → ∀ {p : ℕ}, p.Prime →
    p ∣ depLevel l M → p ∣ M ∨ p ∈ l
  | [], _, _, _, _, h => Or.inl h
  | q :: l, M, hl, p, hp, h => by
      rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (hl q List.mem_cons_self)).mp (hp.dvd_of_dvd_pow h))))
      · rcases prime_dvd_depLevel l M (fun r hr => hl r (List.mem_cons_of_mem q hr)) hp h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem q h)

private def depriveList {k : ℤ} : (l : List ℕ) → (∀ q ∈ l, q.Prime) → {M : ℕ} → [NeZero M] →
    CuspForm (Gamma1 M) k → CuspForm (Gamma1 (depLevel l M)) k
  | [], _, _, _, f => f
  | q :: l, hl, M, _, f =>
      haveI : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
      haveI : NeZero (depLevel l M) :=
        ⟨depLevel_ne_zero l (fun r hr => (hl r (List.mem_cons_of_mem q hr)).ne_zero) (NeZero.ne M)⟩
      deprive₁ q (depriveList l (fun r hr => hl r (List.mem_cons_of_mem q hr)) f)

private theorem depriveList_slash_Gamma0_chiNegThree {k : ℤ} : ∀ (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) {M : ℕ} [NeZero M],
    3 ∣ M → ∀ (f : CuspForm (Gamma1 M) k),
    (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑f) ∣[k] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑f)) →
    ∀ γ : SL(2, ℤ), γ ∈ Gamma0 (depLevel l M) →
      (⇑(depriveList l hl f)) ∣[k] γ =
        ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑(depriveList l hl f))
  | [], _, _, _, _, _, hf => hf
  | q :: l, hl, M, _, hM, f, hf => by
      haveI : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
      haveI : NeZero (depLevel l M) :=
        ⟨depLevel_ne_zero l (fun r hr => (hl r (List.mem_cons_of_mem q hr)).ne_zero) (NeZero.ne M)⟩
      intro γ hγ
      simp only [depriveList]
      exact deprive₁_slash_Gamma0_chiNegThree q ((hM.trans (dvd_depLevel l M))) _
        (depriveList_slash_Gamma0_chiNegThree l _ hM f hf) γ hγ

private theorem qCoeff_depriveList {k : ℤ} : ∀ (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) {M : ℕ} [NeZero M]
    (f : CuspForm (Gamma1 M) k) (n : ℕ),
    ModularFormClass.qCoeff (⇑(depriveList l hl f)) n =
      if ∃ q ∈ l, q ∣ n then 0 else ModularFormClass.qCoeff (⇑f) n
  | [], _, _, _, f, n => by
      rw [if_neg (by simp)]
      rfl
  | q :: l, hl, M, _, f, n => by
      haveI : NeZero q := ⟨(hl q List.mem_cons_self).ne_zero⟩
      haveI : NeZero (depLevel l M) :=
        ⟨depLevel_ne_zero l (fun r hr => (hl r (List.mem_cons_of_mem q hr)).ne_zero) (NeZero.ne M)⟩
      have key := qCoeff_deprive₁ q (depriveList l (fun r hr => hl r (List.mem_cons_of_mem q hr)) f) n
      rw [qCoeff_depriveList l _ f n] at key
      refine key.trans ?_
      by_cases hq : q ∣ n
      · rw [if_pos hq, if_pos ⟨q, List.mem_cons_self, hq⟩]
      · rw [if_neg hq]
        by_cases hr : ∃ r ∈ l, r ∣ n
        · rw [if_pos hr, if_pos (hr.imp fun r ⟨hr, hrn⟩ => ⟨List.mem_cons_of_mem q hr, hrn⟩)]
        · rw [if_neg hr, if_neg]
          rintro ⟨r, hr', hrn⟩
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact hq hrn
          · exact hr ⟨r, hr', hrn⟩

private theorem coe_eq_zero_of_qCoeff_eq_zero {N : ℕ} {k : ℤ} (F : CuspForm (Gamma1 N) k)
    (h : ∀ n, n ≠ 0 → ModularFormClass.qCoeff (⇑F) n = 0) : (⇑F : ℍ → ℂ) = 0 := by
  have h0 : ModularFormClass.qCoeff (⇑F) 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero F one_pos (one_mem_strictPeriods_Gamma1' N)
  have hall : ∀ n, ModularFormClass.qCoeff (⇑F) n = 0 := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · exact h0
    · exact h n hn
  funext τ
  have hs := hasSum_qCoeff_Gamma1 F τ
  simp only [hall, zero_smul] at hs
  exact hs.unique hasSum_zero

set_option linter.unusedVariables false in
private theorem exists_engineInput {N : ℕ} [NeZero N] (hN : 3 ∣ N) (F : CuspForm (Gamma1 N) 1)
    (hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
      (⇑F) ∣[(1 : ℤ)] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑F))
    (𝔅 : Finset ℕ) (a : ℕ → ℤ√(-2))
    (hrel : ∀ p : ℕ, p.Prime → p ∉ 𝔅 → ¬ p ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑F) (p * n) +
          ((chiNegThree p : ℤ) : ℂ) * (if p ∣ n then ModularFormClass.qCoeff (⇑F) (n / p) else 0) =
        (((a p).re : ℂ) + ((a p).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I)) * ModularFormClass.qCoeff (⇑F) n)
    (hF : (⇑F : ℍ → ℂ) ≠ 0) (T : Finset ℕ) :
    ∃ (M : ℕ) (_ : NeZero M), 3 ∣ M ∧ (∀ ℓ ∈ T, ℓ ≠ 0 → ℓ ∣ M) ∧
      ∃ (g : CuspForm (Gamma1 M) 1) (b : ℕ → ℤ√(-2)),
        (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
          (⇑g) ∣[(1 : ℤ)] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑g)) ∧
        (∀ n, ModularFormClass.qCoeff (⇑g) n =
          ((b n).re : ℂ) + ((b n).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I)) ∧
        b 0 = 0 ∧
        FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ M then (0 : ℤ√(-2)) else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬ p ∣ 3 * M → b p = a p := by
  classical

  set t : ℕ := ∏ ℓ ∈ T, max ℓ 1 with ht
  have ht0 : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ℓ _ => (lt_max_of_lt_right one_pos).ne'
  haveI hN't : NeZero (N * t) := ⟨mul_ne_zero (NeZero.ne N) ht0⟩
  have hTdvd : ∀ ℓ ∈ T, ℓ ≠ 0 → ℓ ∣ N * t := fun ℓ hℓ hℓ0 => by
    have h1 : max ℓ 1 ∣ t := Finset.dvd_prod_of_mem (fun ℓ => max ℓ 1) hℓ
    rw [max_eq_left (Nat.one_le_iff_ne_zero.mpr hℓ0)] at h1
    exact h1.trans (dvd_mul_left t N)
  have hN' : 3 ∣ N * t := hN.mul_right t
  set F' : CuspForm (Gamma1 (N * t)) 1 :=
    restrictCusp (Subgroup.map_mono (Gamma1_le_of_dvd (dvd_mul_right N t))) F with hF'
  have hcoeF' : (⇑F' : ℍ → ℂ) = ⇑F := rfl
  have hg' : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 (N * t) →
      (⇑F') ∣[(1 : ℤ)] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑F') := fun γ hγ => by
    rw [hcoeF']
    exact hg γ (Gamma0_le_of_dvd (dvd_mul_right N t) hγ)

  set 𝔅' : Finset ℕ := 𝔅 ∪ (N * t).primeFactors with h𝔅'
  have hgood : ∀ p : ℕ, p.Prime → p ∉ 𝔅' → p ∉ 𝔅 ∧ ¬ p ∣ N * t := fun p hp hpB => by
    rw [h𝔅', Finset.mem_union, not_or] at hpB
    exact ⟨hpB.1, fun h => hpB.2 (Nat.mem_primeFactors.mpr ⟨hp, h, NeZero.ne _⟩)⟩
  have h3B : 3 ∈ 𝔅' := by
    rw [h𝔅', Finset.mem_union]
    exact Or.inr (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hN', NeZero.ne _⟩)
  set a' : ℕ → ℤ√(-2) := fun p => if p ∈ 𝔅' then 0 else a p with ha'
  set w : ℕ → ℤ√(-2) := fun p => if p ∈ 𝔅' then 0 else ((chiNegThree p : ℤ) : ℤ√(-2)) with hw
  set b : ℕ → ℤ√(-2) := extend w a' with hb
  have hb_zero_of_dvd : ∀ {q : ℕ}, q.Prime → q ∈ 𝔅' → ∀ {n : ℕ}, q ∣ n → b n = 0 :=
    fun {q} hq hqB {n} hqn =>
      extend_eq_zero_of_dvd w a' hq (by simp only [hw, if_pos hqB]) (by simp only [ha', if_pos hqB]) hqn

  set c : ℕ → ℂ := fun n => ModularFormClass.qCoeff (⇑F) n with hc
  set ac : ℕ → ℂ := fun p => iotaW (a p) with hac
  set e : ℕ → ℂ := fun p => ((chiNegThree p : ℤ) : ℂ) with he
  set wt : ℕ → ℂ := fun _ => 1 with hwt
  set lam : ℕ → ℂ := fun n => iotaW (b n) with hlam
  have hrel' : ∀ p, p.Prime → p ∉ 𝔅' → ∀ n : ℕ,
      c (p * n) + e p * wt p * (if p ∣ n then c (n / p) else 0) = ac p * c n := by
    intro p hp hpB n
    obtain ⟨h1, h2⟩ := hgood p hp hpB
    have h := hrel p hp h1 (fun h => h2 (h.trans (dvd_mul_right N t))) n
    simp only [hc, he, hwt, hac, mul_one, iotaW_apply]
    exact h
  have hlam_1 : lam 1 = 1 := by simp only [hlam, hb, extend_one, map_one]
  have ha'p : ∀ p, p ∉ 𝔅' → a' p = a p := fun p hpB => by simp only [ha', if_neg hpB]
  have hwp : ∀ p, p ∉ 𝔅' → w p = ((chiNegThree p : ℤ) : ℤ√(-2)) := fun p hpB => by simp only [hw, if_neg hpB]
  have hlam_p : ∀ p, p.Prime → p ∉ 𝔅' → lam p = ac p := fun p hp hpB => by
    have h1 : b p = a p := by rw [hb, extend_prime w a' hp, ha'p p hpB]
    simp only [hlam, hac, h1]
  have hlam_rec : ∀ p, p.Prime → p ∉ 𝔅' → ∀ r : ℕ,
      lam (p ^ (r + 2)) = ac p * lam (p ^ (r + 1)) - e p * wt p * lam (p ^ r) := fun p hp hpB r => by
    have h1 : b (p ^ (r + 2)) = a p * b (p ^ (r + 1)) - ((chiNegThree p : ℤ) : ℤ√(-2)) * b (p ^ r) := by
      rw [hb, extend_prime_pow w a' hp, extend_prime_pow w a' hp, extend_prime_pow w a' hp, ppow_add_two,
        ha'p p hpB, hwp p hpB]
    simp only [hlam, hac, he, hwt, h1, map_sub, map_mul, map_intCast, mul_one]
  have hlam_mul : ∀ m n : ℕ, Nat.Coprime m n → lam (m * n) = lam m * lam n := fun m n hmn => by
    simp only [hlam, hb, extend_mul_of_coprime w a' hmn, map_mul]

  have hne : ∃ n, n ≠ 0 ∧ c n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hF (coe_eq_zero_of_qCoeff_eq_zero F fun n hn => hcon n hn)
  obtain ⟨s, hs0, hsB, hcs⟩ := ArchimedeanDescent.exists_smooth_index_ne_zero 𝔅' c ac e wt lam hrel' hlam_1 hlam_p
    hlam_rec hlam_mul hne
  haveI : NeZero s := ⟨hs0⟩

  set l : List ℕ := (𝔅'.filter Nat.Prime).toList with hl
  have hlmem : ∀ q, q ∈ l ↔ q ∈ 𝔅' ∧ q.Prime := fun q => by
    rw [hl, Finset.mem_toList, Finset.mem_filter]
  have hlprime : ∀ q ∈ l, q.Prime := fun q hq => ((hlmem q).mp hq).2
  set M : ℕ := depLevel l (s * (N * t)) with hM
  have hM0 : M ≠ 0 := depLevel_ne_zero l (fun q hq => (hlprime q hq).ne_zero) (NeZero.ne _)
  haveI hMne : NeZero M := ⟨hM0⟩
  have hNtM : N * t ∣ M := (dvd_mul_left (N * t) s).trans (dvd_depLevel l _)
  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : CuspForm (Gamma1 (s * (N * t))) 1, F₁ = heckeU₁ s F' := ⟨_, rfl⟩
  have hg₁ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 (s * (N * t)) →
      (⇑F₁) ∣[(1 : ℤ)] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑F₁) := by
    rw [hF₁]
    exact heckeU₁_slash_Gamma0_chiNegThree s hN' F' hg'
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : CuspForm (Gamma1 M) 1, F₂ = depriveList l hlprime F₁ := ⟨_, rfl⟩
  have hg₂ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑F₂) ∣[(1 : ℤ)] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑F₂) := by
    rw [hF₂]
    exact depriveList_slash_Gamma0_chiNegThree l hlprime (hN'.trans (dvd_mul_left (N * t) s)) F₁ hg₁

  have hprimeM : ∀ p : ℕ, p.Prime → (p ∣ M ↔ p ∈ 𝔅') := fun p hp => by
    constructor
    · intro hpM
      rcases prime_dvd_depLevel l (s * (N * t)) hlprime hp hpM with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact hsB p hp h
        · rw [h𝔅', Finset.mem_union]
          exact Or.inr (Nat.mem_primeFactors.mpr ⟨hp, h, NeZero.ne _⟩)
      · exact ((hlmem p).mp h).1
    · intro hpB
      exact dvd_depLevel_of_mem l _ ((hlmem p).mpr ⟨hpB, hp⟩)
  obtain ⟨g, hgdef⟩ : ∃ g : CuspForm (Gamma1 M) 1, g = (c s)⁻¹ • F₂ := ⟨_, rfl⟩

  refine ⟨M, hMne, hN'.trans hNtM, fun ℓ hℓ hℓ0 => (hTdvd ℓ hℓ hℓ0).trans hNtM, g, b, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro γ hγ
    rw [hgdef, CuspForm.IsGLPos.coe_smul, ModularForm.SL_smul_slash, hg₂ γ hγ, smul_comm]
  ·
    intro n
    rw [← iotaW_apply, hgdef, qCoeff_smul_Gamma1, hF₂, qCoeff_depriveList, hF₁, qCoeff_heckeU₁]
    by_cases hex : ∃ q ∈ l, q ∣ n
    · obtain ⟨q, hq, hqn⟩ := hex
      rw [if_pos ⟨q, hq, hqn⟩, mul_zero, hb_zero_of_dvd (hlprime q hq) ((hlmem q).mp hq).1 hqn, map_zero]
    · rw [if_neg hex]
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hex ⟨3, (hlmem 3).mpr ⟨h3B, Nat.prime_three⟩, dvd_zero 3⟩
      have hngood : ∀ q, q.Prime → q ∣ n → q ∉ 𝔅' := fun q hq hqn hqB =>
        hex ⟨q, (hlmem q).mpr ⟨hqB, hq⟩, hqn⟩
      have hcop : Nat.Coprime s n :=
        Nat.coprime_of_dvd fun q hq hqs hqn => hngood q hq hqn (hsB q hq hqs)
      have hfac := ArchimedeanDescent.coeff_factorization 𝔅' c ac e wt lam hrel' hlam_1 hlam_p hlam_rec hlam_mul s n hn0
        hngood hcop
      show (c s)⁻¹ * ModularFormClass.qCoeff (⇑F') (s * n) = iotaW (b n)
      rw [hcoeF', show ModularFormClass.qCoeff (⇑F) (s * n) = c (s * n) from rfl, hfac,
        inv_mul_cancel_left₀ hcs]
  ·
    exact extend_zero w a'
  ·
    have hE := isEigensystem_extend w a'
    refine ⟨hE.1, fun ℓ hℓ n => ?_⟩
    have hwℓ : (if ℓ ∣ M then (0 : ℤ√(-2)) else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) = w ℓ := by
      simp only [hw, hprimeM ℓ hℓ]
    dsimp only
    rw [hwℓ]
    exact hE.2 ℓ hℓ n
  ·
    intro p hp hp3M
    have hpB : p ∉ 𝔅' := fun hpB => hp3M (((hprimeM p hp).mpr hpB).trans (dvd_mul_left M 3))
    show extend w a' p = a p
    rw [extend_prime w a' hp]
    simp only [ha', if_neg hpB]

end Extract
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part07
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part08

noncomputable section

open Complex MeasureTheory Set Filter

open scoped Real Topology Manifold

namespace HeckeDictionary

private theorem fcoeff_eq_integral (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hper : Function.Periodic f 1) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    fcoeff f n = ∫ x in (0:ℝ)..1, f (↑x + ↑y * Complex.I) *
      Complex.exp (-(2 * ↑π * Complex.I * ↑n * (↑x + ↑y * Complex.I))) := by
  set G : ℂ → ℂ := fun z => f z * Complex.exp (-(2 * ↑π * Complex.I * ↑n * z)) with hG
  have he : Differentiable ℂ (fun z : ℂ => Complex.exp (-(2 * ↑π * Complex.I * ↑n * z))) :=
    Complex.differentiable_exp.comp (((differentiable_const _).mul differentiable_id).neg)
  have hGd : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} := hf.mul he.differentiableOn
  have hrect : (Set.uIcc (0:ℝ) 1 ×ℂ Set.uIcc (1:ℝ) y) ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have h2 : z.im ∈ Set.uIcc (1:ℝ) y := hz.2
    rw [Set.mem_uIcc] at h2
    show 0 < z.im
    rcases h2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have key : (∫ x in (0:ℝ)..1, G (↑x + ↑(1:ℝ) * I)) - (∫ x in (0:ℝ)..1, G (↑x + ↑y * I)) +
      I • (∫ t in (1:ℝ)..y, G (↑(1:ℝ) + ↑t * I)) - I • (∫ t in (1:ℝ)..y, G (↑(0:ℝ) + ↑t * I)) = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn G ⟨0, 1⟩ ⟨1, y⟩ (hGd.mono hrect)
  have hvert : (∫ t in (1:ℝ)..y, G (↑(1:ℝ) + ↑t * I)) = ∫ t in (1:ℝ)..y, G (↑(0:ℝ) + ↑t * I) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hG, ofReal_one, ofReal_zero, zero_add]
    rw [add_comm (1:ℂ) _, hper]
    congr 1
    rw [show -(2 * ↑π * I * ↑n * (↑t * I + 1)) = -(2 * ↑π * I * ↑n * (↑t * I)) + ((-n : ℤ) : ℂ) * (2 * ↑π * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hvert, add_sub_cancel_right, sub_eq_zero] at key
  have lhs : fcoeff f n = ∫ x in (0:ℝ)..1, G (↑x + ↑(1:ℝ) * I) := by
    simp only [fcoeff, hG, ofReal_one, one_mul]
  rw [lhs, key]

private theorem continuous_slice (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => f (↑x + ↑y * Complex.I) :=
  hf.continuousOn.comp_continuous (by fun_prop) fun x => by
    show 0 < (↑x + ↑y * Complex.I).im
    simp [hy]

private theorem norm_fcoeff_le (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hper : Function.Periodic f 1) (n : ℤ) {y : ℝ} (hy : 0 < y) {C : ℝ}
    (hC : ∀ x ∈ Set.Icc (0:ℝ) 1, ‖f (↑x + ↑y * Complex.I)‖ ≤ C) :
    ‖fcoeff f n‖ ≤ C * Real.exp (2 * π * n * y) := by
  rw [fcoeff_eq_integral f hf hper n hy]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (C := C * Real.exp (2 * π * n * y))
    (f := fun x : ℝ => f (↑x + ↑y * I) * Complex.exp (-(2 * ↑π * I * ↑n * (↑x + ↑y * I)))) ?_
  · simpa using h
  · intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(2 * ↑π * I * ↑n * (↑x + ↑y * I))).re = 2 * π * n * y := by
      simp only [neg_re, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
        intCast_re, intCast_im, re_ofNat, im_ofNat]
      ring
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hC x ⟨hx.1.le, hx.2⟩) (Real.exp_pos _).le

private theorem hasSum_fcoeff (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hper : Function.Periodic f 1) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun n : ℤ => fcoeff f n * Complex.exp (2 * ↑π * Complex.I * ↑n * z)) (f z) := by
  haveI : Fact ((0:ℝ) < 1) := ⟨one_pos⟩
  set Y : ℝ := z.im with hY

  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    (continuous_slice f hf (half_pos hz)).continuousOn
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    (continuous_slice f hf (mul_pos two_pos hz)).continuousOn

  have hsum : Summable (fun n : ℤ => ‖fcoeff f n‖ * Real.exp (-(2 * π * n * Y))) := by
    refine Summable.of_nat_of_neg ?_ ?_
    · have hr0 : 0 ≤ Real.exp (-(π * Y)) := (Real.exp_pos _).le
      have hr1 : Real.exp (-(π * Y)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
      refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
        ((summable_geometric_of_lt_one hr0 hr1).mul_left (max C₁ 0))
      have hb := norm_fcoeff_le f hf hper (m : ℤ) (half_pos hz)
        (fun x hx => (hC₁ x hx).trans (le_max_left C₁ 0))
      calc ‖fcoeff f (m : ℤ)‖ * Real.exp (-(2 * π * ((m : ℤ) : ℝ) * Y))
          ≤ max C₁ 0 * Real.exp (2 * π * ((m : ℤ) : ℝ) * (Y / 2)) * Real.exp (-(2 * π * ((m : ℤ) : ℝ) * Y)) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = max C₁ 0 * Real.exp (-(π * Y)) ^ m := by
            rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
            congr 2
            push_cast
            ring
    · have hr0 : 0 ≤ Real.exp (-(2 * π * Y)) := (Real.exp_pos _).le
      have hr1 : Real.exp (-(2 * π * Y)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
      refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
        ((summable_geometric_of_lt_one hr0 hr1).mul_left (max C₂ 0))
      have hb := norm_fcoeff_le f hf hper (-(m : ℤ)) (mul_pos two_pos hz)
        (fun x hx => (hC₂ x hx).trans (le_max_left C₂ 0))
      calc ‖fcoeff f (-(m : ℤ))‖ * Real.exp (-(2 * π * ((-(m : ℤ) : ℤ) : ℝ) * Y))
          ≤ max C₂ 0 * Real.exp (2 * π * ((-(m : ℤ) : ℤ) : ℝ) * (2 * Y)) *
              Real.exp (-(2 * π * ((-(m : ℤ) : ℤ) : ℝ) * Y)) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = max C₂ 0 * Real.exp (-(2 * π * Y)) ^ m := by
            rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
            congr 2
            push_cast
            ring

  set k : ℤ := ⌊z.re⌋ with hk
  set x₀ : ℝ := z.re - k with hx₀
  have hx₀mem : x₀ ∈ Set.Ico (0:ℝ) 1 :=
    ⟨by rw [hx₀]; linarith [Int.floor_le z.re], by rw [hx₀]; linarith [Int.lt_floor_add_one z.re]⟩
  have hzeq : z = (↑x₀ + ↑Y * I) + (k : ℂ) := Complex.ext (by simp [hx₀]) (by simp [hY])
  have hfz : f ((↑x₀ + ↑Y * I) + (k : ℂ)) = f (↑x₀ + ↑Y * I) := by
    have := (hper.int_mul k) (↑x₀ + ↑Y * I)
    rwa [mul_one] at this
  have hez : ∀ n : ℤ, Complex.exp (2 * ↑π * I * ↑n * ((↑x₀ + ↑Y * I) + (k : ℂ))) =
      Complex.exp (2 * ↑π * I * ↑n * (↑x₀ + ↑Y * I)) := fun n => by
    rw [mul_add, Complex.exp_add, show 2 * ↑π * I * ↑n * (k : ℂ) = ((n * k : ℤ) : ℂ) * (2 * ↑π * I) by
      push_cast; ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hzeq]
  simp_rw [hez, hfz]

  set h : ℝ → ℂ := fun x => f (↑x + ↑Y * I) with hh
  have hh01 : h 0 = h 1 := by
    show f (↑(0:ℝ) + ↑Y * I) = f (↑(1:ℝ) + ↑Y * I)
    rw [ofReal_zero, ofReal_one, zero_add, show (1:ℂ) + ↑Y * I = ↑Y * I + 1 by ring]
    exact (hper _).symm
  let g : C(AddCircle (1:ℝ), ℂ) :=
    ⟨AddCircle.liftIco 1 0 h, AddCircle.liftIco_zero_continuous hh01 (continuous_slice f hf hz).continuousOn⟩
  have hgx : ∀ x ∈ Set.Icc (0:ℝ) 1, g ↑x = h x := by
    intro x hx
    rcases lt_or_eq_of_le hx.2 with hlt | rfl
    · show AddCircle.liftIco 1 0 h ↑x = h x
      exact AddCircle.liftIco_zero_coe_apply ⟨hx.1, hlt⟩
    · have e : ((1:ℝ) : AddCircle (1:ℝ)) = ((0:ℝ) : AddCircle (1:ℝ)) := by
        have := AddCircle.coe_add_period (1:ℝ) (0:ℝ)
        rwa [zero_add] at this
      show AddCircle.liftIco 1 0 h ↑(1:ℝ) = h 1
      rw [e, AddCircle.liftIco_zero_coe_apply ⟨le_rfl, one_pos⟩]
      exact hh01

  have hexpY : ∀ n : ℤ, ∀ x : ℝ, Complex.exp (2 * ↑π * I * ↑(-n) * ↑x / ↑(1:ℝ)) =
      Complex.exp (2 * ↑π * I * ↑n * (↑Y * I)) * Complex.exp (-(2 * ↑π * I * ↑n * (↑x + ↑Y * I))) := by
    intro n x
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hgc : ∀ n : ℤ, fourierCoeff g n = Complex.exp (2 * ↑π * I * ↑n * (↑Y * I)) * fcoeff f n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral g n 0, zero_add, fcoeff_eq_integral f hf hper n hz,
      ← intervalIntegral.integral_const_mul, div_one, one_smul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    rw [fourier_coe_apply, smul_eq_mul, hgx x hx, hexpY n x]
    simp only [hh]
    ring

  have hreY : ∀ n : ℤ, (2 * ↑π * I * ↑n * (↑Y * I)).re = -(2 * π * n * Y) := fun n => by
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, intCast_re, intCast_im, re_ofNat, im_ofNat]
    ring
  have hgsum : Summable (fourierCoeff g) := by
    refine Summable.of_norm (hsum.congr fun n => ?_)
    rw [hgc, norm_mul, Complex.norm_exp, hreY, mul_comm]
  have hps := has_pointwise_sum_fourier_series_of_summable hgsum ((x₀ : ℝ) : AddCircle (1:ℝ))
  have hexp0 : ∀ n : ℤ, Complex.exp (2 * ↑π * I * ↑n * (↑x₀ + ↑Y * I)) =
      Complex.exp (2 * ↑π * I * ↑n * (↑Y * I)) * Complex.exp (2 * ↑π * I * ↑n * ↑x₀ / ↑(1:ℝ)) := by
    intro n
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hgx x₀ ⟨hx₀mem.1, hx₀mem.2.le⟩] at hps
  convert hps using 1
  funext n
  rw [hgc, fourier_coe_apply, smul_eq_mul, hexp0 n]
  ring

private theorem isZeroAtImInfty_of_fcoeff_nonpos_eq_zero (F : UpperHalfPlane → ℂ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hvan : ∀ n : ℤ, n ≤ 0 → fcoeff (F ∘ UpperHalfPlane.ofComplex) n = 0) :
    UpperHalfPlane.IsZeroAtImInfty F := by
  set f : ℂ → ℂ := F ∘ UpperHalfPlane.ofComplex with hfF
  have hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := UpperHalfPlane.mdifferentiable_iff.mp hF

  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    (continuous_slice f hf one_half_pos).continuousOn
  set C : ℝ := max C₀ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCb : ∀ x ∈ Set.Icc (0:ℝ) 1, ‖f (↑x + ↑(1/2 : ℝ) * I)‖ ≤ C := fun x hx => (hC₀ x hx).trans (le_max_left _ _)

  set r : ℝ := Real.exp (-π) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos)
  set K : ℝ := C * ((1 - r)⁻¹ + r * (1 - r)⁻¹) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < (1 - r)⁻¹ := inv_pos.mpr (by linarith)
    exact mul_nonneg hC0 (add_nonneg this.le (mul_nonneg hr0 this.le))

  have hbound : ∀ τ : UpperHalfPlane, 1 ≤ τ.im → ‖F τ‖ ≤ K * Real.exp (-(2 * π * (τ.im - 1))) := by
    intro τ hτ
    have hs := hasSum_fcoeff f hf hper τ.im_pos
    have hFτ : f (τ : ℂ) = F τ := by
      show F (UpperHalfPlane.ofComplex (τ : ℂ)) = F τ
      rw [UpperHalfPlane.ofComplex_apply]
    rw [hFτ] at hs
    rw [← hs.tsum_eq]
    set C' : ℝ := C * Real.exp (-(2 * π * (τ.im - 1))) with hC'
    have hg : HasSum (fun n : ℤ => C' * r ^ n.natAbs) (C' * (1 - r)⁻¹ + C' * r * (1 - r)⁻¹) := by
      refine HasSum.of_nat_of_neg_add_one ?_ ?_
      · simpa using (hasSum_geometric_of_lt_one hr0 hr1).mul_left C'
      · have h2 := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (C' * r)
        convert h2 using 1
        all_goals try rfl
        funext n
        rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ]
        ring
    have hle : ∀ n : ℤ, ‖fcoeff f n * Complex.exp (2 * ↑π * I * ↑n * (τ : ℂ))‖ ≤ C' * r ^ n.natAbs := by
      intro n
      rcases le_or_gt n 0 with hn | hn
      · rw [hvan n hn, zero_mul, norm_zero]
        exact mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le) (pow_nonneg hr0 _)
      · rw [norm_mul, Complex.norm_exp]
        have hre : (2 * ↑π * I * ↑n * (τ : ℂ)).re = -(2 * π * n * τ.im) := by
          simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, intCast_re, intCast_im, re_ofNat,
            im_ofNat, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
          ring
        rw [hre]
        have hb := norm_fcoeff_le f hf hper n one_half_pos hCb
        have hnat : ((n.natAbs : ℕ) : ℝ) = (n : ℝ) := by
          rw [← Int.cast_natCast (R := ℝ), Int.natAbs_of_nonneg hn.le]
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        calc ‖fcoeff f n‖ * Real.exp (-(2 * π * n * τ.im))
            ≤ C * Real.exp (2 * π * n * (1/2 : ℝ)) * Real.exp (-(2 * π * n * τ.im)) :=
              mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
          _ = C * Real.exp (π * n - 2 * π * n * τ.im) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
          _ ≤ C * Real.exp (-(2 * π * (τ.im - 1)) + n.natAbs * (-π)) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
              rw [hnat]
              nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hτ)]
          _ = C' * r ^ n.natAbs := by rw [Real.exp_add, Real.exp_nat_mul]; simp only [hC', hr]; ring
    refine (tsum_of_norm_bounded hg hle).trans (le_of_eq ?_)
    rw [hC', hK]
    ring

  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro ε hε
  have ht : Tendsto (fun A : ℝ => K * Real.exp (2 * π) * Real.exp (-(2 * π) * A)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun A : ℝ => -(2 * π) * A) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos])
    have h3 := Real.tendsto_exp_atBot.comp h2
    have h4 := h3.const_mul (K * Real.exp (2 * π))
    rw [mul_zero] at h4
    exact h4
  obtain ⟨A₀, hA₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 ht).2 ε hε)
  refine ⟨max A₀ 1, fun τ hτ => ?_⟩
  have h1 : 1 ≤ τ.im := (le_max_right _ _).trans hτ
  have hA : A₀ ≤ τ.im := (le_max_left _ _).trans hτ
  have := hA₀ τ.im hA
  refine (hbound τ h1).trans ?_
  rw [show -(2 * π * (τ.im - 1)) = 2 * π + (-(2 * π) * τ.im) by ring, Real.exp_add, ← mul_assoc]
  exact this.le

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part08
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part09

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup

open scoped MatrixGroups ModularForm Manifold

private def slashInvariantForm_gamma1_of_slash (N : ℕ) (F : ℍ → ℂ)
    (hslash : ∀ δ ∈ Gamma1 N, F ∣[(1 : ℤ)] δ = F) :
    SlashInvariantForm (Gamma1 N) 1 where
  toFun := F
  slash_action_eq' := by
    rintro γ ⟨δ, hδ, rfl⟩
    exact hslash δ hδ

@[scoped simp] private lemma coe_slashInvariantForm_gamma1_of_slash (N : ℕ) (F : ℍ → ℂ)
    (hslash : ∀ δ ∈ Gamma1 N, F ∣[(1 : ℤ)] δ = F) :
    ⇑(slashInvariantForm_gamma1_of_slash N F hslash) = F := rfl

private def cuspForm_of_slash_of_zeroAtCosets (N : ℕ) [NeZero N] (F : ℍ → ℂ)
    (hslash : ∀ δ ∈ Gamma1 N, F ∣[(1 : ℤ)] δ = F)
    (hholo : MDiff F)
    (hzero : ∀ γ : SL(2, ℤ), IsZeroAtImInfty (F ∣[(1 : ℤ)] γ)) :
    CuspForm (Gamma1 N) 1 where
  __ := slashInvariantForm_gamma1_of_slash N F hslash
  holo' := hholo
  zero_at_cusps' := by
    intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    exact (OnePoint.isZeroAt_iff rfl).mpr (hzero γ)

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part09
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part10

open MeasureTheory Set Filter Topology UpperHalfPlane

open scoped Manifold

noncomputable section

namespace HeckeDictionary

private theorem Icc_zero_natCast_subset_iUnion (M : ℕ) :
    Icc (0:ℝ) ((M:ℝ) + 1) ⊆ ⋃ k ∈ Finset.range (M + 1), Icc (k:ℝ) ((k:ℝ) + 1) := by
  induction M with
  | zero =>
    intro x hx
    exact mem_iUnion₂.mpr ⟨0, by simp, by simpa using hx⟩
  | succ M ih =>
    intro x hx
    rcases le_or_gt x ((M:ℝ) + 1) with h | h
    · have hx' : x ∈ Icc (0:ℝ) ((M:ℝ) + 1) := ⟨hx.1, h⟩
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp (ih hx')
      exact mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hk; omega), hxk⟩
    · refine mem_iUnion₂.mpr ⟨M + 1, Finset.mem_range.mpr (by omega), ?_⟩
      refine ⟨by push_cast; exact h.le, ?_⟩
      have := hx.2
      push_cast at this ⊢
      linarith

private theorem integrable_box_comp_natMul_of_translates (f : ℂ → ℂ) (N : ℕ) (hN : 0 < N)
    (hk : ∀ k : ℕ, k < N →
      Integrable (fun p : ℝ × ℝ => ‖f (↑p.1 + ↑p.2 * Complex.I + (k:ℂ))‖ ^ 2 * p.2⁻¹)
        (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)))) :
    Integrable (fun p : ℝ × ℝ => ‖f ((N:ℂ) * (↑p.1 + ↑p.2 * Complex.I))‖ ^ 2 * p.2⁻¹)
      (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ))) := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure ℝ)))
  set G : ℝ × ℝ → ℝ := fun p => ‖f (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹ with hG_def
  have hbox_meas : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)) := measurableSet_Icc.prod measurableSet_Ici

  have hshift : ∀ k : ℕ, k < N →
      IntegrableOn G (Icc (k:ℝ) ((k:ℝ) + 1) ×ˢ Ici (1/2:ℝ)) volume := by
    intro k hkN
    have hmp : MeasurePreserving (fun p : ℝ × ℝ => ((k:ℝ), (0:ℝ)) + p) volume volume :=
      measurePreserving_add_left volume _
    have hemb : MeasurableEmbedding (fun p : ℝ × ℝ => ((k:ℝ), (0:ℝ)) + p) :=
      measurableEmbedding_addLeft _
    rw [← hmp.integrableOn_comp_preimage hemb]
    have hpre : (fun p : ℝ × ℝ => ((k:ℝ), (0:ℝ)) + p) ⁻¹' (Icc (k:ℝ) ((k:ℝ) + 1) ×ˢ Ici (1/2:ℝ))
        = (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)) := by
      ext ⟨x, y⟩
      simp only [mem_preimage, Prod.mk_add_mk, zero_add, mem_prod, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩
    rw [hpre]
    have hfun : (G ∘ fun p : ℝ × ℝ => ((k:ℝ), (0:ℝ)) + p)
        = fun p : ℝ × ℝ => ‖f (↑p.1 + ↑p.2 * Complex.I + (k:ℂ))‖ ^ 2 * p.2⁻¹ := by
      funext ⟨x, y⟩
      have harg : (((k:ℝ) + x : ℝ) : ℂ) + (y:ℂ) * Complex.I = (x:ℂ) + (y:ℂ) * Complex.I + (k:ℂ) := by
        push_cast; ring
      simp only [Function.comp_apply, hG_def, Prod.mk_add_mk, zero_add]
      rw [harg]
    rw [hfun]
    exact hk k hkN

  have hbig : IntegrableOn G (Icc (0:ℝ) (N:ℝ) ×ˢ Ici (1/2:ℝ)) volume := by
    obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
    have hsub : Icc (0:ℝ) ((M + 1 : ℕ) : ℝ) ×ˢ Ici (1/2:ℝ)
        ⊆ ⋃ k ∈ Finset.range (M + 1), Icc (k:ℝ) ((k:ℝ) + 1) ×ˢ Ici (1/2:ℝ) := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      have hx' : x ∈ Icc (0:ℝ) ((M:ℝ) + 1) := by simpa [Nat.cast_succ] using hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp (Icc_zero_natCast_subset_iUnion M hx')
      exact mem_iUnion₂.mpr ⟨k, hk, ⟨hxk, hy⟩⟩
    refine IntegrableOn.mono_set ?_ hsub
    refine integrableOn_finset_iUnion.mpr ?_
    intro k hk
    exact hshift k (Finset.mem_range.mp hk)

  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hind : Integrable ((Icc (0:ℝ) (N:ℝ) ×ˢ Ici (1/2:ℝ)).indicator G) volume :=
    (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Ici)).mpr hbig
  have hsc := hind.comp_smul hNr
  have hsc' : Integrable
      (((fun p : ℝ × ℝ => (N:ℝ) • p) ⁻¹' (Icc (0:ℝ) (N:ℝ) ×ˢ Ici (1/2:ℝ))).indicator
        (G ∘ fun p : ℝ × ℝ => (N:ℝ) • p)) volume := by
    refine hsc.congr (Eventually.of_forall fun p => ?_)
    exact (Set.indicator_comp_right (fun p : ℝ × ℝ => (N:ℝ) • p)).symm
  have hpre_meas : MeasurableSet ((fun p : ℝ × ℝ => (N:ℝ) • p) ⁻¹' (Icc (0:ℝ) (N:ℝ) ×ˢ Ici (1/2:ℝ))) :=
    (measurableSet_Icc.prod measurableSet_Ici).preimage (continuous_const_smul (N:ℝ)).measurable
  have hon : IntegrableOn (G ∘ fun p : ℝ × ℝ => (N:ℝ) • p)
      ((fun p : ℝ × ℝ => (N:ℝ) • p) ⁻¹' (Icc (0:ℝ) (N:ℝ) ×ˢ Ici (1/2:ℝ))) volume :=
    (integrable_indicator_iff hpre_meas).mp hsc'

  have hbox_sub : (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)) ⊆ (fun p : ℝ × ℝ => (N:ℝ) • p) ⁻¹' (Icc (0:ℝ) (N:ℝ) ×ˢ Ici (1/2:ℝ)) := by
    rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, hy⟩
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    simp only [mem_preimage, Prod.smul_mk, smul_eq_mul, mem_prod, mem_Icc, mem_Ici] at hy ⊢
    refine ⟨⟨by positivity, ?_⟩, ?_⟩
    · calc (N:ℝ) * x ≤ (N:ℝ) * 1 := by gcongr
        _ = N := mul_one _
    · calc (1/2:ℝ) = 1 * (1/2) := (one_mul _).symm
        _ ≤ (N:ℝ) * y := by gcongr
  have hon' : IntegrableOn (G ∘ fun p : ℝ × ℝ => (N:ℝ) • p) (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)) volume := hon.mono_set hbox_sub

  have hfinal : IntegrableOn (fun p : ℝ × ℝ => (N:ℝ) * (G ∘ fun p : ℝ × ℝ => (N:ℝ) • p) p)
      (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)) volume := hon'.const_mul _
  show IntegrableOn _ (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)) volume
  refine hfinal.congr_fun (fun p hp => ?_) hbox_meas
  obtain ⟨x, y⟩ := p
  have hy : y ≠ 0 := by
    have : (1/2:ℝ) ≤ y := hp.2
    linarith
  simp only [Function.comp_apply, hG_def, Prod.smul_mk, smul_eq_mul]
  have harg : ((((N:ℝ) * x : ℝ) : ℂ) + (((N:ℝ) * y : ℝ) : ℂ) * Complex.I)
      = (N:ℂ) * (↑x + ↑y * Complex.I) := by push_cast; ring
  rw [harg]
  field_simp

private theorem integrable_box_of_translates (N : ℕ) (hN : 0 < N) (f h : ℂ → ℂ) (g : ℕ → ℂ → ℂ)
    (hg : ∀ k, k < N → Integrable (fun p : ℝ × ℝ => ‖g k (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹)
      (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ))))
    (hrel : ∀ k, k < N → ∀ z : ℂ, 0 < z.im → f (z + k) = g k z)
    (hh : ∀ z : ℂ, 0 < z.im → h z = f ((N : ℂ) * z)) :
    Integrable (fun p : ℝ × ℝ => ‖h (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹)
      (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ))) := by
  have hbox_meas : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)) := measurableSet_Icc.prod measurableSet_Ici
  have him : ∀ p : ℝ × ℝ, p ∈ Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ) → 0 < (↑p.1 + ↑p.2 * Complex.I).im := by
    intro p hp
    have h2 : (1/2:ℝ) ≤ p.2 := hp.2
    have hi : (↑p.1 + ↑p.2 * Complex.I).im = p.2 := by simp
    rw [hi]
    linarith
  have hmain := integrable_box_comp_natMul_of_translates f N hN (fun k hk => by
    refine IntegrableOn.congr_fun (hg k hk) (fun p hp => ?_) hbox_meas
    simp only [hrel k hk _ (him p hp)])
  refine IntegrableOn.congr_fun hmain (fun p hp => ?_) hbox_meas
  simp only [hh _ (him p hp)]

private theorem periodic_comp_natMul (f : ℂ → ℂ) (N : ℕ) (hper : ∀ z : ℂ, f (z + (N:ℂ)) = f z) :
    Function.Periodic (fun z : ℂ => f ((N:ℂ) * z)) 1 := by
  intro z
  simp only [mul_add, mul_one]
  exact hper _

private theorem differentiableOn_comp_natMul (f : ℂ → ℂ) (N : ℕ) (hN : 0 < N)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) :
    DifferentiableOn ℂ (fun z : ℂ => f ((N:ℂ) * z)) {z : ℂ | 0 < z.im} := by
  refine hf.comp (differentiableOn_id.const_mul _) ?_
  intro z hz
  have hz' : 0 < z.im := hz
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  show 0 < ((N:ℂ) * z).im
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  positivity

private theorem mdifferentiable_comp_posRealSmul (g : ℍ → ℂ) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (c : {x : ℝ // 0 < x}) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => g (c • τ)) := by
  rw [mdifferentiable_iff] at hg ⊢
  have hmaps : ∀ z : ℂ, 0 < z.im → 0 < (((c:ℝ):ℂ) * z).im := by
    intro z hz
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos c.2 hz
  have hcomp : DifferentiableOn ℂ (fun z : ℂ => (g ∘ ofComplex) (((c:ℝ):ℂ) * z)) {z : ℂ | 0 < z.im} :=
    hg.comp (differentiableOn_id.const_mul _) (fun z hz => hmaps z hz)
  refine hcomp.congr (fun z hz => ?_)
  have hz' : 0 < z.im := hz
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos (hmaps z hz')]
  congr 1

private theorem tendsto_posRealSmul_atImInfty (c : {x : ℝ // 0 < x}) :
    Tendsto (fun τ : ℍ => c • τ) atImInfty atImInfty := by
  simp only [atImInfty, tendsto_comap_iff]
  have h : (UpperHalfPlane.im ∘ fun τ : ℍ => c • τ) = fun τ : ℍ => (c:ℝ) * τ.im := by
    funext τ; exact pos_real_im c τ
  rw [h]
  exact tendsto_comap.const_mul_atTop c.2

private theorem isZeroAtImInfty_of_comp_posRealSmul (g : ℍ → ℂ) (c : {x : ℝ // 0 < x})
    (h : IsZeroAtImInfty (fun τ : ℍ => g (c • τ))) : IsZeroAtImInfty g := by
  have hc : (c * c⁻¹ : {x : ℝ // 0 < x}) = 1 := mul_inv_cancel c
  have hfun : g = fun τ : ℍ => (fun σ : ℍ => g (c • σ)) (c⁻¹ • τ) := by
    funext τ
    simp only [smul_smul, hc, one_smul]
  have h' : Tendsto (fun σ : ℍ => g (c • σ)) atImInfty (𝓝 (0:ℂ)) := h
  show Tendsto g atImInfty (𝓝 (0:ℂ))
  rw [hfun]
  exact h'.comp (tendsto_posRealSmul_atImInfty c⁻¹)

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end Part10
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

section Part11

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

open UpperHalfPlane CongruenceSubgroup ModularForm EisensteinWeightOne MeasureTheory Set

open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace HeckeDictionary

variable {Ψ : HeckeEigensystem ℚ ℂ}

private def ratRealPlace : InfinitePlace ℚ := InfinitePlace.mk (Complex.ofRealHom.comp (Rat.castHom ℝ))

private theorem ratRealPlace_isReal : ratRealPlace.IsReal :=
  ⟨_, RingHom.ext fun x => Complex.conj_ofReal (Rat.castHom ℝ x), rfl⟩

private theorem hhol_storey (R : SmoothCuspRealizationAt ℚ h4pins Ψ) (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hhol : IsArchHolomorphicAt w hw R.toFun) :
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, MDifferentiable (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
        ((z.im : ℝ) : ℂ)⁻¹ * R.toFun (g * archAt w hw (iwasawaSec z)) := by
  intro g
  have h := hhol g
  simp only [archAt, MonoidHom.comp_apply, iwasawaSec_eq_iwasawaSectionGL] at h ⊢
  exact h

private theorem mdifferentiable_descentF (R : SmoothCuspRealizationAt ℚ h4pins Ψ) (w : InfinitePlace ℚ)
    (hw : w.IsReal) (hhol : IsArchHolomorphicAt w hw R.toFun) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (descentF R w hw) := by
  have h := hhol 1
  have hfun : descentF R w hw = fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ *
      R.toFun (1 * adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom) (iwasawaSectionGL z))) := by
    funext z
    simp only [descentF, descentFn, ofComplex_apply, one_mul, UpperHalfPlane.coe_im]
    rw [OneMemClass.coe_one, map_one, mul_one]
  rw [hfun]
  exact h

private theorem descentF_ne_zero (R : SmoothCuspRealizationAt ℚ h4pins Ψ) (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hN : Ψ.level ≠ ⊥) (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun) :
    descentF R w hw ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_descent_ne_zero R w hw hN harch
  intro h0
  apply hz
  have hz0 := congrFun h0 z
  simp only [descentF, descentFn, ofComplex_apply, Pi.zero_apply, UpperHalfPlane.coe_im] at hz0
  rw [OneMemClass.coe_one, map_one, mul_one] at hz0
  rcases mul_eq_zero.mp hz0 with hinv | hval
  · exfalso
    have : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    exact this (inv_eq_zero.mp hinv)
  · simpa only [archAt, MonoidHom.comp_apply, iwasawaSec_eq_iwasawaSectionGL] using hval

private theorem norm_archWeightOneℝ (k : rowIsometrySubgroup₀ ℝ) : ‖((archWeightOneℝ k : ℂˣ) : ℂ)‖ = 1 := by
  show ‖firstRowℂ (k : GL (Fin 2) ℝ)‖ = 1
  rw [Complex.norm_def, normSq_firstRowℂ_of_mem k.2, Real.sqrt_one]

private theorem norm_archWeightOneAt (w : InfinitePlace ℚ) (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    ‖((archWeightOneAt hw k : ℂˣ) : ℂ)‖ = 1 := by

  unfold archWeightOneAt
  rw [MonoidHom.comp_apply]
  exact norm_archWeightOneℝ _

open AutomorphicForm.WindowedSiegel in
private theorem hKinf_of_harch (R : SmoothCuspRealizationAt ℚ h4pins Ψ) (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun) :
    ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k → (k : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖R.toFun (g * adelicArchGLInclAt ℚ w k)‖ = ‖R.toFun g‖ := by
  intro k hk hdet g
  have hmem : k ∈ rowIsometrySubgroup₀ w.Completion :=
    (mem_rowIsometrySubgroup₀_iff (K := w.Completion)).mpr ⟨hdet, hk⟩
  have h : R.toFun (g * adelicArchGLInclAt ℚ w k) = _ := harch ⟨k, hmem⟩ g
  rw [h, norm_mul, norm_archWeightOneAt w hw ⟨k, hmem⟩, one_mul]

open NumberField.AdelicHaar AutomorphicForm.WindowedSiegel in
private theorem memLp_toFun (R : SmoothCuspRealizationAt ℚ h4pins Ψ) :
    letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
    MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
      (centreCutSiegelSet ℚ (1/2:ℝ) 1 (1/2) 2)) := by

  letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
  have h := R.smoothCusp.1.1
  exact ((lsXiMemberAt_iff ..).mp h).2

private theorem hlev_of_level_invariant (R : SmoothCuspRealizationAt ℚ h4pins Ψ) :
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ levelOne (𝓞 ℚ) ℚ Ψ.level ⊓ (glArch (𝓞 ℚ) ℚ).ker,
      R.toFun (g * u) = R.toFun g :=
  fun g u hu => R.level_invariant g u hu

private theorem cusp_leg (R : SmoothCuspRealizationAt ℚ h4pins Ψ) (w : InfinitePlace ℚ) (hw : w.IsReal)
    (harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun)
    (hhol : IsArchHolomorphicAt w hw R.toFun)
    (homega : ∀ (t : ℝˣ), (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      R.toFun (adelicArchGLInclAt ℚ w (Matrix.GeneralLinearGroup.map
          ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g)
        = ((t : ℝ) : ℂ) * R.toFun g)
    (hslash : ∀ δ ∈ Gamma1 (Ideal.absNorm Ψ.level), (descentF R w hw) ∣[(1 : ℤ)] δ = descentF R w hw)
    (γ : SL(2, ℤ)) :
    IsZeroAtImInfty ((descentF R w hw) ∣[(1 : ℤ)] γ) := by
  set N : ℕ := Ideal.absNorm Ψ.level with hN_def
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by
    rw [hN_def]; exact Ideal.absNorm_eq_zero_iff.not.mpr Ψ.level_ne_bot)
  set Fγ : ℍ → ℂ := (descentF R w hw) ∣[(1 : ℤ)] γ with hFγ_def

  have hG : ∀ h : ↥(finiteIntegralGL2 (𝓞 ℚ) ℚ),
      Integrable (fun p : ℝ × ℝ => ‖descentFn w hw R.toFun h (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹)
        (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ))) :=
    fun h => adelicL2_dominates_lebesgueBox w hw R.toFun (memLp_toFun R) homega Ψ.level Ψ.level_ne_bot
      (hlev_of_level_invariant R) (hKinf_of_harch R w hw harch) h

  have hslashδ : ∀ δ : SL(2, ℤ), ∀ z : ℍ,
      ((descentF R w hw) ∣[(1 : ℤ)] δ) z = descentFn w hw R.toFun (slGammaFinLift δ⁻¹) (z : ℂ) :=
    fun δ z => congrFun (slash_descentF_eq R w hw harch homega δ) z

  have hT_apply : ∀ (n : ℕ) (f : ℍ → ℂ) (τ : ℍ),
      (f ∣[(1 : ℤ)] (ModularGroup.T ^ (n : ℤ))) τ = f ((n : ℝ) +ᵥ τ) := by
    intro n f τ
    rw [SL_slash_apply, modular_T_zpow_smul, ModularGroup.denom_apply, ModularGroup.coe_T_zpow]
    simp

  have htrans : ∀ (k : ℕ) (τ : ℍ), Fγ ((k : ℝ) +ᵥ τ)
      = descentFn w hw R.toFun (slGammaFinLift (γ * ModularGroup.T ^ (k : ℤ))⁻¹) (τ : ℂ) := by
    intro k τ
    rw [← hT_apply k Fγ τ, hFγ_def, ← SlashAction.slash_mul, hslashδ]

  have hTN : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
    simpa using ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have hconj : γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ Gamma1 N := by
    have hmem : γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ Gamma N :=
      (Gamma_normal (N := N)).conj_mem _ hTN γ
    rw [Gamma_mem] at hmem
    rw [Gamma1_mem]
    exact ⟨hmem.1, hmem.2.2.2, hmem.2.2.1⟩
  have hper : ∀ τ : ℍ, Fγ ((N : ℝ) +ᵥ τ) = Fγ τ := by
    intro τ
    have h1 : γ * ModularGroup.T ^ (N : ℤ) = (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) * γ := by group
    rw [← hT_apply N Fγ τ, hFγ_def, ← SlashAction.slash_mul, h1, SlashAction.slash_mul, hslash _ hconj]

  set c : {x : ℝ // 0 < x} := ⟨(N : ℝ), by exact_mod_cast hNpos⟩ with hc_def
  have hcN : ((c : {x : ℝ // 0 < x}) : ℝ) = (N : ℝ) := rfl
  set G : ℍ → ℂ := fun τ => Fγ (c • τ) with hG_def
  have hG_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Fγ := by
      rw [hFγ_def, SL_slash]
      exact (mdifferentiable_descentF R w hw hhol).slash _ _
    exact mdifferentiable_comp_posRealSmul Fγ hF c
  have hG_per : Function.Periodic (G ∘ ofComplex) 1 := by
    intro z
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1, hG_def]
      have hpt : c • (⟨z + 1, hz1⟩ : ℍ) = (N : ℝ) +ᵥ (c • (⟨z, hz⟩ : ℍ)) := by
        ext
        simp only [coe_pos_real_smul, coe_vadd, Complex.real_smul, hcN]
        ring
      rw [hpt, hper]
    · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
      simp only [Function.comp_apply, ofComplex_apply_eq_ite, dif_neg hz, dif_neg hz1]

  have brick : ∀ (f h : ℂ → ℂ) (g : ℕ → ℂ → ℂ),
      (∀ k, k < N → Integrable (fun p : ℝ × ℝ => ‖g k (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹)
        (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ)))) →
      (∀ k, k < N → ∀ z : ℂ, 0 < z.im → f (z + k) = g k z) →
      (∀ z : ℂ, 0 < z.im → h z = f ((N : ℂ) * z)) →
      Integrable (fun p : ℝ × ℝ => ‖h (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹)
        (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ))) :=
    fun f h g hg hrel hh => integrable_box_of_translates N hNpos f h g hg hrel hh
  have hbox : Integrable (fun p : ℝ × ℝ => ‖(G ∘ ofComplex) (↑p.1 + ↑p.2 * Complex.I)‖ ^ 2 * p.2⁻¹)
      (volume.restrict (Icc (0:ℝ) 1 ×ˢ Ici (1/2:ℝ))) := by
    refine brick (descentFn w hw R.toFun (slGammaFinLift γ⁻¹)) (G ∘ ofComplex)
      (fun k => descentFn w hw R.toFun (slGammaFinLift (γ * ModularGroup.T ^ (k : ℤ))⁻¹))
      (fun k _ => hG _) ?_ ?_
    · intro k _ z hz
      have h1 := htrans k ⟨z, hz⟩
      rw [hFγ_def, hslashδ γ] at h1
      simpa [coe_vadd, add_comm] using h1
    · intro z hz
      have h1 := hslashδ γ (c • ⟨z, hz⟩)
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, hG_def, hFγ_def, h1, coe_pos_real_smul,
        hcN, Complex.real_smul, Complex.ofReal_natCast]
  have hG_vanish : ∀ n : ℤ, n ≤ 0 → fcoeff (G ∘ ofComplex) n = 0 :=
    fcoeff_nonpos_eq_zero_of_weighted_l2_box (G ∘ ofComplex) (mdifferentiable_iff.mp hG_mdiff) hG_per hbox
  have hG_zero : IsZeroAtImInfty G :=
    isZeroAtImInfty_of_fcoeff_nonpos_eq_zero G hG_mdiff hG_per hG_vanish
  exact isZeroAtImInfty_of_comp_posRealSmul Fγ c hG_zero

end HeckeDictionary
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

open HeckeDictionary in
theorem solution
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) (hΦ : AutomorphicForm.viaCompactCuspNotion.IsCusp ℚ Φ)
    (T : Finset ℕ) :
    ∃ (M : ℕ) (_ : NeZero M), 3 ∣ M ∧ (∀ ℓ ∈ T, ℓ ≠ 0 → ℓ ∣ M) ∧
      ∃ (g : CuspForm (Gamma1 M) 1) (b : ℕ → ℤ√(-2)),
        (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
          (⇑g) ∣[(1 : ℤ)] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑g)) ∧
        (∀ n, ModularFormClass.qCoeff (⇑g) n =
          ((b n).re : ℂ) + ((b n).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I)) ∧
        b 0 = 0 ∧
        FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ M then (0 : ℤ√(-2)) else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬ p ∣ 3 * M → b p = Φ.a (AutomorphicForm.ratPrime ⟨p, hp⟩) := by
  classical

  obtain ⟨⟨R₀, harch₀, hhol₀⟩, S, hS⟩ := hΦ

  let R : SmoothCuspRealizationAt ℚ h4pins ((Φ.map iotaZsqrtdNegTwo).toRawCentral) :=
    { R₀ with
      exceptionalSet := R₀.exceptionalSet ∪ S
      hecke_eigen := fun v hv => R₀.hecke_eigen v (fun h => hv (Finset.mem_union_left _ h))
      central_eigen := fun v hv => R₀.central_eigen v (fun h => hv (Finset.mem_union_left _ h)) }
  have hRfun : R.toFun = R₀.toFun := rfl
  set w : InfinitePlace ℚ := ratRealPlace with hw_def
  have hw : w.IsReal := ratRealPlace_isReal
  have harch : HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun := by rw [hRfun]; exact harch₀ w hw
  have hhol : IsArchHolomorphicAt w hw R.toFun := by rw [hRfun]; exact hhol₀ w hw

  set N : ℕ := Ideal.absNorm ((Φ.map iotaZsqrtdNegTwo).toRawCentral).level with hN_def
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by
    rw [hN_def]; exact Ideal.absNorm_eq_zero_iff.not.mpr ((Φ.map iotaZsqrtdNegTwo).toRawCentral).level_ne_bot)
  haveI : NeZero N := ⟨hNpos.ne'⟩

  have homega := homega_of_archType R w hw ((Φ.map iotaZsqrtdNegTwo).toRawCentral).level_ne_bot harch
    (hhol_storey R w hw hhol)
  have hepsval := fun (m : ℕ) (hm : 0 < m) hgood => omegaEps_eq_chi R w hw homega m hm hgood

  have hdet : ∀ q : ℕ, ∀ hq : q.Prime, ¬ q ∣ Ideal.absNorm ((Φ.map iotaZsqrtdNegTwo).toRawCentral).level → q ≠ 3 →
      ratPrime ⟨q, hq⟩ ∉ R.exceptionalSet →
      ((Φ.map iotaZsqrtdNegTwo).toRawCentral).b (ratPrime ⟨q, hq⟩) = ((chiNegThree q : ℤ) : ℂ) * ((q : ℂ))⁻¹ := by
    intro q hq _ _ hqR
    have hqS : ratPrime ⟨q, hq⟩ ∉ S := fun h => hqR (Finset.mem_union_right _ h)
    have hb := hS _ hqS
    have hq' : ((⟨q, hq⟩ : Nat.Primes) : ℕ) = q := rfl
    show (HeckeEigensystem.cNorm (ratPrime ⟨q, hq⟩))⁻¹ * iotaZsqrtdNegTwo (Φ.b (ratPrime ⟨q, hq⟩)) = _
    rw [cNorm_ratPrime, hb, absNorm_ratPrime, map_intCast, hq']
    ring
  have hN3 : 3 ∣ N := three_dvd_absNorm R w hw homega hdet

  have hslash : ∀ δ ∈ Gamma1 N, (descentF R w hw) ∣[(1 : ℤ)] δ = descentF R w hw :=
    fun δ hδ => descent_slash_gamma1 R w hw harch homega hepsval hdet hN3 δ hδ
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (descentF R w hw) := mdifferentiable_descentF R w hw hhol
  have hzero : ∀ γ : SL(2, ℤ), IsZeroAtImInfty ((descentF R w hw) ∣[(1 : ℤ)] γ) :=
    fun γ => cusp_leg R w hw harch hhol homega hslash γ
  let Fc : CuspForm (Gamma1 N) 1 := cuspForm_of_slash_of_zeroAtCosets N (descentF R w hw) hslash hholo hzero
  have hFc : (⇑Fc : ℍ → ℂ) = descentF R w hw := rfl

  have hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
      (⇑Fc) ∣[(1 : ℤ)] γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) • (⇑Fc) := by
    intro γ hγ
    rw [hFc]
    exact descent_slash_gamma0 R w hw harch homega hepsval hdet hN3 γ hγ

  let 𝔅 : Finset ℕ := R.exceptionalSet.image fun v => Ideal.absNorm v.asIdeal
  let a : ℕ → ℤ√(-2) := fun p => if hp : p.Prime then Φ.a (ratPrime ⟨p, hp⟩) else 0
  have hrel : ∀ p : ℕ, p.Prime → p ∉ 𝔅 → ¬ p ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑Fc) (p * n) +
          ((chiNegThree p : ℤ) : ℂ) * (if p ∣ n then ModularFormClass.qCoeff (⇑Fc) (n / p) else 0) =
        (((a p).re : ℂ) + ((a p).im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I)) * ModularFormClass.qCoeff (⇑Fc) n := by
    intro p hp hpB hpN n
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hpR : ratPrime ⟨p, hp⟩ ∉ R.exceptionalSet := fun h =>
      hpB (Finset.mem_image.mpr ⟨_, h, absNorm_ratPrime ⟨p, hp⟩⟩)
    have hp3 : p ≠ 3 := fun h => hpN (h ▸ hN3)
    have hT := qCoeff_rel_of_heckeT_char_eq_mul_weightOne p Fc ((chiNegThree p : ℤ) : ℂ)
      (((Φ.map iotaZsqrtdNegTwo).toRawCentral).a (ratPrime ⟨p, hp⟩))
      (fun τ => by
        rw [hFc]
        exact descentF_heckeT_char_eigen R w hw homega hepsval hN3 p hp hpN hpR (hdet p hp hpN hp3 hpR) τ) n
    rw [hT]
    congr 1
    have ha : a p = Φ.a (ratPrime ⟨p, hp⟩) := dif_pos hp
    rw [ha]
    exact iotaZsqrtdNegTwo_apply _
  have hF0 : (⇑Fc : ℍ → ℂ) ≠ 0 := by
    rw [hFc]
    exact descentF_ne_zero R w hw ((Φ.map iotaZsqrtdNegTwo).toRawCentral).level_ne_bot harch

  obtain ⟨M, hM, h3M, hTM, g, b, hg', hqb, hb0, heig, hbp⟩ :=
    exists_engineInput (N := N) hN3 Fc hg 𝔅 a hrel hF0 T
  refine ⟨M, hM, h3M, hTM, g, b, hg', hqb, hb0, heig, ?_⟩
  intro p hp hpM
  rw [hbp p hp hpM]
  exact dif_pos hp

end Part11
p2m_reactivate "P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion.HeckeDictionary"

end S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion
end P2MW
export P2MW.S_AutomorphicForm_exists_weightOne_cuspForm_of_isCusp_viaCompactCuspNotion (solution)
