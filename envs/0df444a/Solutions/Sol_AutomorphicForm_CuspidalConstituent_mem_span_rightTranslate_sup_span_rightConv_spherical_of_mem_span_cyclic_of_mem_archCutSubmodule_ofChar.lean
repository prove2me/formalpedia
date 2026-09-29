-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/03a0e064-b881-52d9-8475-d468ccc9a861

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg
import Theorems.Thm_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar

set_option autoImplicit false

section Gamma4Block

open NumberField
open AutomorphicForm
open MeasureTheory Topology

noncomputable section

namespace R5bC

variable (F : Type) [Field F] [NumberField F]

private theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion :=
    fun w => NumberField.AdelicBox.properSpace_completion (K := F) w
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

private theorem secondCountableTopology_archMatrix :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  haveI := secondCountableTopology_infiniteAdeleRing F
  exact inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing F))

omit [NumberField F] in
private theorem t2Space_archMatrix' : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))

private theorem secondCountableTopology_archGL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing F)) := by
  haveI := secondCountableTopology_archMatrix F

  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem locallyCompactSpace_archMatrix :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))

private theorem locallyCompactSpace_archGL : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := by
  haveI := t2Space_archMatrix' F
  haveI := locallyCompactSpace_archMatrix F
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

omit [NumberField F] in
private theorem secondCountableTopology_placeGL (w : InfinitePlace F) :
    SecondCountableTopology (GL (Fin 2) w.Completion) := by
  haveI : ProperSpace w.Completion := NumberField.AdelicBox.properSpace_completion (K := F) w
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → w.Completion))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

omit [NumberField F] in
private theorem secondCountableTopology_rowIsometrySubgroup₀ (w : InfinitePlace F) :
    SecondCountableTopology (rowIsometrySubgroup₀ w.Completion) := by
  haveI := secondCountableTopology_placeGL F w

  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

private theorem secondCountableTopology_piRowIsometrySubgroup₀ :
    SecondCountableTopology (Π w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := by
  haveI : ∀ w : InfinitePlace F, SecondCountableTopology (rowIsometrySubgroup₀ w.Completion) :=
    secondCountableTopology_rowIsometrySubgroup₀ F
  infer_instance

omit [NumberField F] in
private theorem isTopologicalGroup_archGL : IsTopologicalGroup (GL (Fin 2) (InfiniteAdeleRing F)) := inferInstance

end R5bC

end

end Gamma4Block

section AlphaBlock

open NumberField NumberField.AdelicLevel
open AutomorphicForm.WindowedSiegel
open IsDedekindDomain
open AutomorphicForm

noncomputable section

namespace R5bK

attribute [local instance] R5bC.t2Space_archMatrix' R5bC.locallyCompactSpace_archMatrix
  R5bC.locallyCompactSpace_archGL R5bC.isTopologicalGroup_archGL
  R5bC.secondCountableTopology_archGL R5bC.secondCountableTopology_piRowIsometrySubgroup₀

section Compact

variable (K : Type*) [NormedField K]

private def rowIsoSet : Set (Matrix (Fin 2) (Fin 2) K) :=
  {m | m.det = 1} ∩ ({m | ‖m.det‖ = 1} ∩ ⋂ x : K, ⋂ y : K,
    {m | ‖x * m 0 0 + y * m 1 0‖ ^ 2 + ‖x * m 0 1 + y * m 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2})

private theorem mem_rowIsoSet_iff (k : GL (Fin 2) K) :
    (k : Matrix (Fin 2) (Fin 2) K) ∈ rowIsoSet K ↔ k ∈ rowIsometrySubgroup₀ K := by
  simp only [rowIsoSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
    mem_rowIsometrySubgroup₀_iff, IsRowIsometry]

private theorem continuous_entry (i j : Fin 2) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) K => m i j :=
  continuous_id.matrix_elem i j

private theorem isClosed_rowIsoSet : IsClosed (rowIsoSet K) := by
  have hdet : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m.det := continuous_id.matrix_det
  refine (isClosed_eq hdet continuous_const).inter
    ((isClosed_eq hdet.norm continuous_const).inter ?_)
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
  have h0 : Continuous fun m : Matrix (Fin 2) (Fin 2) K => x * m 0 0 + y * m 1 0 :=
    (continuous_const.mul (continuous_entry K 0 0)).add
      (continuous_const.mul (continuous_entry K 1 0))
  have h1 : Continuous fun m : Matrix (Fin 2) (Fin 2) K => x * m 0 1 + y * m 1 1 :=
    (continuous_const.mul (continuous_entry K 0 1)).add
      (continuous_const.mul (continuous_entry K 1 1))
  exact (h0.norm.pow 2).add (h1.norm.pow 2)

private theorem norm_entry_le_one {m : Matrix (Fin 2) (Fin 2) K} (hm : m ∈ rowIsoSet K) (i j : Fin 2) :
    ‖m i j‖ ≤ 1 := by
  have hrow : ∀ x y : K,
      ‖x * m 0 0 + y * m 1 0‖ ^ 2 + ‖x * m 0 1 + y * m 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := hm.2.2
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at h
    exact h
  have hr0 : ‖m 0 0‖ ^ 2 + ‖m 0 1‖ ^ 2 = 1 := by
    have h := hrow 1 0
    simpa using h
  have hr1 : ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2 = 1 := by
    have h := hrow 0 1
    simpa using h
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 2 + b ^ 2 = 1 → a ≤ 1 := by
    intro a b ha hb h
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  fin_cases i <;> fin_cases j
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) hr0
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) (by rw [add_comm]; exact hr0)
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) hr1
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) (by rw [add_comm]; exact hr1)

private theorem isCompact_rowIsoSet [ProperSpace K] : IsCompact (rowIsoSet K) := by
  have hbox : IsCompact ((Set.pi Set.univ fun _ : Fin 2 =>
      Set.pi Set.univ fun _ : Fin 2 => Metric.closedBall (0 : K) 1) :
        Set (Matrix (Fin 2) (Fin 2) K)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hbox.of_isClosed_subset (isClosed_rowIsoSet K) fun m hm => ?_
  exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j =>
    mem_closedBall_zero_iff.mpr (norm_entry_le_one K hm i j)

private def toUnit (m : rowIsoSet K) : GL (Fin 2) K where
  val := m.1
  inv := m.1.adjugate
  val_inv := by
    have hd : m.1.det = 1 := m.2.1
    rw [Matrix.mul_adjugate, hd, one_smul]
  inv_val := by
    have hd : m.1.det = 1 := m.2.1
    rw [Matrix.adjugate_mul, hd, one_smul]

private theorem continuous_toUnit : Continuous (toUnit K) :=
  Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_adjugate⟩

private theorem range_toUnit :
    Set.range (toUnit K) = (rowIsometrySubgroup₀ K : Set (GL (Fin 2) K)) := by
  ext k
  constructor
  · rintro ⟨m, rfl⟩
    exact (mem_rowIsoSet_iff K (toUnit K m)).mp m.2
  · intro hk
    exact ⟨⟨(k : Matrix (Fin 2) (Fin 2) K), (mem_rowIsoSet_iff K k).mpr hk⟩, Units.ext rfl⟩

private theorem isCompact_rowIsometrySubgroup₀ [ProperSpace K] :
    IsCompact (rowIsometrySubgroup₀ K : Set (GL (Fin 2) K)) := by
  rw [← range_toUnit]
  haveI : CompactSpace (rowIsoSet K) := isCompact_iff_compactSpace.mp (isCompact_rowIsoSet K)
  exact isCompact_range (continuous_toUnit K)

end Compact

section Setting

variable (F : Type) [Field F] [NumberField F]

private abbrev Kw (w : InfinitePlace F) : Type := rowIsometrySubgroup₀ w.Completion

private abbrev Kprod : Type := Π w : InfinitePlace F, Kw F w

private scoped instance compactSpace_Kw (w : InfinitePlace F) : CompactSpace (Kw F w) :=
  haveI : ProperSpace w.Completion := NumberField.AdelicBox.properSpace_completion (K := F) w
  isCompact_iff_compactSpace.mp (isCompact_rowIsometrySubgroup₀ w.Completion)

omit [NumberField F] in
private theorem commute_archRowIsometryInclAt₀ {v w : InfinitePlace F} (hvw : v ≠ w) (a : Kw F v) (b : Kw F w) :
    Commute (archRowIsometryInclAt₀ F v a) (archRowIsometryInclAt₀ F w b) := by
  unfold archRowIsometryInclAt₀
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact commute_archGLIncl_of_ne F hvw _ _

private def inclArch : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) :=
  MonoidHom.noncommPiCoprod (archRowIsometryInclAt₀ F)
    (fun _ _ hvw => commute_archRowIsometryInclAt₀ F hvw)

private def inclAdelic : Kprod F →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F).comp (inclArch F)

variable {F}

private theorem inclAdelic_apply (κ : Kprod F) : inclAdelic F κ = adelicArchGLIncl F (inclArch F κ) :=
  rfl

private theorem inclArch_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclArch F (Pi.mulSingle w k) = archRowIsometryInclAt₀ F w k :=
  MonoidHom.noncommPiCoprod_mulSingle _ w k

private theorem inclAdelic_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclAdelic F (Pi.mulSingle w k) = rowIsometryInclAt₀ F w k :=
  congrArg (adelicArchGLIncl F) (inclArch_mulSingle w k)

private theorem inclArch_entry (κ : Kprod F) (i j : Fin 2) (w : InfinitePlace F) :
    ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
      = ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  classical
  let f : Kprod F →* (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    ((archMatrixPiEquiv F : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) →*
        Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion).comp
      (Units.coeHom (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))).comp (inclArch F)
  let g : Kprod F →* (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    MonoidHom.pi fun v : InfinitePlace F =>
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) v.Completion)).comp
        (rowIsometrySubgroup₀ v.Completion).subtype).comp
          (Pi.evalMonoidHom (fun u : InfinitePlace F => Kw F u) v)
  have hfg : f = g := by
    refine MonoidHom.pi_ext fun v k => ?_
    funext u
    show archMatrixPiEquiv F
        ((inclArch F (Pi.mulSingle v k) : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) u
      = ((Pi.mulSingle v k u : Kw F u) : GL (Fin 2) u.Completion)
    rw [inclArch_mulSingle]
    show archMatrixPiEquiv F (archMatrixUpdate F v ((k : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion)) u = _
    rw [archMatrixPiEquiv_archMatrixUpdate]
    by_cases huv : u = v
    · subst huv
      simp
    · simp [Function.update_of_ne huv, Pi.mulSingle_eq_of_ne huv]
  have h : f κ = g κ := by rw [hfg]
  have hw := congrFun h w
  exact congrFun (congrFun hw i) j

private theorem archComponent_inclArch (κ : Kprod F) (w : InfinitePlace F) :
    archComponent F w (inclArch F κ) = (κ w : GL (Fin 2) w.Completion) := by
  ext i j
  rw [AdelicLevel.archComponent_apply, inclArch_entry]

private theorem continuous_inclArch : Continuous (inclArch F) := by
  have hval : Continuous fun κ : Kprod F =>
      ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    refine continuous_matrix fun i j => ?_
    refine continuous_pi fun w => ?_
    simp only [inclArch_entry]
    exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w))).matrix_elem
      i j
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

private theorem continuous_inclAdelic : Continuous (inclAdelic F) :=
  continuous_adelicArchGLIncl.comp continuous_inclArch

end Setting

section HaarKprod

open MeasureTheory TopologicalSpace

variable (F : Type) [Field F]

private abbrev KprodMeasurableSpace : MeasurableSpace (Kprod F) := borel (Kprod F)

attribute [local instance] KprodMeasurableSpace

private theorem KprodBorelSpace : BorelSpace (Kprod F) := ⟨rfl⟩

attribute [local instance] KprodBorelSpace

private def KprodTop : PositiveCompacts (Kprod F) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by
    rw [interior_univ]
    exact ⟨1, Set.mem_univ 1⟩

private def muK : Measure (Kprod F) := Measure.haarMeasure (KprodTop F)

private theorem muK_univ : muK F Set.univ = 1 :=
  Measure.haarMeasure_self (K₀ := KprodTop F)

private scoped instance isProbabilityMeasure_muK : IsProbabilityMeasure (muK F) := ⟨muK_univ F⟩

private scoped instance isMulLeftInvariant_muK : (muK F).IsMulLeftInvariant := by
  unfold muK
  infer_instance

private scoped instance isHaarMeasure_muK : (muK F).IsHaarMeasure := by
  unfold muK
  infer_instance

private theorem isMulRightInvariant_muK : (muK F).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hg : Measurable fun κ : Kprod F => κ * g := (continuous_mul_const g).measurable
  haveI : IsFiniteMeasureOnCompacts (Measure.map (· * g) (muK F)) := ⟨fun _ _ => measure_lt_top _ _⟩
  have hfac : (Measure.map (· * g) (muK F)).haarScalarFactor (muK F) = 1 := by
    have h := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (Measure.map (· * g) (muK F))
      (muK F) (s := Set.univ) isClosed_closure.isCompact
    rw [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ, muK_univ, ENNReal.smul_def, smul_eq_mul,
      mul_one] at h
    exact ENNReal.coe_eq_one.mp h.symm
  ext s _
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (Measure.map (· * g) (muK F)) (muK F)
    isClosed_closure.isCompact, hfac, one_smul]

private theorem integral_mul_right_muK (h : Kprod F → ℂ) (k : Kprod F) :
    ∫ κ, h (κ * k) ∂muK F = ∫ κ, h κ ∂muK F :=
  haveI := isMulRightInvariant_muK F
  integral_mul_right_eq_self h k

private theorem integral_mul_left_muK (h : Kprod F → ℂ) (k : Kprod F) :
    ∫ κ, h (k * κ) ∂muK F = ∫ κ, h κ ∂muK F :=
  integral_mul_left_eq_self h k

end HaarKprod

end R5bK
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

end AlphaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

section AVGBlock

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm
open scoped Classical ContDiff

namespace R5bE

section ChiProd

variable (F : Type) [Field F] [NumberField F]

private def chiProd (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    R5bK.Kprod F →* ℂ where
  toFun κ := ∏ w, ((χ w (κ w) : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' κ κ' := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Pi.mul_apply, map_mul, Units.val_mul]

variable {F}

private theorem chiProd_apply (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (κ : R5bK.Kprod F) : chiProd F χ κ = ∏ w, ((χ w (κ w) : ℂˣ) : ℂ) := rfl

private theorem chiProd_mulSingle (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    chiProd F χ (Pi.mulSingle w k) = ((χ w k : ℂˣ) : ℂ) := by
  rw [chiProd_apply, Finset.prod_eq_single w]
  · rw [Pi.mulSingle_eq_same]
  · intro v _ hvw
    rw [Pi.mulSingle_eq_of_ne hvw, map_one, Units.val_one]
  · intro h
    exact absurd (Finset.mem_univ w) h

private theorem continuous_chiProd (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ)) :
    Continuous (chiProd F χ) := by
  show Continuous fun κ : R5bK.Kprod F => ∏ w, ((χ w (κ w) : ℂˣ) : ℂ)
  exact continuous_finsetProd _ fun w _ => (hχ w).comp (continuous_apply w)

private theorem eq_inclArch (ι : R5bK.Kprod F →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : R5bK.Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) :
    ι = R5bK.inclArch F := by
  refine MonoidHom.ext fun κ => Units.ext (Matrix.ext fun i j => funext fun w => ?_)
  have h1 := AdelicLevel.archComponent_apply (K := F) w (ι κ) i j
  have h2 := AdelicLevel.archComponent_apply (K := F) w (R5bK.inclArch F κ) i j
  rw [← h1, ← h2, hι, R5bK.archComponent_inclArch]

end ChiProd
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

end AVGBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

section MainBlock

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open scoped Classical

namespace R5bE

section Glue

variable {F : Type} [Field F] [NumberField F]

private theorem ext_of_glArch_glFin {a b : AdelicGL2 (𝓞 F) F}
    (h1 : glArch (𝓞 F) F a = glArch (𝓞 F) F b) (h2 : glFin (𝓞 F) F a = glFin (𝓞 F) F b) : a = b := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · have := congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing F) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h1
    simpa only [glArch_apply] using this
  · have := congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h2
    simpa only [glFin_apply] using this

private theorem commute_of_mem_finiteAdelicGL2Subgroup {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) : g * adelicArchGLIncl F y = adelicArchGLIncl F y * g := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg
  refine ext_of_glArch_glFin ?_ ?_
  · rw [map_mul, map_mul, hg, glArch_adelicArchGLIncl, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_adelicArchGLIncl, one_mul, mul_one]

private theorem exists_eq_inclAdelic_of_mem_iSup {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) : ∃ κ : R5bK.Kprod F, k = R5bK.inclAdelic F κ := by
  have hle : (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) ≤ (R5bK.inclAdelic F).range := by
    refine iSup_le fun w => ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨Pi.mulSingle w k, R5bK.inclAdelic_mulSingle w k⟩
  obtain ⟨κ, hκ⟩ := hle hk
  exact ⟨κ, hκ.symm⟩

private theorem continuous_rowIsometryInclAt₀ (w : InfinitePlace F) : Continuous (rowIsometryInclAt₀ F w) := by
  have h : (rowIsometryInclAt₀ F w : rowIsometrySubgroup₀ w.Completion → AdelicGL2 (𝓞 F) F) =
      fun k => R5bK.inclAdelic F (Pi.mulSingle w k) := by
    funext k
    exact (R5bK.inclAdelic_mulSingle w k).symm
  rw [h]
  exact R5bK.continuous_inclAdelic.comp (continuous_mulSingle w)

private theorem continuous_char_of_ne_zero
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {Ψ : AdelicGL2 (𝓞 F) F → ℂ} (hΨc : Continuous Ψ) (hΨ : Ψ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    {x₀ : AdelicGL2 (𝓞 F) F} (hx₀ : Ψ x₀ ≠ 0) (w : InfinitePlace F) :
    Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ) := by
  rw [mem_archCutSubmodule_ofChar_iff] at hΨ
  have heq : (fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ)) =
      fun k => Ψ (x₀ * rowIsometryInclAt₀ F w k) * (Ψ x₀)⁻¹ := by
    funext k
    rw [show x₀ * rowIsometryInclAt₀ F w k = x₀ * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) from rfl,
      hΨ w k x₀, mul_assoc, mul_inv_cancel₀ hx₀, mul_one]
  rw [heq]
  exact (hΨc.comp (continuous_const.mul (continuous_rowIsometryInclAt₀ w))).mul continuous_const

private theorem conj_invariant_of_isArchFactorBiFinite
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hbf : IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)) :
    fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x := by
  obtain ⟨hl, hr⟩ := hbf
  change (fun x => fa x⁻¹) ∈
    ⨅ w : InfinitePlace F, ⨆ _ : Fin 1, archFactorTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w)) at hl
  change fa ∈ ⨅ w : InfinitePlace F, ⨆ _ : Fin 1, archFactorDualTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w)) at hr
  simp only [iSup_const, Submodule.mem_iInf] at hl hr
  have hl' := (mem_typeSubmodule_charRep_iff (archRowIsometryInclAt₀ F w) (χ w) _).mp (hl w)
  have hr' := (mem_typeSubmodule_charRep_dual_iff (archRowIsometryInclAt₀ F w) (χ w) _).mp (hr w)

  have hleft : ∀ (k : rowIsometrySubgroup₀ w.Completion) (z : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * z) = ((χ w k⁻¹ : ℂˣ) : ℂ) * fa z := by
    intro k z
    have h := hl' k⁻¹ z⁻¹
    simp only [mul_inv_rev, ← map_inv, inv_inv] at h
    exact h
  rw [← map_inv, hr' k⁻¹ (archRowIsometryInclAt₀ F w k * x), hleft k x, inv_inv, ← mul_assoc, ← Units.val_mul,
    ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul]

end Glue
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

section Main

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] R5bK.KprodMeasurableSpace R5bK.KprodBorelSpace

private theorem r5b_main
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (Ψ₁ φ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ₁ : Continuous Ψ₁)
    (hχ₁ : Ψ₁ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hχφ : φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hφ : φ ∈ Submodule.span ℂ
      {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F (g * k) Ψ₁ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          ψ = rightTranslate F (g * k) (rightConv F Ψ₁ f)}) :
    φ ∈ Submodule.span ℂ ((fun g => rightTranslate F g Ψ₁) '' (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))) ⊔
      Submodule.span ℂ
        {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F,
          ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
            IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa ∧
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
              fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
            IsFinTestFactor F ff ∧
            ψ = rightTranslate F g (rightConv F Ψ₁
              (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)))} := by

  set T : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    Submodule.span ℂ ((fun g => rightTranslate F g Ψ₁) '' (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))) ⊔
      Submodule.span ℂ
        {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F,
          ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
            IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa ∧
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
              fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
            IsFinTestFactor F ff ∧
            ψ = rightTranslate F g (rightConv F Ψ₁
              (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)))} with hT

  by_cases h0 : Ψ₁ = 0
  · subst h0
    have hsub : Submodule.span ℂ
        {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          ψ = rightTranslate F (g * k) (0 : AdelicGL2 (𝓞 F) F → ℂ) ∨
          ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
            ψ = rightTranslate F (g * k) (rightConv F 0 f)} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro ψ ⟨g, -, k, -, hψ⟩
      rcases hψ with rfl | ⟨f, tys, -, -, rfl⟩
      · exact (Submodule.mem_bot ℂ).mpr rfl
      · refine (Submodule.mem_bot ℂ).mpr ?_
        show rightTranslate F (g * k) (rightConv F (fun _ => 0) f) = 0
        rw [rightConv_zero_left]
        rfl
    have hφ0 : φ = 0 := (Submodule.mem_bot ℂ).mp (hsub hφ)
    rw [hφ0]
    exact Submodule.zero_mem _

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Ψ₁ x₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (funext h)
  have hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ) :=
    continuous_char_of_ne_zero χ hΨ₁ hχ₁ hx₀

  haveI := R5bK.isMulRightInvariant_muK F
  let μ : Measure (R5bK.Kprod F) := R5bK.muK F
  let ι : R5bK.Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) := R5bK.inclArch F
  have hι : ∀ (κ : R5bK.Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
    fun κ w => R5bK.archComponent_inclArch κ w
  have hιA : ∀ κ : R5bK.Kprod F, adelicArchGLIncl F (ι κ) = R5bK.inclAdelic F κ := fun κ => rfl

  let P : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun θ x =>
    ∫ κ, (∏ w, ((χ w (κ w)⁻¹ : ℂˣ) : ℂ)) * θ (x * adelicArchGLIncl F (ι κ)) ∂μ
  have hP : ∀ (θ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F),
      P θ x = ∫ κ, (∏ w, ((χ w (κ w)⁻¹ : ℂˣ) : ℂ)) * θ (x * adelicArchGLIncl F (ι κ)) ∂μ := fun _ _ => rfl
  have packet := fun (θ : AdelicGL2 (𝓞 F) F → ℂ) (hθ : Continuous θ) =>
    AutomorphicForm.CuspidalConstituent.continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl F χ hχ μ ι hι P hP θ hθ
  have hP0 : P 0 = 0 := by
    funext x
    rw [hP]
    simp

  suffices hind : ∀ ψ ∈ Submodule.span ℂ
      {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F (g * k) Ψ₁ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          ψ = rightTranslate F (g * k) (rightConv F Ψ₁ f)}, Continuous ψ ∧ P ψ ∈ T by
    obtain ⟨hφc, hPφ⟩ := hind φ hφ
    obtain ⟨-, -, hfix, -⟩ := packet φ hφc
    rw [← hfix hχφ]
    exact hPφ
  intro ψ hψ
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  ·
    rintro ψ ⟨g, hg, k, hk, hgen⟩
    obtain ⟨κ₀, rfl⟩ := exists_eq_inclAdelic_of_mem_iSup hk
    have hcommg : ∀ κ, g * adelicArchGLIncl F (ι κ) = adelicArchGLIncl F (ι κ) * g :=
      fun κ => commute_of_mem_finiteAdelicGL2Subgroup hg (ι κ)
    rcases hgen with rfl | ⟨f, tys, hf, -, rfl⟩
    ·
      have hc : Continuous (rightTranslate F (R5bK.inclAdelic F κ₀) Ψ₁) := continuous_rightTranslate F hΨ₁ _
      refine ⟨continuous_rightTranslate F hΨ₁ _, ?_⟩
      obtain ⟨-, -, hfix, -, hchar, -⟩ := packet Ψ₁ hΨ₁
      obtain ⟨-, -, -, hcomm, -⟩ := packet _ hc
      rw [← rightTranslate_rightTranslate, hcomm g hcommg, ← hιA, hchar κ₀, hfix hχ₁, rightTranslate_smul]
      refine Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩))
    ·
      obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
      have hfeq' : f = fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y) := funext hfeq
      have hconvc : Continuous (rightConv F Ψ₁ f) :=
        (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F Ψ₁ hΨ₁ f
          ⟨fa, ff, hfa, hff, hfeq⟩).1
      have hc : Continuous (rightTranslate F (R5bK.inclAdelic F κ₀) (rightConv F Ψ₁ f)) :=
        continuous_rightTranslate F hconvc _
      refine ⟨continuous_rightTranslate F hconvc _, ?_⟩
      obtain ⟨-, -, -, -, hchar, -⟩ := packet _ hconvc
      obtain ⟨-, -, -, hcomm, -⟩ := packet _ hc

      let fa' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun y => ∫ p : R5bK.Kprod F × R5bK.Kprod F,
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
          ∂(μ.prod μ)
      obtain ⟨hfa't, hfa'b⟩ :=
        AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor F χ hχ μ ι hι fa hfa
      have hconv : P (rightConv F Ψ₁ f) = rightConv F Ψ₁
          (fun y => fa' (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)) := by
        have h := AutomorphicForm.CuspidalConstituent.integral_rightConv_rightTranslate_eq_rightConv_doubleAvg F χ hχ μ
          ι hι Ψ₁ hΨ₁ hχ₁ fa hfa ff hff
        rw [hfeq']
        exact h
      rw [← rightTranslate_rightTranslate, hcomm g hcommg, ← hιA, hchar κ₀, hconv, rightTranslate_smul]
      refine Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      exact ⟨g, hg, fa', ff, hfa't, hfa'b, conj_invariant_of_isArchFactorBiFinite χ hfa'b, hff, rfl⟩
  · exact ⟨continuous_const, by rw [hP0]; exact Submodule.zero_mem _⟩
  · rintro ψ₁ ψ₂ - - ⟨h1c, h1P⟩ ⟨h2c, h2P⟩
    refine ⟨h1c.add h2c, ?_⟩
    obtain ⟨-, -, -, -, -, hadd, -⟩ := packet ψ₁ h1c
    rw [hadd ψ₂ h2c]
    exact T.add_mem h1P h2P
  · rintro c ψ - ⟨hc, hPψ⟩
    refine ⟨hc.const_smul c, ?_⟩
    obtain ⟨-, -, -, -, -, -, hsmul⟩ := packet ψ hc
    rw [hsmul c]
    exact T.smul_mem c hPψ

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

end MainBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

section SolutionBlock

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem solution
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (Ψ₁ φ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ₁ : Continuous Ψ₁)
    (hχ₁ : Ψ₁ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hχφ : φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hφ : φ ∈ Submodule.span ℂ
      {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F (g * k) Ψ₁ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          ψ = rightTranslate F (g * k) (rightConv F Ψ₁ f)}) :
    φ ∈ Submodule.span ℂ ((fun g => rightTranslate F g Ψ₁) '' (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))) ⊔
      Submodule.span ℂ
        {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F,
          ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
            IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa ∧
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
              fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
            IsFinTestFactor F ff ∧
            ψ = rightTranslate F g (rightConv F Ψ₁
              (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)))} :=
  R5bE.r5b_main F χ Ψ₁ φ hΨ₁ hχ₁ hχφ hφ

end SolutionBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.R5bK"

end S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar (solution)
