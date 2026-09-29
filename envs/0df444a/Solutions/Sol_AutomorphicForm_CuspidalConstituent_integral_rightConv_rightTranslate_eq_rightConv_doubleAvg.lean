-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.integral_rightConv_rightTranslate_eq_rightConv_doubleAvg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ef435e31-5f85-5489-a7c6-3afce98b361f

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg

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
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

end AlphaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

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
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

end AVGBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

section CONVBlock

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open scoped Classical

namespace R5bE

section KprodFacts

variable {F : Type} [Field F] [NumberField F]

private theorem Kprod_induction {p : R5bK.Kprod F → Prop} (h1 : p 1)
    (hmul : ∀ κ κ' : R5bK.Kprod F, p κ → p κ' → p (κ * κ'))
    (hs : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), p (Pi.mulSingle w k))
    (κ : R5bK.Kprod F) : p κ := by
  rw [← Finset.noncommProd_mulSingle κ]
  exact Finset.noncommProd_induction _ _ _ p hmul h1 fun w _ => hs w (κ w)

private theorem apply_mul_inclAdelic_of_mem_archCutSubmodule
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {Ψ : AdelicGL2 (𝓞 F) F → ℂ} (hΨ : Ψ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (κ : R5bK.Kprod F) (x : AdelicGL2 (𝓞 F) F) :
    Ψ (x * R5bK.inclAdelic F κ) = chiProd F χ κ * Ψ x := by
  rw [mem_archCutSubmodule_ofChar_iff] at hΨ
  revert x
  refine Kprod_induction (p := fun κ => ∀ x, Ψ (x * R5bK.inclAdelic F κ) = chiProd F χ κ * Ψ x) ?_ ?_ ?_ κ
  · intro x
    rw [map_one, map_one, mul_one, one_mul]
  · intro κ κ' hκ hκ' x
    rw [map_mul, map_mul, ← mul_assoc, hκ', hκ]
    ring
  · intro w k x
    rw [R5bK.inclAdelic_mulSingle, chiProd_mulSingle]
    exact hΨ w k x

private theorem rightTranslate_inclAdelic_of_mem_archCutSubmodule
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {Ψ : AdelicGL2 (𝓞 F) F → ℂ} (hΨ : Ψ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (κ : R5bK.Kprod F) :
    rightTranslate F (R5bK.inclAdelic F κ) Ψ = chiProd F χ κ • Ψ := by
  funext x
  exact apply_mul_inclAdelic_of_mem_archCutSubmodule χ hΨ κ x

end KprodFacts
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

section Conv

variable (F : Type) [Field F] [NumberField F]

private abbrev GMeas : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F

attribute [local instance] GMeas

private theorem GBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F

attribute [local instance] GBorel

private theorem GHaar : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

attribute [local instance] GHaar

variable {F}

private theorem rightConv_smul_left (c : ℂ) (Ψ g : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    rightConv F (c • Ψ) g x = c * rightConv F Ψ g x := by
  rw [rightConv_apply, rightConv_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show c * Ψ (x * y) * g y = c * (Ψ (x * y) * g y)
  ring

private theorem rightConv_apply_mul (Ψ g : AdelicGL2 (𝓞 F) F → ℂ) (x h : AdelicGL2 (𝓞 F) F) :
    rightConv F Ψ g (x * h) = rightConv F Ψ (fun y => g (h⁻¹ * y)) x := by
  rw [rightConv_apply, rightConv_apply]
  rw [← integral_mul_left_eq_self (fun y => Ψ (x * y) * g (h⁻¹ * y)) h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show Ψ (x * h * y) * g y = Ψ (x * (h * y)) * g (h⁻¹ * (h * y))
  rw [mul_assoc, inv_mul_cancel_left]

private theorem rightConv_comp_mul_inv_inclAdelic
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {Ψ : AdelicGL2 (𝓞 F) F → ℂ} (hΨ : Ψ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (g : AdelicGL2 (𝓞 F) F → ℂ) (κ : R5bK.Kprod F) (x : AdelicGL2 (𝓞 F) F) :
    rightConv F Ψ (fun y => g (y * (R5bK.inclAdelic F κ)⁻¹)) x = chiProd F χ κ * rightConv F Ψ g x := by
  have e1 : (fun y => g (y * (R5bK.inclAdelic F κ)⁻¹)) =
      fun y => g ((R5bK.inclAdelic F κ)⁻¹ * (R5bK.inclAdelic F κ * y * (R5bK.inclAdelic F κ)⁻¹)) := by
    funext y
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
  have e2 : (fun y => g ((R5bK.inclAdelic F κ)⁻¹ * ((R5bK.inclAdelic F κ)⁻¹⁻¹ * y))) = g := by
    funext y
    rw [inv_inv, inv_mul_cancel_left]
  have hcomm := congrFun
    (AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj F
      (R5bK.inclAdelic F κ) Ψ (fun y => g ((R5bK.inclAdelic F κ)⁻¹ * y))) (x * (R5bK.inclAdelic F κ)⁻¹)
  rw [rightTranslate_apply, inv_mul_cancel_right, rightTranslate_inclAdelic_of_mem_archCutSubmodule χ hΨ κ,
    rightConv_smul_left, rightConv_apply_mul] at hcomm

  rw [e1, ← hcomm]
  simp only [inv_inv, inv_mul_cancel_left]

private theorem conv_main
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (Ψ : AdelicGL2 (𝓞 F) F → ℂ) (hΨc : Continuous Ψ)
    (hΨ : Ψ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff)
    (x : AdelicGL2 (𝓞 F) F) :
    ∫ k, (∏ w, ((χ w (k w)⁻¹ : ℂˣ) : ℂ)) *
        rightConv F Ψ (fun y => fa (glArch (𝓞 F) F y) * ff (glFin (𝓞 F) F y)) (x * adelicArchGLIncl F (ι k)) ∂μ =
      rightConv F Ψ (fun y => (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
            (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
          (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) *
            fa ((ι p.1)⁻¹ * glArch (𝓞 F) F y * (ι p.2)⁻¹) ∂(μ.prod μ)) * ff (glFin (𝓞 F) F y)) x := by
  obtain rfl : ι = R5bK.inclArch F := eq_inclArch ι hι
  haveI : SecondCountableTopology (R5bK.Kprod F) := R5bC.secondCountableTopology_piRowIsometrySubgroup₀ F

  let e : R5bK.Kprod F → ℂ := fun κ => chiProd F χ κ⁻¹
  have he : Continuous e := (continuous_chiProd χ hχ).comp continuous_inv
  have he_chi : ∀ κ : R5bK.Kprod F, e κ * chiProd F χ κ = 1 := by
    intro κ
    show chiProd F χ κ⁻¹ * chiProd F χ κ = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  let a : R5bK.Kprod F →* AdelicGL2 (𝓞 F) F := R5bK.inclAdelic F
  have ha : Continuous a := R5bK.continuous_inclAdelic
  have ha_apply : ∀ κ : R5bK.Kprod F, adelicArchGLIncl F (R5bK.inclArch F κ) = a κ := fun κ => rfl
  let f : AdelicGL2 (𝓞 F) F → ℂ := fun y => fa (glArch (𝓞 F) F y) * ff (glFin (𝓞 F) F y)
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f
    ⟨fa, ff, hfa, hff, fun _ => rfl⟩

  have hf_conj : ∀ (p : R5bK.Kprod F × R5bK.Kprod F) (y : AdelicGL2 (𝓞 F) F),
      f ((a p.1)⁻¹ * y * (a p.2)⁻¹) =
        fa ((R5bK.inclArch F p.1)⁻¹ * glArch (𝓞 F) F y * (R5bK.inclArch F p.2)⁻¹) * ff (glFin (𝓞 F) F y) := by
    intro p y
    show fa (glArch (𝓞 F) F _) * ff (glFin (𝓞 F) F _) = _
    rw [map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_inv, map_inv, ← ha_apply, ← ha_apply,
      glArch_adelicArchGLIncl, glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, glFin_adelicArchGLIncl, inv_one,
      one_mul, mul_one]
  have hRHSfun : (fun y => (∫ p : R5bK.Kprod F × R5bK.Kprod F,
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) *
          fa ((R5bK.inclArch F p.1)⁻¹ * glArch (𝓞 F) F y * (R5bK.inclArch F p.2)⁻¹) ∂(μ.prod μ)) *
        ff (glFin (𝓞 F) F y)) =
      fun y => ∫ p : R5bK.Kprod F × R5bK.Kprod F, e p.1 * e p.2 * f ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ) := by
    funext y
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) *
        fa ((R5bK.inclArch F p.1)⁻¹ * glArch (𝓞 F) F y * (R5bK.inclArch F p.2)⁻¹) * ff (glFin (𝓞 F) F y) =
      e p.1 * e p.2 * f ((a p.1)⁻¹ * y * (a p.2)⁻¹)
    rw [hf_conj p y, ← mul_assoc]
    rfl
  rw [hRHSfun]
  show ∫ k, e k * rightConv F Ψ f (x * a k) ∂μ =
    rightConv F Ψ (fun y => ∫ p : R5bK.Kprod F × R5bK.Kprod F,
      e p.1 * e p.2 * f ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) x

  let H : AdelicGL2 (𝓞 F) F → R5bK.Kprod F × R5bK.Kprod F → ℂ := fun y p =>
    Ψ (x * y) * (e p.1 * e p.2 * f ((a p.1)⁻¹ * y * (a p.2)⁻¹))
  have hHc : Continuous (Function.uncurry H) := by
    refine ((hΨc.comp (continuous_const.mul continuous_fst)).mul ?_)
    refine (((he.comp (continuous_fst.comp continuous_snd)).mul
      (he.comp (continuous_snd.comp continuous_snd))).mul (hfc.comp ?_))
    exact (((ha.comp (continuous_fst.comp continuous_snd)).inv).mul continuous_fst).mul
      (ha.comp (continuous_snd.comp continuous_snd)).inv
  let S : Set (AdelicGL2 (𝓞 F) F) :=
    (fun q : (R5bK.Kprod F × AdelicGL2 (𝓞 F) F) × R5bK.Kprod F => a q.1.1 * q.1.2 * a q.2) ''
      ((Set.univ ×ˢ tsupport f) ×ˢ Set.univ)
  have hS : IsCompact S :=
    ((isCompact_univ.prod hfs.isCompact).prod isCompact_univ).image
      (((ha.comp (continuous_fst.comp continuous_fst)).mul (continuous_snd.comp continuous_fst)).mul
        (ha.comp continuous_snd))
  have hf_zero : ∀ (y : AdelicGL2 (𝓞 F) F) (p : R5bK.Kprod F × R5bK.Kprod F), y ∉ S →
      f ((a p.1)⁻¹ * y * (a p.2)⁻¹) = 0 := by
    intro y p hy
    by_contra hne
    refine hy ⟨((p.1, (a p.1)⁻¹ * y * (a p.2)⁻¹), p.2), ⟨⟨Set.mem_univ _, subset_tsupport _ hne⟩, Set.mem_univ _⟩,
      ?_⟩
    show a p.1 * ((a p.1)⁻¹ * y * (a p.2)⁻¹) * a p.2 = y
    group
  have hHs : HasCompactSupport (Function.uncurry H) := by
    refine HasCompactSupport.intro (hS.prod isCompact_univ) fun q hq => ?_
    have hy : q.1 ∉ S := fun h => hq ⟨h, Set.mem_univ _⟩
    show Ψ (x * q.1) * (e q.2.1 * e q.2.2 * f ((a q.2.1)⁻¹ * q.1 * (a q.2.2)⁻¹)) = 0
    rw [hf_zero q.1 q.2 hy, mul_zero, mul_zero]

  have step1 : rightConv F Ψ (fun y => ∫ p : R5bK.Kprod F × R5bK.Kprod F,
        e p.1 * e p.2 * f ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) x =
      ∫ y, ∫ p, H y p ∂(μ.prod μ) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (integral_const_mul _ _).symm
  haveI : IsFiniteMeasure (μ.prod μ) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (μ.prod μ) := ⟨fun _ _ => measure_lt_top _ _⟩
  have step2 : ∫ y, ∫ p, H y p ∂(μ.prod μ) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ p, ∫ y, H y p ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) ∂(μ.prod μ) :=
    integral_integral_swap_of_hasCompactSupport hHc hHs
  have step3 : ∀ p : R5bK.Kprod F × R5bK.Kprod F,
      ∫ y, H y p ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
        e p.1 * rightConv F Ψ f (x * a p.1) := by
    intro p
    have hI3 := rightConv_comp_mul_inv_inclAdelic χ hΨ (fun y => f ((a p.1)⁻¹ * y)) p.2 x
    calc ∫ y, H y p ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
        = e p.1 * e p.2 * rightConv F Ψ (fun y => f ((a p.1)⁻¹ * (y * (a p.2)⁻¹))) x := by
          rw [rightConv_apply, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show Ψ (x * y) * (e p.1 * e p.2 * f ((a p.1)⁻¹ * y * (a p.2)⁻¹)) =
            e p.1 * e p.2 * (Ψ (x * y) * f ((a p.1)⁻¹ * (y * (a p.2)⁻¹)))
          rw [mul_assoc ((a p.1)⁻¹)]
          ring
      _ = e p.1 * e p.2 * (chiProd F χ p.2 * rightConv F Ψ (fun y => f ((a p.1)⁻¹ * y)) x) := by rw [hI3]
      _ = e p.1 * rightConv F Ψ (fun y => f ((a p.1)⁻¹ * y)) x := by
          rw [show e p.1 * e p.2 * (chiProd F χ p.2 * rightConv F Ψ (fun y => f ((a p.1)⁻¹ * y)) x) =
            e p.1 * (e p.2 * chiProd F χ p.2) * rightConv F Ψ (fun y => f ((a p.1)⁻¹ * y)) x by ring,
            he_chi, mul_one]
      _ = e p.1 * rightConv F Ψ f (x * a p.1) := by rw [rightConv_apply_mul]
  let g : R5bK.Kprod F → ℂ := fun k => e k * rightConv F Ψ f (x * a k)
  have step4 : ∫ p, ∫ y, H y p ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) ∂(μ.prod μ) =
      ∫ p : R5bK.Kprod F × R5bK.Kprod F, g p.1 ∂(μ.prod μ) :=
    integral_congr_ae (Filter.Eventually.of_forall step3)
  haveI : SigmaFinite μ := IsFiniteMeasure.toSigmaFinite μ
  haveI : SFinite μ := inferInstance
  have step5 : ∫ p : R5bK.Kprod F × R5bK.Kprod F, g p.1 ∂(μ.prod μ) = ∫ k, g k ∂μ := by
    rw [integral_fun_fst g]
    simp [Measure.real]
  rw [step1, step2, step4, step5]

private theorem conv_main_v4
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (Ψ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ : Continuous Ψ)
    (hΨχ : Ψ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    (fun x => ∫ κ, (∏ w, ((χ w (κ w)⁻¹ : ℂˣ) : ℂ)) *
        rightConv F Ψ (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y))
          (x * adelicArchGLIncl F (ι κ)) ∂μ)
      = rightConv F Ψ (fun y =>
          (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
        ∂(μ.prod μ)) (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)) := by
  funext x
  exact conv_main χ hχ μ ι hι Ψ hΨ hΨχ fa hfa ff hff x

end Conv
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

end CONVBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

section SolutionBlock

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem solution
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (Ψ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ : Continuous Ψ)
    (hΨχ : Ψ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    (fun x => ∫ κ, (∏ w, ((χ w (κ w)⁻¹ : ℂˣ) : ℂ)) *
        rightConv F Ψ (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y))
          (x * adelicArchGLIncl F (ι κ)) ∂μ)
      = rightConv F Ψ (fun y =>
          (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
        ∂(μ.prod μ)) (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)) :=
  R5bE.conv_main_v4 χ hχ μ ι hι Ψ hΨ hΨχ fa hfa ff hff

end SolutionBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.R5bK"

end S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg (solution)
