-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/956a5dd2-8e5c-5d8a-81b3-42deafdda7ff

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl

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
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

end AlphaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

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
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

end AVGBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

section PCHIBlock

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.CuspidalConstituent
open IsDedekindDomain Filter Topology
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
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

section PCHI

variable (F : Type) [Field F] [NumberField F]

private theorem pchi_main
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hP : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F),
      P φ x = ∫ κ, (∏ w, ((χ w (κ w)⁻¹ : ℂˣ) : ℂ)) * φ (x * adelicArchGLIncl F (ι κ)) ∂μ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    Continuous (P φ) ∧
    P φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) ∧
    (φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) → P φ = φ) ∧
    (∀ g : AdelicGL2 (𝓞 F) F, (∀ κ, g * adelicArchGLIncl F (ι κ) = adelicArchGLIncl F (ι κ) * g) →
      P (rightTranslate F g φ) = rightTranslate F g (P φ)) ∧
    (∀ κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion,
      P (rightTranslate F (adelicArchGLIncl F (ι κ)) φ) = (∏ w, ((χ w (κ w) : ℂˣ) : ℂ)) • P φ) ∧
    (∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, Continuous ψ → P (φ + ψ) = P φ + P ψ) ∧
    (∀ c : ℂ, P (c • φ) = c • P φ) := by
  obtain rfl : ι = R5bK.inclArch F := eq_inclArch ι hι
  haveI : SecondCountableTopology (R5bK.Kprod F) := R5bC.secondCountableTopology_piRowIsometrySubgroup₀ F

  let e : R5bK.Kprod F → ℂ := fun κ => chiProd F χ κ⁻¹
  have he : Continuous e := (continuous_chiProd χ hχ).comp continuous_inv
  have he_mul : ∀ κ κ' : R5bK.Kprod F, e (κ * κ') = e κ * e κ' := by
    intro κ κ'
    show chiProd F χ (κ * κ')⁻¹ = chiProd F χ κ⁻¹ * chiProd F χ κ'⁻¹
    rw [mul_inv_rev, map_mul, mul_comm]
  have he_chi : ∀ κ : R5bK.Kprod F, e κ * chiProd F χ κ = 1 := by
    intro κ
    show chiProd F χ κ⁻¹ * chiProd F χ κ = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  let a : R5bK.Kprod F →* AdelicGL2 (𝓞 F) F := R5bK.inclAdelic F
  have ha : Continuous a := R5bK.continuous_inclAdelic
  have hP' : ∀ (θ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F), P θ x = ∫ κ, e κ * θ (x * a κ) ∂μ :=
    fun θ x => hP θ x
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun _ _ => measure_lt_top _ _⟩

  have hint : ∀ (θ : AdelicGL2 (𝓞 F) F → ℂ), Continuous θ → ∀ x : AdelicGL2 (𝓞 F) F,
      Integrable (fun κ => e κ * θ (x * a κ)) μ := by
    intro θ hθ x
    have hc : Continuous fun κ => e κ * θ (x * a κ) := he.mul (hθ.comp (continuous_const.mul ha))
    exact hc.integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
  have he_single : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      e (Pi.mulSingle w k) = ((χ w k⁻¹ : ℂˣ) : ℂ) := by
    intro w k
    show chiProd F χ (Pi.mulSingle w k)⁻¹ = _
    rw [← Pi.mulSingle_inv, chiProd_mulSingle]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    letI : UniformSpace (AdelicGL2 (𝓞 F) F) := IsTopologicalGroup.rightUniformSpace _
    letI : UniformSpace (R5bK.Kprod F) := IsTopologicalGroup.rightUniformSpace _
    have hF : Continuous ↿(fun (x : AdelicGL2 (𝓞 F) F) (κ : R5bK.Kprod F) => e κ * φ (x * a κ)) := by
      show Continuous fun p : AdelicGL2 (𝓞 F) F × R5bK.Kprod F => e p.2 * φ (p.1 * a p.2)
      exact (he.comp continuous_snd).mul (hφ.comp (continuous_fst.mul (ha.comp continuous_snd)))
    rw [continuous_iff_continuousAt]
    intro x₀
    have hU := Continuous.tendstoUniformly (fun (x : AdelicGL2 (𝓞 F) F) (κ : R5bK.Kprod F) => e κ * φ (x * a κ))
      hF x₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have hU' := Metric.tendstoUniformly_iff.mp hU (ε / 2) (half_pos hε)
    filter_upwards [hU'] with x hx
    rw [hP', hP', dist_eq_norm, ← integral_sub (hint φ hφ x) (hint φ hφ x₀)]
    have hle : ‖∫ κ, (e κ * φ (x * a κ) - e κ * φ (x₀ * a κ)) ∂μ‖ ≤ ε / 2 * μ.real Set.univ := by
      refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun κ => ?_)
      rw [← dist_eq_norm, dist_comm]
      exact (hx κ).le
    rw [probReal_univ, mul_one] at hle
    exact lt_of_le_of_lt hle (half_lt_self hε)
  ·
    rw [mem_archCutSubmodule_ofChar_iff]
    intro w k x
    show P φ (x * rowIsometryInclAt₀ F w k) = ((χ w k : ℂˣ) : ℂ) * P φ x
    rw [← R5bK.inclAdelic_mulSingle w k, hP', hP', ← integral_const_mul,
      ← integral_mul_left_eq_self (fun κ => ((χ w k : ℂˣ) : ℂ) * (e κ * φ (x * a κ))) (Pi.mulSingle w k)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    dsimp only
    rw [he_mul, he_single, map_mul, ← mul_assoc x, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← map_mul,
      mul_inv_cancel, map_one, Units.val_one, one_mul]
  ·
    intro hφcut
    funext x
    rw [hP']
    have key : (fun κ => e κ * φ (x * a κ)) = fun _ => φ x := by
      funext κ
      rw [apply_mul_inclAdelic_of_mem_archCutSubmodule χ hφcut κ x, ← mul_assoc, he_chi, one_mul]
    rw [key, integral_const, probReal_univ, one_smul]
  ·
    intro g hg
    funext x
    rw [rightTranslate_apply, hP', hP']
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    show e κ * φ (x * adelicArchGLIncl F (R5bK.inclArch F κ) * g) =
      e κ * φ (x * g * adelicArchGLIncl F (R5bK.inclArch F κ))
    rw [mul_assoc x g, hg κ, ← mul_assoc]
  ·
    intro κ₀
    funext x
    rw [Pi.smul_apply, smul_eq_mul, hP', hP', ← integral_const_mul,
      ← integral_mul_right_eq_self (fun κ => (∏ w, ((χ w (κ₀ w) : ℂˣ) : ℂ)) * (e κ * φ (x * a κ))) κ₀]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    dsimp only [rightTranslate]
    rw [he_mul, map_mul, ← mul_assoc x, ← mul_assoc (∏ w, ((χ w (κ₀ w) : ℂˣ) : ℂ)), ← mul_assoc (∏ w, ((χ w (κ₀ w) : ℂˣ) : ℂ)),
      mul_comm (∏ w, ((χ w (κ₀ w) : ℂˣ) : ℂ)) (e κ), mul_assoc (e κ) _ (e κ₀),
      show (∏ w, ((χ w (κ₀ w) : ℂˣ) : ℂ)) * e κ₀ = 1 from (mul_comm _ _).trans (he_chi κ₀), mul_one]
    rfl
  ·
    intro ψ hψ
    funext x
    rw [Pi.add_apply, hP', hP', hP', ← integral_add (hint φ hφ x) (hint ψ hψ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    show e κ * (φ (x * a κ) + ψ (x * a κ)) = e κ * φ (x * a κ) + e κ * ψ (x * a κ)
    ring
  ·
    intro c
    funext x
    rw [Pi.smul_apply, smul_eq_mul, hP', hP', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    show e κ * (c * φ (x * a κ)) = c * (e κ * φ (x * a κ))
    ring

end PCHI
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

end PCHIBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

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
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hP : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F),
      P φ x = ∫ κ, (∏ w, ((χ w (κ w)⁻¹ : ℂˣ) : ℂ)) * φ (x * adelicArchGLIncl F (ι κ)) ∂μ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    Continuous (P φ) ∧
    P φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) ∧
    (φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) → P φ = φ) ∧
    (∀ g : AdelicGL2 (𝓞 F) F, (∀ κ, g * adelicArchGLIncl F (ι κ) = adelicArchGLIncl F (ι κ) * g) →
      P (rightTranslate F g φ) = rightTranslate F g (P φ)) ∧
    (∀ κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion,
      P (rightTranslate F (adelicArchGLIncl F (ι κ)) φ) = (∏ w, ((χ w (κ w) : ℂˣ) : ℂ)) • P φ) ∧
    (∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, Continuous ψ → P (φ + ψ) = P φ + P ψ) ∧
    (∀ c : ℂ, P (c • φ) = c • P φ) :=
  R5bE.pchi_main F χ hχ μ ι hι P hP φ hφ

end SolutionBlock
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.R5bK"

end S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl (solution)
