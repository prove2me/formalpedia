-- Prove2me | solution 1 for AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b330cb03-d638-583a-bfc0-fbe789d8ec56

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Mathlib.Analysis.Calculus.ParametricIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor

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
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end AlphaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section GammaBlock

open NumberField NumberField.AdelicLevel
open AutomorphicForm
open IsDedekindDomain
open MeasureTheory Filter Topology

noncomputable section

namespace R5bG

attribute [local instance] R5bC.t2Space_archMatrix' R5bC.locallyCompactSpace_archMatrix
  R5bC.locallyCompactSpace_archGL R5bC.isTopologicalGroup_archGL
  R5bC.secondCountableTopology_archGL R5bC.secondCountableTopology_piRowIsometrySubgroup₀

section Gamma

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem t2Space_archMatrix : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))

attribute [local instance] t2Space_archMatrix

private abbrev EntrySpace : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

private def matrixEntries (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) : EntrySpace F :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace F (m i j)

omit [NumberField F] in
private theorem archEntries_eq (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F g = matrixEntries F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  rfl

omit [NumberField F] in
private theorem ringEquiv_mixedSpace_eq :
    ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = fun x : InfiniteAdeleRing F =>
      ((fun v : {w : InfinitePlace F // w.IsReal} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // w.IsComplex} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) :=
  funext fun x => InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x

omit [NumberField F] in
private theorem continuous_matrixEntries : Continuous (matrixEntries F) :=
  continuous_pi fun i => continuous_pi fun j =>
    (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (continuous_id.matrix_elem i j)

omit [NumberField F] in
private theorem continuous_archEntries : Continuous (archEntries F) :=
  (continuous_matrixEntries F).comp Units.continuous_val

end Gamma
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end R5bG
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end GammaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section ZetaBlock

noncomputable section

open MeasureTheory AutomorphicForm

namespace R5bE

section ZetaB

private def contSubmodule (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {u | Continuous u}
  add_mem' hu hv := hu.add hv
  zero_mem' := continuous_const
  smul_mem' c _ hu := hu.const_smul c

private theorem mem_contSubmodule {X : Type*} [TopologicalSpace X] {u : X → ℂ} : u ∈ contSubmodule X ↔ Continuous u :=
  Iff.rfl

variable {H Kc : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group Kc] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [SecondCountableTopology Kc]
  [MeasurableSpace Kc] [BorelSpace Kc]
variable (μ : Measure Kc) [IsFiniteMeasure μ] (a : Kc →* H)

private def dconvWith (e₁ e₂ : Kc → ℂ) (ψ : H → ℂ) (y : H) : ℂ :=
  ∫ p : Kc × Kc, e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)

omit [IsTopologicalGroup Kc] [CompactSpace Kc] [SecondCountableTopology Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
private theorem continuous_dconvIntegrand {e₁ e₂ : Kc → ℂ} (he₁ : Continuous e₁) (he₂ : Continuous e₂) {ψ : H → ℂ}
    (hψ : Continuous ψ) (ha : Continuous a) (y : H) :
    Continuous fun p : Kc × Kc => e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) :=
  ((he₁.comp continuous_fst).mul (he₂.comp continuous_snd)).mul
    (hψ.comp ((((ha.comp continuous_fst).inv).mul continuous_const).mul (ha.comp continuous_snd).inv))

omit [Group Kc] [IsTopologicalGroup Kc] in
private theorem integrable_of_continuous_prod {F : Kc × Kc → ℂ} (hF : Continuous F) : Integrable F (μ.prod μ) :=
  hF.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport F) (Set.subset_univ _))

section Linear

variable {μ a}
variable {e₁ e₂ u v : Kc → ℂ} {ψ : H → ℂ}

omit [IsTopologicalGroup Kc] in
private theorem dconvWith_add_right (he₁ : Continuous e₁) (hu : Continuous u) (hv : Continuous v) (hψ : Continuous ψ)
    (ha : Continuous a) (y : H) :
    dconvWith μ a e₁ (u + v) ψ y = dconvWith μ a e₁ u ψ y + dconvWith μ a e₁ v ψ y := by
  unfold dconvWith
  rw [← integral_add (integrable_of_continuous_prod μ (continuous_dconvIntegrand a he₁ hu hψ ha y))
    (integrable_of_continuous_prod μ (continuous_dconvIntegrand a he₁ hv hψ ha y))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show e₁ p.1 * (u p.2 + v p.2) * _ = _
  ring

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc]
  [SecondCountableTopology Kc] [BorelSpace Kc] [IsFiniteMeasure μ] in
private theorem dconvWith_smul_right (c : ℂ) (y : H) : dconvWith μ a e₁ (c • u) ψ y = c * dconvWith μ a e₁ u ψ y := by
  unfold dconvWith
  rw [show (fun p : Kc × Kc => e₁ p.1 * (c • u) p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹)) =
      fun p => c * (e₁ p.1 * u p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹)) from
    funext fun p => by simp only [Pi.smul_apply, smul_eq_mul]; ring]
  exact integral_const_mul c _

omit [IsTopologicalGroup Kc] in
private theorem dconvWith_add_left (hu : Continuous u) (hv : Continuous v) (he₂ : Continuous e₂) (hψ : Continuous ψ)
    (ha : Continuous a) (y : H) :
    dconvWith μ a (u + v) e₂ ψ y = dconvWith μ a u e₂ ψ y + dconvWith μ a v e₂ ψ y := by
  unfold dconvWith
  rw [← integral_add (integrable_of_continuous_prod μ (continuous_dconvIntegrand a hu he₂ hψ ha y))
    (integrable_of_continuous_prod μ (continuous_dconvIntegrand a hv he₂ hψ ha y))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show (u p.1 + v p.1) * e₂ p.2 * _ = _
  ring

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc]
  [SecondCountableTopology Kc] [BorelSpace Kc] [IsFiniteMeasure μ] in
private theorem dconvWith_smul_left (c : ℂ) (y : H) : dconvWith μ a (c • u) e₂ ψ y = c * dconvWith μ a u e₂ ψ y := by
  unfold dconvWith
  rw [show (fun p : Kc × Kc => (c • u) p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹)) =
      fun p => c * (u p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹)) from
    funext fun p => by simp only [Pi.smul_apply, smul_eq_mul]; ring]
  exact integral_const_mul c _

end Linear
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section Substitution

variable {μ a}
variable [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
variable {Kw : Type*} [Group Kw] {j : Kw →* Kc} {ι' : Kw →* H} (haj : ∀ k, a (j k) = ι' k)
variable (e₁ e₂ : Kc → ℂ) (ψ : H → ℂ)

omit [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace Kc] [μ.IsMulLeftInvariant] in
include haj in
private theorem dconvWith_rt_right (k : Kw) (y : H) :
    dconvWith μ a e₁ (fun κ => e₂ (κ * j k)) ψ y = dconvWith μ a e₁ e₂ ψ (y * ι' k) := by
  unfold dconvWith
  rw [← integral_mul_right_eq_self
    (fun p : Kc × Kc => e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * (y * ι' k) * (a p.2)⁻¹)) ((1 : Kc), j k)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show e₁ p.1 * e₂ (p.2 * j k) * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) =
    e₁ (p.1 * 1) * e₂ (p.2 * j k) * ψ ((a (p.1 * 1))⁻¹ * (y * ι' k) * (a (p.2 * j k))⁻¹)
  rw [mul_one, map_mul, haj, mul_inv_rev,
    show (a p.1)⁻¹ * (y * ι' k) * ((ι' k)⁻¹ * (a p.2)⁻¹) = (a p.1)⁻¹ * y * (a p.2)⁻¹ by group]

omit [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace Kc] [μ.IsMulRightInvariant] in
include haj in
private theorem dconvWith_rt_left (u : Kc → ℂ) (k : Kw) (y : H) :
    dconvWith μ a (fun κ => u (κ⁻¹ * j k)) e₂ ψ y⁻¹ = dconvWith μ a (fun κ => u κ⁻¹) e₂ ψ (y * ι' k)⁻¹ := by
  unfold dconvWith
  rw [← integral_mul_left_eq_self
    (fun p : Kc × Kc => u p.1⁻¹ * e₂ p.2 * ψ ((a p.1)⁻¹ * (y * ι' k)⁻¹ * (a p.2)⁻¹)) (j k⁻¹, (1 : Kc))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show u (p.1⁻¹ * j k) * e₂ p.2 * ψ ((a p.1)⁻¹ * y⁻¹ * (a p.2)⁻¹) =
    u (j k⁻¹ * p.1)⁻¹ * e₂ (1 * p.2) * ψ ((a (j k⁻¹ * p.1))⁻¹ * (y * ι' k)⁻¹ * (a (1 * p.2))⁻¹)
  have hu : (j k⁻¹ * p.1)⁻¹ = p.1⁻¹ * j k := by
    rw [map_inv]
    group
  have harg : (a (j k⁻¹ * p.1))⁻¹ * (y * ι' k)⁻¹ * (a (1 * p.2))⁻¹ = (a p.1)⁻¹ * y⁻¹ * (a p.2)⁻¹ := by
    rw [one_mul, map_mul, map_inv, map_inv, haj]
    group
  rw [hu, harg, one_mul]

end Substitution
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section Support

variable {μ a}
variable {e : Kc → ℂ} {ψ : H → ℂ}

omit [IsTopologicalGroup Kc] [SecondCountableTopology Kc] [BorelSpace Kc] [IsFiniteMeasure μ] in
private theorem hasCompactSupport_dconvWith (ha : Continuous a) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (dconvWith μ a e e ψ) := by

  let S : Set H := (fun q : (Kc × H) × Kc => a q.1.1 * q.1.2 * a q.2) '' ((Set.univ ×ˢ tsupport ψ) ×ˢ Set.univ)
  have hS : IsCompact S :=
    ((isCompact_univ.prod hψ).prod isCompact_univ).image
      (((ha.comp (continuous_fst.comp continuous_fst)).mul (continuous_snd.comp continuous_fst)).mul
        (ha.comp continuous_snd))
  refine HasCompactSupport.intro hS fun y hy => ?_

  have hzero : ∀ p : Kc × Kc, e p.1 * e p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) = 0 := by
    intro p
    have hnot : (a p.1)⁻¹ * y * (a p.2)⁻¹ ∉ tsupport ψ := by
      intro hmem
      refine hy ⟨((p.1, (a p.1)⁻¹ * y * (a p.2)⁻¹), p.2), ⟨⟨Set.mem_univ _, hmem⟩, Set.mem_univ _⟩, ?_⟩
      show a p.1 * ((a p.1)⁻¹ * y * (a p.2)⁻¹) * a p.2 = y
      group
    rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  show (∫ p : Kc × Kc, e p.1 * e p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = 0
  simp_rw [hzero]
  exact integral_zero _ _

end Support
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end ZetaB
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end ZetaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section DUIBlock

noncomputable section

open Set Filter Function MeasureTheory Matrix
open scoped ENNReal NNReal BigOperators Classical ContDiff

namespace R5bE

section DominatedDUIEngine

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
private theorem archDUI_apply_mem_closedBall {Φw : P →L[ℝ] E} {C : ℝ} (hΦ : ‖Φw‖ ≤ C)
    {x₀ x : P} (hx : x ∈ Metric.ball x₀ 1) :
    Φw x ∈ Metric.closedBall (0 : E) (C * (‖x₀‖ + 1)) := by
  have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have h1 : ‖x‖ - ‖x₀‖ ≤ ‖x - x₀‖ := norm_sub_norm_le x x₀
    have h2 : ‖x - x₀‖ < 1 := mem_ball_iff_norm.mp hx
    linarith
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hΦ
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖Φw x‖ ≤ ‖Φw‖ * ‖x‖ := Φw.le_opNorm x
    _ ≤ C * (‖x₀‖ + 1) := mul_le_mul hΦ hxn (norm_nonneg _) hC0

set_option maxHeartbeats 4000000 in
private theorem contDiffNat_parametricIntegral_postcompCLM [IsFiniteMeasure μ]
    (Φ : α → P →L[ℝ] E) (hΦm : AEStronglyMeasurable Φ μ)
    {C : ℝ} (hC : 0 ≤ C) (hΦb : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ C) (n : ℕ) :
    ∀ (E₁ E₂ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
      [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
      (G : E → E₁), ContDiff ℝ n G →
      ∀ T : α → E₁ →L[ℝ] E₂, AEStronglyMeasurable T μ →
      ∀ D : ℝ, 0 ≤ D → (∀ᵐ w ∂μ, ‖T w‖ ≤ D) →
      ContDiff ℝ n (fun x : P => ∫ w, T w (G (Φ w x)) ∂μ) := by
  induction n with
  | zero =>
    intro E₁ E₂ _ _ _ _ _ G hG T hT D hD hTD
    have h0 : ((0 : ℕ) : WithTop ℕ∞) = 0 := by norm_cast
    rw [h0, contDiff_zero, continuous_iff_continuousAt]
    intro x₀
    obtain ⟨M₀, hM₀⟩ :=
      (isCompact_closedBall (0 : E) (C * (‖x₀‖ + 1))).exists_bound_of_continuousOn
        (hG.continuous.continuousOn (s := Metric.closedBall (0 : E) (C * (‖x₀‖ + 1))))
    refine continuousAt_of_dominated (F := fun x w => T w (G (Φ w x)))
      (bound := fun _ => D * M₀) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x =>
        (ContinuousLinearMap.id ℝ (E₁ →L[ℝ] E₂)).aestronglyMeasurable_comp₂ hT
          (hG.continuous.comp_aestronglyMeasurable (hΦm.apply_continuousLinearMap x))
    · refine Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ one_pos) fun x hx => ?_
      filter_upwards [hTD, hΦb] with w hTw hΦw
      have hmem := archDUI_apply_mem_closedBall hΦw hx
      calc ‖T w (G (Φ w x))‖ ≤ ‖T w‖ * ‖G (Φ w x)‖ := (T w).le_opNorm _
        _ ≤ D * M₀ := mul_le_mul hTw (hM₀ _ hmem) (norm_nonneg _) hD
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun w =>
        ((T w).continuous.comp (hG.continuous.comp (Φ w).continuous)).continuousAt
  | succ n IH =>
    intro E₁ E₂ _ _ _ _ _ G hG T hT D hD hTD
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
      exact_mod_cast rfl
    rw [hcast] at hG ⊢
    have hGdiff : Differentiable ℝ G :=
      hG.differentiable (by exact_mod_cast Nat.succ_ne_zero n)
    have hG' : ContDiff ℝ n (fderiv ℝ G) := hG.fderiv_right le_rfl

    set T' : α → (E →L[ℝ] E₁) →L[ℝ] (P →L[ℝ] E₂) := fun w =>
      ((ContinuousLinearMap.compL ℝ P E₁ E₂) (T w)).comp
        ((ContinuousLinearMap.compL ℝ P E E₁).flip (Φ w)) with hT'def
    have hT'apply : ∀ (w : α) (Ψ : E →L[ℝ] E₁),
        T' w Ψ = (T w).comp (Ψ.comp (Φ w)) := by
      intro w Ψ
      simp only [hT'def, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
    have hAmeas : AEStronglyMeasurable
        (fun w => (ContinuousLinearMap.compL ℝ P E₁ E₂) (T w)) μ :=
      (ContinuousLinearMap.compL ℝ P E₁ E₂).continuous.comp_aestronglyMeasurable hT
    have hBmeas : AEStronglyMeasurable
        (fun w => (ContinuousLinearMap.compL ℝ P E E₁).flip (Φ w)) μ :=
      ((ContinuousLinearMap.compL ℝ P E E₁).flip).continuous.comp_aestronglyMeasurable hΦm
    have hT'meas : AEStronglyMeasurable T' μ := by
      have hcomp : Continuous fun q : ((P →L[ℝ] E₁) →L[ℝ] (P →L[ℝ] E₂)) ×
          ((E →L[ℝ] E₁) →L[ℝ] (P →L[ℝ] E₁)) => q.1.comp q.2 :=
        isBoundedBilinearMap_comp.continuous
      exact (hcomp.comp_aestronglyMeasurable (hAmeas.prodMk hBmeas) :)
    have hT'bd : ∀ᵐ w ∂μ, ‖T' w‖ ≤ D * C := by
      filter_upwards [hTD, hΦb] with w hTw hΦw
      refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hD hC) fun Ψ => ?_
      rw [hT'apply]
      calc ‖(T w).comp (Ψ.comp (Φ w))‖
          ≤ ‖T w‖ * ‖Ψ.comp (Φ w)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖T w‖ * (‖Ψ‖ * ‖Φ w‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
        _ ≤ D * (‖Ψ‖ * C) :=
            mul_le_mul hTw (mul_le_mul_of_nonneg_left hΦw (norm_nonneg _)) (by positivity) hD
        _ = D * C * ‖Ψ‖ := by ring

    have key : ∀ x₀ : P, HasFDerivAt (fun x : P => ∫ w, T w (G (Φ w x)) ∂μ)
        (∫ w, T' w (fderiv ℝ G (Φ w x₀)) ∂μ) x₀ := by
      intro x₀
      obtain ⟨M₀, hM₀⟩ :=
        (isCompact_closedBall (0 : E) (C * (‖x₀‖ + 1))).exists_bound_of_continuousOn
          (hG.continuous.continuousOn (s := Metric.closedBall (0 : E) (C * (‖x₀‖ + 1))))
      obtain ⟨M₁, hM₁⟩ :=
        (isCompact_closedBall (0 : E) (C * (‖x₀‖ + 1))).exists_bound_of_continuousOn
          (hG'.continuous.continuousOn (s := Metric.closedBall (0 : E) (C * (‖x₀‖ + 1))))
      have hM₁0 : 0 ≤ M₁ := by
        refine le_trans (norm_nonneg (fderiv ℝ G 0)) (hM₁ 0 ?_)
        rw [Metric.mem_closedBall, dist_self]
        positivity
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun x w => T w (G (Φ w x)))
        (F' := fun x w => T' w (fderiv ℝ G (Φ w x)))
        (bound := fun _ => D * (M₁ * C)) (s := Metric.ball x₀ 1)
        (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun x =>
          (ContinuousLinearMap.id ℝ (E₁ →L[ℝ] E₂)).aestronglyMeasurable_comp₂ hT
            (hG.continuous.comp_aestronglyMeasurable (hΦm.apply_continuousLinearMap x))
      · refine (integrable_const (D * M₀)).mono'
          ((ContinuousLinearMap.id ℝ (E₁ →L[ℝ] E₂)).aestronglyMeasurable_comp₂ hT
            (hG.continuous.comp_aestronglyMeasurable (hΦm.apply_continuousLinearMap x₀))) ?_
        filter_upwards [hTD, hΦb] with w hTw hΦw
        have hmem : Φ w x₀ ∈ Metric.closedBall (0 : E) (C * (‖x₀‖ + 1)) :=
          archDUI_apply_mem_closedBall hΦw (Metric.mem_ball_self one_pos)
        calc ‖T w (G (Φ w x₀))‖ ≤ ‖T w‖ * ‖G (Φ w x₀)‖ := (T w).le_opNorm _
          _ ≤ D * M₀ := mul_le_mul hTw (hM₀ _ hmem) (norm_nonneg _) hD
      · have happly : Continuous fun q : ((E →L[ℝ] E₁) →L[ℝ] (P →L[ℝ] E₂)) × (E →L[ℝ] E₁) =>
            q.1 q.2 := isBoundedBilinearMap_apply.continuous
        exact (happly.comp_aestronglyMeasurable (hT'meas.prodMk
          (hG'.continuous.comp_aestronglyMeasurable (hΦm.apply_continuousLinearMap x₀))) :)
      · filter_upwards [hTD, hΦb] with w hTw hΦw
        intro x hx
        have hmem := archDUI_apply_mem_closedBall hΦw hx
        rw [hT'apply]
        calc ‖(T w).comp ((fderiv ℝ G (Φ w x)).comp (Φ w))‖
            ≤ ‖T w‖ * ‖(fderiv ℝ G (Φ w x)).comp (Φ w)‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖T w‖ * (‖fderiv ℝ G (Φ w x)‖ * ‖Φ w‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
                (norm_nonneg _)
          _ ≤ D * (M₁ * C) :=
              mul_le_mul hTw (mul_le_mul (hM₁ _ hmem) hΦw (norm_nonneg _) hM₁0)
                (by positivity) hD
      · exact integrable_const (D * (M₁ * C))
      · refine Filter.Eventually.of_forall fun w => ?_
        intro x _hx
        show HasFDerivAt (fun y : P => T w (G (Φ w y))) (T' w (fderiv ℝ G (Φ w x))) x
        have h1 : HasFDerivAt G (fderiv ℝ G (Φ w x)) (Φ w x) :=
          (hGdiff (Φ w x)).hasFDerivAt
        have h2 : HasFDerivAt (fun y : P => G (Φ w y))
            ((fderiv ℝ G (Φ w x)).comp (Φ w)) x := h1.comp x (Φ w).hasFDerivAt
        have h3 : HasFDerivAt (fun y : P => T w (G (Φ w y)))
            ((T w).comp ((fderiv ℝ G (Φ w x)).comp (Φ w))) x :=
          (T w).hasFDerivAt.comp x h2
        rw [hT'apply]
        exact h3
    have hdiff : Differentiable ℝ (fun x : P => ∫ w, T w (G (Φ w x)) ∂μ) :=
      fun x => (key x).differentiableAt
    have hfd : (fderiv ℝ (fun x : P => ∫ w, T w (G (Φ w x)) ∂μ))
        = fun x => ∫ w, T' w (fderiv ℝ G (Φ w x)) ∂μ := by
      funext x
      exact (key x).fderiv
    rw [contDiff_succ_iff_fderiv]
    refine ⟨hdiff, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · rw [hfd]
      exact IH (E →L[ℝ] E₁) (P →L[ℝ] E₂) (fderiv ℝ G) hG' T' hT'meas (D * C)
        (mul_nonneg hD hC) hT'bd

private theorem contDiff_parametricIntegral_clm_comp [IsFiniteMeasure μ]
    (Φ : α → P →L[ℝ] E) (hΦm : AEStronglyMeasurable Φ μ)
    {C : ℝ} (hΦb : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ C)
    {F : E → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x : P => ∫ w, F (Φ w x) ∂μ) := by
  rw [contDiff_infty]
  intro n
  have hΦb' : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ max C 0 :=
    hΦb.mono fun w h => le_trans h (le_max_left _ _)
  have h := contDiffNat_parametricIntegral_postcompCLM Φ hΦm (le_max_right C 0) hΦb' n
    ℝ ℝ F (hF.of_le (by exact_mod_cast le_top))
    (fun _ => ContinuousLinearMap.id ℝ ℝ) aestronglyMeasurable_const
    1 zero_le_one (Filter.Eventually.of_forall fun _ => ContinuousLinearMap.norm_id_le)
  simpa only [ContinuousLinearMap.id_apply] using h

end DominatedDUIEngine
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section ScalarWeighted

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

private theorem contDiff_parametricIntegral_mul [IsFiniteMeasure μ]
    (Φ : α → P →L[ℝ] E) (hΦm : AEStronglyMeasurable Φ μ)
    {C : ℝ} (hΦb : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ C)
    {G : E → ℂ} (hG : ContDiff ℝ ∞ G) {t : α → ℂ} (ht : AEStronglyMeasurable t μ)
    {D : ℝ} (hD : 0 ≤ D) (htD : ∀ᵐ w ∂μ, ‖t w‖ ≤ D) :
    ContDiff ℝ ∞ (fun x : P => ∫ w, t w * G (Φ w x) ∂μ) := by
  rw [contDiff_infty]
  intro n
  have hΦb' : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ max C 0 :=
    hΦb.mono fun w h => le_trans h (le_max_left _ _)
  let T : α → ℂ →L[ℝ] ℂ := fun w => t w • ContinuousLinearMap.id ℝ ℂ
  have hTm : AEStronglyMeasurable T μ := ht.fun_smul aestronglyMeasurable_const
  have hTD : ∀ᵐ w ∂μ, ‖T w‖ ≤ D := htD.mono fun w hw =>
    (norm_smul_le (t w) (ContinuousLinearMap.id ℝ ℂ)).trans (by
      calc ‖t w‖ * ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖t w‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ D := by rw [mul_one]; exact hw)
  have h := contDiffNat_parametricIntegral_postcompCLM Φ hΦm (le_max_right C 0) hΦb' n
    ℂ ℂ G (hG.of_le (by exact_mod_cast le_top)) T hTm D hD hTD
  have hT : ∀ w x, T w (G (Φ w x)) = t w * G (Φ w x) := fun w x => by
    simp only [T, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  simp_rw [hT] at h
  exact h

end ScalarWeighted
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end DUIBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section InstBlock

noncomputable section

open NumberField NumberField.AdelicLevel AutomorphicForm MeasureTheory Filter Topology

namespace R5bE

section Instantiate

section Stable

variable {G : Type*} [Group G] {Pl : Type*} [Fintype Pl] {K : Pl → Type*} [∀ w, Group (K w)]

private def rtStabilizer (E' : Submodule ℂ (G → ℂ)) : Submonoid G where
  carrier := {g | ∀ v ∈ E', (fun x => v (x * g)) ∈ E'}
  one_mem' v hv := by simpa only [mul_one] using hv
  mul_mem' {g} {h} hg hh v hv := by
    have h1 : (fun x => v (x * (g * h))) = fun x => (fun y => v (y * h)) (x * g) := by
      funext x
      simp only [mul_assoc]
    rw [h1]
    exact hg _ (hh v hv)

private theorem mem_rtStabilizer {E' : Submodule ℂ (G → ℂ)} {g : G} :
    g ∈ rtStabilizer E' ↔ ∀ v ∈ E', (fun x => v (x * g)) ∈ E' :=
  Iff.rfl

private theorem rt_noncommPiCoprod_mem {E' : Submodule ℂ (G → ℂ)} (ι : ∀ w, K w →* G)
    (hcomm : Pairwise fun w w' => ∀ (k : K w) (k' : K w'), Commute (ι w k) (ι w' k'))
    (hst : ∀ (w : Pl) (k : K w), ∀ v ∈ E', (fun x => v (x * ι w k)) ∈ E') (κ : ∀ w, K w) :
    ∀ v ∈ E', (fun x => v (x * MonoidHom.noncommPiCoprod ι hcomm κ)) ∈ E' := by
  have hmem : MonoidHom.noncommPiCoprod ι hcomm κ ∈ rtStabilizer E' := by
    rw [MonoidHom.noncommPiCoprod_apply]
    exact Submonoid.noncommProd_mem _ _ _ _ fun w _ => (mem_rtStabilizer.mpr (hst w (κ w)))
  exact mem_rtStabilizer.mp hmem

end Stable
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section Entries

open scoped Classical

variable (L : Type) [Field L] [NumberField L]

private abbrev Ent : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L

private def twoSided (A B : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) : Ent L →ₗ[ℝ] Ent L where
  toFun X i j := ∑ k, ∑ l, InfiniteAdeleRing.ringEquiv_mixedSpace L (A i k) * X k l *
    InfiniteAdeleRing.ringEquiv_mixedSpace L (B l j)
  map_add' X Y := by
    funext i j
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

omit [NumberField L] in
private theorem twoSided_apply (A B : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) (X : Ent L) (i j : Fin 2) :
    twoSided L A B X i j = ∑ k, ∑ l, InfiniteAdeleRing.ringEquiv_mixedSpace L (A i k) * X k l *
      InfiniteAdeleRing.ringEquiv_mixedSpace L (B l j) :=
  rfl

omit [NumberField L] in
private theorem archEntries_mul_mul (A y B : GL (Fin 2) (InfiniteAdeleRing L)) :
    archEntries L (A * y * B) =
      twoSided L (A : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) (B : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
        (archEntries L y) := by
  funext i j
  rw [twoSided_apply]
  show InfiniteAdeleRing.ringEquiv_mixedSpace L (((A * y * B : GL (Fin 2) (InfiniteAdeleRing L)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j) = _
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul, map_sum, map_mul]
  rw [Finset.sum_comm]
  rfl

private theorem continuous_twoSided_family {T : Type*} [TopologicalSpace T]
    {A B : T → GL (Fin 2) (InfiniteAdeleRing L)} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun t => LinearMap.toContinuousLinearMap
      (twoSided L (A t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
        (B t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))) := by
  refine (continuous_clm_apply (𝕜 := ℝ)).mpr fun X => ?_
  have hεA : ∀ i k, Continuous fun t => InfiniteAdeleRing.ringEquiv_mixedSpace L ((A t : Matrix _ _ _) i k) :=
    fun i k => (continuous_apply k).comp ((continuous_apply i).comp ((R5bG.continuous_archEntries L).comp hA))
  have hεB : ∀ l j, Continuous fun t => InfiniteAdeleRing.ringEquiv_mixedSpace L ((B t : Matrix _ _ _) l j) :=
    fun l j => (continuous_apply j).comp ((continuous_apply l).comp ((R5bG.continuous_archEntries L).comp hB))
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun t => ∑ k, ∑ l, InfiniteAdeleRing.ringEquiv_mixedSpace L ((A t : Matrix _ _ _) i k) * X k l *
    InfiniteAdeleRing.ringEquiv_mixedSpace L ((B t : Matrix _ _ _) l j)
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    (((hεA i k).mul continuous_const).mul (hεB l j))

end Entries
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section Main

open scoped Classical

variable (L : Type) [Field L] [NumberField L]

private theorem exists_contDiff_dconvWith [MeasurableSpace (R5bK.Kprod L)] [BorelSpace (R5bK.Kprod L)]
    [SecondCountableTopology (R5bK.Kprod L)] (μ : Measure (R5bK.Kprod L)) [IsFiniteMeasure μ]
    {e : R5bK.Kprod L → ℂ} (he : Continuous e) {ψ : GL (Fin 2) (InfiniteAdeleRing L) → ℝ}
    (hψt : IsArchTestFactor L fun g => (ψ g : ℂ)) :
    ∃ Φ : Ent L → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ y, dconvWith μ (R5bK.inclArch L) e e (fun z => (ψ z : ℂ)) y = Φ (archEntries L y) := by
  obtain ⟨⟨Φψ, hΦψ, hψΦ⟩, -⟩ := hψt
  let a := R5bK.inclArch L
  have ha : Continuous a := R5bK.continuous_inclArch (F := L)
  let Φf : R5bK.Kprod L × R5bK.Kprod L → Ent L →L[ℝ] Ent L := fun p =>
    LinearMap.toContinuousLinearMap (twoSided L ((a p.1)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L))
      ((a p.2)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)))
  have hΦf : Continuous Φf :=
    continuous_twoSided_family L ((ha.comp continuous_fst).inv) ((ha.comp continuous_snd).inv)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hΦf.continuousOn
  have ht : Continuous fun p : R5bK.Kprod L × R5bK.Kprod L => e p.1 * e p.2 :=
    (he.comp continuous_fst).mul (he.comp continuous_snd)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn ht.continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨fun X => ∫ p, (e p.1 * e p.2) * Φψ (Φf p X) ∂(μ.prod μ), ?_, fun y => ?_⟩
  · exact contDiff_parametricIntegral_mul Φf hΦf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hC p (Set.mem_univ _)) hΦψ ht.aestronglyMeasurable hB0
      (Filter.Eventually.of_forall fun p => (hB p (Set.mem_univ _)).trans (le_max_left _ _))
  · show (∫ p, e p.1 * e p.2 * (fun z => (ψ z : ℂ)) ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show e p.1 * e p.2 * (ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) : ℂ) = e p.1 * e p.2 * Φψ (Φf p (archEntries L y))
    rw [show ((ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) : ℝ) : ℂ) = Φψ (archEntries L ((a p.1)⁻¹ * y * (a p.2)⁻¹)) from
      hψΦ _, archEntries_mul_mul]
    rfl

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end Instantiate
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end InstBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

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
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section Smooth

variable (L : Type) [Field L] [NumberField L]

private theorem exists_contDiff_dconvWithC [MeasurableSpace (R5bK.Kprod L)] [BorelSpace (R5bK.Kprod L)]
    [SecondCountableTopology (R5bK.Kprod L)] (μ : Measure (R5bK.Kprod L)) [IsFiniteMeasure μ]
    {e : R5bK.Kprod L → ℂ} (he : Continuous e) {ψ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    (hψt : IsArchTestFactor L ψ) :
    ∃ Φ : Ent L → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ y, dconvWith μ (R5bK.inclArch L) e e ψ y = Φ (archEntries L y) := by
  obtain ⟨⟨Φψ, hΦψ, hψΦ⟩, -⟩ := hψt
  let a := R5bK.inclArch L
  have ha : Continuous a := R5bK.continuous_inclArch (F := L)
  let Φf : R5bK.Kprod L × R5bK.Kprod L → Ent L →L[ℝ] Ent L := fun p =>
    LinearMap.toContinuousLinearMap (twoSided L ((a p.1)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L))
      ((a p.2)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)))
  have hΦf : Continuous Φf :=
    continuous_twoSided_family L ((ha.comp continuous_fst).inv) ((ha.comp continuous_snd).inv)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hΦf.continuousOn
  have ht : Continuous fun p : R5bK.Kprod L × R5bK.Kprod L => e p.1 * e p.2 :=
    (he.comp continuous_fst).mul (he.comp continuous_snd)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn ht.continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨fun X => ∫ p, (e p.1 * e p.2) * Φψ (Φf p X) ∂(μ.prod μ), ?_, fun y => ?_⟩
  · exact contDiff_parametricIntegral_mul Φf hΦf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hC p (Set.mem_univ _)) hΦψ ht.aestronglyMeasurable hB0
      (Filter.Eventually.of_forall fun p => (hB p (Set.mem_univ _)).trans (le_max_left _ _))
  · show (∫ p, e p.1 * e p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show e p.1 * e p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) = e p.1 * e p.2 * Φψ (Φf p (archEntries L y))
    rw [hψΦ, archEntries_mul_mul]
    rfl

end Smooth
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section AVG

variable (F : Type) [Field F] [NumberField F]

private theorem avg_main
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
        ∂(μ.prod μ)) ∧
    IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) (fun y => ∫ p : (∀ w : InfinitePlace F,
          rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
        ∂(μ.prod μ)) := by
  obtain rfl : ι = R5bK.inclArch F := eq_inclArch ι hι
  haveI : SecondCountableTopology (R5bK.Kprod F) := R5bC.secondCountableTopology_piRowIsometrySubgroup₀ F

  let e : R5bK.Kprod F → ℂ := fun κ => chiProd F χ κ⁻¹
  have he : Continuous e := (continuous_chiProd χ hχ).comp continuous_inv
  have he_mul : ∀ κ κ' : R5bK.Kprod F, e (κ * κ') = e κ * e κ' := by
    intro κ κ'
    show chiProd F χ (κ * κ')⁻¹ = chiProd F χ κ⁻¹ * chiProd F χ κ'⁻¹
    rw [mul_inv_rev, map_mul, mul_comm]
  have he_inv_inv : ∀ κ : R5bK.Kprod F, e κ⁻¹⁻¹ = e κ := fun κ => by rw [inv_inv]
  have ha : Continuous (R5bK.inclArch F) := R5bK.continuous_inclArch

  have hD : (fun y => ∫ p : R5bK.Kprod F × R5bK.Kprod F,
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) *
          fa ((R5bK.inclArch F p.1)⁻¹ * y * (R5bK.inclArch F p.2)⁻¹) ∂(μ.prod μ)) =
      dconvWith μ (R5bK.inclArch F) e e fa := by
    funext y
    rfl
  rw [hD]

  have haj : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      R5bK.inclArch F (MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w k) =
        archRowIsometryInclAt₀ F w k :=
    fun w k => R5bK.inclArch_mulSingle w k
  have he_single : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      e (MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w k) =
        ((χ w k⁻¹ : ℂˣ) : ℂ) := by
    intro w k
    show chiProd F χ (Pi.mulSingle w k)⁻¹ = _
    rw [← Pi.mulSingle_inv, chiProd_mulSingle]
  refine ⟨⟨?_, hasCompactSupport_dconvWith ha hfa.2⟩, ?_, ?_⟩
  ·
    obtain ⟨Φ, hΦ, hΦeq⟩ := exists_contDiff_dconvWithC F μ he hfa
    exact ⟨Φ, hΦ, hΦeq⟩
  ·
    show (fun x => dconvWith μ (R5bK.inclArch F) e e fa x⁻¹) ∈
      ⨅ w : InfinitePlace F, ⨆ _ : Fin 1, archFactorTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w))
    simp only [iSup_const, Submodule.mem_iInf]
    intro w
    refine (mem_typeSubmodule_charRep_iff (archRowIsometryInclAt₀ F w) (χ w) _).mpr fun k x => ?_
    have h := dconvWith_rt_left (μ := μ) (a := R5bK.inclArch F)
      (j := MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w)
      (ι' := archRowIsometryInclAt₀ F w) (haj w) e fa (fun κ => e κ⁻¹) k x
    have hw : (fun κ : R5bK.Kprod F => (fun κ => e κ⁻¹)
        (κ⁻¹ * MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w k)) =
        ((χ w k : ℂˣ) : ℂ) • e := by
      funext κ
      show e (κ⁻¹ * _)⁻¹ = ((χ w k : ℂˣ) : ℂ) * e κ
      rw [mul_inv_rev, inv_inv, he_mul, ← map_inv, he_single, inv_inv, mul_comm]
    have hw' : (fun κ : R5bK.Kprod F => (fun κ => e κ⁻¹) κ⁻¹) = e := funext he_inv_inv
    rw [hw, hw', dconvWith_smul_left] at h
    exact h.symm
  ·
    show dconvWith μ (R5bK.inclArch F) e e fa ∈
      ⨅ w : InfinitePlace F, ⨆ _ : Fin 1, archFactorDualTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w))
    simp only [iSup_const, Submodule.mem_iInf]
    intro w
    refine (mem_typeSubmodule_charRep_dual_iff (archRowIsometryInclAt₀ F w) (χ w) _).mpr fun k x => ?_
    have h := dconvWith_rt_right (μ := μ) (a := R5bK.inclArch F)
      (j := MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w)
      (ι' := archRowIsometryInclAt₀ F w) (haj w) e e fa k x
    have hw : (fun κ : R5bK.Kprod F =>
        e (κ * MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w k)) =
        ((χ w k⁻¹ : ℂˣ) : ℂ) • e := by
      funext κ
      show e (κ * _) = ((χ w k⁻¹ : ℂˣ) : ℂ) * e κ
      rw [he_mul, he_single, mul_comm]
    rw [hw, dconvWith_smul_right] at h
    exact h.symm

end AVG
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end AVGBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

section SolutionBlock

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
        ∂(μ.prod μ)) ∧
    IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) (fun y => ∫ p : (∀ w : InfinitePlace F,
          rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
        ∂(μ.prod μ)) :=
  R5bE.avg_main F χ hχ μ ι hι fa hfa

end SolutionBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.R5bK"

end S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor
end P2MW
export P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor (solution)
