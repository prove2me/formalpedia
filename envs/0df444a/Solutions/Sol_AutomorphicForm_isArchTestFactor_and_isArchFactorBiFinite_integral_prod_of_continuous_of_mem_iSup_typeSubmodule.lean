-- Prove2me | solution 1 for AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a8ad9a5a-d9fc-5e7a-b8f8-4ad222a37c2c

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective
import Mathlib.Analysis.Calculus.ParametricIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule

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

end R5bK
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end AlphaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

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
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end R5bG
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end GammaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

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
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

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
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

section Support

variable {μ a}
variable {e₁ e₂ : Kc → ℂ} {ψ : H → ℂ}

omit [IsTopologicalGroup Kc] [SecondCountableTopology Kc] [BorelSpace Kc] [IsFiniteMeasure μ] in
private theorem hasCompactSupport_dconvWith (ha : Continuous a) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (dconvWith μ a e₁ e₂ ψ) := by

  let S : Set H := (fun q : (Kc × H) × Kc => a q.1.1 * q.1.2 * a q.2) '' ((Set.univ ×ˢ tsupport ψ) ×ˢ Set.univ)
  have hS : IsCompact S :=
    ((isCompact_univ.prod hψ).prod isCompact_univ).image
      (((ha.comp (continuous_fst.comp continuous_fst)).mul (continuous_snd.comp continuous_fst)).mul
        (ha.comp continuous_snd))
  refine HasCompactSupport.intro hS fun y hy => ?_

  have hzero : ∀ p : Kc × Kc, e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) = 0 := by
    intro p
    have hnot : (a p.1)⁻¹ * y * (a p.2)⁻¹ ∉ tsupport ψ := by
      intro hmem
      refine hy ⟨((p.1, (a p.1)⁻¹ * y * (a p.2)⁻¹), p.2), ⟨⟨Set.mem_univ _, hmem⟩, Set.mem_univ _⟩, ?_⟩
      show a p.1 * ((a p.1)⁻¹ * y * (a p.2)⁻¹) * a p.2 = y
      group
    rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  show (∫ p : Kc × Kc, e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = 0
  simp_rw [hzero]
  exact integral_zero _ _

end Support
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end ZetaB
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end ZetaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

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
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

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
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end DUIBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

section InstBlock

noncomputable section

open NumberField NumberField.AdelicLevel AutomorphicForm MeasureTheory Filter Topology

namespace R5bE

section Instantiate

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
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end Instantiate
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end InstBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

section SmoothBlock

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm
open scoped Classical ContDiff

namespace R5bE

section Smooth

variable (L : Type) [Field L] [NumberField L]

private theorem exists_contDiff_dconvWithC [MeasurableSpace (R5bK.Kprod L)] [BorelSpace (R5bK.Kprod L)]
    [SecondCountableTopology (R5bK.Kprod L)] (μ : Measure (R5bK.Kprod L)) [IsFiniteMeasure μ]
    {e₁ e₂ : R5bK.Kprod L → ℂ} (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    {ψ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    (hψt : IsArchTestFactor L ψ) :
    ∃ Φ : Ent L → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ y, dconvWith μ (R5bK.inclArch L) e₁ e₂ ψ y = Φ (archEntries L y) := by
  obtain ⟨⟨Φψ, hΦψ, hψΦ⟩, -⟩ := hψt
  let a := R5bK.inclArch L
  have ha : Continuous a := R5bK.continuous_inclArch (F := L)
  let Φf : R5bK.Kprod L × R5bK.Kprod L → Ent L →L[ℝ] Ent L := fun p =>
    LinearMap.toContinuousLinearMap (twoSided L ((a p.1)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L))
      ((a p.2)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)))
  have hΦf : Continuous Φf :=
    continuous_twoSided_family L ((ha.comp continuous_fst).inv) ((ha.comp continuous_snd).inv)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hΦf.continuousOn
  have ht : Continuous fun p : R5bK.Kprod L × R5bK.Kprod L => e₁ p.1 * e₂ p.2 :=
    (he₁.comp continuous_fst).mul (he₂.comp continuous_snd)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn ht.continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨fun X => ∫ p, (e₁ p.1 * e₂ p.2) * Φψ (Φf p X) ∂(μ.prod μ), ?_, fun y => ?_⟩
  · exact contDiff_parametricIntegral_mul Φf hΦf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hC p (Set.mem_univ _)) hΦψ ht.aestronglyMeasurable hB0
      (Filter.Eventually.of_forall fun p => (hB p (Set.mem_univ _)).trans (le_max_left _ _))
  · show (∫ p, e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) = e₁ p.1 * e₂ p.2 * Φψ (Φf p (archEntries L y))
    rw [hψΦ, archEntries_mul_mul]
    rfl

end Smooth
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end SmoothBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

section AVGBlock

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm
open scoped ContDiff

namespace R5bE

section InclArch

variable {F : Type} [Field F] [NumberField F]

private theorem eq_inclArch (ι : R5bK.Kprod F →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : R5bK.Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) :
    ι = R5bK.inclArch F := by
  refine MonoidHom.ext fun κ => Units.ext (Matrix.ext fun i j => funext fun w => ?_)
  have h1 := AdelicLevel.archComponent_apply (K := F) w (ι κ) i j
  have h2 := AdelicLevel.archComponent_apply (K := F) w (R5bK.inclArch F κ) i j
  rw [← h1, ← h2, hι, R5bK.archComponent_inclArch]

omit [NumberField F] in

private theorem injective_archRowIsometryInclAt₀ (w : InfinitePlace F) :
    Function.Injective (archRowIsometryInclAt₀ F w) := by
  intro a b h
  apply Subtype.ext
  have h1 : archComponent F w (archGLIncl F w (a : GL (Fin 2) w.Completion)) =
      archComponent F w (archGLIncl F w (b : GL (Fin 2) w.Completion)) :=
    congrArg (archComponent F w) h
  rwa [archComponent_archGLIncl_self, archComponent_archGLIncl_self] at h1

open scoped Classical in

private theorem continuous_of_isArchTestFactor {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchTestFactor F fa) : Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hΦeq⟩, -⟩ := hfa
  rw [show fa = fun y => Φ (archEntries F y) from funext hΦeq]
  exact hΦ.continuous.comp (R5bG.continuous_archEntries F)

end InclArch
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

section TypePush

variable {K Kc Hg : Type*} [Group K] [Group Kc] [Group Hg]

private def rightRegular (j : K →* Kc) : Representation ℂ K (Kc → ℂ) where
  toFun k :=
    { toFun := fun u κ => u (κ * j k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro u
    funext κ
    show u (κ * j 1) = u κ
    rw [map_one, mul_one]
  map_mul' k k' := by
    apply LinearMap.ext
    intro u
    funext κ
    show u (κ * j (k * k')) = u (κ * j k * j k')
    rw [map_mul, mul_assoc]

private theorem rightRegular_apply (j : K →* Kc) (k : K) (u : Kc → ℂ) :
    rightRegular j k u = fun κ => u (κ * j k) :=
  rfl

private theorem map_typeSubmodule_le_of_isRightEquivariant (j : K →* Kc) (ι' : K →* Hg)
    (Text : (Kc → ℂ) →ₗ[ℂ] (Hg → ℂ)) (hText : IsRightEquivariant ι' (rightRegular j) Text)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) :
    (typeSubmodule j ρ).map Text ≤ typeSubmodule ι' ρ := by
  show (Submodule.span ℂ _).map Text ≤ _
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, ⟨T, hT, v, rfl⟩, rfl⟩
  have hTT : IsRightEquivariant ι' ρ (Text ∘ₗ T) := by
    intro k v' x
    show Text (T (ρ k v')) x = Text (T v') (x * ι' k)
    have h1 : T (ρ k v') = rightRegular j k (T v') := funext fun κ => hT k v' κ
    rw [h1]
    exact hText k (T v') x
  exact mem_typeSubmodule_of_isRightEquivariant hTT v

private theorem apply_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule (j : K →* Kc) (ι' : K →* Hg)
    (hι' : Function.Injective ι')
    (C : Submodule ℂ (Kc → ℂ)) (hC : ∀ (k : K) (u : Kc → ℂ), u ∈ C → rightRegular j k u ∈ C)
    (S : ↥C →ₗ[ℂ] (Hg → ℂ))
    (hS : ∀ (k : K) (u : ↥C) (x : Hg), S ⟨rightRegular j k u, hC k u u.2⟩ x = S u (x * ι' k))
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ K (W i))
    (u : ↥C) (hu : (u : Kc → ℂ) ∈ ⨆ i, typeSubmodule j (ρ i)) :
    S u ∈ ⨆ i, typeSubmodule ι' (ρ i) := by
  obtain ⟨Text, hText, hTextC⟩ :=
    AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective ι' hι' (rightRegular j) C hC S hS
  have hSu : S u = Text u := by
    rw [← hTextC]
    rfl
  rw [hSu]
  have hle : (⨆ i, typeSubmodule j (ρ i)).map Text ≤ ⨆ i, typeSubmodule ι' (ρ i) := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun i => map_typeSubmodule_le_of_isRightEquivariant j ι' Text hText (ρ i)
  exact hle ⟨u, hu, rfl⟩

end TypePush
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

section BiAvg

variable (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)]

private theorem biavg_main
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (e₁ e₂ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ) (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hh : IsArchTestFactor F h) :
    IsArchTestFactor F (dconvWith μ ι e₁ e₂ h) ∧
    ((∀ w : InfinitePlace F,
        e₂ ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ.dual) →
      (∀ w : InfinitePlace F,
        (fun κ => e₁ κ⁻¹) ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ) →
      IsArchFactorBiFinite F tys (dconvWith μ ι e₁ e₂ h)) := by
  obtain rfl : ι = R5bK.inclArch F := eq_inclArch ι hι
  haveI : SecondCountableTopology (R5bK.Kprod F) := R5bC.secondCountableTopology_piRowIsometrySubgroup₀ F
  have ha : Continuous (R5bK.inclArch F) := R5bK.continuous_inclArch
  have hhc : Continuous h := continuous_of_isArchTestFactor hh

  have haj : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      R5bK.inclArch F (MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w k) =
        archRowIsometryInclAt₀ F w k :=
    fun w k => R5bK.inclArch_mulSingle w k
  refine ⟨⟨?_, hasCompactSupport_dconvWith ha hh.2⟩, fun he₂t he₁t => ⟨?_, ?_⟩⟩
  ·
    obtain ⟨Φ, hΦ, hΦeq⟩ := exists_contDiff_dconvWithC F μ he₁ he₂ hh
    exact ⟨Φ, hΦ, hΦeq⟩
  ·
    show (fun x => dconvWith μ (R5bK.inclArch F) e₁ e₂ h x⁻¹) ∈
      ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archFactorTypeSubmoduleAt F w (tys.rep w i)
    refine (Submodule.mem_iInf _).mpr fun w => ?_
    show _ ∈ ⨆ i : Fin (tys.card w), typeSubmodule (archRowIsometryInclAt₀ F w) (tys.rep w i).ρ
    let j : rowIsometrySubgroup₀ w.Completion →* R5bK.Kprod F :=
      MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w
    let C : Submodule ℂ (R5bK.Kprod F → ℂ) := contSubmodule (R5bK.Kprod F)
    have hC : ∀ (k : rowIsometrySubgroup₀ w.Completion) (u : R5bK.Kprod F → ℂ), u ∈ C → rightRegular j k u ∈ C :=
      fun k u hu => mem_contSubmodule.mpr ((mem_contSubmodule.mp hu).comp (continuous_id.mul continuous_const))
    let S : ↥C →ₗ[ℂ] (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
      { toFun := fun u x => dconvWith μ (R5bK.inclArch F) (fun κ => (u : R5bK.Kprod F → ℂ) κ⁻¹) e₂ h x⁻¹
        map_add' := fun u v => by
          funext x
          show dconvWith μ (R5bK.inclArch F) (fun κ => ((u : R5bK.Kprod F → ℂ) + (v : R5bK.Kprod F → ℂ)) κ⁻¹)
              e₂ h x⁻¹ = _
          rw [show (fun κ => ((u : R5bK.Kprod F → ℂ) + (v : R5bK.Kprod F → ℂ)) κ⁻¹) =
              (fun κ => (u : R5bK.Kprod F → ℂ) κ⁻¹) + fun κ => (v : R5bK.Kprod F → ℂ) κ⁻¹ from rfl]
          exact dconvWith_add_left ((mem_contSubmodule.mp u.2).comp continuous_inv)
            ((mem_contSubmodule.mp v.2).comp continuous_inv) he₂ hhc ha x⁻¹
        map_smul' := fun c u => by
          funext x
          show dconvWith μ (R5bK.inclArch F) (fun κ => (c • (u : R5bK.Kprod F → ℂ)) κ⁻¹) e₂ h x⁻¹ = _
          rw [show (fun κ => (c • (u : R5bK.Kprod F → ℂ)) κ⁻¹) = c • fun κ => (u : R5bK.Kprod F → ℂ) κ⁻¹ from rfl]
          exact dconvWith_smul_left c x⁻¹ }
    have hS : ∀ (k : rowIsometrySubgroup₀ w.Completion) (u : ↥C) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        S ⟨rightRegular j k u, hC k u u.2⟩ x = S u (x * archRowIsometryInclAt₀ F w k) := by
      intro k u x
      show dconvWith μ (R5bK.inclArch F) (fun κ => (u : R5bK.Kprod F → ℂ) (κ⁻¹ * j k)) e₂ h x⁻¹ =
        dconvWith μ (R5bK.inclArch F) (fun κ => (u : R5bK.Kprod F → ℂ) κ⁻¹) e₂ h (x * archRowIsometryInclAt₀ F w k)⁻¹
      exact dconvWith_rt_left (haj w) e₂ h (u : R5bK.Kprod F → ℂ) k x
    have he₁' : Continuous fun κ : R5bK.Kprod F => e₁ κ⁻¹ := he₁.comp continuous_inv
    have hmem := apply_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule j (archRowIsometryInclAt₀ F w)
      (injective_archRowIsometryInclAt₀ w) C hC S hS (fun i : Fin (tys.card w) => (tys.rep w i).ρ)
      ⟨fun κ => e₁ κ⁻¹, mem_contSubmodule.mpr he₁'⟩ (he₁t w)
    have hSe : S ⟨fun κ => e₁ κ⁻¹, mem_contSubmodule.mpr he₁'⟩ =
        fun x => dconvWith μ (R5bK.inclArch F) e₁ e₂ h x⁻¹ := by
      funext x
      show dconvWith μ (R5bK.inclArch F) (fun κ => (fun κ => e₁ κ⁻¹) κ⁻¹) e₂ h x⁻¹ = _
      simp only [inv_inv]
    rw [hSe] at hmem
    exact hmem
  ·
    show dconvWith μ (R5bK.inclArch F) e₁ e₂ h ∈
      ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archFactorDualTypeSubmoduleAt F w (tys.rep w i)
    refine (Submodule.mem_iInf _).mpr fun w => ?_
    show _ ∈ ⨆ i : Fin (tys.card w), typeSubmodule (archRowIsometryInclAt₀ F w) (tys.rep w i).ρ.dual
    let j : rowIsometrySubgroup₀ w.Completion →* R5bK.Kprod F :=
      MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w
    let C : Submodule ℂ (R5bK.Kprod F → ℂ) := contSubmodule (R5bK.Kprod F)
    have hC : ∀ (k : rowIsometrySubgroup₀ w.Completion) (u : R5bK.Kprod F → ℂ), u ∈ C → rightRegular j k u ∈ C :=
      fun k u hu => mem_contSubmodule.mpr ((mem_contSubmodule.mp hu).comp (continuous_id.mul continuous_const))
    let S : ↥C →ₗ[ℂ] (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
      { toFun := fun u => dconvWith μ (R5bK.inclArch F) e₁ (u : R5bK.Kprod F → ℂ) h
        map_add' := fun u v => by
          funext x
          exact dconvWith_add_right he₁ (mem_contSubmodule.mp u.2) (mem_contSubmodule.mp v.2) hhc ha x
        map_smul' := fun c u => by
          funext x
          exact dconvWith_smul_right c x }
    have hS : ∀ (k : rowIsometrySubgroup₀ w.Completion) (u : ↥C) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        S ⟨rightRegular j k u, hC k u u.2⟩ x = S u (x * archRowIsometryInclAt₀ F w k) := by
      intro k u x
      show dconvWith μ (R5bK.inclArch F) e₁ (fun κ => (u : R5bK.Kprod F → ℂ) (κ * j k)) h x =
        dconvWith μ (R5bK.inclArch F) e₁ (u : R5bK.Kprod F → ℂ) h (x * archRowIsometryInclAt₀ F w k)
      exact dconvWith_rt_right (haj w) e₁ (u : R5bK.Kprod F → ℂ) h k x
    exact apply_mem_iSup_typeSubmodule_of_mem_iSup_typeSubmodule j (archRowIsometryInclAt₀ F w)
      (injective_archRowIsometryInclAt₀ w) C hC S hS (fun i : Fin (tys.card w) => (tys.rep w i).ρ.dual)
      ⟨e₂, mem_contSubmodule.mpr he₂⟩ (he₂t w)

end BiAvg
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end R5bE
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end AVGBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

section SolutionBlock

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (e₁ e₂ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ) (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hh : IsArchTestFactor F h) :
    IsArchTestFactor F (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        e₁ p.1 * e₂ p.2 * h ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ)) ∧
    ((∀ w : InfinitePlace F,
        e₂ ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ.dual) →
      (∀ w : InfinitePlace F,
        (fun κ => e₁ κ⁻¹) ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ) →
      IsArchFactorBiFinite F tys (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        e₁ p.1 * e₂ p.2 * h ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ))) :=
  R5bE.biavg_main F μ ι hι tys e₁ e₂ he₁ he₂ h hh

end SolutionBlock
p2m_reactivate "P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.R5bK"

end S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
end P2MW
export P2MW.S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule (solution)
