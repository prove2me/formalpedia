-- Prove2me | solution 1 for AutomorphicForm.exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fa019503-8c53-59bc-a63f-faec0400fc76

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen
import Theorems.Thm_AutomorphicForm_exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory IsDedekindDomain NumberField.AdelicLevel

open scoped Classical

noncomputable section

namespace R4PFprime

theorem contDiff_of_contDiffOn_of_eqOn_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {s k : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (hk : IsClosed k) (hks : k ⊆ s)
    (hf0 : ∀ x, x ∉ k → f x = 0) : ContDiff ℝ (⊤ : ℕ∞) f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact hf.contDiffAt (hs.mem_nhds hx)
  · have hxk : x ∉ k := fun h => hx (hks h)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (hk.isOpen_compl.mem_nhds hxk) (fun y hy => hf0 y hy)

section Bridge

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def entriesEquiv :
    (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) ≃L[ℝ] Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

theorem contDiff_comp_of_iff {n : WithTop ℕ∞} {F : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) → ℂ} :
    ContDiff ℝ n (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => F (Matrix.of E)) ↔ ContDiff ℝ n F :=
  (entriesEquiv K).contDiff_comp_iff

end Bridge

section Weight

variable (K : Type) [Field K] [NumberField K]

theorem contDiff_norm_det_sq :
    ContDiff ℝ (⊤ : ℕ∞) (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
      (mixedEmbedding.norm (Matrix.det (Matrix.of E))) ^ 2) := by
  have hform : (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
        (mixedEmbedding.norm (Matrix.det (Matrix.of E))) ^ 2) =
      fun E => ∏ w : InfinitePlace K,
        ((mixedEmbedding.normAtPlace w (Matrix.det (Matrix.of E))) ^ 2) ^ w.mult := by
    funext E
    rw [mixedEmbedding.norm_apply, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hform]
  refine contDiff_prod (fun w _ => ContDiff.pow ?_ _)
  by_cases hw : w.IsReal
  · simp only [mixedEmbedding.normAtPlace_apply_of_isReal hw, Matrix.det_fin_two, Matrix.of_apply, Prod.fst_sub,
      Prod.fst_mul, Pi.sub_apply, Pi.mul_apply]
    exact (show ContDiff ℝ (⊤ : ℕ∞) (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
      (E 0 0).1 ⟨w, hw⟩ * (E 1 1).1 ⟨w, hw⟩ - (E 0 1).1 ⟨w, hw⟩ * (E 1 0).1 ⟨w, hw⟩) by fun_prop).norm_sq (𝕜 := ℝ)
  · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    simp only [mixedEmbedding.normAtPlace_apply_of_isComplex hw', Matrix.det_fin_two, Matrix.of_apply,
      Prod.snd_sub, Prod.snd_mul, Pi.sub_apply, Pi.mul_apply]
    exact (show ContDiff ℝ (⊤ : ℕ∞) (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
      (E 0 0).2 ⟨w, hw'⟩ * (E 1 1).2 ⟨w, hw'⟩ - (E 0 1).2 ⟨w, hw'⟩ * (E 1 0).2 ⟨w, hw'⟩) by fun_prop).norm_sq (𝕜 := ℂ)

theorem norm_det_ne_zero_of_mem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    mixedEmbedding.norm (Matrix.det (Matrix.of E)) ≠ 0 :=
  ((hE : IsUnit (Matrix.det (Matrix.of E))).map
    (mixedEmbedding.norm : mixedEmbedding.mixedSpace K →*₀ ℝ)).ne_zero

theorem norm_det_inv_pow_mul_pow_of_mem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    (mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 * (mixedEmbedding.norm (Matrix.det (Matrix.of E))) ^ 2
      = 1 := by
  rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (norm_det_ne_zero_of_mem K hE))]

end Weight

section InversionAlgebra

variable (K : Type) [Field K]

theorem mem_setOf_isUnit_det_inverse {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    Matrix.of.symm (Ring.inverse (Matrix.of E)) ∈ {E | IsUnit (Matrix.det (Matrix.of E))} := by
  have hu : IsUnit (Matrix.of E) := (Matrix.isUnit_iff_isUnit_det _).mpr hE
  show IsUnit (Matrix.det (Matrix.of (Matrix.of.symm (Ring.inverse (Matrix.of E)))))
  rw [Equiv.apply_symm_apply, ← Matrix.isUnit_iff_isUnit_det, ← hu.unit_spec, Ring.inverse_unit]
  exact Units.isUnit _

theorem inverse_inverse_of_mem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    Matrix.of.symm (Ring.inverse (Matrix.of (Matrix.of.symm (Ring.inverse (Matrix.of E))))) = E := by
  have hu : IsUnit (Matrix.of E) := (Matrix.isUnit_iff_isUnit_det _).mpr hE
  rw [Equiv.apply_symm_apply, ← hu.unit_spec, Ring.inverse_unit, Ring.inverse_unit, inv_inv, hu.unit_spec]
  exact Equiv.symm_apply_apply _ _

theorem inverse_eq_zero_of_notMem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∉ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    Matrix.of.symm (Ring.inverse (Matrix.of E)) = 0 := by
  have hu : ¬ IsUnit (Matrix.of E) := fun h => hE ((Matrix.isUnit_iff_isUnit_det _).mp h)
  rw [Ring.inverse_non_unit _ hu]
  rfl

end InversionAlgebra

section Inversion

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem isOpen_setOf_isUnit_det :
    IsOpen {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K | IsUnit (Matrix.det (Matrix.of E))} := by
  have hdet : Continuous (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => Matrix.det (Matrix.of E)) :=
    Continuous.matrix_det
      (continuous_id : Continuous (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => Matrix.of E))
  exact Units.isOpen.preimage hdet

theorem zero_notMem_setOf_isUnit_det :
    (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) ∉ {E | IsUnit (Matrix.det (Matrix.of E))} := by
  intro h
  have h1 := norm_det_ne_zero_of_mem K h
  apply h1
  have h0 : Matrix.of (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) = 0 := rfl
  rw [h0, Matrix.det_zero, map_zero]

theorem contDiffAt_comp_inverse_of_mem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
      Matrix.of.symm (Ring.inverse (Matrix.of E))) E := by
  have hu : IsUnit (Matrix.of E) := (Matrix.isUnit_iff_isUnit_det _).mpr hE
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Ring.inverse : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) →
      Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) (Matrix.of E) := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := (⊤ : ℕ∞)) hu.unit
    rwa [hu.unit_spec] at this
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) =>
      (entriesEquiv K).symm (Ring.inverse A)) (Matrix.of E) :=
    ((entriesEquiv K).symm.contDiff.contDiffAt).comp _ h1
  exact h2.comp E (entriesEquiv K).contDiff.contDiffAt

theorem continuous_comp_inverse {Ψ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ}
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (hΨS : tsupport Ψ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    Continuous (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
        Ψ (Matrix.of.symm (Ring.inverse (Matrix.of E)))) ∧
      HasCompactSupport (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
        Ψ (Matrix.of.symm (Ring.inverse (Matrix.of E)))) ∧
      tsupport (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => Ψ (Matrix.of.symm (Ring.inverse (Matrix.of E))))
        ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := by
  set ι : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :=
    fun E => Matrix.of.symm (Ring.inverse (Matrix.of E)) with hι
  have hιS : ContinuousOn ι {E | IsUnit (Matrix.det (Matrix.of E))} :=
    fun E hE => (contDiffAt_comp_inverse_of_mem K hE).continuousAt.continuousWithinAt
  have hK : IsCompact (ι '' tsupport Ψ) := hΨc.image_of_continuousOn (hιS.mono hΨS)
  have hKS : ι '' tsupport Ψ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := by
    rintro _ ⟨F, hF, rfl⟩
    exact mem_setOf_isUnit_det_inverse K (hΨS hF)
  have hsupp : Function.support (fun E => Ψ (ι E)) ⊆ ι '' tsupport Ψ := by
    intro E hE
    have hne : Ψ (ι E) ≠ 0 := hE
    have hES : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))} := by
      by_contra hES
      apply hne
      rw [hι]
      simp only
      rw [inverse_eq_zero_of_notMem K hES]
      exact image_eq_zero_of_notMem_tsupport (fun h0 => zero_notMem_setOf_isUnit_det K (hΨS h0))
    refine ⟨ι E, subset_tsupport _ hne, ?_⟩
    exact inverse_inverse_of_mem K hES
  have hzero : ∀ E, E ∉ ι '' tsupport Ψ → Ψ (ι E) = 0 := fun E hE => by
    by_contra h
    exact hE (hsupp h)
  refine ⟨?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro E
    by_cases hE : E ∈ {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K | IsUnit (Matrix.det (Matrix.of E))}
    · exact hΨ.continuousAt.comp (contDiffAt_comp_inverse_of_mem K hE).continuousAt
    · have hEK : E ∉ ι '' tsupport Ψ := fun h => hE (hKS h)
      refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      exact Filter.eventuallyEq_of_mem (hK.isClosed.isOpen_compl.mem_nhds hEK) fun y hy => (hzero y hy).symm
  · exact HasCompactSupport.of_support_subset_isCompact hK hsupp
  · exact (closure_minimal hsupp hK.isClosed).trans hKS

end Inversion

section field

variable (K : Type) [Field K]

theorem of_archEntries_eq (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  Matrix.ext fun _ _ => rfl

theorem of_archEntries_mul (g h : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K (g * h)) = Matrix.of (archEntries K g) * Matrix.of (archEntries K h) := by
  simp only [of_archEntries_eq, Units.val_mul, map_mul]

theorem archEntries_mul (g h : GL (Fin 2) (InfiniteAdeleRing K)) :
    archEntries K (g * h) = Matrix.of.symm (Matrix.of (archEntries K g) * Matrix.of (archEntries K h)) := by
  rw [← of_archEntries_mul, Equiv.symm_apply_apply]

theorem of_archEntries_inv (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g⁻¹) = (Matrix.of (archEntries K g))⁻¹ := by
  rw [of_archEntries_eq, of_archEntries_eq]
  symm
  apply Matrix.inv_eq_right_inv
  rw [← map_mul, Units.mul_inv, map_one]

theorem isUnit_det_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    IsUnit (Matrix.det (Matrix.of (archEntries K g))) := by
  rw [of_archEntries_eq, ← RingHom.map_det]
  exact (Matrix.isUnits_det_units g).map _

theorem det_of_archEntries_conj (a g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.det (Matrix.of (archEntries K (a * g * a⁻¹))) = Matrix.det (Matrix.of (archEntries K g)) := by
  rw [of_archEntries_mul, of_archEntries_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← of_archEntries_mul, inv_mul_cancel, of_archEntries_eq, Units.val_one, map_one,
    Matrix.det_one, one_mul]

theorem continuous_archEntries : Continuous (archEntries K) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (AdelicBox.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)

theorem exists_archEntries_eq {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : IsUnit (Matrix.det (Matrix.of E))) : ∃ g : GL (Fin 2) (InfiniteAdeleRing K), archEntries K g = E := by
  have hm : IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.mapMatrix (Matrix.of E)) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det]
    exact hE.map _
  refine ⟨hm.unit, ?_⟩
  funext i j
  show InfiniteAdeleRing.ringEquiv_mixedSpace K ((hm.unit : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j)
    = E i j
  rw [IsUnit.unit_spec]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply (E i j)

theorem continuous_entriesMap :
    Continuous fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
      (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j) : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :=
  continuous_pi fun i => continuous_pi fun j =>
    (AdelicBox.continuous_ringEquiv_mixedSpace K).comp (continuous_id.matrix_elem i j)

end field

section numberField

variable (K : Type) [Field K] [NumberField K]

theorem continuousAt_ringInverse {x : InfiniteAdeleRing K} (hx : IsUnit x) :
    ContinuousAt (Ring.inverse : InfiniteAdeleRing K → InfiniteAdeleRing K) x := by
  change ContinuousAt (Ring.inverse : (∀ v : InfinitePlace K, v.Completion) → ∀ v : InfinitePlace K, v.Completion) x
  have hx' : IsUnit (x : ∀ v : InfinitePlace K, v.Completion) := hx
  have hne : ∀ v : InfinitePlace K, (x : ∀ v : InfinitePlace K, v.Completion) v ≠ 0 :=
    fun v => (Pi.isUnit_iff.mp hx' v).ne_zero
  have key : ∀ y : ∀ v : InfinitePlace K, v.Completion, (∀ v, y v ≠ 0) → Ring.inverse y = fun v => (y v)⁻¹ := by
    intro y hy
    have hyu : IsUnit y := Pi.isUnit_iff.mpr fun v => (hy v).isUnit
    have h1 : Ring.inverse y = ((hyu.unit⁻¹ : (∀ v : InfinitePlace K, v.Completion)ˣ) :
        ∀ v : InfinitePlace K, v.Completion) := by
      conv_lhs => rw [← hyu.unit_spec]
      exact Ring.inverse_unit hyu.unit
    rw [h1]
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hyu.unit_spec]
    funext v
    exact mul_inv_cancel₀ (hy v)
  have hW : IsOpen {y : ∀ v : InfinitePlace K, v.Completion | ∀ v, y v ≠ 0} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_ne.preimage (continuous_apply v)
  have hcont : ContinuousAt (fun y : ∀ v : InfinitePlace K, v.Completion => fun v => (y v)⁻¹) x :=
    continuousAt_pi.mpr fun v => (continuousAt_inv₀ (hne v)).comp (continuous_apply v).continuousAt
  exact hcont.congr (Filter.eventuallyEq_of_mem (hW.mem_nhds hne) fun y hy => (key y hy).symm)

theorem isCompact_preimage_entriesMap {C : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)} (hC : IsCompact C) :
    IsCompact {m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) |
      (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)) ∈ C} := by
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hC.isBounded
  haveI : ∀ v : InfinitePlace K, ProperSpace v.Completion := fun v => AdelicBox.properSpace_completion K v
  have hB : IsCompact {m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) |
      ∀ (i j : Fin 2) (v : InfinitePlace K), ‖m i j v‖ ≤ r} := by
    have heq : {m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) |
          ∀ (i j : Fin 2) (v : InfinitePlace K), ‖m i j v‖ ≤ r}
        = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
            Set.pi Set.univ fun v : InfinitePlace K => Metric.closedBall (0 : v.Completion) r := by
      ext m
      exact ⟨fun h i _ j _ v _ => mem_closedBall_zero_iff.mpr (h i j v),
        fun h i j v => mem_closedBall_zero_iff.mp (h i (Set.mem_univ i) j (Set.mem_univ j) v (Set.mem_univ v))⟩
    rw [heq]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun v =>
      isCompact_closedBall (0 : v.Completion) r
  refine hB.of_isClosed_subset (hC.isClosed.preimage (continuous_entriesMap K)) ?_
  intro m hm i j v
  have h1 : ‖InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)‖ ≤ r := by
    refine le_trans ?_ (hr _ hm)
    exact (norm_le_pi_norm (fun j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)) j).trans
      (norm_le_pi_norm (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)) i)
  by_cases hv : v.IsReal
  · exact (AdelicBox.norm_apply_le_of_isReal K (m i j) hv).trans h1
  · exact (AdelicBox.norm_apply_le_of_isComplex K (m i j) (InfinitePlace.not_isReal_iff_isComplex.mp hv)).trans h1

theorem isCompact_setOf_archEntries_mem {C : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)}
    (hCc : IsCompact C) (hCS : C ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    IsCompact {g : GL (Fin 2) (InfiniteAdeleRing K) | archEntries K g ∈ C} := by
  have hC : IsCompact {m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) |
      (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)) ∈ C} :=
    isCompact_preimage_entriesMap K hCc
  have hunit : ∀ m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K),
      (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)) ∈ C → IsUnit m := by
    intro m hm
    have h1 : IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix m).det := hCS hm
    rw [← RingHom.map_det] at h1
    have h2 := h1.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
    have h3 : (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom m.det) = m.det :=
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply m.det
    rw [h3] at h2
    exact (Matrix.isUnit_iff_isUnit_det m).mpr h2
  have hinv : ContinuousOn (fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) => m⁻¹)
      {m | (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)) ∈ C} := by
    intro m hm
    have hdet : IsUnit m.det := (Matrix.isUnit_iff_isUnit_det m).mp (hunit m hm)
    exact (continuousAt_matrix_inv m (continuousAt_ringInverse K hdet)).continuousWithinAt
  rw [Units.isInducing_embedProduct.isCompact_iff]
  have himg := hC.image_of_continuousOn (continuous_id.continuousOn.prodMk
    (MulOpposite.continuous_op.comp_continuousOn hinv))
  convert himg using 1
  ext p
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)), hg, ?_⟩
    simp only [Units.embedProduct_apply, id, Function.comp_apply, Matrix.coe_units_inv]
  · rintro ⟨m, hm, rfl⟩
    refine ⟨(hunit m hm).unit, ?_, ?_⟩
    · show (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K
        (((hunit m hm).unit : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j)) ∈ C
      rw [IsUnit.unit_spec]
      exact hm
    · simp only [Units.embedProduct_apply, id, Function.comp_apply, Matrix.coe_units_inv, IsUnit.unit_spec]

theorem hasCompactSupport_comp_archEntries {Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ}
    (hΦc : HasCompactSupport Φ) (hΦS : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    HasCompactSupport (fun g : GL (Fin 2) (InfiniteAdeleRing K) => Φ (archEntries K g)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_setOf_archEntries_mem K hΦc hΦS) ?_
  intro g hg
  exact subset_tsupport Φ hg

theorem exists_contDiff_tsupport_subset_of_isArchTestFactor {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (hfa : IsArchTestFactor K fa) :
    ∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} ∧ ∀ g, fa g = Φ (archEntries K g) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hfac⟩ := hfa
  have hK : IsCompact (archEntries K '' tsupport fa) := IsCompact.image hfac (continuous_archEntries K)
  have hKS : ∀ E ∈ archEntries K '' tsupport fa, IsUnit (Matrix.det (Matrix.of E)) := by
    rintro _ ⟨g, -, rfl⟩
    exact isUnit_det_of_archEntries K g
  have hvan : ∀ E, IsUnit (Matrix.det (Matrix.of E)) → E ∉ archEntries K '' tsupport fa → Φ E = 0 := by
    intro E hE hEK
    obtain ⟨g, rfl⟩ := exists_archEntries_eq K hE
    have hg : g ∉ tsupport fa := fun h => hEK ⟨g, h, rfl⟩
    rw [← hfaΦ g]
    exact image_eq_zero_of_notMem_tsupport hg
  have hsupp : Function.support ({E | IsUnit (Matrix.det (Matrix.of E))}.indicator Φ) ⊆
      archEntries K '' tsupport fa := by
    intro E hE
    by_contra hEK
    apply hE
    by_cases hES : IsUnit (Matrix.det (Matrix.of E))
    · rw [Set.indicator_of_mem (show E ∈ {E | IsUnit (Matrix.det (Matrix.of E))} from hES)]
      exact hvan E hES hEK
    · exact Set.indicator_of_notMem (show E ∉ {E | IsUnit (Matrix.det (Matrix.of E))} from hES) Φ
  have hts : tsupport ({E | IsUnit (Matrix.det (Matrix.of E))}.indicator Φ) ⊆ archEntries K '' tsupport fa :=
    closure_minimal hsupp hK.isClosed
  refine ⟨{E | IsUnit (Matrix.det (Matrix.of E))}.indicator Φ, ?_, ?_, fun E hE => hKS E (hts hE), fun g => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun E => ?_
    by_cases hES : IsUnit (Matrix.det (Matrix.of E))
    · refine hΦ.contDiffAt.congr_of_eventuallyEq ?_
      refine Filter.eventuallyEq_of_mem ((isOpen_setOf_isUnit_det K).mem_nhds hES) fun y hy => ?_
      exact Set.indicator_of_mem hy Φ
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      have hEK : E ∉ archEntries K '' tsupport fa := fun h => hES (hKS E h)
      refine Filter.eventuallyEq_of_mem (hK.isClosed.isOpen_compl.mem_nhds hEK) fun y hy => ?_
      by_contra hne
      exact hy (hsupp hne)
  · exact hK.of_isClosed_subset (isClosed_tsupport _) hts
  · rw [Set.indicator_of_mem (show archEntries K g ∈ {E | IsUnit (Matrix.det (Matrix.of E))} from
      isUnit_det_of_archEntries K g)]
    exact hfaΦ g

end numberField

section FinLevel

variable (K : Type) [Field K] [NumberField K]

def finPrincipalLevel (N : Ideal (𝓞 K)) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
  finiteLevelOne (𝓞 K) K N ⊓
    (finiteLevelOne (𝓞 K) K N).map (MulAut.conj (glFin (𝓞 K) K (weyl (𝓞 K) K))).toMonoidHom

theorem mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (w x : G) :
    x ∈ H.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * x * w ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem mem_principalLevel_inf_iff (N : Ideal (𝓞 K)) (u : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ↔
      glArch (𝓞 K) K u = 1 ∧ glFin (𝓞 K) K u ∈ finPrincipalLevel K N := by
  rw [Subgroup.mem_inf, mem_finiteAdelicGL2Subgroup_iff, mem_principalLevel_iff, finPrincipalLevel,
    Subgroup.mem_inf, mem_map_conj_iff, mem_map_conj_iff, mem_levelOne_iff, mem_levelOne_iff, map_mul, map_mul,
    map_inv]
  tauto

theorem isCompact_finPrincipalLevel (N : Ideal (𝓞 K)) :
    IsCompact (finPrincipalLevel K N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  have h1 : IsCompact (finiteLevelOne (𝓞 K) K N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :=
    isCompact_finiteLevelOne (𝓞 K) K N
  have hc : Continuous fun x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      glFin (𝓞 K) K (weyl (𝓞 K) K) * x * (glFin (𝓞 K) K (weyl (𝓞 K) K))⁻¹ := by fun_prop
  have h2 : IsClosed (((finiteLevelOne (𝓞 K) K N).map
      (MulAut.conj (glFin (𝓞 K) K (weyl (𝓞 K) K))).toMonoidHom : Subgroup _) :
      Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
    rw [Subgroup.coe_map]
    have heq : ((MulAut.conj (glFin (𝓞 K) K (weyl (𝓞 K) K))).toMonoidHom :
        GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ''
        (finiteLevelOne (𝓞 K) K N : Set _) =
        (fun x => glFin (𝓞 K) K (weyl (𝓞 K) K) * x * (glFin (𝓞 K) K (weyl (𝓞 K) K))⁻¹) ''
          (finiteLevelOne (𝓞 K) K N : Set _) := Set.image_congr fun x _ => rfl
    rw [heq]
    exact (h1.image hc).isClosed
  exact h1.inter_right h2

theorem isOpen_finPrincipalLevel {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) :
    IsOpen (finPrincipalLevel K N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  have h1 : IsOpen (finiteLevelOne (𝓞 K) K N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :=
    isOpen_finiteLevelOne (𝓞 K) K hN
  have hom : IsOpenMap (fun x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      glFin (𝓞 K) K (weyl (𝓞 K) K) * x * (glFin (𝓞 K) K (weyl (𝓞 K) K))⁻¹) :=
    (isOpenMap_mul_right _).comp (isOpenMap_mul_left _)
  have h2 : IsOpen (((finiteLevelOne (𝓞 K) K N).map
      (MulAut.conj (glFin (𝓞 K) K (weyl (𝓞 K) K))).toMonoidHom : Subgroup _) :
      Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
    rw [Subgroup.coe_map]
    have heq : ((MulAut.conj (glFin (𝓞 K) K (weyl (𝓞 K) K))).toMonoidHom :
        GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ''
        (finiteLevelOne (𝓞 K) K N : Set _) =
        (fun x => glFin (𝓞 K) K (weyl (𝓞 K) K) * x * (glFin (𝓞 K) K (weyl (𝓞 K) K))⁻¹) ''
          (finiteLevelOne (𝓞 K) K N : Set _) := Set.image_congr fun x _ => rfl
    rw [heq]
    exact hom _ h1
  exact h1.inter h2

private abbrev _root_.R4PFprime.finLift (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : GL (Fin 2) (AdeleRing (𝓞 K) K) :=
  AutomorphicForm.GaussTwist.finLift g

p2m_export "R4PFprime" "finLift"
theorem glArch_finLift (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : glArch (𝓞 K) K (finLift K g) = 1 := by
  ext i j
  rw [Units.val_one]
  rfl

theorem glFin_finLift (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : glFin (𝓞 K) K (finLift K g) = g := by
  ext i j
  rfl

abbrev archLift (a : GL (Fin 2) (InfiniteAdeleRing K)) : GL (Fin 2) (AdeleRing (𝓞 K) K) := adelicArchGLIncl K a

theorem eq_of_glArch_eq_of_glFin_eq {g g' : GL (Fin 2) (AdeleRing (𝓞 K) K)} (h1 : glArch (𝓞 K) K g = glArch (𝓞 K) K g')
    (h2 : glFin (𝓞 K) K g = glFin (𝓞 K) K g') : g = g' := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have h : (glArch (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
        (glArch (𝓞 K) K g' : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := Units.ext_iff.mp h1
    have hij := congrArg (fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) => m i j) h
    simp only [glArch_apply] at hij
    exact hij
  · have h : (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) =
        (glFin (𝓞 K) K g' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := Units.ext_iff.mp h2
    have hij := congrArg (fun m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) => m i j) h
    simp only [glFin_apply] at hij
    exact hij

theorem eq_archLift_mul_finLift (z : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    z = archLift K (glArch (𝓞 K) K z) * finLift K (glFin (𝓞 K) K z) := by
  refine eq_of_glArch_eq_of_glFin_eq K ?_ ?_
  · rw [map_mul, glArch_adelicArchGLIncl, glArch_finLift, mul_one]
  · rw [map_mul, glFin_adelicArchGLIncl, glFin_finLift, one_mul]

theorem continuous_finLift : Continuous (finLift K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

theorem continuous_archLift : Continuous (archLift K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · have h : (fun a : GL (Fin 2) (InfiniteAdeleRing K) =>
        (((archLift K a)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) =
        fun a => ((archLift K a⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
      funext a
      exact congrArg Units.val (map_inv (adelicArchGLIncl K) a).symm
    show Continuous fun a : GL (Fin 2) (InfiniteAdeleRing K) =>
      (((archLift K a)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    rw [h]
    refine continuous_matrix fun i j => ?_
    exact (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const

theorem isCompact_setOf_glArch_mem_and_glFin_mem {C : Set (GL (Fin 2) (InfiniteAdeleRing K))} (hC : IsCompact C)
    {D : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))} (hD : IsCompact D) :
    IsCompact {z : GL (Fin 2) (AdeleRing (𝓞 K) K) | glArch (𝓞 K) K z ∈ C ∧ glFin (𝓞 K) K z ∈ D} := by
  have himg : {z : GL (Fin 2) (AdeleRing (𝓞 K) K) | glArch (𝓞 K) K z ∈ C ∧ glFin (𝓞 K) K z ∈ D} =
      (fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        archLift K p.1 * finLift K p.2) '' (C ×ˢ D) := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(glArch (𝓞 K) K z, glFin (𝓞 K) K z), ⟨h1, h2⟩, (eq_archLift_mul_finLift K z).symm⟩
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show glArch (𝓞 K) K (archLift K p.1 * finLift K p.2) ∈ C
        rw [map_mul, glArch_adelicArchGLIncl, glArch_finLift, mul_one]; exact hp1
      · show glFin (𝓞 K) K (archLift K p.1 * finLift K p.2) ∈ D
        rw [map_mul, glFin_adelicArchGLIncl, glFin_finLift, one_mul]; exact hp2
  rw [himg]
  exact (hC.prod hD).image (((continuous_archLift K).comp continuous_fst).mul ((continuous_finLift K).comp continuous_snd))

theorem indicator_mul_right_eq (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    {y u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hu : u ∈ U') :
    (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) (y * u) =
      (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) y := by
  by_cases hy : y ∈ U'
  · rw [Set.indicator_of_mem (show y * u ∈ (U' : Set _) from U'.mul_mem hy hu),
      Set.indicator_of_mem (show y ∈ (U' : Set _) from hy)]
  · have hy' : y * u ∉ (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :=
      fun h => hy ((Subgroup.mul_mem_cancel_right U' hu).mp h)
    rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem (show y ∉ (U' : Set _) from hy)]

theorem indicator_mul_left_eq (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    {y u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hu : u ∈ U') :
    (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) (u * y) =
      (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) y := by
  by_cases hy : y ∈ U'
  · rw [Set.indicator_of_mem (show u * y ∈ (U' : Set _) from U'.mul_mem hu hy),
      Set.indicator_of_mem (show y ∈ (U' : Set _) from hy)]
  · have hy' : u * y ∉ (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :=
      fun h => hy ((Subgroup.mul_mem_cancel_left U' hu).mp h)
    rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem (show y ∉ (U' : Set _) from hy)]

theorem indicator_inv_eq (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) y⁻¹ =
      (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) y := by
  by_cases hy : y ∈ U'
  · rw [Set.indicator_of_mem (show y⁻¹ ∈ (U' : Set _) from U'.inv_mem hy),
      Set.indicator_of_mem (show y ∈ (U' : Set _) from hy)]
  · have hy' : y⁻¹ ∉ (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := fun h => hy (by simpa using U'.inv_mem h)
    rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem (show y ∉ (U' : Set _) from hy)]

theorem isLocallyConstant_indicator {U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))}
    (hU'o : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) :
    IsLocallyConstant ((U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))) := by
  have hcl : IsClosed (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := U'.isClosed_of_isOpen hU'o
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
  · exact ⟨U', hU'o, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(U' : Set _)ᶜ, hcl.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem (show y ∉ (U' : Set _) from hy), Set.indicator_of_notMem hx]⟩

end FinLevel

section Main

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance] NumberField.AdelicHaar.glBorel

theorem setOf_isUnit_det_mem_nhds_archEntries_one :
    {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K | IsUnit (Matrix.det (Matrix.of E))} ∈ nhds (archEntries K 1) :=
  (isOpen_setOf_isUnit_det K).mem_nhds (isUnit_det_of_archEntries K 1)

omit [NumberField K] in
theorem ringInverse_of_archEntries (a : GL (Fin 2) (InfiniteAdeleRing K)) :
    Ring.inverse (Matrix.of (archEntries K a)) = Matrix.of (archEntries K a⁻¹) := by
  have h : Matrix.of (archEntries K a) * Matrix.of (archEntries K a⁻¹) = 1 := by
    rw [← of_archEntries_mul, mul_inv_cancel, of_archEntries_eq, Units.val_one, map_one]
  have h' : Matrix.of (archEntries K a⁻¹) * Matrix.of (archEntries K a) = 1 := by
    rw [← of_archEntries_mul, inv_mul_cancel, of_archEntries_eq, Units.val_one, map_one]
  have hu : IsUnit (Matrix.of (archEntries K a)) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_of_archEntries K a)
  rw [← hu.unit_spec, Ring.inverse_unit]
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hu.unit_spec, h]

theorem main (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f)
    (hfU : ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K),
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, f (x * u) = f x) :
    ∃ (n : ℕ) (fs gs : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ),
      (∀ k, IsFactorizableTestFn K (fs k)) ∧
      (∀ k, Continuous (gs k) ∧ HasCompactSupport (gs k) ∧
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (gs k) ∧
        (∀ (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion)
            (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          gs k (rowIsometryInclAt₀ K w κ * x * (rowIsometryInclAt₀ K w κ)⁻¹) = gs k x) ∧
        (∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), gs k x ≠ 0 →
          ∃ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
            glFin (𝓞 K) K u = glFin (𝓞 K) K x)) ∧
      ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f x = ∑ k, rightConv K (fs k) (fun y => gs k y⁻¹) x := by
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf

  by_cases hfa0 : ∀ a, fa a = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, fun x => ?_⟩
    rw [hfeq x, hfa0, zero_mul, Finset.univ_eq_empty, Finset.sum_empty]
  push Not at hfa0
  obtain ⟨a₀, ha₀⟩ := hfa0

  set U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := finPrincipalLevel K N with hU'
  have hU'c : IsCompact (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := isCompact_finPrincipalLevel K N
  have hU'o : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := isOpen_finPrincipalLevel K hN

  have hinv : ∀ y, ∀ u ∈ U', ff (y * u) = ff y := by
    intro y u hu
    have hmem : finLift K u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K :=
      (mem_principalLevel_inf_iff K N _).mpr ⟨glArch_finLift K u, by rw [glFin_finLift]; exact hu⟩
    have h := hfU (archLift K a₀ * finLift K y) (finLift K u) hmem
    rw [hfeq, hfeq, map_mul, map_mul, map_mul, map_mul, glArch_adelicArchGLIncl, glArch_finLift, glArch_finLift,
      mul_one, mul_one, glFin_adelicArchGLIncl, glFin_finLift, glFin_finLift, one_mul] at h
    exact mul_left_cancel₀ ha₀ h

  obtain ⟨c, hc, hD⟩ :=
    AutomorphicForm.exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen K U'
      hU'c hU'o

  obtain ⟨n, Ψ, hΨ, hpar⟩ :=
    AutomorphicForm.exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries K
      {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K | IsUnit (Matrix.det (Matrix.of E))}
      (setOf_isUnit_det_mem_nhds_archEntries_one K)
  have hΨcont : ∀ k, Continuous (Ψ k) := fun k => (hΨ k).1
  have hΨc : ∀ k, HasCompactSupport (Ψ k) := fun k => (hΨ k).2.1
  have hΨS : ∀ k, tsupport (Ψ k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k => (hΨ k).2.2.1
  have hΨconj := fun k => (hΨ k).2.2.2

  obtain ⟨Φ, hΦs, hΦc, hΦS, hfaΦ⟩ := exists_contDiff_tsupport_subset_of_isArchTestFactor K hfa
  obtain ⟨Φ', hΦ', hid⟩ := hpar Φ hΦs hΦc hΦS
  have hΦ'c : ∀ k, HasCompactSupport (Φ' k) := fun k =>
    IsCompact.of_isClosed_subset hΦc (isClosed_tsupport _) (hΦ' k).2
  have hΦ'S : ∀ k, tsupport (Φ' k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k => (hΦ' k).2.trans hΦS

  let w2 : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℝ := fun E =>
    (mixedEmbedding.norm (Matrix.det (Matrix.of E))) ^ 2 / c
  have hw2c : Continuous (fun E => ((w2 E : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((contDiff_norm_det_sq K).continuous.div_const c)
  let Ψs : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ := fun k E => Ψ k E * (w2 E : ℂ)
  have hΨsc : ∀ k, Continuous (Ψs k) := fun k => (hΨcont k).mul hw2c
  have hΨss : ∀ k, HasCompactSupport (Ψs k) := fun k => (hΨc k).mul_right
  have hΨsS : ∀ k, tsupport (Ψs k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k =>
    (tsupport_mul_subset_left).trans (hΨS k)
  let Ψi : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ := fun k E =>
    Ψs k (Matrix.of.symm (Ring.inverse (Matrix.of E)))
  have hΨi : ∀ k, Continuous (Ψi k) ∧ HasCompactSupport (Ψi k) ∧
      tsupport (Ψi k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k =>
    continuous_comp_inverse K (hΨsc k) (hΨss k) (hΨsS k)

  have hΨi_arch : ∀ k (a : GL (Fin 2) (InfiniteAdeleRing K)), Ψi k (archEntries K a) = Ψs k (archEntries K a⁻¹) := by
    intro k a
    show Ψs k (Matrix.of.symm (Ring.inverse (Matrix.of (archEntries K a)))) = Ψs k (archEntries K a⁻¹)
    rw [ringInverse_of_archEntries, Equiv.symm_apply_apply]

  have hΨs_conj : ∀ k (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion)
      (a : GL (Fin 2) (InfiniteAdeleRing K)),
      Ψs k (archEntries K (archRowIsometryInclAt₀ K w κ * a * (archRowIsometryInclAt₀ K w κ)⁻¹)) =
        Ψs k (archEntries K a) := by
    intro k w κ a
    have h1 : Ψ k (archEntries K (archRowIsometryInclAt₀ K w κ * a * (archRowIsometryInclAt₀ K w κ)⁻¹)) =
        Ψ k (archEntries K a) := by
      have := hΨconj k w κ (archEntries K a)
      rw [map_inv, ← of_archEntries_mul, ← of_archEntries_mul, Equiv.symm_apply_apply] at this
      exact this
    have h2 : w2 (archEntries K (archRowIsometryInclAt₀ K w κ * a * (archRowIsometryInclAt₀ K w κ)⁻¹)) =
        w2 (archEntries K a) := by
      show (mixedEmbedding.norm (Matrix.det (Matrix.of (archEntries K _)))) ^ 2 / c = _
      rw [det_of_archEntries_conj]
    show Ψ k _ * (w2 _ : ℂ) = Ψ k _ * (w2 _ : ℂ)
    rw [h1, h2]

  let fs : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun k z =>
    Φ' k (archEntries K (glArch (𝓞 K) K z)) * ff (glFin (𝓞 K) K z)
  let gs : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun k z =>
    Ψi k (archEntries K (glArch (𝓞 K) K z)) *
      (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) (glFin (𝓞 K) K z)
  refine ⟨n, fs, gs, fun k => ?_, fun k => ⟨?_, ?_, ?_, ?_, ?_⟩, fun x => ?_⟩

  · exact ⟨fun a => Φ' k (archEntries K a), ff, ⟨⟨Φ' k, (hΦ' k).1, fun _ => rfl⟩,
      hasCompactSupport_comp_archEntries K (hΦ'c k) (hΦ'S k)⟩, hff, fun _ => rfl⟩

  · exact ((hΨi k).1.comp ((continuous_archEntries K).comp (continuous_glArch (𝓞 K) K))).mul
      ((isLocallyConstant_indicator K hU'o).continuous.comp (continuous_glFin (𝓞 K) K))

  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_setOf_glArch_mem_and_glFin_mem K
        (isCompact_setOf_archEntries_mem K (hΨi k).2.1 (hΨi k).2.2) hU'c) ?_
    intro z hz
    have hz' : gs k z ≠ 0 := hz
    refine ⟨?_, ?_⟩
    · show archEntries K (glArch (𝓞 K) K z) ∈ tsupport (Ψi k)
      exact subset_tsupport _ (left_ne_zero_of_mul hz')
    · show glFin (𝓞 K) K z ∈ (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
      by_contra h
      exact (right_ne_zero_of_mul hz') (Set.indicator_of_notMem h _)

  · intro u hu z
    obtain ⟨hua, huf⟩ := (mem_principalLevel_inf_iff K N u).mp hu
    refine ⟨?_, ?_⟩
    · show Ψi k (archEntries K (glArch (𝓞 K) K (u * z))) * _ = Ψi k (archEntries K (glArch (𝓞 K) K z)) * _
      rw [map_mul, map_mul, hua, one_mul, indicator_mul_left_eq K U' huf]
    · show Ψi k (archEntries K (glArch (𝓞 K) K (z * u))) * _ = Ψi k (archEntries K (glArch (𝓞 K) K z)) * _
      rw [map_mul, map_mul, hua, mul_one, indicator_mul_right_eq K U' huf]

  · intro w κ x
    show Ψi k (archEntries K (glArch (𝓞 K) K _)) * _ = Ψi k (archEntries K (glArch (𝓞 K) K x)) * _
    rw [map_mul, map_mul, map_inv, glArch_rowIsometryInclAt₀, map_mul, map_mul, map_inv, glFin_rowIsometryInclAt₀,
      inv_one, one_mul, mul_one, hΨi_arch, hΨi_arch, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, hΨs_conj]

  · intro z hz
    have hzf : glFin (𝓞 K) K z ∈ U' := by
      by_contra h
      exact (right_ne_zero_of_mul hz) (Set.indicator_of_notMem h _)
    exact ⟨finLift K (glFin (𝓞 K) K z),
      (mem_principalLevel_inf_iff K N _).mpr ⟨glArch_finLift K _, by rw [glFin_finLift]; exact hzf⟩, glFin_finLift K _⟩

  · set X : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) :=
      Matrix.of (archEntries K (glArch (𝓞 K) K x)) with hX
    let Θ : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ := fun k E =>
      Φ' k (Matrix.of.symm (X * Matrix.of E)) * Ψs k E
    have hΘc : ∀ k, Continuous (Θ k) := fun k =>
      ((hΦ' k).1.continuous.comp ((entriesEquiv K).symm.continuous.comp (continuous_const.mul
        (continuous_id : Continuous fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
          (Matrix.of E : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)))))).mul (hΨsc k)
    have hΘcs : ∀ k, HasCompactSupport (Θ k) := fun k => (hΨss k).mul_left
    have hΘS : ∀ k, tsupport (Θ k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k =>
      (tsupport_mul_subset_right).trans (hΨsS k)
    have hpt : ∀ k y, fs k (x * y) * gs k y⁻¹ =
        ff (glFin (𝓞 K) K x) *
          (Θ k (archEntries K (glArch (𝓞 K) K y)) *
            (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))
              (glFin (𝓞 K) K y)) := by
      intro k y
      have harch : Ψi k (archEntries K (glArch (𝓞 K) K y⁻¹)) = Ψs k (archEntries K (glArch (𝓞 K) K y)) := by
        rw [map_inv, hΨi_arch, inv_inv]
      have hfinv : (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))
            (glFin (𝓞 K) K y⁻¹) =
          (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) (glFin (𝓞 K) K y) := by
        rw [map_inv]
        exact indicator_inv_eq K U' _
      have hg : fs k (x * y) = Φ' k (Matrix.of.symm (X * Matrix.of (archEntries K (glArch (𝓞 K) K y)))) *
          ff (glFin (𝓞 K) K x * glFin (𝓞 K) K y) := by
        simp only [fs, map_mul, archEntries_mul, hX]
      simp only [gs, harch, hfinv, hg]
      by_cases hy : glFin (𝓞 K) K y ∈ U'
      · rw [hinv _ _ hy, Set.indicator_of_mem (show glFin (𝓞 K) K y ∈ (U' : Set _) from hy)]
        simp only [Θ]
        ring
      · rw [Set.indicator_of_notMem (show glFin (𝓞 K) K y ∉ (U' : Set _) from hy)]
        simp only [mul_zero]
    have hwt : ∀ k (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K),
        Θ k E * (((mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 : ℝ) : ℂ) =
          (c⁻¹ : ℂ) * (Φ' k (Matrix.of.symm (X * Matrix.of E)) * Ψ k E) := by
      intro k E
      by_cases hE : E ∈ {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K | IsUnit (Matrix.det (Matrix.of E))}
      · have h1 := norm_det_inv_pow_mul_pow_of_mem K hE
        have h2 : ((mixedEmbedding.norm (Matrix.det (Matrix.of E)) ^ 2 / c : ℝ) : ℂ) *
            (((mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 : ℝ) : ℂ) = (c⁻¹ : ℂ) := by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_inv]
          congr 1
          rw [div_mul_eq_mul_div, mul_comm, h1, one_div]
        simp only [Θ, Ψs, w2]
        linear_combination (Φ' k (Matrix.of.symm (X * Matrix.of E)) * Ψ k E) * h2
      · have h0 : Ψ k E = 0 := image_eq_zero_of_notMem_tsupport fun h' => hE (hΨS k h')
        simp only [Θ, Ψs, h0, zero_mul, mul_zero]
    have hconv : ∀ k, rightConv K (fs k) (fun y => gs k y⁻¹) x =
        ff (glFin (𝓞 K) K x) * ∫ E, Φ' k (Matrix.of.symm (X * Matrix.of E)) * Ψ k E := by
      intro k
      show (∫ y, fs k (x * y) * gs k y⁻¹ ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) = _
      rw [integral_congr_ae (Filter.Eventually.of_forall (hpt k)), integral_const_mul,
        hD (Θ k) (hΘc k) (hΘcs k) (hΘS k), integral_congr_ae (Filter.Eventually.of_forall (hwt k)),
        integral_const_mul, mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr hc.ne')]
    have hidX : Φ (archEntries K (glArch (𝓞 K) K x)) =
        ∑ k, ∫ E, Φ' k (Matrix.of.symm (X * Matrix.of E)) * Ψ k E := by
      rw [hid (archEntries K (glArch (𝓞 K) K x))]
    calc f x = fa (glArch (𝓞 K) K x) * ff (glFin (𝓞 K) K x) := hfeq x
      _ = ff (glFin (𝓞 K) K x) * Φ (archEntries K (glArch (𝓞 K) K x)) := by rw [hfaΦ, mul_comm]
      _ = ff (glFin (𝓞 K) K x) * ∑ k, ∫ E, Φ' k (Matrix.of.symm (X * Matrix.of E)) * Ψ k E := by rw [hidX]
      _ = ∑ k, ff (glFin (𝓞 K) K x) * ∫ E, Φ' k (Matrix.of.symm (X * Matrix.of E)) * Ψ k E := Finset.mul_sum _ _ _
      _ = ∑ k, rightConv K (fs k) (fun y => gs k y⁻¹) x := Finset.sum_congr rfl fun k _ => (hconv k).symm

end Main

end R4PFprime

end

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f)
    (hfU : ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K),
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, f (x * u) = f x) :
    ∃ (n : ℕ) (fs gs : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ),
      (∀ k, IsFactorizableTestFn K (fs k)) ∧
      (∀ k, Continuous (gs k) ∧ HasCompactSupport (gs k) ∧
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (gs k) ∧
        (∀ (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion)
            (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          gs k (rowIsometryInclAt₀ K w κ * x * (rowIsometryInclAt₀ K w κ)⁻¹) = gs k x) ∧
        (∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), gs k x ≠ 0 →
          ∃ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
            glFin (𝓞 K) K u = glFin (𝓞 K) K x)) ∧
      ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f x = ∑ k, rightConv K (fs k) (fun y => gs k y⁻¹) x :=
  R4PFprime.main K N hN f hf hfU

end S_AutomorphicForm_exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn (solution)
