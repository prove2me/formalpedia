-- Prove2me | solution 1 for AutomorphicForm.exists_eq_sum_rightConv_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b5c2f9ed-d64a-5c2f-b27f-99991d299138

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen
import Theorems.Thm_DixmierMalliavin_exists_eq_sum_integral_mul_comp_mul
import Theorems.Thm_AutomorphicForm_IsFinTestFactor_exists_isCompact_isOpen_forall_mul_eq
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_NumberField_AdelicBox
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

namespace P2MW.S_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn

set_option autoImplicit false
open NumberField AutomorphicForm

set_option autoImplicit false

open NumberField MeasureTheory

open scoped Classical

noncomputable section

namespace TestFunctionFactorization

private theorem contDiff_of_contDiffOn_of_eqOn_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

private def entriesEquiv :
    (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) ≃L[ℝ] Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

private theorem entriesEquiv_apply (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) : entriesEquiv K E = Matrix.of E := rfl

private theorem entriesEquiv_symm_apply (A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :
    (entriesEquiv K).symm A = Matrix.of.symm A := rfl

private theorem contDiff_comp_of_iff {n : WithTop ℕ∞} {F : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) → ℂ} :
    ContDiff ℝ n (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => F (Matrix.of E)) ↔ ContDiff ℝ n F :=
  (entriesEquiv K).contDiff_comp_iff

end Bridge

section Weight

variable (K : Type) [Field K] [NumberField K]

private theorem contDiff_norm_det_sq :
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

private theorem norm_det_ne_zero_of_mem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    mixedEmbedding.norm (Matrix.det (Matrix.of E)) ≠ 0 :=
  ((hE : IsUnit (Matrix.det (Matrix.of E))).map
    (mixedEmbedding.norm : mixedEmbedding.mixedSpace K →*₀ ℝ)).ne_zero

private theorem norm_det_inv_pow_mul_pow_of_mem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    (mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 * (mixedEmbedding.norm (Matrix.det (Matrix.of E))) ^ 2
      = 1 := by
  rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (norm_det_ne_zero_of_mem K hE))]

end Weight

section InversionAlgebra

variable (K : Type) [Field K]

private theorem mem_setOf_isUnit_det_inverse {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    Matrix.of.symm (Ring.inverse (Matrix.of E)) ∈ {E | IsUnit (Matrix.det (Matrix.of E))} := by
  have hu : IsUnit (Matrix.of E) := (Matrix.isUnit_iff_isUnit_det _).mpr hE
  show IsUnit (Matrix.det (Matrix.of (Matrix.of.symm (Ring.inverse (Matrix.of E)))))
  rw [Equiv.apply_symm_apply, ← Matrix.isUnit_iff_isUnit_det, ← hu.unit_spec, Ring.inverse_unit]
  exact Units.isUnit _

private theorem inverse_inverse_of_mem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    Matrix.of.symm (Ring.inverse (Matrix.of (Matrix.of.symm (Ring.inverse (Matrix.of E))))) = E := by
  have hu : IsUnit (Matrix.of E) := (Matrix.isUnit_iff_isUnit_det _).mpr hE
  rw [Equiv.apply_symm_apply, ← hu.unit_spec, Ring.inverse_unit, Ring.inverse_unit, inv_inv, hu.unit_spec]
  exact Equiv.symm_apply_apply _ _

private theorem inverse_eq_zero_of_notMem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∉ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    Matrix.of.symm (Ring.inverse (Matrix.of E)) = 0 := by
  have hu : ¬ IsUnit (Matrix.of E) := fun h => hE ((Matrix.isUnit_iff_isUnit_det _).mp h)
  rw [Ring.inverse_non_unit _ hu]
  rfl

end InversionAlgebra

section Inversion

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem isOpen_setOf_isUnit_det :
    IsOpen {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K | IsUnit (Matrix.det (Matrix.of E))} := by
  have hdet : Continuous (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => Matrix.det (Matrix.of E)) :=
    Continuous.matrix_det
      (continuous_id : Continuous (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => Matrix.of E))
  exact Units.isOpen.preimage hdet

private theorem zero_notMem_setOf_isUnit_det :
    (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) ∉ {E | IsUnit (Matrix.det (Matrix.of E))} := by
  intro h
  have h1 := norm_det_ne_zero_of_mem K h
  apply h1
  have h0 : Matrix.of (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) = 0 := rfl
  rw [h0, Matrix.det_zero, map_zero]

private theorem contDiffAt_comp_inverse_of_mem {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
    (hE : E ∈ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
      Matrix.of.symm (Ring.inverse (Matrix.of E))) E := by
  have hu : IsUnit (Matrix.of E) := (Matrix.isUnit_iff_isUnit_det _).mpr hE
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Ring.inverse : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) →
      Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) (Matrix.of E) := by
    haveI : HasSummableGeomSeries (Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :=
      @instHasSummableGeomSeriesOfCompleteSpace _ _
        (by exact (inferInstance : CompleteSpace (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)))
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := (⊤ : ℕ∞)) hu.unit
    rwa [hu.unit_spec] at this
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) =>
      (entriesEquiv K).symm (Ring.inverse A)) (Matrix.of E) :=
    ((entriesEquiv K).symm.contDiff.contDiffAt).comp _ h1
  exact h2.comp E (entriesEquiv K).contDiff.contDiffAt

private theorem contDiff_comp_inverse {Ψ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ)
    (hΨS : tsupport Ψ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
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
  · refine contDiff_of_contDiffOn_of_eqOn_zero (isOpen_setOf_isUnit_det K) ?_ hK.isClosed hKS hzero
    intro E hE
    exact ((hΨ.contDiffAt).comp E (contDiffAt_comp_inverse_of_mem K hE)).contDiffWithinAt
  · exact HasCompactSupport.of_support_subset_isCompact hK hsupp
  · exact (closure_minimal hsupp hK.isClosed).trans hKS

end Inversion

end TestFunctionFactorization

end

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain
open scoped Classical

namespace TestFunctionFactorization

section field

variable (K : Type) [Field K]

private theorem of_archEntries_eq (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  Matrix.ext fun _ _ => rfl

private theorem of_archEntries_mul (g h : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K (g * h)) = Matrix.of (archEntries K g) * Matrix.of (archEntries K h) := by
  simp only [of_archEntries_eq, Units.val_mul, map_mul]

private theorem of_archEntries_inv (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g⁻¹) = (Matrix.of (archEntries K g))⁻¹ := by
  rw [of_archEntries_eq, of_archEntries_eq]
  symm
  apply Matrix.inv_eq_right_inv
  rw [← map_mul, Units.mul_inv, map_one]

private theorem isUnit_det_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    IsUnit (Matrix.det (Matrix.of (archEntries K g))) := by
  rw [of_archEntries_eq, ← RingHom.map_det]
  exact (Matrix.isUnits_det_units g).map _

private theorem continuous_archEntries : Continuous (archEntries K) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (AdelicBox.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)

private theorem exists_archEntries_eq {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K}
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

private theorem continuous_entriesMap :
    Continuous fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
      (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j) : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :=
  continuous_pi fun i => continuous_pi fun j =>
    (AdelicBox.continuous_ringEquiv_mixedSpace K).comp (continuous_id.matrix_elem i j)

end field

section numberField

variable (K : Type) [Field K] [NumberField K]

private theorem continuousAt_ringInverse {x : InfiniteAdeleRing K} (hx : IsUnit x) :
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

private theorem isCompact_preimage_entriesMap {C : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)} (hC : IsCompact C) :
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

private theorem hasCompactSupport_comp_archEntries {Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ}
    (hΦc : HasCompactSupport Φ) (hΦS : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    HasCompactSupport (fun g : GL (Fin 2) (InfiniteAdeleRing K) => Φ (archEntries K g)) := by

  have hC : IsCompact {m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) |
      (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)) ∈ tsupport Φ} :=
    isCompact_preimage_entriesMap K hΦc
  have hunit : ∀ m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K),
      (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)) ∈ tsupport Φ → IsUnit m := by
    intro m hm
    have h1 : IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix m).det := hΦS hm
    rw [← RingHom.map_det] at h1
    have h2 := h1.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
    have h3 : (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom m.det) = m.det :=
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply m.det
    rw [h3] at h2
    exact (Matrix.isUnit_iff_isUnit_det m).mpr h2
  have hinv : ContinuousOn (fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) => m⁻¹)
      {m | (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (m i j)) ∈ tsupport Φ} := by
    intro m hm
    have hdet : IsUnit m.det := (Matrix.isUnit_iff_isUnit_det m).mp (hunit m hm)
    exact (continuousAt_matrix_inv m (continuousAt_ringInverse K hdet)).continuousWithinAt

  have hP : IsCompact {g : GL (Fin 2) (InfiniteAdeleRing K) | archEntries K g ∈ tsupport Φ} := by
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
          (((hunit m hm).unit : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j)) ∈ tsupport Φ
        rw [IsUnit.unit_spec]
        exact hm
      · simp only [Units.embedProduct_apply, id, Function.comp_apply, Matrix.coe_units_inv, IsUnit.unit_spec]
  refine HasCompactSupport.of_support_subset_isCompact hP ?_
  intro g hg
  exact subset_tsupport Φ hg

private theorem exists_contDiff_tsupport_subset_of_isArchTestFactor {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
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

end TestFunctionFactorization

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory IsDedekindDomain
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace TestFunctionFactorization

variable (K : Type) [Field K] [NumberField K]

private theorem isAddHaarMeasure_volume_entries :
    (volume : Measure (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)).IsAddHaarMeasure := by
  haveI s0 : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace K)) := inferInstance
  haveI m0 : MeasurableAdd (mixedEmbedding.mixedSpace K) := inferInstance
  haveI h1 : (volume : Measure (Fin 2 → mixedEmbedding.mixedSpace K)).IsAddHaarMeasure := inferInstance
  haveI s1 : SigmaFinite (volume : Measure (Fin 2 → mixedEmbedding.mixedSpace K)) := inferInstance
  haveI b1 : BorelSpace (Fin 2 → mixedEmbedding.mixedSpace K) := Pi.borelSpace
  haveI m1 : MeasurableAdd (Fin 2 → mixedEmbedding.mixedSpace K) := inferInstance
  infer_instance

private scoped instance instMeasurableSpaceMat : MeasurableSpace (Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :=
  inferInstanceAs (MeasurableSpace (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K))

private theorem borelSpace_mat : BorelSpace (Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) := by
  change BorelSpace (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)
  exact Pi.borelSpace

private def μM : Measure (Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :=
  (volume : Measure (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K))

private theorem isAddHaarMeasure_μM : (μM K).IsAddHaarMeasure := by
  change (volume : Measure (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)).IsAddHaarMeasure
  exact isAddHaarMeasure_volume_entries K

private theorem integral_μM_eq (F : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) → ℂ) :
    ∫ y, F y ∂(μM K) = ∫ E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K, F (Matrix.of E) := rfl

private theorem setOf_isUnit_det_mem_nhds_one :
    {Y : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) | IsUnit (Matrix.det Y)} ∈
      nhds (1 : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) := by
  refine IsOpen.mem_nhds ?_ ?_
  · change IsOpen {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K | IsUnit (Matrix.det (Matrix.of E))}
    exact Units.isOpen.preimage (Continuous.matrix_det
      (A := fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => Matrix.of E) continuous_id)
  · simp only [Set.mem_setOf_eq, Matrix.det_one, isUnit_one]

omit [NumberField K] in
private theorem ringInverse_inv_of_isUnit_det {Y : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)}
    (hY : IsUnit (Matrix.det Y)) : Ring.inverse Y⁻¹ = Y := by
  have hu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).mpr hY
  obtain ⟨u, rfl⟩ := hu
  rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit, Ring.inverse_unit, inv_inv]

private theorem indicator_inv_eq (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) y⁻¹ =
      (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) y := by
  by_cases hy : y ∈ U'
  · rw [Set.indicator_of_mem (show y⁻¹ ∈ (U' : Set _) from U'.inv_mem hy),
      Set.indicator_of_mem (show y ∈ (U' : Set _) from hy)]
  · have hy' : y⁻¹ ∉ (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := fun h => hy (by simpa using U'.inv_mem h)
    rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem (show y ∉ (U' : Set _) from hy)]

private theorem isLocallyConstant_indicator {U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))}
    (hU'o : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) :
    IsLocallyConstant ((U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))) := by
  have hcl : IsClosed (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := U'.isClosed_of_isOpen hU'o
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
  · exact ⟨U', hU'o, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(U' : Set _)ᶜ, hcl.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem (show y ∉ (U' : Set _) from hy), Set.indicator_of_notMem hx]⟩

private theorem hasCompactSupport_indicator {U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))}
    (hU'c : IsCompact (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) :
    HasCompactSupport ((U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))) :=
  HasCompactSupport.intro hU'c fun _ hx => Set.indicator_of_notMem hx _

private theorem main (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f) :
    ∃ n : ℕ, ∃ g h : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      (∀ k, IsFactorizableTestFn K (g k)) ∧ (∀ k, IsFactorizableTestFn K (h k)) ∧
        ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f x = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x := by
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf

  obtain ⟨U', hU'c, hU'o, hinv⟩ :=
    AutomorphicForm.IsFinTestFactor.exists_isCompact_isOpen_forall_mul_eq K ff hff

  obtain ⟨c, hc, hD⟩ :=
    AutomorphicForm.exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen K U'
      hU'c hU'o

  obtain ⟨Φ, hΦs, hΦc, hΦS, hfaΦ⟩ := exists_contDiff_tsupport_subset_of_isArchTestFactor K hfa

  let ΦM : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) → ℂ := fun Y => Φ (Matrix.of.symm Y)
  have hΦMs : ContDiff ℝ (⊤ : ℕ∞) ΦM := (contDiff_comp_of_iff K).mp hΦs
  have hΦMc : HasCompactSupport ΦM := hΦc

  obtain ⟨n, Φ', Ψ, hΦ', hΨ, hid⟩ :=
    @DixmierMalliavin.exists_eq_sum_integral_mul_comp_mul
      (Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) _ _ _ _ (borelSpace_mat K) (μM K)
      (isAddHaarMeasure_μM K) {Y : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) | IsUnit (Matrix.det Y)}
      (setOf_isUnit_det_mem_nhds_one K) ΦM hΦMs hΦMc

  let ΦV : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ := fun k E => Φ' k (Matrix.of E)
  let ΨV : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ := fun k E => Ψ k (Matrix.of E)
  have hΦVs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ΦV k) := fun k => (contDiff_comp_of_iff K).mpr (hΦ' k).1
  have hΦVS : ∀ k, tsupport (ΦV k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k =>
    ((hΦ' k).2.trans (show tsupport ΦM ⊆ tsupport Φ from subset_rfl)).trans hΦS
  have hΦVc : ∀ k, HasCompactSupport (ΦV k) := fun k =>
    IsCompact.of_isClosed_subset hΦc (isClosed_tsupport _) ((hΦ' k).2.trans subset_rfl)
  have hΨVs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ΨV k) := fun k => (contDiff_comp_of_iff K).mpr (hΨ k).1
  have hΨVc : ∀ k, HasCompactSupport (ΨV k) := fun k => (hΨ k).2.1
  have hΨVS : ∀ k, tsupport (ΨV k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k => (hΨ k).2.2

  let w2 : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℝ := fun E =>
    (mixedEmbedding.norm (Matrix.det (Matrix.of E))) ^ 2 / c
  let Ψs : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ := fun k E => ΨV k E * (w2 E : ℂ)
  have hw2 : ContDiff ℝ (⊤ : ℕ∞) (fun E => ((w2 E : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_norm_det_sq K).div_const c)
  have hΨss : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψs k) := fun k => (hΨVs k).mul hw2
  have hΨsc : ∀ k, HasCompactSupport (Ψs k) := fun k => (hΨVc k).mul_right
  have hΨsS : ∀ k, tsupport (Ψs k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k =>
    (tsupport_mul_subset_left).trans (hΨVS k)

  let Ψi : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ := fun k E =>
    Ψs k (Matrix.of.symm (Ring.inverse (Matrix.of E)))
  have hΨi : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψi k) ∧ HasCompactSupport (Ψi k) ∧
      tsupport (Ψi k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k =>
    contDiff_comp_inverse K (hΨss k) (hΨsc k) (hΨsS k)

  let g : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun k z =>
    ΦV k (archEntries K (AdelicLevel.glArch (𝓞 K) K z)) * ff (AdelicLevel.glFin (𝓞 K) K z)
  let h : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun k z =>
    Ψi k (archEntries K (AdelicLevel.glArch (𝓞 K) K z)) *
      (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 K) K z)
  refine ⟨n, g, h, fun k => ?_, fun k => ?_, fun x => ?_⟩
  · exact ⟨fun a => ΦV k (archEntries K a), ff, ⟨⟨ΦV k, hΦVs k, fun _ => rfl⟩,
      hasCompactSupport_comp_archEntries K (hΦVc k) (hΦVS k)⟩, hff, fun _ => rfl⟩
  · exact ⟨fun a => Ψi k (archEntries K a),
      (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)),
      ⟨⟨Ψi k, (hΨi k).1, fun _ => rfl⟩,
      hasCompactSupport_comp_archEntries K (hΨi k).2.1 (hΨi k).2.2⟩,
      ⟨isLocallyConstant_indicator K hU'o, hasCompactSupport_indicator K hU'c⟩, fun _ => rfl⟩
  ·
    set X : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K) :=
      Matrix.of (archEntries K (AdelicLevel.glArch (𝓞 K) K x)) with hX

    let Θ : Fin n → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ := fun k E =>
      Φ' k (X * Matrix.of E) * Ψs k E
    have hΘc : ∀ k, Continuous (Θ k) := fun k =>
      ((hΦ' k).1.continuous.comp (continuous_const.mul
        (continuous_id : Continuous fun E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
          (Matrix.of E : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K))))).mul (hΨss k).continuous
    have hΘcs : ∀ k, HasCompactSupport (Θ k) := fun k => (hΨsc k).mul_left
    have hΘS : ∀ k, tsupport (Θ k) ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := fun k =>
      (tsupport_mul_subset_right).trans (hΨsS k)

    have hpt : ∀ k y, g k (x * y) * h k y⁻¹ =
        ff (AdelicLevel.glFin (𝓞 K) K x) *
          (Θ k (archEntries K (AdelicLevel.glArch (𝓞 K) K y)) *
            (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))
              (AdelicLevel.glFin (𝓞 K) K y)) := by
      intro k y
      have harch : Ψi k (archEntries K (AdelicLevel.glArch (𝓞 K) K y⁻¹)) =
          Ψs k (archEntries K (AdelicLevel.glArch (𝓞 K) K y)) :=
        congrArg (Ψs k) (by
          rw [map_inv, of_archEntries_inv, ringInverse_inv_of_isUnit_det K (isUnit_det_of_archEntries K _),
            Equiv.symm_apply_apply])
      have hfinv : (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))
            (AdelicLevel.glFin (𝓞 K) K y⁻¹) =
          (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))
            (AdelicLevel.glFin (𝓞 K) K y) := by
        rw [map_inv]
        exact indicator_inv_eq K U' _
      have hg : g k (x * y) = Φ' k (X * Matrix.of (archEntries K (AdelicLevel.glArch (𝓞 K) K y))) *
          ff (AdelicLevel.glFin (𝓞 K) K x * AdelicLevel.glFin (𝓞 K) K y) := by
        simp only [g, ΦV, map_mul, of_archEntries_mul, hX]
      simp only [h, harch, hfinv, hg]
      by_cases hy : AdelicLevel.glFin (𝓞 K) K y ∈ U'
      · rw [hinv _ _ hy, Set.indicator_of_mem (show AdelicLevel.glFin (𝓞 K) K y ∈ (U' : Set _) from hy)]
        simp only [Θ]
        ring
      · rw [Set.indicator_of_notMem (show AdelicLevel.glFin (𝓞 K) K y ∉ (U' : Set _) from hy)]
        simp only [mul_zero]

    have hwt : ∀ k (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K),
        Θ k E * (((mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 : ℝ) : ℂ) =
          (c⁻¹ : ℂ) * (Φ' k (X * Matrix.of E) * ΨV k E) := by
      intro k E
      by_cases hE : E ∈ {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K | IsUnit (Matrix.det (Matrix.of E))}
      · have h1 := norm_det_inv_pow_mul_pow_of_mem K hE
        have h2 : ((mixedEmbedding.norm (Matrix.det (Matrix.of E)) ^ 2 / c : ℝ) : ℂ) *
            (((mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 : ℝ) : ℂ) = (c⁻¹ : ℂ) := by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_inv]
          congr 1
          rw [div_mul_eq_mul_div, mul_comm, h1, one_div]
        simp only [Θ, Ψs, w2]
        linear_combination (Φ' k (X * Matrix.of E) * ΨV k E) * h2
      · have h0 : ΨV k E = 0 := image_eq_zero_of_notMem_tsupport fun h' => hE (hΨVS k h')
        simp only [Θ, Ψs, h0, zero_mul, mul_zero]

    have hconv : ∀ k, rightConv K (g k) (fun y => h k y⁻¹) x =
        ff (AdelicLevel.glFin (𝓞 K) K x) * ∫ Y, Φ' k (X * Y) * Ψ k Y ∂(μM K) := by
      intro k
      show (∫ y, g k (x * y) * h k y⁻¹ ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) = _
      rw [integral_congr_ae (Filter.Eventually.of_forall (hpt k)), integral_const_mul,
        hD (Θ k) (hΘc k) (hΘcs k) (hΘS k), integral_congr_ae (Filter.Eventually.of_forall (hwt k)),
        integral_const_mul, mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr hc.ne')]
      rfl
    calc f x = fa (AdelicLevel.glArch (𝓞 K) K x) * ff (AdelicLevel.glFin (𝓞 K) K x) := hfeq x
      _ = ff (AdelicLevel.glFin (𝓞 K) K x) * ΦM X := by
          simp only [hfaΦ, ΦM, hX, Equiv.symm_apply_apply, mul_comm]
      _ = ff (AdelicLevel.glFin (𝓞 K) K x) * ∑ k, ∫ Y, Φ' k (X * Y) * Ψ k Y ∂(μM K) := by rw [hid X]
      _ = ∑ k, ff (AdelicLevel.glFin (𝓞 K) K x) * ∫ Y, Φ' k (X * Y) * Ψ k Y ∂(μM K) := Finset.mul_sum _ _ _
      _ = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x := Finset.sum_congr rfl fun k _ => (hconv k).symm

end TestFunctionFactorization
p2m_reactivate "P2MW.S_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn.TestFunctionFactorization"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn.TestFunctionFactorization"

theorem solution (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f) :
    ∃ n : ℕ, ∃ g h : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      (∀ k, IsFactorizableTestFn K (g k)) ∧ (∀ k, IsFactorizableTestFn K (h k)) ∧
        ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f x = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x := by
  exact TestFunctionFactorization.main K f hf

end S_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn (solution)
