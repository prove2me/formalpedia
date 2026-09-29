-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_mul_of_isComplex_place
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a3a4d179-a877-591c-b524-edea1b5b6068

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

import Definitions.Def_M4aHerbrand_ArchSemilocal
import Theorems.Thm_AutomorphicForm_exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap
import Theorems.Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_NumberField_InfiniteAdeleRing_isEmbedding_units_val
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_mul_of_isComplex_place

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped NumberField.LiesOver
open scoped Classical

set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace LayerPlumbing

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def iotaL (y : L ⊗[K] InfiniteAdeleRing K) : NumberField.mixedEmbedding.mixedSpace L :=
  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)

theorem iotaL_apply (y : L ⊗[K] InfiniteAdeleRing K) :
    iotaL K L y = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y) := rfl

def iotaLHomeomorph : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ NumberField.mixedEmbedding.mixedSpace L :=
  (AutomorphicForm.archIdentHomeomorph K L).trans
    ((NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L).homeomorph
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L))

theorem iotaLHomeomorph_apply (y : L ⊗[K] InfiniteAdeleRing K) : iotaLHomeomorph K L y = iotaL K L y := rfl

def iotaLRingEquiv : (L ⊗[K] InfiniteAdeleRing K) ≃+* NumberField.mixedEmbedding.mixedSpace L :=
  (AutomorphicForm.archIdentEquiv K L).trans (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L)

theorem iotaLRingEquiv_apply (y : L ⊗[K] InfiniteAdeleRing K) : iotaLRingEquiv K L y = iotaL K L y := rfl

theorem continuous_iotaL : Continuous (iotaL K L) := (iotaLHomeomorph K L).continuous

theorem isUnit_iotaL {y : L ⊗[K] InfiniteAdeleRing K} (hy : IsUnit y) : IsUnit (iotaL K L y) :=
  hy.map (iotaLRingEquiv K L).toMonoidHom

section Transport
variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]

theorem integral_comp_iotaL {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) (e : NumberField.mixedEmbedding.mixedSpace L ≃ₜ X)
    (ν : Measure X) (κ : NNReal)
    (hmap : Measure.map (fun y : L ⊗[K] InfiniteAdeleRing K =>
      e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))) lam = κ • ν)
    (F : X → G) :
    ∫ y, F (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))) ∂lam =
      (κ : ℝ) • ∫ x, F x ∂ν := by
  set H : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ X := (iotaLHomeomorph K L).trans e with hH
  have hHc : (H.toMeasurableEquiv : (L ⊗[K] InfiniteAdeleRing K) → X) =
      fun y => e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)) := rfl
  have h1 := integral_map_equiv (μ := lam) H.toMeasurableEquiv F
  rw [hHc, hmap] at h1
  rw [← h1, show ((κ • ν : Measure X)) = ((κ : ENNReal) • ν) from rfl, integral_smul_measure, ENNReal.coe_toReal]

theorem integrable_comp_iotaL_iff {G : Type} [NormedAddCommGroup G]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) (e : NumberField.mixedEmbedding.mixedSpace L ≃ₜ X)
    (ν : Measure X) (κ : NNReal) (hκ : κ ≠ 0)
    (hmap : Measure.map (fun y : L ⊗[K] InfiniteAdeleRing K =>
      e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))) lam = κ • ν)
    (F : X → G) :
    Integrable (fun y => F (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)))) lam ↔
      Integrable F ν := by
  set H : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ X := (iotaLHomeomorph K L).trans e with hH
  have hHc : (H.toMeasurableEquiv : (L ⊗[K] InfiniteAdeleRing K) → X) =
      fun y => e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)) := rfl
  have h1 := integrable_map_equiv (μ := lam) H.toMeasurableEquiv F
  rw [hHc, hmap] at h1
  rw [show ((κ • ν : Measure X)) = ((κ : ENNReal) • ν) from rfl, integrable_smul_measure (by simpa using hκ) (by simp)] at h1
  exact h1.symm

end Transport

theorem isUnit_mixedSpace_iff (x : NumberField.mixedEmbedding.mixedSpace L) :
    IsUnit x ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ w, x.2 w ≠ 0) := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  exact and_congr (forall_congr' fun w => isUnit_iff_ne_zero) (forall_congr' fun w => isUnit_iff_ne_zero)

theorem isOpen_setOf_isUnit_mixedSpace : IsOpen {x : NumberField.mixedEmbedding.mixedSpace L | IsUnit x} := by
  have h : {x : NumberField.mixedEmbedding.mixedSpace L | IsUnit x} =
      (⋂ w, {x | x.1 w ≠ 0}) ∩ (⋂ w, {x | x.2 w ≠ 0}) := by
    ext x; simp [isUnit_mixedSpace_iff]
  rw [h]
  refine (isOpen_iInter_of_finite fun w => ?_).inter (isOpen_iInter_of_finite fun w => ?_)
  · exact isOpen_ne_fun ((continuous_apply w).comp continuous_fst) continuous_const
  · exact isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const

section Bump
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
omit K L in
theorem exists_smooth_bump {S U : Set E} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x ∈ S, χ x = 1) ∧ tsupport χ ⊆ U := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_ball 0
  set U' : Set E := U ∩ Metric.ball 0 R with hU'
  have hU'o : IsOpen U' := hU.inter Metric.isOpen_ball
  have hd : Disjoint U'ᶜ S := by
    rw [Set.disjoint_left]
    intro x hx hxS
    exact hx ⟨hSU hxS, hR hxS⟩
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ E) (n := (⊤ : ℕ∞)) hU'o.isClosed_compl hS.isClosed hd
  obtain ⟨V, hVo, hsV, hV⟩ := eventually_nhdsSet_iff_exists.mp hf0
  have hts : tsupport (⇑f) ⊆ U' := by
    refine (closure_minimal (fun x hx => ?_) hVo.isClosed_compl).trans (Set.compl_subset_comm.mp hsV)
    exact fun hxV => hx (hV x hxV)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, fun x hx => hf1.self_of_nhdsSet x hx,
    hts.trans Set.inter_subset_left⟩
  exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 R) (isClosed_tsupport _)
    (hts.trans (Set.inter_subset_right.trans Metric.ball_subset_closedBall))
end Bump

theorem exists_cutoff
    (Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ) (hΦc : HasCompactSupport Φ)
    (hΦu : ∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) :
    ∃ χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ p : Fin 3 → NumberField.mixedEmbedding.mixedSpace L, p ∈ tsupport Φ → χ ![p 0, p 1] = 1) ∧
      (∀ p ∈ tsupport χ, IsUnit (p 0) ∧ IsUnit (p 1)) := by
  classical
  obtain ⟨C, hC, hCar⟩ := hΦu
  set S2 : Set (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) :=
    (fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace L => (![p 0, p 1] : Fin 2 → NumberField.mixedEmbedding.mixedSpace L)) '' tsupport Φ with hS2
  have hS2c : IsCompact S2 := by
    refine hΦc.image (continuous_pi fun i => ?_)
    fin_cases i
    · exact (show Continuous (fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace L => p 0) from continuous_apply 0)
    · exact (show Continuous (fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace L => p 1) from continuous_apply 1)
  set U2 : Set (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) := {p | IsUnit (p 0) ∧ IsUnit (p 1)} with hU2
  have hU2o : IsOpen U2 := by
    have h0 : IsOpen ((fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => p 0) ⁻¹'
        {x : NumberField.mixedEmbedding.mixedSpace L | IsUnit x}) :=
      (isOpen_setOf_isUnit_mixedSpace L).preimage (continuous_apply 0)
    have h1 : IsOpen ((fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => p 1) ⁻¹'
        {x : NumberField.mixedEmbedding.mixedSpace L | IsUnit x}) :=
      (isOpen_setOf_isUnit_mixedSpace L).preimage (continuous_apply 1)
    exact h0.inter h1
  have hS2U : S2 ⊆ U2 := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, -, h0, h1⟩ := hCar p hp
    refine ⟨?_, ?_⟩
    · show IsUnit ((![p 0, p 1] : Fin 2 → NumberField.mixedEmbedding.mixedSpace L) 0)
      simp only [Matrix.cons_val_zero, h0]
      exact isUnit_iotaL K L (Units.isUnit _)
    · show IsUnit ((![p 0, p 1] : Fin 2 → NumberField.mixedEmbedding.mixedSpace L) 1)
      simp only [Matrix.cons_val_one, Matrix.head_cons, h1]
      exact isUnit_iotaL K L (Units.isUnit _)
  obtain ⟨χ, hχ, hχc, hχ1, hχU⟩ := exists_smooth_bump hS2c hU2o hS2U
  exact ⟨χ, hχ, hχc, fun p hp => hχ1 _ ⟨p, hp, rfl⟩, fun p hp => hχU hp⟩

theorem isEmbedding_units_val_tensor :
    Topology.IsEmbedding (Units.val : (L ⊗[K] InfiniteAdeleRing K)ˣ → L ⊗[K] InfiniteAdeleRing K) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have hL := NumberField.InfiniteAdeleRing.isEmbedding_units_val L

  set φ : (L ⊗[K] InfiniteAdeleRing K) ≃+* InfiniteAdeleRing L := AutomorphicForm.archIdentEquiv K L with hφ
  have hφc : Continuous φ := (AutomorphicForm.archIdentHomeomorph K L).continuous
  have hφsc : Continuous φ.symm := (AutomorphicForm.archIdentHomeomorph K L).symm.continuous
  have hmc : Continuous (Units.map (φ : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L)) :=
    Continuous.units_map _ hφc
  have hmsc : Continuous (Units.map (φ.symm : InfiniteAdeleRing L →* (L ⊗[K] InfiniteAdeleRing K))) :=
    Continuous.units_map _ hφsc

  have hcomp : (Units.val : (L ⊗[K] InfiniteAdeleRing K)ˣ → L ⊗[K] InfiniteAdeleRing K) =
      (φ.symm : InfiniteAdeleRing L → L ⊗[K] InfiniteAdeleRing K) ∘ Units.val ∘
        Units.map (φ : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L) := by
    funext u
    simp
  rw [hcomp]
  refine (AutomorphicForm.archIdentHomeomorph K L).symm.isEmbedding.comp (hL.comp ?_)

  refine (Homeomorph.mk ⟨Units.map (φ : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L),
    Units.map (φ.symm : InfiniteAdeleRing L →* (L ⊗[K] InfiniteAdeleRing K)), fun u => ?_, fun u => ?_⟩ hmc hmsc).isEmbedding
  · ext; simp
  · ext; simp

theorem exists_unit_carrier
    (χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℝ) (hχc : HasCompactSupport χ)
    (hχU : ∀ p ∈ tsupport χ, IsUnit (p 0) ∧ IsUnit (p 1)) :
    ∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
      ∀ (G : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ), tsupport G ⊆ tsupport χ →
        ∀ p ∈ tsupport G, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) := by
  classical
  have hUE := isEmbedding_units_val_tensor K L
  set ψ : NumberField.mixedEmbedding.mixedSpace L → L ⊗[K] InfiniteAdeleRing K := fun x => (iotaLRingEquiv K L).symm x with hψ
  have hψeq : ∀ x, (iotaLHomeomorph K L).symm x = ψ x := by
    intro x
    apply (iotaLHomeomorph K L).injective
    rw [Homeomorph.apply_symm_apply]
    exact ((iotaLRingEquiv K L).apply_symm_apply x).symm
  have hψc : Continuous ψ := by
    have h : ψ = fun x => (iotaLHomeomorph K L).symm x := funext fun x => (hψeq x).symm
    rw [h]; exact (iotaLHomeomorph K L).symm.continuous
  have hψι : ∀ x, NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (ψ x)) = x :=
    fun x => (iotaLRingEquiv K L).apply_symm_apply x
  obtain ⟨Cset, hCset⟩ : ∃ Cset : Fin 2 → Set ((L ⊗[K] InfiniteAdeleRing K)ˣ), Cset = fun i =>
      Units.val ⁻¹' ((fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => ψ (p i)) '' tsupport χ) := ⟨_, rfl⟩
  have hCc : ∀ i : Fin 2, IsCompact (Cset i) := by
    intro i
    rw [hCset]
    refine hUE.isInducing.isCompact_iff.mpr ?_
    have hsub : (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => ψ (p i)) '' tsupport χ ⊆
        Set.range (Units.val : (L ⊗[K] InfiniteAdeleRing K)ˣ → L ⊗[K] InfiniteAdeleRing K) := by
      rintro _ ⟨p, hp, rfl⟩
      have hu : IsUnit (p i) := by
        obtain ⟨h0, h1⟩ := hχU p hp
        fin_cases i
        · exact h0
        · exact h1
      obtain ⟨u, hu⟩ := hu.map (iotaLRingEquiv K L).symm.toMonoidHom
      exact ⟨u, hu⟩
    rw [Set.image_preimage_eq_of_subset hsub]
    exact hχc.image (hψc.comp (continuous_apply i))
  refine ⟨Cset 0 ×ˢ Cset 1, (hCc 0).prod (hCc 1), fun G hG p hp => ?_⟩
  have hp' := hG hp
  obtain ⟨h0, h1⟩ := hχU p hp'
  obtain ⟨u₀, hu₀⟩ := h0.map (iotaLRingEquiv K L).symm.toMonoidHom
  obtain ⟨u₁, hu₁⟩ := h1.map (iotaLRingEquiv K L).symm.toMonoidHom
  refine ⟨(u₀, u₁), ⟨?_, ?_⟩, ?_, ?_⟩
  · show u₀ ∈ Cset 0
    rw [hCset]; exact ⟨p, hp', hu₀.symm⟩
  · show u₁ ∈ Cset 1
    rw [hCset]; exact ⟨p, hp', hu₁.symm⟩
  · show p 0 = _
    rw [hu₀]; exact (hψι (p 0)).symm
  · show p 1 = _
    rw [hu₁]; exact (hψι (p 1)).symm

end LayerPlumbing

namespace K55S5

theorem continuous_ringEquiv_mixedSpace (K : Type) [Field K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  have h : (InfiniteAdeleRing.ringEquiv_mixedSpace K :
        InfiniteAdeleRing K → mixedEmbedding.mixedSpace K)
      = fun x => (fun (w : {w : InfinitePlace K // w.IsReal}) =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (x w.1),
        fun (w : {w : InfinitePlace K // w.IsComplex}) =>
          InfinitePlace.Completion.extensionEmbedding w.1 (x w.1)) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  rw [h]
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
      (continuous_apply w.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
      (continuous_apply w.1)

noncomputable def chart (K : Type) [Field K] (q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) :
    Fin 2 → mixedEmbedding.mixedSpace K :=
  ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]

theorem chart_apply_zero (K : Type) [Field K] (q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) :
    chart K q 0 = InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) :=
  rfl

theorem chart_apply_one (K : Type) [Field K] (q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) :
    chart K q 1 = InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) :=
  rfl

theorem continuous_chart (K : Type) [Field K] : Continuous (chart K) := by
  rw [continuous_pi_iff, Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · simp only [chart_apply_zero]
    exact (continuous_ringEquiv_mixedSpace K).comp
      ((Units.continuous_val : Continuous ((↑) : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K)).comp
        continuous_fst)
  · simp only [chart_apply_one]
    exact (continuous_ringEquiv_mixedSpace K).comp
      ((Units.continuous_val : Continuous ((↑) : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K)).comp
        continuous_snd)

def swapDiv {M : Type} [Monoid M] (q : Mˣ × Mˣ) : Mˣ × Mˣ := (q.1⁻¹ * q.2, q.1)

theorem continuous_swapDiv {M : Type} [Monoid M] [TopologicalSpace M] [ContinuousMul M] :
    Continuous (swapDiv (M := M)) :=
  ((continuous_fst.inv).mul continuous_snd).prodMk continuous_fst

theorem contDiff_reparamMap (K : Type) [Field K] [NumberField K] :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin 2 → mixedEmbedding.mixedSpace K => ![z 1, z 1 * z 0]) := by
  refine contDiff_pi.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simp only [Matrix.cons_val_zero]
    exact contDiff_apply ℝ (mixedEmbedding.mixedSpace K) (1 : Fin 2)
  · simp only [Matrix.cons_val_one]
    exact (contDiff_apply ℝ (mixedEmbedding.mixedSpace K) (1 : Fin 2)).mul
      (contDiff_apply ℝ (mixedEmbedding.mixedSpace K) (0 : Fin 2))

theorem reparam_apply {K : Type} [Field K] {β : Type}
    (F : (Fin 2 → mixedEmbedding.mixedSpace K) → β) (x y : mixedEmbedding.mixedSpace K) :
    (fun z : Fin 2 → mixedEmbedding.mixedSpace K => F ![z 1, z 1 * z 0]) ![x, y] = F ![y, y * x] := by
  simp

theorem reparam_apply_ringEquiv {K : Type} [Field K] {β : Type}
    (F : (Fin 2 → mixedEmbedding.mixedSpace K) → β) (t a : InfiniteAdeleRing K) :
    (fun z : Fin 2 → mixedEmbedding.mixedSpace K => F ![z 1, z 1 * z 0])
        ![InfiniteAdeleRing.ringEquiv_mixedSpace K t, InfiniteAdeleRing.ringEquiv_mixedSpace K a]
      = F ![InfiniteAdeleRing.ringEquiv_mixedSpace K a,
            InfiniteAdeleRing.ringEquiv_mixedSpace K (a * t)] := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_mul]

set_option linter.unusedVariables false in

theorem reparam_norm_coords
    (K : Type) [Field K] [NumberField K]
    (F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F)
    (hFu : ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport F, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => F ![z 1, z 1 * z 0]) ∧
    HasCompactSupport (fun z : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => F ![z 1, z 1 * z 0]) ∧
    ∃ Ca' : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca' ∧
        ∀ p ∈ tsupport (fun z : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => F ![z 1, z 1 * z 0]), ∃ q ∈ Ca',
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] := by
  obtain ⟨Ca, hCa, hFCa⟩ := hFu
  have hCa' : IsCompact (swapDiv '' Ca) := hCa.image continuous_swapDiv
  have hS : IsCompact (chart K '' (swapDiv '' Ca)) := hCa'.image (continuous_chart K)

  have hsupp : Function.support
      (fun z : Fin 2 → mixedEmbedding.mixedSpace K => F ![z 1, z 1 * z 0]) ⊆
        chart K '' (swapDiv '' Ca) := by
    intro z hz
    have hz' : ![z 1, z 1 * z 0] ∈ tsupport F := subset_tsupport F hz
    obtain ⟨q, hq, hzq⟩ := hFCa _ hz'
    have h1 : z 1 = InfiniteAdeleRing.ringEquiv_mixedSpace K
        ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) := by
      have h := congrFun hzq 0
      simp only [Matrix.cons_val_zero] at h
      exact h
    have h2 : z 1 * z 0 = InfiniteAdeleRing.ringEquiv_mixedSpace K
        ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) := by
      have h := congrFun hzq 1
      simp only [Matrix.cons_val_one] at h
      exact h
    have h0 : InfiniteAdeleRing.ringEquiv_mixedSpace K
        (((q.1⁻¹ * q.2 : (InfiniteAdeleRing K)ˣ)) : InfiniteAdeleRing K) = z 0 := by
      rw [Units.val_mul, map_mul, ← h2, h1, ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
        one_mul]
    refine ⟨swapDiv q, ⟨q, hq, rfl⟩, ?_⟩
    funext i
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨h0, h1.symm⟩
  have htsupp : tsupport
      (fun z : Fin 2 → mixedEmbedding.mixedSpace K => F ![z 1, z 1 * z 0]) ⊆
        chart K '' (swapDiv '' Ca) :=
    closure_minimal hsupp hS.isClosed
  refine ⟨hF.comp (contDiff_reparamMap K), ?_, swapDiv '' Ca, hCa', ?_⟩
  · exact hS.of_isClosed_subset (isClosed_tsupport _) htsupp
  · intro p hp
    obtain ⟨q', hq', rfl⟩ := htsupp hp
    exact ⟨q', hq', rfl⟩

end K55S5

namespace TwIL

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L)

section HNorm

variable (A : Type) [CommRing A] [Algebra K A]

theorem norm_algEquiv {S T : Type} [Ring S] [Ring T] [Algebra A S] [Algebra A T] (e : S ≃ₐ[A] T) (x : S) :
    Algebra.norm A (e x) = Algebra.norm A x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : (Algebra.lmul A T (e x) : T →ₗ[A] T) =
      (e.toLinearEquiv : S →ₗ[A] T) ∘ₗ (Algebra.lmul A S x : S →ₗ[A] S) ∘ₗ (e.toLinearEquiv.symm : T →ₗ[A] S) := by
    ext y
    simp [Algebra.coe_lmul_eq_mul]
  rw [h, LinearMap.det_conj]

theorem rcomm_tmul (a : A) (l : L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L (a ⊗ₜ[K] l) = l ⊗ₜ[K] a := by
  rfl

theorem rcomm_map (g : L ≃ₐ[K] L) (z : A ⊗[K] L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L (Algebra.TensorProduct.map (AlgHom.id K A) (g : L →ₐ[K] L) z) =
      AutomorphicForm.sigmaTensor K L A g (TensorProduct.RightActions.Algebra.TensorProduct.comm K A L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    rw [Algebra.TensorProduct.map_tmul, rcomm_tmul, rcomm_tmul]
    show (g : L →ₐ[K] L) l ⊗ₜ[K] (AlgHom.id K A) a = (Algebra.TensorProduct.map (g : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
    rw [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem algebraMap_norm_eq_prod_sigmaTensor (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) = ∏ g : L ≃ₐ[K] L, AutomorphicForm.sigmaTensor K L A g x := by
  classical
  set c := TensorProduct.RightActions.Algebra.TensorProduct.comm K A L with hc
  obtain ⟨z, rfl⟩ : ∃ z, x = c z := ⟨c.symm x, (c.apply_symm_apply x).symm⟩
  rw [norm_algEquiv, ← c.commutes, Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv K L A z, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [hc, rcomm_map]

theorem sigmaTensor_iterate (i : ℕ) (x : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[i] x = AutomorphicForm.sigmaTensor K L A (σ ^ i) x := by
  induction i generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show l ⊗ₜ[K] a = (Algebra.TensorProduct.map ((1 : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
      rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K A))
          ((Algebra.TensorProduct.map ((σ ^ n : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)) =
        (Algebra.TensorProduct.map ((σ * σ ^ n : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]

theorem list_prod_range_eq {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, Finset.prod_range_succ, ih]

theorem orderOf_eq_finrank' (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    orderOf σ = Module.finrank K L := by
  rw [← IsGalois.card_aut_eq_finrank, orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card]

theorem algebraMap_norm_eq_prod_range (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) =
      ((List.range (Module.finrank K L)).map fun i => (AutomorphicForm.sigmaTensor K L A σ)^[i] x).prod := by
  classical
  rw [algebraMap_norm_eq_prod_sigmaTensor, list_prod_range_eq]
  have hn : orderOf σ = Module.finrank K L := orderOf_eq_finrank' K L σ hgen
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Finset.range (Module.finrank K L) : Set ℕ) := by
    intro i hi j hj hij
    rw [Finset.coe_range, Set.mem_Iio, ← hn] at hi hj
    exact pow_injOn_Iio_orderOf hi hj hij
  have himg : (Finset.range (Module.finrank K L)).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank]
  rw [← himg, Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sigmaTensor_iterate]

end HNorm

section HNorm2

variable (A : Type) [CommRing A] [Algebra K A]

theorem sigmaGL_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.sigmaGL K L A σ (diagUnits2 x y) =
      diagUnits2 (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) x)
        (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.sigmaGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]

omit σ in
theorem diagUnits2_mul (x y x' y' : (L ⊗[K] A)ˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaGL_iterate_diagUnits2 (i : ℕ) (x y : (L ⊗[K] A)ˣ) :
    (AutomorphicForm.sigmaGL K L A σ)^[i] (diagUnits2 x y) =
      diagUnits2 ((Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] x)
        ((Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] y) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, sigmaGL_diagUnits2, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

theorem normString_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.normString K L A σ (diagUnits2 x y) =
      diagUnits2 (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] x).prod)
        (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] y).prod) := by
  unfold AutomorphicForm.normString
  induction Module.finrank K L with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil]
    apply Units.ext
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, List.prod_range_succ, ih, sigmaGL_iterate_diagUnits2,
      diagUnits2_mul]

omit σ in
theorem toTensorGL_diagUnits2 (a b : Aˣ) :
    AutomorphicForm.toTensorGL K L A (diagUnits2 a b) =
      diagUnits2 (Units.map (algebraMap A (L ⊗[K] A) : A →* L ⊗[K] A) a)
        (Units.map (algebraMap A (L ⊗[K] A) : A →* L ⊗[K] A) b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2,
      TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.includeRight_apply]

omit σ in
theorem val_list_prod_iterate_map (f : L ⊗[K] A →* L ⊗[K] A) (x : (L ⊗[K] A)ˣ) (m : ℕ) :
    ((((List.range m).map fun i => (Units.map f)^[i] x).prod : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      ((List.range m).map fun i => (⇑f)^[i] (x : L ⊗[K] A)).prod := by
  have hit : ∀ i, (((Units.map f)^[i] x : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (⇑f)^[i] (x : L ⊗[K] A) := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ih]
  induction m with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, Units.val_mul, ih, hit]

omit σ in
theorem algebraMap_tensor_injective : Function.Injective (algebraMap A (L ⊗[K] A)) := by
  have h : (algebraMap A (L ⊗[K] A) : A → L ⊗[K] A) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
    funext a
    rw [TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.includeRight_apply]
  rw [h]
  exact Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

theorem norm_eq_of_normString_diagUnits2 (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a b : Aˣ) (α β : (L ⊗[K] A)ˣ)
    (h : AutomorphicForm.normString K L A σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    Algebra.norm A (α : L ⊗[K] A) = a ∧ Algebra.norm A (β : L ⊗[K] A) = b := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2] at h
  have hv := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2] at hv
  have h00 := congrFun (congrFun hv 0) 0
  have h11 := congrFun (congrFun hv 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at h00 h11
  rw [val_list_prod_iterate_map, Units.coe_map] at h00 h11
  have h00' : ((List.range (Module.finrank K L)).map fun i =>
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (α : L ⊗[K] A)).prod = algebraMap A (L ⊗[K] A) a := h00
  have h11' : ((List.range (Module.finrank K L)).map fun i =>
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (β : L ⊗[K] A)).prod = algebraMap A (L ⊗[K] A) b := h11
  rw [← algebraMap_norm_eq_prod_range K L σ A hgen] at h00' h11'
  exact ⟨algebraMap_tensor_injective K L A h00', algebraMap_tensor_injective K L A h11'⟩

end HNorm2

theorem norm_of_normString_eq (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a t : (InfiniteAdeleRing K)ˣ) (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (h : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)))
    (u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
    Algebra.norm (InfiniteAdeleRing K) (1 : (L ⊗[K] InfiniteAdeleRing K)) -
        Algebra.norm (InfiniteAdeleRing K) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = 1 - (t : InfiniteAdeleRing K) := by
  obtain ⟨hα, hβ⟩ := norm_eq_of_normString_diagUnits2 K L σ (InfiniteAdeleRing K) hgen a (a * t) α β h
  have hNα : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) α = a := Units.ext (by rw [Units.coe_map]; exact hα)
  have hNβ : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) β = a * t := Units.ext (by rw [Units.coe_map]; exact hβ)
  have hu1 : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = 1 := (MonoidHom.mem_ker).mp u.1.2
  have hu2 : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = 1 := (MonoidHom.mem_ker).mp u.2.2
  have hr : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ))) = t := by
    rw [map_mul, map_inv, map_mul, map_mul, hNα, hNβ, hu1, hu2, mul_one, mul_one, inv_mul_cancel_left]
  have hval : Algebra.norm (InfiniteAdeleRing K) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = (t : InfiniteAdeleRing K) := by
    have := congrArg Units.val hr
    rw [Units.coe_map] at this
    exact this
  rw [map_one, hval]

end TwIL

end

set_option maxHeartbeats 8000000 in
open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦc : HasCompactSupport Φ)
    (hΦu : ∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))))
    (w : NumberField.InfinitePlace K) (w' : NumberField.InfinitePlace L) (hw'w : w'.comap (algebraMap K L) = w)
    (hw : w.IsReal) (hw' : w'.IsComplex) :
    ∃ A B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport A ∧ HasCompactSupport B ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), (∀ v : NumberField.InfinitePlace K, (t : InfiniteAdeleRing K) v ≠ 1) →
      ∀ (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
      ∀ (Mu : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker → ((L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K))),
        (∀ u, (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (Mu u y) - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * Mu u y =
              ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) • y) ∧
          (∀ y, Mu u (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y) =
              ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) • y)) →
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
          ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam) (θ.prod θ) ∧
        ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam ∂(θ.prod θ) =
          A ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
  classical

  obtain ⟨e, κ, hκ0, hmap, he1, hres⟩ :=
    AutomorphicForm.exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap K L σ hgen hdeg lam w w' hw'w hw hw'

  obtain ⟨C, hCc, hCmem⟩ := hΦu

  let zc : NumberField.mixedEmbedding.mixedSpace L → ℂ := fun X => X.2 ⟨w', hw'⟩
  have hzc : ContDiff ℝ (⊤ : ℕ∞) zc :=
    (contDiff_apply ℝ ℂ (⟨w', hw'⟩ : {v : NumberField.InfinitePlace L // v.IsComplex})).comp contDiff_snd

  have S1 : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ tsupport Φ, 2 * δ ≤ ‖zc (p 0)‖ := by
    have hpos : ∀ p ∈ tsupport Φ, 0 < ‖zc (p 0)‖ := by
      intro p hp
      obtain ⟨x, -, h0, -⟩ := hCmem p hp
      have hu : IsUnit (p 0) := by rw [h0]; exact LayerPlumbing.isUnit_iotaL K L (Units.isUnit _)
      exact norm_pos_iff.mpr (((LayerPlumbing.isUnit_mixedSpace_iff L (p 0)).mp hu).2 ⟨w', hw'⟩)
    by_cases hne : (tsupport Φ).Nonempty
    · have hcont : Continuous fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace L => ‖zc (p 0)‖ :=
        (hzc.continuous.comp (continuous_apply 0)).norm
      obtain ⟨p₀, hp₀, hmin⟩ := hΦc.exists_isMinOn hne hcont.continuousOn
      refine ⟨‖zc (p₀ 0)‖ / 2, by linarith [hpos p₀ hp₀], fun p hp => ?_⟩
      have := hmin hp
      simp only [Set.mem_setOf_eq] at this
      linarith
    · refine ⟨1, one_pos, fun p hp => ?_⟩
      exact absurd ⟨p, hp⟩ hne
  obtain ⟨δ, hδ, hδC⟩ := S1

  have S2 : ∃ η₁ η₂ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η₁ ∧ ContDiff ℝ (⊤ : ℕ∞) η₂ ∧
      (∀ s, δ ^ 2 ≤ s → η₁ s = 1) ∧ (∀ s, s ≤ δ ^ 2 / 4 → η₁ s = 0) ∧
      (∀ s, (2 * δ) ^ 2 ≤ s → η₂ s = 1) ∧ (∀ s, s ≤ δ ^ 2 → η₂ s = 0) := by
    have hd1 : 0 < δ ^ 2 - δ ^ 2 / 4 := by nlinarith
    have hd2 : 0 < (2 * δ) ^ 2 - δ ^ 2 := by nlinarith
    refine ⟨fun s => Real.smoothTransition ((s - δ ^ 2 / 4) / (δ ^ 2 - δ ^ 2 / 4)),
      fun s => Real.smoothTransition ((s - δ ^ 2) / ((2 * δ) ^ 2 - δ ^ 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    · exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    · intro s hs; exact Real.smoothTransition.one_of_one_le ((one_le_div hd1).mpr (by linarith))
    · intro s hs; exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hd1.le)
    · intro s hs; exact Real.smoothTransition.one_of_one_le ((one_le_div hd2).mpr (by linarith))
    · intro s hs; exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hd2.le)
  obtain ⟨η₁, η₂, hη₁, hη₂, hη₁one, hη₁zero, hη₂one, hη₂zero⟩ := S2

  let ϱ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ := fun q => ((η₁ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * (zc (q 0))⁻¹ * zc (q 1)
  have S3 : ContDiff ℝ (⊤ : ℕ∞) ϱ := by
    have hz0 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) => zc (q 0)) := hzc.comp (contDiff_apply ℝ _ (0 : Fin 2))
    have hz1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) => zc (q 1)) := hzc.comp (contDiff_apply ℝ _ (1 : Fin 2))
    have hη : ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) => ((η₁ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hη₁.comp ((contDiff_norm_sq ℝ).comp hz0))
    refine contDiff_iff_contDiffAt.mpr fun q => ?_
    by_cases h0 : ‖zc (q 0)‖ < δ / 2
    ·
      have hopen : IsOpen {q' : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) | ‖zc (q' 0)‖ < δ / 2} :=
        isOpen_lt (hz0.continuous.norm) continuous_const
      have hev : ϱ =ᶠ[nhds q] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds h0] with q' hq'
        show ((η₁ (‖zc (q' 0)‖ ^ 2) : ℝ) : ℂ) * (zc (q' 0))⁻¹ * zc (q' 1) = 0
        have : ‖zc (q' 0)‖ ^ 2 ≤ δ ^ 2 / 4 := by
          have hn := norm_nonneg (zc (q' 0))
          have hq'' : ‖zc (q' 0)‖ < δ / 2 := hq'
          nlinarith
        rw [hη₁zero _ this, Complex.ofReal_zero, zero_mul, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hne : zc (q 0) ≠ 0 := by
        intro h; rw [h, norm_zero] at h0; linarith
      exact ((hη.contDiffAt.mul (hz0.contDiffAt.inv hne)).mul hz1.contDiffAt)

  let g : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))) → ℂ := fun qX => Φ ![qX.1 0, qX.1 1, e.symm qX.2]
  have S4 : ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g := by

    let Afun : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))) → (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) := fun qX => ![qX.1 0, qX.1 1, e.symm qX.2]
    let Ainv : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))) := fun p => (![p 0, p 1], e (p 2))
    have hAc : Continuous Afun :=
      ((continuous_apply 0).comp continuous_fst).matrixVecCons
        (((continuous_apply 1).comp continuous_fst).matrixVecCons
          ((e.symm.continuous.comp continuous_snd).matrixVecCons continuous_const))
    have hAic : Continuous Ainv :=
      Continuous.prodMk ((continuous_apply 0).matrixVecCons ((continuous_apply 1).matrixVecCons continuous_const))
        (e.continuous.comp (continuous_apply 2))
    let AH : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))) ≃ₜ (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) :=
      { toFun := Afun, invFun := Ainv,
        left_inv := fun qX => by
          obtain ⟨q, X⟩ := qX
          simp only [Afun, Ainv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
            Matrix.tail_cons, ContinuousLinearEquiv.apply_symm_apply, Prod.mk.injEq, and_true]
          funext i; fin_cases i <;> rfl
        right_inv := fun p => by
          simp only [Afun, Ainv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            ContinuousLinearEquiv.symm_apply_apply]
          funext i; fin_cases i <;> rfl
        continuous_toFun := hAc, continuous_invFun := hAic }
    have hgA : g = Φ ∘ AH := rfl
    refine ⟨?_, ?_⟩
    · refine hΦ.comp (contDiff_pi.mpr fun i => ?_)
      fin_cases i
      · show ContDiff ℝ _ (fun x : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))) => x.1 0)
        exact (contDiff_apply ℝ _ (0 : Fin 2)).comp contDiff_fst
      · show ContDiff ℝ _ (fun x : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))) => x.1 1)
        exact (contDiff_apply ℝ _ (1 : Fin 2)).comp contDiff_fst
      · show ContDiff ℝ _ (fun x : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))) => e.symm x.2)
        exact e.symm.contDiff.comp contDiff_snd
    · rw [hgA]; exact hΦc.comp_homeomorph AH

  haveI hVH : ((volume : Measure ({v : NumberField.InfinitePlace L // v.IsReal} → ℝ)).prod
      (volume : Measure ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨A₀, B₀, hA₀, hB₀, hcore⟩ :=
    MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_one_sub_normSq_add_normSq_conj_add_conj_mul_eq_add_abs_mul_of_hasCompactSupport
      ((volume : Measure ({v : NumberField.InfinitePlace L // v.IsReal} → ℝ)).prod
        (volume : Measure ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)))
      g S4.1 S4.2 ϱ S3

  obtain ⟨χ, hχ, hχc, hχone, hχU⟩ := LayerPlumbing.exists_cutoff K L Φ hΦc ⟨C, hCc, hCmem⟩
  obtain ⟨C', hC'c, hC'mem⟩ := LayerPlumbing.exists_unit_carrier K L χ hχc hχU

  let G₁ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ := fun q => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * A₀ q
  let G₂ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ := fun q => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * B₀ q
  have hG : ∀ F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F →
      ContDiff ℝ (⊤ : ℕ∞) (fun q => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * F q) ∧
      HasCompactSupport (fun q => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * F q) ∧
      (∃ C' : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C' ∧
        ∀ p ∈ tsupport (fun q => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * F q), ∃ x ∈ C',
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((x.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧ p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((x.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) := by
    intro F hF
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ)) := by
      refine (Complex.ofRealCLM.contDiff.comp ?_)
      refine hχ.mul (hη₂.comp ?_)
      exact (contDiff_norm_sq ℝ).comp (hzc.comp (contDiff_apply ℝ _ (0 : Fin 2)))
    have hfe : (fun q : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ)) =
        Complex.ofReal ∘ ((fun q => χ q) * (fun q => η₂ (‖zc (q 0)‖ ^ 2))) := rfl
    have hcs : HasCompactSupport (fun q : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ)) := by
      rw [hfe]; exact (hχc.mul_right).comp_left Complex.ofReal_zero
    have hts : tsupport (fun q : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ)) ⊆ tsupport χ := by
      rw [hfe]; exact (tsupport_comp_subset Complex.ofReal_zero _).trans (tsupport_mul_subset_left)
    have hsub : tsupport (fun q => ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * F q) ⊆ tsupport χ :=
      (tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans hts))
    exact ⟨(hsm.mul contDiff_const).mul hF, (hcs.mul_right).mul_right, C', hC'c, fun p hp => hC'mem _ hsub p hp⟩
  obtain ⟨F₁, hF₁, hF₁c, hF₁u, hF₁eq⟩ := AutomorphicForm.exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff K L θ G₁ (hG A₀ hA₀).1 (hG A₀ hA₀).2.1 (hG A₀ hA₀).2.2
  obtain ⟨F₂, hF₂, hF₂c, hF₂u, hF₂eq⟩ := AutomorphicForm.exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff K L θ G₂ (hG B₀ hB₀).1 (hG B₀ hB₀).2.1 (hG B₀ hB₀).2.2

  let rp : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) := fun p => ![p 1, p 1 * p 0]
  have S6 : ∀ F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport F, ∃ q ∈ Ca, p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) →
      ContDiff ℝ (⊤ : ℕ∞) (F ∘ rp) ∧ HasCompactSupport (F ∘ rp) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport (F ∘ rp), ∃ q ∈ Ca, p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) := by
    intro F hF hFc hFu
    exact K55S5.reparam_norm_coords K F hF hFc hFu
  obtain ⟨hA, hAc, ⟨CaA, hCaA, hCaAm⟩⟩ := S6 F₁ hF₁ hF₁c hF₁u
  obtain ⟨hB, hBc, ⟨CaB, hCaB, hCaBm⟩⟩ := S6 F₂ hF₂ hF₂c hF₂u
  refine ⟨F₁ ∘ rp, F₂ ∘ rp, hA, hB, hAc, hBc, ⟨CaA ∪ CaB, hCaA.union hCaB, fun p hp => ?_⟩, ?_⟩
  · rcases hp with h | h
    · obtain ⟨q, hq, e⟩ := hCaAm p h; exact ⟨q, Set.mem_union_left _ hq, e⟩
    · obtain ⟨q, hq, e⟩ := hCaBm p h; exact ⟨q, Set.mem_union_right _ hq, e⟩

  intro a t ht α β hαβ Mu hMu
  have hunit : IsUnit ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) := by
    refine Pi.isUnit_iff.mpr fun v => isUnit_iff_ne_zero.mpr ?_
    show (1 : v.Completion) - (t : InfiniteAdeleRing K) v ≠ 0
    exact sub_ne_zero.mpr (ht v).symm
  have hNr : ∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
      ((hunit.unit : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) := by
    intro u
    have h := TwIL.norm_of_normString_eq K L σ hgen a t α β hαβ u
    rw [map_one] at h
    rw [hunit.unit_spec, ← h]

  have hresu := fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
    hres (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) hunit.unit (hNr u) (Mu u)
      (fun y => by rw [(hMu u).1 y, hunit.unit_spec]) (fun y => by rw [(hMu u).2 y, hunit.unit_spec])

  have S7 : ∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
      ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam =
        G₁ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] +
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            G₂ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] := by
    intro u

    set q : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) := ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] with hq
    have hq0 : q 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) := by simp [hq]
    have hq1 : q 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) := by simp [hq]

    let ζ : (L ⊗[K] InfiniteAdeleRing K) →+* ℂ :=
      (Pi.evalRingHom _ (⟨w', hw'⟩ : {v : NumberField.InfinitePlace L // v.IsComplex})).comp
        ((RingHom.snd _ _).comp ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).toRingHom.comp
          (AutomorphicForm.archIdentEquiv K L).toRingHom))
    have hζ : ∀ y : (L ⊗[K] InfiniteAdeleRing K), zc (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)) = ζ y := fun y => rfl
    obtain ⟨hres1, hres2⟩ := hresu u

    rw [hunit.unit_spec] at hres2

    have hζinv : ζ (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = (ζ ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    have hϱu : zc (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) = (zc (q 0))⁻¹ * zc (q 1) := by
      rw [hq0, hq1, hζ, hζ, hζ, Units.val_mul, map_mul, hζinv]

    have hcar : ∀ m, Φ ![q 0, q 1, m] ≠ 0 → χ q = 1 ∧ 2 * δ ≤ ‖zc (q 0)‖ := by
      intro m hm
      have hp := subset_tsupport _ hm
      have h1 := hχone _ hp
      have h2 := hδC _ hp
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1 h2
      refine ⟨?_, h2⟩
      rw [show (![q 0, q 1] : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L)) = q from funext fun i => by fin_cases i <;> rfl] at h1
      exact h1
    have hinner0 : (∀ m, Φ ![q 0, q 1, m] = 0) →
        ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam = 0 := by
      intro h0
      rw [← hq0, ← hq1]
      simp [h0]
    by_cases hδ1 : δ ^ 2 ≤ ‖zc (q 0)‖ ^ 2
    ·
      have hϱq : ϱ q = zc (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) := by
        show ((η₁ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * (zc (q 0))⁻¹ * zc (q 1) = _
        rw [hη₁one _ hδ1, Complex.ofReal_one, one_mul, hϱu]
      have hoff : |1 - ‖ϱ q‖ ^ 2| = ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ := by
        rw [hϱq, ← hres2]

      have hH := NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L
      let eH : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ NumberField.mixedEmbedding.mixedSpace L := (AutomorphicForm.archIdentHomeomorph K L).trans (hH.homeomorph _)
      let eM : (L ⊗[K] InfiniteAdeleRing K) ≃ᵐ (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))) := (eH.trans e.toHomeomorph).toMeasurableEquiv
      have heM : ∀ y, eM y = e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)) := fun y => rfl
      have hcv : ∀ G : ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)) → ℂ,
          ∫ y, G (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))) ∂lam =
            ((κ : ℝ) : ℂ) * ∫ X, G X ∂((volume : Measure ℂ).prod
              ((volume : Measure ({v : NumberField.InfinitePlace L // v.IsReal} → ℝ)).prod
                (volume : Measure ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)))) := by
        intro G
        have h1 := integral_map_equiv (μ := lam) eM G
        simp only [heM] at h1
        rw [← h1, show (⇑eM : (L ⊗[K] InfiniteAdeleRing K) → ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))) = fun y => e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)) from funext heM, hmap,
          show ((κ • ((volume : Measure ℂ).prod ((volume : Measure ({v : NumberField.InfinitePlace L // v.IsReal} → ℝ)).prod
            (volume : Measure ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ))))) : Measure _) =
            ((κ : ENNReal) • _) from rfl,
          integral_smul_measure, ENNReal.coe_toReal, RCLike.real_smul_eq_coe_mul]
        rfl
      have hid : ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam =
          ((κ : ℝ) : ℂ) * (A₀ q + ((|1 - ‖ϱ q‖ ^ 2| : ℝ) : ℂ) * B₀ q) := by
        rw [← (hcore q).2, ← hcv]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show _ = Φ ![q 0, q 1, e.symm (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)))] * _
        beta_reduce
        have hϱq' : (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))).2 ⟨w', hw'⟩ = ϱ q := hϱq.symm
        rw [ContinuousLinearEquiv.symm_apply_apply, hq0, hq1, hres1 y, ← hoff, sq_abs, he1 y, hϱq']

      by_cases hz : ∀ m, Φ ![q 0, q 1, m] = 0
      · rw [hinner0 hz]
        have : A₀ q + ((|1 - ‖ϱ q‖ ^ 2| : ℝ) : ℂ) * B₀ q = 0 := by
          have := hid; rw [hinner0 hz] at this
          rcases mul_eq_zero.mp this.symm with h | h
          · exact absurd (by exact_mod_cast h : (κ : ℝ) = 0) (by exact_mod_cast hκ0)
          · exact h
        show (0 : ℂ) = ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * A₀ q +
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            (((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * B₀ q)
        rw [← hoff]
        linear_combination (-(((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ))) * this
      · push Not at hz
        obtain ⟨m, hm⟩ := hz
        obtain ⟨hχ1, h2δ⟩ := hcar m hm
        have hη2 : η₂ (‖zc (q 0)‖ ^ 2) = 1 := by
          apply hη₂one
          nlinarith [h2δ, hδ]
        rw [hid]
        show _ = ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * A₀ q +
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            (((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * B₀ q)
        rw [hχ1, hη2, ← hoff]
        push_cast
        ring
    ·
      push Not at hδ1
      have hη2 : η₂ (‖zc (q 0)‖ ^ 2) = 0 := hη₂zero _ hδ1.le
      have hz : ∀ m, Φ ![q 0, q 1, m] = 0 := by
        intro m
        by_contra hm
        obtain ⟨-, h2δ⟩ := hcar m hm
        nlinarith [h2δ, hδ, hδ1]
      rw [hinner0 hz]
      show (0 : ℂ) = ((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * A₀ q +
        ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
          (((χ q * η₂ (‖zc (q 0)‖ ^ 2) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * B₀ q)
      rw [hη2]; push_cast; ring
  obtain ⟨hI1, hE1⟩ := hF₁eq α β
  obtain ⟨hI2, hE2⟩ := hF₂eq α β
  obtain ⟨hα, hβ⟩ := TwIL.norm_eq_of_normString_diagUnits2 K L σ (InfiniteAdeleRing K) hgen a (a * t) α β hαβ
  refine ⟨?_, ?_⟩
  ·
    have : (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
        ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam) =
        fun u => G₁ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] +
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            G₂ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] := funext S7
    rw [this]
    exact hI1.add (hI2.const_mul _)
  · rw [integral_congr_ae (Filter.Eventually.of_forall S7), integral_add hI1 (hI2.const_mul _), integral_const_mul,
      ← hE1, ← hE2]
    simp only [Function.comp_apply, rp, hα, hβ, Units.val_mul, map_mul]
    congr 2 <;> (funext i; fin_cases i <;> simp [mul_comm])

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_mul_of_isComplex_place
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_mul_of_isComplex_place (solution)
