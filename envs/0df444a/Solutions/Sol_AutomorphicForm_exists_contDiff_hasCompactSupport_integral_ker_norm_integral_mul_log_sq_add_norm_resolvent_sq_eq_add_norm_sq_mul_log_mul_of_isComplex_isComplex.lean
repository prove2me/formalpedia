-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f3218173-cd6b-5448-af4c-9fb66512b69b

import Mathlib
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_norm_fst_add_of_isComplex_of_isComplex_comap
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_NumberField_InfiniteAdeleRing_isEmbedding_units_val
import Theorems.Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open scoped Classical

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

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

namespace LayerPlumbing

variable (K : Type) [Field K] [NumberField K]

theorem kside
    (F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F)
    (hFu : ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport F, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)])
    (κ : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => κ * F ![q 1, q 1 * q 0]) ∧
    HasCompactSupport (fun q : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => κ * F ![q 1, q 1 * q 0]) ∧
    (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport (fun q : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => κ * F ![q 1, q 1 * q 0]), ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
    ∀ a t : (InfiniteAdeleRing K)ˣ,
      (fun q : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => κ * F ![q 1, q 1 * q 0])
        ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] =
        κ * F ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((a * t : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] := by
  classical
  set ιK : InfiniteAdeleRing K → NumberField.mixedEmbedding.mixedSpace K :=
    fun x => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x with hιK
  have hιKc : Continuous ιK := (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K).continuous

  set m : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) :=
    fun q => ![q 1, q 1 * q 0] with hm
  have hm1 : ContDiff ℝ (⊤ : ℕ∞) fun q : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => q 1 := contDiff_apply ℝ _ 1
  have hm0 : ContDiff ℝ (⊤ : ℕ∞) fun q : Fin 2 → NumberField.mixedEmbedding.mixedSpace K => q 0 := contDiff_apply ℝ _ 0
  have hms : ContDiff ℝ (⊤ : ℕ∞) m := by
    refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · exact hm1
    · exact hm1.mul hm0
  have hmc : Continuous m := hms.continuous
  obtain ⟨Ca, hCa, hCar⟩ := hFu

  set Ca' : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) := (fun q => (q.1⁻¹ * q.2, q.1)) '' Ca with hCa'
  have hCa'c : IsCompact Ca' := hCa.image (by fun_prop)
  have hcarr : ∀ p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K, m p ∈ tsupport F → ∃ q ∈ Ca',
      p = ![ιK ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), ιK ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hCar _ hp
    have h1 : p 1 = ιK (q.1 : InfiniteAdeleRing K) := by
      have := congr_fun hpq 0; simpa [hm, hιK] using this
    have h10 : p 1 * p 0 = ιK (q.2 : InfiniteAdeleRing K) := by
      have := congr_fun hpq 1; simpa [hm, hιK] using this
    have h0 : p 0 = ιK (((q.1⁻¹ * q.2 : (InfiniteAdeleRing K)ˣ)) : InfiniteAdeleRing K) := by
      have : p 0 = ιK ((q.1⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * (p 1 * p 0) := by
        rw [← mul_assoc, h1, ← map_mul, Units.inv_mul, map_one, one_mul]
      rw [this, h10, ← map_mul, Units.val_mul]
    refine ⟨(q.1⁻¹ * q.2, q.1), ⟨q, hq, rfl⟩, ?_⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have htsub : tsupport (fun q => κ * F (m q)) ⊆ m ⁻¹' tsupport F := by
    refine (tsupport_mul_subset_right (f := fun _ => κ) (g := fun q => F (m q))).trans ?_
    exact tsupport_comp_subset_preimage F hmc
  refine ⟨contDiff_const.mul (hF.comp hms), ?_, ⟨Ca', hCa'c, fun p hp => hcarr p (htsub hp)⟩, fun a t => ?_⟩
  ·
    refine IsCompact.of_isClosed_subset (hCa'c.image (f := fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      (![ιK ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), ιK ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] :
        Fin 2 → NumberField.mixedEmbedding.mixedSpace K)) ?_) (isClosed_tsupport _) ?_
    · refine continuous_pi fun i => ?_
      fin_cases i
      · exact hιKc.comp (Units.continuous_val.comp continuous_fst)
      · exact hιKc.comp (Units.continuous_val.comp continuous_snd)
    · intro p hp
      obtain ⟨q, hq, hpq⟩ := hcarr p (htsub hp)
      exact ⟨q, hq, hpq.symm⟩
  · show κ * F (m ![ιK (t : InfiniteAdeleRing K), ιK (a : InfiniteAdeleRing K)]) = κ * F _
    congr 2
    funext i
    fin_cases i
    · rfl
    · show ιK (a : InfiniteAdeleRing K) * ιK (t : InfiniteAdeleRing K) =
        NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (((a * t : (InfiniteAdeleRing K)ˣ)) : InfiniteAdeleRing K)
      rw [Units.val_mul, map_mul]

end LayerPlumbing

namespace LayerPlumbing

variable (L : Type) [Field L] [NumberField L]

theorem contDiffAt_inv_mixedSpace {x : NumberField.mixedEmbedding.mixedSpace L} (hx : IsUnit x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : NumberField.mixedEmbedding.mixedSpace L => y⁻¹) x := by
  rw [isUnit_mixedSpace_iff] at hx
  obtain ⟨h1, h2⟩ := hx
  show ContDiffAt ℝ (⊤ : ℕ∞)
    (fun y : NumberField.mixedEmbedding.mixedSpace L => ((fun w => (y.1 w)⁻¹), (fun w => (y.2 w)⁻¹))) x
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun w => ?_) (contDiffAt_pi.mpr fun w => ?_)
  · have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : NumberField.mixedEmbedding.mixedSpace L => y.1 w) x :=
      (contDiffAt_apply ℝ ℝ w x.1).comp x contDiffAt_fst
    exact (contDiffAt_inv ℝ (h1 w)).comp x h
  · have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : NumberField.mixedEmbedding.mixedSpace L => y.2 w) x :=
      (contDiffAt_apply ℝ ℂ w x.2).comp x contDiffAt_snd
    exact (contDiffAt_inv ℝ (h2 w)).comp x h

omit L in

theorem contDiff_cutoff_smul {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : E → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (U : Set E) (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
    (f : E → F) (hf : ∀ x ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul (hf x hx)
  · have hx' : x ∉ tsupport χ := fun h => hx (hχU h)
    have h0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    have hev : (fun x => χ x • f x) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [h0] with y hy
      rw [hy, Pi.zero_apply, zero_smul]
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hev

end LayerPlumbing

namespace LayerPlumbing

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit L in
theorem isUnit_infiniteAdeleRing_iff (x : InfiniteAdeleRing K) :
    IsUnit x ↔ ∀ v : NumberField.InfinitePlace K, x v ≠ 0 := by
  rw [show IsUnit x ↔ ∀ v : NumberField.InfinitePlace K, IsUnit (x v) from Pi.isUnit_iff]
  exact forall_congr' fun v => isUnit_iff_ne_zero

omit K in

theorem inv_mul_cancel_of_isUnit_mixedSpace {x : NumberField.mixedEmbedding.mixedSpace L} (hx : IsUnit x) :
    x⁻¹ * x = 1 := by
  rw [isUnit_mixedSpace_iff] at hx
  obtain ⟨h1, h2⟩ := hx
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · show (x.1 w)⁻¹ * x.1 w = 1
    exact inv_mul_cancel₀ (h1 w)
  · show (x.2 w)⁻¹ * x.2 w = 1
    exact inv_mul_cancel₀ (h2 w)

theorem inv_iotaL_mul_iotaL (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ) :
    (iotaL K L (α : L ⊗[K] InfiniteAdeleRing K))⁻¹ * iotaL K L (β : L ⊗[K] InfiniteAdeleRing K) =
      iotaL K L (((α⁻¹ * β : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : L ⊗[K] InfiniteAdeleRing K) := by
  have hu : IsUnit (iotaL K L (α : L ⊗[K] InfiniteAdeleRing K)) := isUnit_iotaL K L (Units.isUnit α)
  have h1 : iotaL K L (α : L ⊗[K] InfiniteAdeleRing K) * iotaL K L ((α⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) = 1 := by
    rw [← iotaLRingEquiv_apply, ← iotaLRingEquiv_apply, ← map_mul, Units.mul_inv, map_one]
  have h2 : (iotaL K L (α : L ⊗[K] InfiniteAdeleRing K))⁻¹ =
      iotaL K L ((α⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) := by
    calc (iotaL K L (α : L ⊗[K] InfiniteAdeleRing K))⁻¹
        = (iotaL K L (α : L ⊗[K] InfiniteAdeleRing K))⁻¹ * (iotaL K L (α : L ⊗[K] InfiniteAdeleRing K) *
            iotaL K L ((α⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)) := by rw [h1, mul_one]
      _ = iotaL K L ((α⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) := by
          rw [← mul_assoc, inv_mul_cancel_of_isUnit_mixedSpace L hu, one_mul]
  rw [h2, ← iotaLRingEquiv_apply, ← iotaLRingEquiv_apply, ← iotaLRingEquiv_apply, ← map_mul, Units.val_mul]

end LayerPlumbing

namespace LayerPlumbing

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem iotaLHomeomorph_symm_apply (x : NumberField.mixedEmbedding.mixedSpace L) :
    (iotaLHomeomorph K L).symm x = (iotaLRingEquiv K L).symm x := by
  apply (iotaLHomeomorph K L).injective
  rw [Homeomorph.apply_symm_apply]
  exact ((iotaLRingEquiv K L).apply_symm_apply x).symm

theorem continuous_iotaL_symm : Continuous fun x => (iotaLRingEquiv K L).symm x := by
  have h : (fun x => (iotaLRingEquiv K L).symm x) = fun x => (iotaLHomeomorph K L).symm x :=
    funext fun x => (iotaLHomeomorph_symm_apply K L x).symm
  rw [h]; exact (iotaLHomeomorph K L).symm.continuous

def normCoord (P : NumberField.mixedEmbedding.mixedSpace L) : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
    (Algebra.norm (InfiniteAdeleRing K) ((iotaLRingEquiv K L).symm P))

theorem normCoord_iotaL (x : L ⊗[K] InfiniteAdeleRing K) :
    normCoord K L (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L x)) =
      NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (Algebra.norm (InfiniteAdeleRing K) x) := by
  show normCoord K L (iotaLRingEquiv K L x) = _
  simp only [normCoord, RingEquiv.symm_apply_apply]

theorem contDiff_normCoord : ContDiff ℝ (⊤ : ℕ∞) (normCoord K L) := by
  classical
  haveI hTR := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  let b := Module.Free.chooseBasis (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  have hLc : Continuous (Algebra.leftMulMatrix b : L ⊗[K] InfiniteAdeleRing K → Matrix _ _ (InfiniteAdeleRing K)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hιKc : Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K → _) :=
    (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K).continuous

  have hent : ∀ i j : Module.Free.ChooseBasisIndex (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K),
      ∃ T : NumberField.mixedEmbedding.mixedSpace L →L[ℝ] NumberField.mixedEmbedding.mixedSpace K,
        ∀ P, T P = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
          (Algebra.leftMulMatrix b ((iotaLRingEquiv K L).symm P) i j) := by
    intro i j
    let f : NumberField.mixedEmbedding.mixedSpace L →+ NumberField.mixedEmbedding.mixedSpace K :=
      { toFun := fun P => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
          (Algebra.leftMulMatrix b ((iotaLRingEquiv K L).symm P) i j)
        map_zero' := by simp only [map_zero, Matrix.zero_apply]
        map_add' := fun P Q => by simp only [map_add, Matrix.add_apply] }
    have hf : Continuous f := by
      show Continuous fun P => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
        (Algebra.leftMulMatrix b ((iotaLRingEquiv K L).symm P) i j)
      refine hιKc.comp ?_
      have h1 : Continuous fun M : Matrix (Module.Free.ChooseBasisIndex (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K))
          (Module.Free.ChooseBasisIndex (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)) (InfiniteAdeleRing K) => M i j :=
        (continuous_apply j).comp (continuous_apply i)
      exact h1.comp (hLc.comp (continuous_iotaL_symm K L))
    exact ⟨f.toRealLinearMap hf, fun P => rfl⟩
  choose T hT using hent
  have hΨ : normCoord K L = fun P => Matrix.det fun i j => T i j P := by
    funext P
    simp only [normCoord]
    rw [Algebra.norm_eq_matrix_det b, ← RingEquiv.coe_toRingHom, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    rw [hT, RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.coe_toRingHom]
  rw [hΨ]
  have hdet : (fun P => Matrix.det fun i j => T i j P) =
      fun P => ∑ σ : Equiv.Perm (Module.Free.ChooseBasisIndex (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)),
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : NumberField.mixedEmbedding.mixedSpace K) * ∏ i, T (σ i) i P := by
    funext P; rw [Matrix.det_apply']
  rw [hdet]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => (T (σ i) i).contDiff)

omit L in

theorem norm_ringEquiv_mixedSpace_snd (x : InfiniteAdeleRing K) (w : NumberField.InfinitePlace K) (hw : w.IsComplex) :
    ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x).2 ⟨w, hw⟩‖ = ‖NumberField.AdelicLevel.archEval K w x‖ := by
  rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show ‖NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)‖ = ‖x w‖
  exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

end LayerPlumbing

end

namespace A5RN
open AutomorphicForm

section generic
variable {R : Type*} [CommRing R]

theorem val_mul_apply (x y : GL (Fin 2) R) (i j : Fin 2) :
    ((x * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (x : Matrix (Fin 2) (Fin 2) R) i 0 * (y : Matrix (Fin 2) (Fin 2) R) 0 j +
        (x : Matrix (Fin 2) (Fin 2) R) i 1 * (y : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

def IsDiag (x : GL (Fin 2) R) : Prop :=
  (x : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) R) 1 0 = 0

theorem offdiag_eq_zero_of_commute (T t : GL (Fin 2) R)
    (hT01 : (T : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hreg : IsUnit ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1))
    (hc : T * t = t * T) : IsDiag t := by
  have hv := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) hc
  have e01 := congrFun (congrFun hv 0) 1
  have e10 := congrFun (congrFun hv 1) 0
  try simp only [] at e01 e10
  rw [val_mul_apply, val_mul_apply, hT01, zero_mul, add_zero, mul_zero, zero_add] at e01
  rw [val_mul_apply, val_mul_apply, hT10, zero_mul, zero_add, mul_zero, add_zero] at e10
  constructor
  · have h : ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        (t : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by
      rw [sub_mul, e01, mul_comm, sub_self]
    exact (hreg.mul_right_eq_zero).mp h
  · have h : ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        (t : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
      rw [sub_mul, e10, mul_comm, sub_self]
    exact (hreg.mul_right_eq_zero).mp h

theorem isUnit_sub_of_isRegularSemisimple (T : GL (Fin 2) R)
    (hT01 : (T : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hreg : IsRegularSemisimple T) :
    IsUnit ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  have h : Matrix.trace (T : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (T : Matrix (Fin 2) (Fin 2) R) =
      ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) *
        ((T : Matrix (Fin 2) (Fin 2) R) 0 0 - (T : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two, hT01, hT10]; ring
  have h2 : IsUnit (Matrix.trace (T : Matrix (Fin 2) (Fin 2) R) ^ 2 -
      4 * Matrix.det (T : Matrix (Fin 2) (Fin 2) R)) := hreg
  rw [h] at h2
  exact (IsUnit.mul_iff.mp h2).1

theorem diag_comm {x y : GL (Fin 2) R} (hx : IsDiag x) (hy : IsDiag y) : x * y = y * x := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, val_mul_apply, hx.1, hy.1, hx.2, hy.2, mul_zero, zero_mul, add_zero]
    exact mul_comm _ _
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, val_mul_apply, hx.1, hy.1, mul_zero, zero_mul, add_zero]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, val_mul_apply, hx.2, hy.2, mul_zero, zero_mul, add_zero]
  · simp only [Fin.isValue, Fin.mk_one, val_mul_apply, hx.1, hy.1, hx.2, hy.2, mul_zero, zero_mul, zero_add]
    exact mul_comm _ _

theorem isDiag_mul {x y : GL (Fin 2) R} (hx : IsDiag x) (hy : IsDiag y) : IsDiag (x * y) := by
  constructor
  · rw [val_mul_apply, hx.1, hy.1, mul_zero, zero_mul, add_zero]
  · rw [val_mul_apply, hx.2, hy.2, mul_zero, zero_mul, add_zero]

theorem isUnit_diag_entries {x : GL (Fin 2) R} (hx : IsDiag x) :
    IsUnit ((x : Matrix (Fin 2) (Fin 2) R) 0 0) ∧ IsUnit ((x : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  have hdet : IsUnit (x : Matrix (Fin 2) (Fin 2) R).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  rw [Matrix.det_fin_two, hx.1, zero_mul, sub_zero] at hdet
  exact ⟨isUnit_of_mul_isUnit_left hdet, isUnit_of_mul_isUnit_right hdet⟩

theorem isDiag_inv {x : GL (Fin 2) R} (hx : IsDiag x) : IsDiag x⁻¹ := by
  obtain ⟨h00, h11⟩ := isUnit_diag_entries hx
  have hone := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) (mul_inv_cancel x)
  have e01 := congrFun (congrFun hone 0) 1
  have e10 := congrFun (congrFun hone 1) 0
  try simp only [] at e01 e10
  rw [val_mul_apply, hx.1, zero_mul, add_zero, Units.val_one, Matrix.one_apply_ne (by decide)] at e01
  rw [val_mul_apply, hx.2, zero_mul, zero_add, Units.val_one, Matrix.one_apply_ne (by decide)] at e10
  exact ⟨(h00.mul_right_eq_zero).mp e01, (h11.mul_right_eq_zero).mp e10⟩

def mkDiag (a b : Rˣ) : GL (Fin 2) R where
  val := !![(a : R), 0; 0, (b : R)]
  inv := !![((a⁻¹ : Rˣ) : R), 0; 0, ((b⁻¹ : Rˣ) : R)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem mkDiag_apply00 (a b : Rˣ) :
    ((mkDiag a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = a := rfl
@[scoped simp] theorem mkDiag_apply01 (a b : Rˣ) :
    ((mkDiag a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := rfl
@[scoped simp] theorem mkDiag_apply10 (a b : Rˣ) :
    ((mkDiag a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := rfl
@[scoped simp] theorem mkDiag_apply11 (a b : Rˣ) :
    ((mkDiag a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = b := rfl

theorem coe_mkDiag_inv (a b : Rˣ) :
    (((mkDiag a b)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![((a⁻¹ : Rˣ) : R), 0; 0, ((b⁻¹ : Rˣ) : R)] :=
  rfl

theorem mkDiag_inv_apply00 (a b : Rˣ) :
    (((mkDiag a b)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = ((a⁻¹ : Rˣ) : R) := rfl
theorem mkDiag_inv_apply11 (a b : Rˣ) :
    (((mkDiag a b)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = ((b⁻¹ : Rˣ) : R) := rfl

theorem isDiag_mkDiag (a b : Rˣ) : IsDiag (mkDiag a b) := ⟨rfl, rfl⟩

end generic

theorem weight_diag_mul {F : Type*} [NormedField F] (d y : GL (Fin 2) F) (hd : IsDiag d) :
    LocalWeight.weight (d * y) = LocalWeight.weight y := by
  have hdet : (d : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have hdet' : (d : Matrix (Fin 2) (Fin 2) F).det =
      (d : Matrix (Fin 2) (Fin 2) F) 0 0 * (d : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.det_fin_two, hd.1, hd.2, mul_zero, sub_zero]
  rw [hdet'] at hdet
  obtain ⟨h0, h1⟩ := mul_ne_zero_iff.mp hdet
  have n0 : 0 < ‖(d : Matrix (Fin 2) (Fin 2) F) 0 0‖ := norm_pos_iff.mpr h0
  have n1 : 0 < ‖(d : Matrix (Fin 2) (Fin 2) F) 1 1‖ := norm_pos_iff.mpr h1
  unfold LocalWeight.weight AdelicHeight.rowMaxNorm
  simp only [val_mul_apply, hd.1, hd.2, zero_mul, add_zero, zero_add, norm_mul, Units.val_mul, Matrix.det_mul,
    hdet']
  rw [← mul_max_of_nonneg _ _ n0.le, ← mul_max_of_nonneg _ _ n1.le]
  congr 1
  field_simp

theorem continuous_weight {F : Type*} [NormedField F] :
    Continuous (LocalWeight.weight : GL (Fin 2) F → ℝ) := by
  have hc : Continuous fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have he : ∀ i j : Fin 2, Continuous fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hc)
  have hdet : Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ := (hc.matrix_det).norm
  have htop : Continuous fun x : GL (Fin 2) F =>
      max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ :=
    ((he 0 0).norm).max ((he 0 1).norm)
  have hbot : Continuous fun x : GL (Fin 2) F =>
      NumberField.AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) :=
    ((he 1 0).norm).max ((he 1 1).norm)
  have hdet0 : ∀ x : GL (Fin 2) F, ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ ≠ 0 := fun x =>
    (norm_pos_iff.mpr (Matrix.isUnits_det_units x).ne_zero).ne'
  have htop0 : ∀ x : GL (Fin 2) F,
      max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ ≠ 0 := by
    intro x h0
    have h00 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 :=
      norm_eq_zero.mp (le_antisymm (le_trans (le_max_left _ _) h0.le) (norm_nonneg _))
    have h01 : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 :=
      norm_eq_zero.mp (le_antisymm (le_trans (le_max_right _ _) h0.le) (norm_nonneg _))
    have hd : (x : Matrix (Fin 2) (Fin 2) F).det = 0 := by
      rw [Matrix.det_fin_two, h00, h01, zero_mul, zero_mul, sub_zero]
    exact (Matrix.isUnits_det_units x).ne_zero hd
  unfold AutomorphicForm.LocalWeight.weight
  exact continuous_const.mul
    (((htop.mul hbot).div hdet hdet0).log fun x =>
      div_ne_zero (mul_ne_zero (htop0 x) (NumberField.AdelicHeight.rowMaxNorm_pos x).ne') (hdet0 x))

section sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_mul_apply (σ τ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    sigmaTensor K L A (σ * τ) x = sigmaTensor K L A σ (sigmaTensor K L A τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (σ * τ).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) =
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
        (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K A) (l ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply (x : L ⊗[K] A) : sigmaTensor K L A 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) = l ⊗ₜ a
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaTensor_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[n] x = sigmaTensor K L A (σ ^ n) x := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, sigmaTensor_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaTensor_mul_apply]

theorem sigmaTensor_one_tmul (σ : L ≃ₐ[K] L) (a : A) :
    sigmaTensor K L A σ ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a := by
  change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) ((1 : L) ⊗ₜ a) = (1 : L) ⊗ₜ a
  rw [Algebra.TensorProduct.map_tmul]
  simp

theorem sigmaGL_apply (σ : L ≃ₐ[K] L) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      sigmaTensor K L A σ ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := rfl

theorem sigmaGL_iterate_apply (σ : L ≃ₐ[K] L) (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (⇑(sigmaTensor K L A σ))^[n] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem toTensorGL_apply (γ : GL (Fin 2) A) (i j : Fin 2) :
    ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j) := rfl

theorem sigmaGL_toTensorGL (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A γ) = toTensorGL K L A γ := by
  apply Units.ext
  ext i j
  rw [sigmaGL_apply, toTensorGL_apply, sigmaTensor_one_tmul]

theorem isDiag_sigmaGL (σ : L ≃ₐ[K] L) {x : GL (Fin 2) (L ⊗[K] A)} (hx : IsDiag x) :
    IsDiag (sigmaGL K L A σ x) := by
  constructor
  · rw [sigmaGL_apply, hx.1, map_zero]
  · rw [sigmaGL_apply, hx.2, map_zero]

theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x := by
  have hdvd : orderOf σ ∣ Module.finrank K L := by
    have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L =
        Nat.card (Subgroup.zpowers σ) :=
      IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
    rw [Nat.card_zpowers] at h1
    rw [← h1]
    exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)
  have hpow : σ ^ Module.finrank K L = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  apply Units.ext
  ext i j
  rw [sigmaGL_iterate_apply, sigmaTensor_iterate, hpow, sigmaTensor_one_apply]

theorem sigma_pow_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  have hdvd : orderOf σ ∣ Module.finrank K L := by
    have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L =
        Nat.card (Subgroup.zpowers σ) :=
      IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
    rw [Nat.card_zpowers] at h1
    rw [← h1]
    exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

def P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod

theorem P_succ (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ δ (n + 1) = P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] δ := by
  simp only [P, List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

theorem normString_eq_P [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = P K L A σ δ (Module.finrank K L) := rfl

theorem iterate_map_mul' (σ : L ≃ₐ[K] L) (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[k] (x * y) = (⇑(sigmaGL K L A σ))^[k] x * (⇑(sigmaGL K L A σ))^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem P_succ' (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ δ (n + 1) = δ * sigmaGL K L A σ (P K L A σ δ n) := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    calc P K L A σ δ (n + 1 + 1) = P K L A σ δ (n + 1) * (⇑(sigmaGL K L A σ))^[n + 1] δ := P_succ K L A σ δ (n + 1)
      _ = δ * sigmaGL K L A σ (P K L A σ δ n) * sigmaGL K L A σ ((⇑(sigmaGL K L A σ))^[n] δ) := by
          rw [ih, Function.iterate_succ_apply']
      _ = δ * sigmaGL K L A σ (P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] δ) := by rw [map_mul, mul_assoc]
      _ = δ * sigmaGL K L A σ (P K L A σ δ (n + 1)) := by rw [← P_succ]

def Nm (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) : L ⊗[K] A :=
  ((List.range n).map fun i => (⇑(sigmaTensor K L A σ))^[i] x).prod

theorem Nm_succ (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) :
    Nm K L A σ (n + 1) x = Nm K L A σ n x * (⇑(sigmaTensor K L A σ))^[n] x := by
  simp only [Nm, List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

theorem sigmaTensor_iterate_mul (σ : L ≃ₐ[K] L) (k : ℕ) (x y : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[k] (x * y) = (⇑(sigmaTensor K L A σ))^[k] x * (⇑(sigmaTensor K L A σ))^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem sigmaTensor_iterate_one (σ : L ≃ₐ[K] L) (k : ℕ) :
    (⇑(sigmaTensor K L A σ))^[k] (1 : L ⊗[K] A) = 1 :=
  Function.iterate_fixed (map_one _) k

theorem sigmaTensor_iterate_zero (σ : L ≃ₐ[K] L) (k : ℕ) :
    (⇑(sigmaTensor K L A σ))^[k] (0 : L ⊗[K] A) = 0 :=
  Function.iterate_fixed (map_zero _) k

theorem Nm_mul (σ : L ≃ₐ[K] L) (n : ℕ) (x y : L ⊗[K] A) :
    Nm K L A σ n (x * y) = Nm K L A σ n x * Nm K L A σ n y := by
  induction n with
  | zero => simp [Nm]
  | succ n ih => rw [Nm_succ, Nm_succ, Nm_succ, ih, sigmaTensor_iterate_mul]; ring

theorem Nm_one (σ : L ≃ₐ[K] L) (n : ℕ) : Nm K L A σ n (1 : L ⊗[K] A) = 1 := by
  induction n with
  | zero => simp [Nm]
  | succ n ih => rw [Nm_succ, ih, sigmaTensor_iterate_one, one_mul]

theorem isUnit_Nm (σ : L ≃ₐ[K] L) (n : ℕ) {x : L ⊗[K] A} (hx : IsUnit x) : IsUnit (Nm K L A σ n x) := by
  obtain ⟨u, rfl⟩ := hx
  have h : Nm K L A σ n (u : L ⊗[K] A) * Nm K L A σ n ((u⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = 1 := by
    rw [← Nm_mul, Units.mul_inv, Nm_one]
  exact isUnit_iff_exists_inv.mpr ⟨_, h⟩

theorem P_entries (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (hδ : IsDiag δ) (n : ℕ) :
    IsDiag (P K L A σ δ n) ∧
    ((P K L A σ δ n : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
      Nm K L A σ n ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) ∧
    ((P K L A σ δ n : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
      Nm K L A σ n ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := by
  induction n with
  | zero =>
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp [P]
    · simp [P]
    · simp [P, Nm]
    · simp [P, Nm]
  | succ n ih =>
    obtain ⟨⟨ih01, ih10⟩, ih00, ih11⟩ := ih
    have e01 : (((⇑(sigmaGL K L A σ))^[n] δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
      rw [sigmaGL_iterate_apply, hδ.1, sigmaTensor_iterate_zero]
    have e10 : (((⇑(sigmaGL K L A σ))^[n] δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
      rw [sigmaGL_iterate_apply, hδ.2, sigmaTensor_iterate_zero]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [P_succ, val_mul_apply, ih01, e01, mul_zero, zero_mul, add_zero]
    · rw [P_succ, val_mul_apply, ih10, e10, mul_zero, zero_mul, add_zero]
    · rw [P_succ, val_mul_apply, ih00, e10, mul_zero, add_zero, sigmaGL_iterate_apply, Nm_succ]
    · rw [P_succ, val_mul_apply, ih11, e01, mul_zero, zero_add, sigmaGL_iterate_apply, Nm_succ]

theorem commute_of_normString_eq [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A))
    (γ : GL (Fin 2) A) (h : normString K L A σ δ = toTensorGL K L A γ) :
    toTensorGL K L A γ * δ = δ * toTensorGL K L A γ := by
  have h1 : P K L A σ δ (Module.finrank K L + 1) = toTensorGL K L A γ * δ := by
    rw [P_succ, sigmaGL_iterate_finrank, ← normString_eq_P, h]
  have h2 : P K L A σ δ (Module.finrank K L + 1) = δ * toTensorGL K L A γ := by
    rw [P_succ', ← normString_eq_P, h, sigmaGL_toTensorGL]
  rw [← h1, h2]

theorem mul_normString_comm [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (δ t : GL (Fin 2) (L ⊗[K] A))
    (ht : t ∈ twistedCentralizer K L A σ δ) :
    normString K L A σ δ * t = t * normString K L A σ δ := by
  set s := sigmaGL K L A σ with hs
  have ht' : t * δ * (s t)⁻¹ = δ := mem_sigmaCentralizer_iff.mp ht
  have htδ : t * δ = δ * s t := by
    calc t * δ = t * δ * (s t)⁻¹ * s t := by group
      _ = δ * s t := by rw [ht']
  have hP : ∀ k : ℕ, t * P K L A σ δ k = P K L A σ δ k * s^[k] t := by
    intro k
    induction k with
    | zero => simp [P]
    | succ k ih =>
        rw [P_succ, ← mul_assoc, ih, mul_assoc, mul_assoc]
        congr 1
        rw [← iterate_map_mul', htδ, iterate_map_mul', ← Function.iterate_succ_apply s k t]
  have h := hP (Module.finrank K L)
  rw [hs, sigmaGL_iterate_finrank, ← normString_eq_P] at h
  exact h.symm

variable {K L A}

theorem mem_twistedCentralizer_conj [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ g t : GL (Fin 2) (L ⊗[K] A)) (hg : IsDiag g) (hg' : IsDiag g⁻¹) (htd : IsDiag t)
    (ht : t ∈ twistedCentralizer K L A σ δ) :
    t ∈ twistedCentralizer K L A σ (g⁻¹ * δ * sigmaGL K L A σ g) := by
  rw [mem_sigmaCentralizer_iff] at ht ⊢
  have h1 : t * g⁻¹ = g⁻¹ * t := diag_comm htd hg'
  have h2 : sigmaGL K L A σ g * (sigmaGL K L A σ t)⁻¹ = (sigmaGL K L A σ t)⁻¹ * sigmaGL K L A σ g :=
    diag_comm (isDiag_sigmaGL K L A σ hg) (isDiag_inv (isDiag_sigmaGL K L A σ htd))
  calc t * (g⁻¹ * δ * sigmaGL K L A σ g) * (sigmaGL K L A σ t)⁻¹
      = (t * g⁻¹) * δ * (sigmaGL K L A σ g * (sigmaGL K L A σ t)⁻¹) := by group
    _ = (g⁻¹ * t) * δ * ((sigmaGL K L A σ t)⁻¹ * sigmaGL K L A σ g) := by rw [h1, h2]
    _ = g⁻¹ * (t * δ * (sigmaGL K L A σ t)⁻¹) * sigmaGL K L A σ g := by group
    _ = g⁻¹ * δ * sigmaGL K L A σ g := by rw [ht]

end sigma

section NormProd

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem Nm_eq_prod_range (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) :
    Nm K L A σ n x = ∏ i ∈ Finset.range n, (⇑(sigmaTensor K L A σ))^[i] x := by
  induction n with
  | zero => simp [Nm]
  | succ n ih => rw [Nm_succ, ih, Finset.prod_range_succ]

theorem comm_sigmaTensor (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    Algebra.TensorProduct.comm K L A (sigmaTensor K L A σ x) =
      Algebra.TensorProduct.map (AlgHom.id K A) (σ : L →ₐ[K] L) (Algebra.TensorProduct.comm K L A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.comm K L A (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K A) (l ⊗ₜ a)) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem comm_sigmaTensor_pow (σ : L ≃ₐ[K] L) (i : ℕ) (x : L ⊗[K] A) :
    Algebra.TensorProduct.comm K L A ((⇑(sigmaTensor K L A σ))^[i] x) =
      Algebra.TensorProduct.map (AlgHom.id K A) ((σ ^ i : L ≃ₐ[K] L) : L →ₐ[K] L) (Algebra.TensorProduct.comm K L A x) := by
  induction i generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero]
    induction (Algebra.TensorProduct.comm K L A x) using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a l => rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ i ih =>
    rw [Function.iterate_succ_apply', comm_sigmaTensor, ih, pow_succ']
    induction (Algebra.TensorProduct.comm K L A x) using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a l => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

noncomputable def commA : (L ⊗[K] A) ≃ₐ[A] (A ⊗[K] L) :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm K L A).toRingEquiv) (fun a => by
    change Algebra.TensorProduct.comm K L A (algebraMap A (L ⊗[K] A) a) = algebraMap A (A ⊗[K] L) a
    rw [show algebraMap A (L ⊗[K] A) a = (1 : L) ⊗ₜ a from rfl, Algebra.TensorProduct.comm_tmul]
    rfl)

theorem commA_apply (x : L ⊗[K] A) : commA K L A x = Algebra.TensorProduct.comm K L A x := rfl

end NormProd

section NormProdGalois

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (A : Type) [CommRing A] [Algebra K A]

theorem algebraMap_norm_eq_Nm (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) = Nm K L A σ (Module.finrank K L) x := by
  classical

  have h54 := Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv K L A (commA K L A x)

  have hN : Algebra.norm A (commA K L A x) = Algebra.norm A x := Algebra.norm_eq_of_algEquiv (commA K L A) x
  rw [hN] at h54

  apply (Algebra.TensorProduct.comm K L A).injective
  have lhs : Algebra.TensorProduct.comm K L A (algebraMap A (L ⊗[K] A) (Algebra.norm A x)) =
      algebraMap A (A ⊗[K] L) (Algebra.norm A x) := by
    rw [show algebraMap A (L ⊗[K] A) (Algebra.norm A x) = (1 : L) ⊗ₜ Algebra.norm A x from rfl,
      Algebra.TensorProduct.comm_tmul]; rfl
  rw [lhs, h54, Nm_eq_prod_range, map_prod]
  simp_rw [comm_sigmaTensor_pow]

  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hcardF : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have htop : Subgroup.zpowers σ = ⊤ := (Subgroup.eq_top_iff' _).mpr hgen
  have horder : orderOf σ = Module.finrank K L := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top, hcard]
  have hinj : ∀ i ∈ Finset.range (Module.finrank K L), ∀ j ∈ Finset.range (Module.finrank K L), σ ^ i = σ ^ j → i = j := by
    intro i hi j hj h
    exact pow_injOn_Iio_orderOf (by simpa [horder] using hi) (by simpa [horder] using hj) h
  have himage : (Finset.range (Module.finrank K L)).image (fun i => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h), Finset.card_range, hcardF]
  rw [← Finset.prod_image (s := Finset.range (Module.finrank K L)) (g := fun i => σ ^ i)
    (f := fun g : L ≃ₐ[K] L => Algebra.TensorProduct.map (AlgHom.id K A) (g : L →ₐ[K] L) (Algebra.TensorProduct.comm K L A x))
    hinj, himage]
  rfl

end NormProdGalois

end A5RN
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex.A5RN"

namespace A5RN
open AutomorphicForm

section Arch
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem diagUnits2_isDiag {A : Type} [CommRing A] (α β : Aˣ) :
    ((diagUnits2 α β : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 ∧
    ((diagUnits2 α β : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧
    ((diagUnits2 α β : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = α ∧
    ((diagUnits2 α β : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = β := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [diagUnits2]

theorem norm_eq_of_normString_diagUnits2 (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ) (a b : (InfiniteAdeleRing K)ˣ)
    (hN : normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
      toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a b)) :
    Algebra.norm (InfiniteAdeleRing K) ((α : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) = a ∧
    Algebra.norm (InfiniteAdeleRing K) ((β : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) = b := by
  obtain ⟨h01, h10, h00, h11⟩ := diagUnits2_isDiag α β
  obtain ⟨k01, k10, k00, k11⟩ := diagUnits2_isDiag a b
  obtain ⟨-, hP00, hP11⟩ := P_entries K L (InfiniteAdeleRing K) σ (diagUnits2 α β) ⟨h01, h10⟩ (Module.finrank K L)
  rw [← normString_eq_P, hN, toTensorGL_apply, h00] at hP00
  rw [← normString_eq_P, hN, toTensorGL_apply, h11] at hP11
  rw [k00] at hP00
  rw [k11] at hP11
  have hinj : Function.Injective (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)) := fun x y h =>
    Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := InfiniteAdeleRing K)
      (algebraMap K L).injective h
  refine ⟨hinj ?_, hinj ?_⟩
  · rw [algebraMap_norm_eq_Nm K L (InfiniteAdeleRing K) σ hgen, ← hP00]; rfl
  · rw [algebraMap_norm_eq_Nm K L (InfiniteAdeleRing K) σ hgen, ← hP11]; rfl

theorem norm_inv_mul_eq (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ) (a t : (InfiniteAdeleRing K)ˣ)
    (hN : normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
      toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)))
    (u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
      ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
    Algebra.norm (InfiniteAdeleRing K)
        (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
          (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = (t : InfiniteAdeleRing K) := by
  obtain ⟨hα, hβ⟩ := norm_eq_of_normString_diagUnits2 K L σ hgen α β a (a * t) hN
  have hu : ∀ v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
      Algebra.norm (InfiniteAdeleRing K) (((v : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : L ⊗[K] InfiniteAdeleRing K) = 1 := by
    intro v
    have h := congrArg Units.val (v.2 : Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) (v : (L ⊗[K] InfiniteAdeleRing K)ˣ) = 1)
    simpa [Units.coe_map] using h
  have hαu : Algebra.norm (InfiniteAdeleRing K) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) :
      L ⊗[K] InfiniteAdeleRing K) = a := by
    rw [Units.val_mul, map_mul, hα, hu, mul_one]
  have hβu : Algebra.norm (InfiniteAdeleRing K) (((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) :
      L ⊗[K] InfiniteAdeleRing K) = a * t := by
    rw [Units.val_mul, map_mul, hβ, hu, mul_one, Units.val_mul]
  have hinv : Algebra.norm (InfiniteAdeleRing K) ((((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ :
      (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)) = ((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) := by
    have h1 : Algebra.norm (InfiniteAdeleRing K) ((((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ :
        (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)) * (a : InfiniteAdeleRing K) = 1 := by
      rw [← hαu, ← map_mul, Units.inv_mul, map_one]
    have h2 : (a : InfiniteAdeleRing K) * ((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := Units.mul_inv a
    exact left_inv_eq_right_inv h1 h2
  rw [Units.val_mul, map_mul, hinv, hβu, ← mul_assoc, Units.inv_mul, one_mul]

end Arch
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex.A5RN"
end A5RN
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex.A5RN"

open scoped Classical in
open LayerPlumbing in
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
    (hw : w.IsComplex) (hw' : w'.IsComplex) :
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
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
  classical

  obtain ⟨d, e, κ, hκ, hmap, Λ, hΛ, hM⟩ :=
    AutomorphicForm.exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_norm_fst_add_of_isComplex_of_isComplex_comap
      K L σ hgen hdeg lam w' hw' (by rw [hw'w]; exact hw)

  obtain ⟨χ, hχ, hχc, hχ1, hχU⟩ := exists_cutoff K L Φ hΦc hΦu
  have hU2o : IsOpen {p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L | IsUnit (p 0) ∧ IsUnit (p 1)} := by
    have h0 : IsOpen ((fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => p 0) ⁻¹'
        {x : NumberField.mixedEmbedding.mixedSpace L | IsUnit x}) :=
      (isOpen_setOf_isUnit_mixedSpace L).preimage (continuous_apply 0)
    have h1 : IsOpen ((fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => p 1) ⁻¹'
        {x : NumberField.mixedEmbedding.mixedSpace L | IsUnit x}) :=
      (isOpen_setOf_isUnit_mixedSpace L).preimage (continuous_apply 1)
    exact h0.inter h1

  obtain ⟨g, hg_def⟩ : ∃ g : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × EuclideanSpace ℝ (Fin d)) → ℂ,
      g = fun x => ((χ x.1 : ℝ) : ℂ) * Φ ![x.1 0, x.1 1, e.symm (x.2.1, x.2.2)] := ⟨_, rfl⟩
  have hvec : ContDiff ℝ (⊤ : ℕ∞) fun x : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × EuclideanSpace ℝ (Fin d)) =>
      (![x.1 0, x.1 1, e.symm (x.2.1, x.2.2)] : Fin 3 → NumberField.mixedEmbedding.mixedSpace L) := by
    have h0 : ContDiff ℝ (⊤ : ℕ∞) fun x : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × EuclideanSpace ℝ (Fin d)) => x.1 0 :=
      (contDiff_apply ℝ _ 0).comp contDiff_fst
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × EuclideanSpace ℝ (Fin d)) => x.1 1 :=
      (contDiff_apply ℝ _ 1).comp contDiff_fst
    have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) × (ℂ × EuclideanSpace ℝ (Fin d)) =>
        e.symm (x.2.1, x.2.2) :=
      e.symm.contDiff.comp ((contDiff_fst.comp contDiff_snd).prodMk (contDiff_snd.comp contDiff_snd))
    refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [hg_def]
    exact (Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_fst)).mul (hΦ.comp hvec)
  have hgc : HasCompactSupport g := by
    set S3 : Set (NumberField.mixedEmbedding.mixedSpace L) :=
      (fun p : Fin 3 → NumberField.mixedEmbedding.mixedSpace L => p 2) '' tsupport Φ with hS3
    have hS3c : IsCompact S3 := hΦc.image (continuous_apply 2)
    refine HasCompactSupport.intro (hχc.prod ((hS3c.image e.continuous))) fun x hx => ?_
    rw [hg_def]
    show ((χ x.1 : ℝ) : ℂ) * Φ ![x.1 0, x.1 1, e.symm (x.2.1, x.2.2)] = 0
    simp only [Set.mem_prod, not_and_or] at hx
    rcases hx with h | h
    · rw [image_eq_zero_of_notMem_tsupport h, Complex.ofReal_zero, zero_mul]
    · have : Φ ![x.1 0, x.1 1, e.symm (x.2.1, x.2.2)] = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => h ?_
        refine ⟨e.symm (x.2.1, x.2.2), ⟨_, hmem, by simp⟩, ?_⟩
        simp
      rw [this, mul_zero]
  obtain ⟨φ, hφ_def⟩ : ∃ φ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℂ),
      φ = fun p => (χ p) • Λ ((p 0)⁻¹ * p 1) := ⟨_, rfl⟩
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    rw [hφ_def]
    refine contDiff_cutoff_smul χ hχ _ hU2o hχU (fun p => Λ ((p 0)⁻¹ * p 1)) fun p hp => ?_
    obtain ⟨h0, -⟩ := hp
    have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => (p 0)⁻¹) p :=
      (contDiffAt_inv_mixedSpace L h0).comp p (contDiffAt_apply ℝ _ 0 p)
    exact hΛ.contDiffAt.comp p (hinv.mul (contDiffAt_apply ℝ _ 1 p))
  obtain ⟨A₁, B₁, hA₁, hB₁, hR2C⟩ :=
    MeasureTheory.exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
      (volume : Measure (EuclideanSpace ℝ (Fin d))) g hg hgc
      (fun _ => ContinuousLinearMap.id ℝ ℂ) contDiff_const (fun _ z hz => hz) φ hφ

  obtain ⟨rt, hrtU, hrt⟩ : ∃ rt : (Fin 2 → NumberField.mixedEmbedding.mixedSpace L) → ℂ,
      (∀ p, IsUnit (p 0) ∧ IsUnit (p 1) → ContDiffAt ℝ (⊤ : ℕ∞) rt p) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ) (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
        ∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
            ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
          ‖rt ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
               NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))]‖ =
            ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ := by
    refine ⟨fun p => ((1 : NumberField.mixedEmbedding.mixedSpace K) - normCoord K L ((p 0)⁻¹ * p 1)).2 ⟨w, hw⟩, ?_, ?_⟩
    · intro p hp
      obtain ⟨h0, -⟩ := hp
      have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => (p 0)⁻¹) p :=
        (contDiffAt_inv_mixedSpace L h0).comp p (contDiffAt_apply ℝ _ 0 p)
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => (p 0)⁻¹ * p 1) p :=
        hinv.mul (contDiffAt_apply ℝ _ 1 p)
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L =>
          (1 : NumberField.mixedEmbedding.mixedSpace K) - normCoord K L ((p 0)⁻¹ * p 1)) p :=
        contDiffAt_const.sub ((contDiff_normCoord K L).contDiffAt.comp p h1)
      have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun x : NumberField.mixedEmbedding.mixedSpace K =>
          x.2 (⟨w, hw⟩ : {v : NumberField.InfinitePlace K // v.IsComplex})) :=
        (contDiff_apply ℝ ℂ (⟨w, hw⟩ : {v : NumberField.InfinitePlace K // v.IsComplex})).comp contDiff_snd
      exact h3.contDiffAt.comp p h2
    · intro a t α β hN u
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
              (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)))⁻¹ *
            NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
              (((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)) =
            NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
              (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
                (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K))
          from inv_iotaL_mul_iotaL K L _ _]
      rw [normCoord_iotaL, A5RN.norm_inv_mul_eq K L σ hgen α β a t hN u]
      have h1 : (1 : NumberField.mixedEmbedding.mixedSpace K) -
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K) =
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) := by
        rw [map_sub, map_one]
      rw [h1, norm_ringEquiv_mixedSpace_snd]
  have hGA : ContDiff ℝ (⊤ : ℕ∞) (fun p => ((χ p : ℝ) : ℂ) * A₁ (p, rt p)) := by
    have := contDiff_cutoff_smul χ hχ _ hU2o hχU (fun p => A₁ (p, rt p)) fun p hp =>
      hA₁.contDiffAt.comp p (contDiffAt_id.prodMk (hrtU p hp))
    have h2 : (fun p => ((χ p : ℝ) : ℂ) * A₁ (p, rt p)) =
        fun p => χ p • (fun p => A₁ (p, rt p)) p := funext fun p => (Complex.real_smul).symm
    rw [h2]; exact this
  have hGB : ContDiff ℝ (⊤ : ℕ∞) (fun p => ((χ p : ℝ) : ℂ) * B₁ (p, rt p)) := by
    have := contDiff_cutoff_smul χ hχ _ hU2o hχU (fun p => B₁ (p, rt p)) fun p hp =>
      hB₁.contDiffAt.comp p (contDiffAt_id.prodMk (hrtU p hp))
    have h2 : (fun p => ((χ p : ℝ) : ℂ) * B₁ (p, rt p)) =
        fun p => χ p • (fun p => B₁ (p, rt p)) p := funext fun p => (Complex.real_smul).symm
    rw [h2]; exact this

  obtain ⟨C, hCc, hCar⟩ := exists_unit_carrier K L χ hχc hχU
  have hco : tsupport (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => ((χ p : ℝ) : ℂ)) ⊆ tsupport χ := by
    intro p hp
    by_contra h
    have h0 := notMem_tsupport_iff_eventuallyEq.mp h
    refine (notMem_tsupport_iff_eventuallyEq.mpr ?_) hp
    filter_upwards [h0] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx, Complex.ofReal_zero]
  have hχcC : HasCompactSupport (fun p : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => ((χ p : ℝ) : ℂ)) :=
    hχc.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)
  obtain ⟨FA, hFA, hFAc, hFAu, hFAid⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff K L θ
      (fun p => ((χ p : ℝ) : ℂ) * A₁ (p, rt p)) hGA hχcC.mul_right
      ⟨C, hCc, hCar _ ((tsupport_mul_subset_left (f := fun p => ((χ p : ℝ) : ℂ)) (g := fun p => A₁ (p, rt p))).trans hco)⟩
  obtain ⟨FB, hFB, hFBc, hFBu, hFBid⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff K L θ
      (fun p => ((χ p : ℝ) : ℂ) * B₁ (p, rt p)) hGB hχcC.mul_right
      ⟨C, hCc, hCar _ ((tsupport_mul_subset_left (f := fun p => ((χ p : ℝ) : ℂ)) (g := fun p => B₁ (p, rt p))).trans hco)⟩

  obtain ⟨hAs, hAc, hAu, hAval⟩ := kside K FA hFA hFAc hFAu ((κ : ℝ) : ℂ)
  obtain ⟨hBs, hBc, hBu, hBval⟩ := kside K FB hFB hFBc hFBu ((κ : ℝ) : ℂ)
  refine ⟨fun q => ((κ : ℝ) : ℂ) * FA ![q 1, q 1 * q 0], fun q => ((κ : ℝ) : ℂ) * FB ![q 1, q 1 * q 0],
    hAs, hBs, hAc, hBc, ?_, ?_⟩
  · obtain ⟨CaA, hCaA, hA'⟩ := hAu
    obtain ⟨CaB, hCaB, hB'⟩ := hBu
    refine ⟨CaA ∪ CaB, hCaA.union hCaB, fun p hp => ?_⟩
    rcases hp with h | h
    · obtain ⟨q, hq, hpq⟩ := hA' p h; exact ⟨q, Or.inl hq, hpq⟩
    · obtain ⟨q, hq, hpq⟩ := hB' p h; exact ⟨q, Or.inr hq, hpq⟩

  intro a t ht α β hN Mu hMu
  have hcU : IsUnit ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) := by
    rw [isUnit_infiniteAdeleRing_iff]
    intro v
    have hv : ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) v = 1 - (t : InfiniteAdeleRing K) v := rfl
    rw [hv, sub_ne_zero]
    exact fun h => ht v h.symm
  set c : (InfiniteAdeleRing K)ˣ := hcU.unit with hc
  have hcval : (c : InfiniteAdeleRing K) = 1 - (t : InfiniteAdeleRing K) := hcU.unit_spec

  have hinner : ∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
      ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
      ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam =
        ((κ : ℝ) : ℂ) *
          ((fun p => ((χ p : ℝ) : ℂ) * A₁ (p, rt p))
              ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))] +
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            (fun p => ((χ p : ℝ) : ℂ) * B₁ (p, rt p))
              ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))]) := by
    intro u

    set P0 : NumberField.mixedEmbedding.mixedSpace L := NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L
      (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) with hP0
    set P1 : NumberField.mixedEmbedding.mixedSpace L := NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L
      (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) with hP1
    set ru : L ⊗[K] InfiniteAdeleRing K := (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) with hru
    set cw : ℝ := ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ with hcw

    have hNru : (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) ru := by
      rw [hcval, hru, A5RN.norm_inv_mul_eq K L σ hgen α β a t hN u]
    have hMn : ∀ y : L ⊗[K] InfiniteAdeleRing K,
        ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ =
          ‖(e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))).1 +
            Λ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ru))
              (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))).2‖ :=
      hM ru c hNru (Mu u) (fun y => by rw [hcval]; exact (hMu u).1 y) (fun y => by rw [hcval]; exact (hMu u).2 y)

    set F : ℂ × EuclideanSpace ℝ (Fin d) → ℂ := fun zv =>
      Φ ![P0, P1, e.symm (zv.1, zv.2)] *
        (Real.log (cw ^ 2 + ‖zv.1 + Λ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ru)) zv.2‖ ^ 2) : ℂ)
      with hF
    have hLHS : (∫ y, Φ ![P0, P1, NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
        (Real.log (cw ^ 2 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam) =
        ∫ y, F (e.toHomeomorph (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))) ∂lam := by
      congr 1; funext y
      show _ = Φ ![P0, P1, e.symm ((e _).1, (e _).2)] * _
      rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, hMn y]
      rfl
    rw [hLHS, integral_comp_iotaL K L lam e.toHomeomorph _ κ hmap F]

    obtain ⟨-, hE⟩ := hR2C ![P0, P1] (rt ![P0, P1])
    have hrtn : ‖rt ![P0, P1]‖ = cw := hrt a t α β hN u
    have hq : ((![P0, P1] : Fin 2 → NumberField.mixedEmbedding.mixedSpace L) 0)⁻¹ * (![P0, P1] : Fin 2 → _) 1 =
        NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ru) := by
      show P0⁻¹ * P1 = _
      rw [hP0, hP1, hru]
      exact inv_iotaL_mul_iotaL K L _ _
    by_cases hsh : ∃ m : NumberField.mixedEmbedding.mixedSpace L,
        (![P0, P1, m] : Fin 3 → NumberField.mixedEmbedding.mixedSpace L) ∈ tsupport Φ
    ·
      obtain ⟨m, hm⟩ := hsh
      have hχP : χ ![P0, P1] = 1 := by
        have := hχ1 _ hm
        simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using this
      have hgF : ∀ zv : ℂ × EuclideanSpace ℝ (Fin d),
          g (![P0, P1], zv) * (Real.log (‖(fun _ : Fin 2 → NumberField.mixedEmbedding.mixedSpace L => ContinuousLinearMap.id ℝ ℂ)
            ![P0, P1] zv.1 + φ ![P0, P1] zv.2‖ ^ 2 + ‖rt ![P0, P1]‖ ^ 2) : ℂ) = F zv := by
        intro zv
        rw [hg_def, hφ_def]
        show ((χ ![P0, P1] : ℝ) : ℂ) * Φ ![(![P0, P1] : Fin 2 → _) 0, (![P0, P1] : Fin 2 → _) 1, e.symm (zv.1, zv.2)] *
            (Real.log (‖ContinuousLinearMap.id ℝ ℂ zv.1 + ((χ ![P0, P1]) • Λ (((![P0, P1] : Fin 2 → _) 0)⁻¹ * (![P0, P1] : Fin 2 → _) 1)) zv.2‖ ^ 2 +
              ‖rt ![P0, P1]‖ ^ 2) : ℂ) = F zv
        rw [hq, hχP, hrtn, one_smul, Complex.ofReal_one, one_mul, ContinuousLinearMap.id_apply, add_comm (‖_‖ ^ 2) (cw ^ 2)]
        rfl
      have hE' : ∫ zv, F zv ∂((volume : Measure ℂ).prod (volume : Measure (EuclideanSpace ℝ (Fin d)))) =
          A₁ (![P0, P1], rt ![P0, P1]) + ((cw ^ 2 * Real.log cw : ℝ) : ℂ) * B₁ (![P0, P1], rt ![P0, P1]) := by
        rw [← hrtn, ← hE]
        congr 1; funext zv; exact (hgF zv).symm
      rw [hE', Complex.real_smul]
      simp only [hχP, Complex.ofReal_one, one_mul]
    ·
      have hΦ0 : ∀ m : NumberField.mixedEmbedding.mixedSpace L,
          Φ ![P0, P1, m] = 0 := fun m => image_eq_zero_of_notMem_tsupport fun h => hsh ⟨m, h⟩
      have hF0 : ∀ zv, F zv = 0 := by intro zv; show Φ ![P0, P1, _] * _ = 0; rw [hΦ0, zero_mul]
      have hg0 : ∀ zv : ℂ × EuclideanSpace ℝ (Fin d), g (![P0, P1], zv) = 0 := by
        intro zv; rw [hg_def]
        show ((χ ![P0, P1] : ℝ) : ℂ) * Φ ![(![P0, P1] : Fin 2 → _) 0, (![P0, P1] : Fin 2 → _) 1, e.symm (zv.1, zv.2)] = 0
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [hΦ0, mul_zero]
      have hAB : A₁ (![P0, P1], rt ![P0, P1]) + ((cw ^ 2 * Real.log cw : ℝ) : ℂ) * B₁ (![P0, P1], rt ![P0, P1]) = 0 := by
        rw [← hrtn, ← hE]
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun zv => ?_)
        show g _ * _ = (0 : ℂ)
        rw [hg0, zero_mul]
      rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun zv => hF0 zv), smul_zero]
      show (0 : ℂ) = ((κ : ℝ) : ℂ) * (((χ ![P0, P1] : ℝ) : ℂ) * A₁ (![P0, P1], rt ![P0, P1]) +
        ((cw ^ 2 * Real.log cw : ℝ) : ℂ) * (((χ ![P0, P1] : ℝ) : ℂ) * B₁ (![P0, P1], rt ![P0, P1])))
      have : ((χ ![P0, P1] : ℝ) : ℂ) * A₁ (![P0, P1], rt ![P0, P1]) +
          ((cw ^ 2 * Real.log cw : ℝ) : ℂ) * (((χ ![P0, P1] : ℝ) : ℂ) * B₁ (![P0, P1], rt ![P0, P1])) =
          ((χ ![P0, P1] : ℝ) : ℂ) * (A₁ (![P0, P1], rt ![P0, P1]) + ((cw ^ 2 * Real.log cw : ℝ) : ℂ) * B₁ (![P0, P1], rt ![P0, P1])) := by
        ring
      rw [this, hAB, mul_zero, mul_zero]
  refine ⟨?_, ?_⟩
  ·
    have hiA := (hFAid α β).1
    have hiB := (hFBid α β).1
    set cg : ℂ := ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
        Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) with hcg
    refine ((hiA.const_mul ((κ : ℝ) : ℂ)).add (hiB.const_mul (((κ : ℝ) : ℂ) * cg))).congr ?_
    refine Filter.Eventually.of_forall fun u => ?_
    rw [Pi.add_apply]
    beta_reduce
    rw [hinner u]
    ring
  ·
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
    have hiA := (hFAid α β).1
    have hiB := (hFBid α β).1
    rw [show (fun u => ((κ : ℝ) : ℂ) * ((fun p => ((χ p : ℝ) : ℂ) * A₁ (p, rt p)) _ +
        ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
          Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
        (fun p => ((χ p : ℝ) : ℂ) * B₁ (p, rt p)) _)) = fun u => ((κ : ℝ) : ℂ) * ((fun p => ((χ p : ℝ) : ℂ) * A₁ (p, rt p)) _) +
        (((κ : ℝ) : ℂ) * ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
          Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ)) *
        ((fun p => ((χ p : ℝ) : ℂ) * B₁ (p, rt p)) _) from by funext u; ring]
    rw [integral_add (hiA.const_mul _) (hiB.const_mul _), integral_const_mul, integral_const_mul,
      ← (hFAid α β).2, ← (hFBid α β).2]
    obtain ⟨hNa, hNb⟩ := A5RN.norm_eq_of_normString_diagUnits2 K L σ hgen α β a (a * t) hN
    rw [hNa, hNb]
    have hA' := hAval a t
    have hB' := hBval a t
    beta_reduce at hA' hB'
    beta_reduce
    rw [hA', hB']
    ring

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex (solution)
