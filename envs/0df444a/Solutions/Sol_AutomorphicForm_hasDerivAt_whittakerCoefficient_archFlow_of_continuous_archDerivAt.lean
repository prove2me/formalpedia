-- Prove2me | solution 1 for AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/86c6566d-4a9d-5161-aabf-977a62cc445b

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.Analysis.Calculus.ParametricIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt

set_option autoImplicit false

p2m_open "MeasureTheory Filter Topology NumberField NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm P2MW.S_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt.AutomorphicForm"
open NumberField.AdelicLevel IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open scoped Classical

namespace AutomorphicForm
p2m_export "AutomorphicForm" "productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add archRealGLAt IsArchSmoothAt ArchDir lowerUnipotentGL2_coe splitTorusGL2_coe archFlowMatrix archFlowAt archFlowAt_zero archFlowAt_add archDerivAt archCasimirAt glEquivOfRingEquiv whittakerCoefficient"
namespace TransferAux
p2m_open "AutomorphicForm"

theorem continuous_unipotentGL2 (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  have hmat : ∀ s : A → A, Continuous s → Continuous (fun x : A => (!![1, s x; 0, 1] : Matrix (Fin 2) (Fin 2) A)) := by
    intro s hs
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [hs, continuous_const]
  rw [Units.continuous_iff]
  constructor
  · have h__af := hmat id continuous_id
    simp [unipotentGL2_coe] at h__af
    exact h__af
  · have hinv : ∀ x : A, ((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) = unipotentGL2 (-x) := by
      intro x
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
    simp only [hinv]
    simpa [unipotentGL2_coe] using hmat Neg.neg continuous_neg

theorem continuous_archFlowMatrix_apply (d : ArchDir) (i j : Fin 2) :
    Continuous fun t : ℝ => (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp [archFlowMatrix, splitTorusGL2_coe, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Real.continuous_exp, continuous_id, continuous_const] <;>
    first
      | exact Real.continuous_exp.comp continuous_neg
      | exact continuous_id

variable {F : Type} [Field F] [NumberField F]

theorem archFlowAt_coe_apply {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) (i j : Fin 2) :
    ((archFlowAt hw d t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((fun v : InfinitePlace F =>
          (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w
            ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (archFlowMatrix d t) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion) v) i j : InfiniteAdeleRing F),
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

theorem archFlowAt_neg {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    archFlowAt hw d (-t) = (archFlowAt hw d t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← archFlowAt_add, neg_add_cancel, archFlowAt_zero]

theorem continuous_archFlowAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) :
    Continuous fun t : ℝ => archFlowAt hw d t := by
  have hval : Continuous fun t : ℝ =>
      ((archFlowAt hw d t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    simp only [archFlowAt_coe_apply]
    refine Continuous.prodMk ?_ continuous_const
    apply continuous_pi; intro v
    by_cases hv : v = w
    · subst hv
      simp only [Function.update_self]
      show Continuous fun t : ℝ => (ringEquivRealOfIsReal hw).symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) i j)
      exact (isometryEquivRealOfIsReal hw).symm.continuous.comp (continuous_archFlowMatrix_apply d i j)
    · simp only [Function.update_of_ne hv]
      exact continuous_const
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have : (fun t : ℝ => (((archFlowAt hw d t)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
      fun t : ℝ => ((archFlowAt hw d (-t) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    funext t; rw [archFlowAt_neg]
  rw [this]
  exact hval.comp continuous_neg

theorem hasDerivAt_flow_of_isArchSmoothAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (g * archFlowAt hw d s)) (archDerivAt hw d φ (g * archFlowAt hw d t)) t := by
  have h0 : HasDerivAt (fun s : ℝ => φ ((g * archFlowAt hw d t) * archFlowAt hw d s))
      (archDerivAt hw d φ (g * archFlowAt hw d t)) 0 :=
    (hφ.differentiableAt_flow d (g * archFlowAt hw d t)).hasDerivAt
  have hsub : HasDerivAt (fun s : ℝ => s - t) 1 t := by simpa using (hasDerivAt_id t).sub_const t
  have h0' : HasDerivAt (fun s : ℝ => φ ((g * archFlowAt hw d t) * archFlowAt hw d s))
      (archDerivAt hw d φ (g * archFlowAt hw d t)) ((fun s : ℝ => s - t) t) := by simp only [sub_self]; exact h0
  have h1 := HasDerivAt.scomp (𝕜 := ℝ) t (h := fun s : ℝ => s - t) h0' hsub
  rw [one_smul] at h1
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show φ (g * archFlowAt hw d s) = φ (g * archFlowAt hw d t * archFlowAt hw d (s - t))
  rw [mul_assoc, ← archFlowAt_add]; congr 2; ring

theorem hasDerivAt_setIntegral_flow (K : Type) [Field K] [NumberField K]
    {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hc : Continuous φ) (hs : IsArchSmoothAt hw φ)
    (hD : Continuous (archDerivAt hw d φ))
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : Continuous ψ) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
    HasDerivAt (fun t : ℝ => ∫ x in adelicBox K,
        φ (unipotentGL2 x * g * archFlowAt hw d t) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) ∂(adelicAddHaar (𝓞 K) K))
      (∫ x in adelicBox K, archDerivAt hw d φ (unipotentGL2 x * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))
        ∂(adelicAddHaar (𝓞 K) K)) 0 := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  set μ : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμ
  set B : Set (AdeleRing (𝓞 K) K) := adelicBox K with hB
  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset K
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top K
  have hBmeas : MeasurableSet B := measurableSet_adelicBox K

  set Fn : ℝ → (AdeleRing (𝓞 K) K) → ℂ := fun t x =>
    φ (unipotentGL2 x * g * archFlowAt hw d t) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) with hFn
  set Fn' : ℝ → (AdeleRing (𝓞 K) K) → ℂ := fun t x =>
    archDerivAt hw d φ (unipotentGL2 x * g * archFlowAt hw d t) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) with hFn'
  have hpt : Continuous fun p : (AdeleRing (𝓞 K) K) × ℝ => unipotentGL2 p.1 * g * archFlowAt hw d p.2 :=
    (((continuous_unipotentGL2 (AdeleRing (𝓞 K) K)).comp continuous_fst).mul continuous_const).mul
      ((continuous_archFlowAt hw d).comp continuous_snd)
  have hψc : Continuous fun x : (AdeleRing (𝓞 K) K) => ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) :=
    hψ.comp ((continuous_const.mul continuous_id).neg)
  have hFn_cont : ∀ t, Continuous (Fn t) := fun t =>
    (hc.comp (hpt.comp (Continuous.prodMk continuous_id continuous_const))).mul hψc
  have hFn'_cont : ∀ t, Continuous (Fn' t) := fun t =>
    (hD.comp (hpt.comp (Continuous.prodMk continuous_id continuous_const))).mul hψc

  have hK : IsCompact (C ×ˢ Set.Icc (-2 : ℝ) 2) := hCc.prod isCompact_Icc
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn (f := fun p : (AdeleRing (𝓞 K) K) × ℝ =>
    archDerivAt hw d φ (unipotentGL2 p.1 * g * archFlowAt hw d p.2)) (hD.comp hpt).continuousOn
  obtain ⟨M₂, hM₂⟩ := hCc.exists_bound_of_continuousOn (f := fun x : (AdeleRing (𝓞 K) K) => ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)))
    hψc.continuousOn
  have hM₁0 : 0 ≤ M₁ := by
    obtain ⟨x₀, hx₀⟩ : B.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have := adelicAddHaar_adelicBox_pos K
      rw [← hB, h, measure_empty] at this
      exact lt_irrefl _ this
    exact (norm_nonneg _).trans (hM₁ ⟨x₀, 0⟩ ⟨hBC hx₀, by norm_num, by norm_num⟩)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict B) (F := Fn) (F' := Fn')
    (x₀ := (0 : ℝ)) (bound := fun _ => M₁ * M₂) (s := Set.Icc (-2 : ℝ) 2) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (hFn_cont t).aestronglyMeasurable)
    (by
      obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (f := Fn 0) (hFn_cont 0).continuousOn
      exact Measure.integrableOn_of_bounded hBfin.ne (hFn_cont 0).aestronglyMeasurable
        (ae_restrict_of_forall_mem hBmeas fun x hx => hM x (hBC hx)))
    (hFn'_cont 0).aestronglyMeasurable
    (by
      refine ae_restrict_of_forall_mem hBmeas fun x hx t ht => ?_
      rw [hFn', norm_mul]
      exact mul_le_mul (hM₁ ⟨x, t⟩ ⟨hBC hx, ht⟩) (hM₂ x (hBC hx)) (norm_nonneg _) hM₁0)
    (integrableOn_const hBfin.ne)
    (by
      refine ae_restrict_of_forall_mem hBmeas fun x hx t ht => ?_
      exact (hasDerivAt_flow_of_isArchSmoothAt hs d (unipotentGL2 x * g) t).mul_const _)
  have h2 := key.2
  simp only [hFn', archFlowAt_zero, mul_one] at h2
  exact h2

end AutomorphicForm.TransferAux

open AutomorphicForm.TransferAux

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφs : IsArchSmoothAt hw φ)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d φ))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' φ)))
    (g₀ : AdelicGL2 (𝓞 K) K) :
    (∀ (d : ArchDir) (h : GL (Fin 2) ℝ),
        HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (φ) 1 (g₀ * archRealGLAt hw (h * archFlowMatrix d t)))
          (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d φ) 1 (g₀ * archRealGLAt hw h)) 0) ∧
    (∀ (d d' : ArchDir) (h : GL (Fin 2) ℝ),
        HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d' φ) 1 (g₀ * archRealGLAt hw (h * archFlowMatrix d t)))
          (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d (archDerivAt hw d' φ)) 1 (g₀ * archRealGLAt hw h)) 0) ∧
    (∀ h : GL (Fin 2) ℝ,
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archCasimirAt hw φ) 1 (g₀ * archRealGLAt hw h) =
          -((1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw .H (archDerivAt hw .H φ)) 1 (g₀ * archRealGLAt hw h)
            - (1 / 2 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw .H φ) 1 (g₀ * archRealGLAt hw h)
            + whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw .E (archDerivAt hw .Fm φ)) 1 (g₀ * archRealGLAt hw h))) := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  set μ : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμ
  set B : Set (AdeleRing (𝓞 K) K) := adelicBox K with hB
  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
  have hW : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) f 1 g =
        ((μ B)⁻¹).toReal • ∫ x in B, f (unipotentGL2 x * g) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ := by
    intro f g
    unfold whittakerCoefficient
    dsimp only [productionPinsOf]
    exact integral_smul_measure _ _
  have hflow : ∀ (h : GL (Fin 2) ℝ) (d : ArchDir) (t : ℝ) (x : (AdeleRing (𝓞 K) K)),
      unipotentGL2 x * (g₀ * archRealGLAt hw (h * archFlowMatrix d t)) =
        unipotentGL2 x * (g₀ * archRealGLAt hw h) * archFlowAt hw d t := by
    intro h d t x; simp only [map_mul, archFlowAt, mul_assoc]

  have core : ∀ (φ' : AdelicGL2 (𝓞 K) K → ℂ), Continuous φ' → IsArchSmoothAt hw φ' →
      ∀ d : ArchDir, Continuous (archDerivAt hw d φ') → ∀ h : GL (Fin 2) ℝ,
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ' 1 (g₀ * archRealGLAt hw (h * archFlowMatrix d t)))
        (whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d φ') 1 (g₀ * archRealGLAt hw h)) 0 := by
    intro φ' hc' hs' d hD' h
    have hk := (hasDerivAt_setIntegral_flow K hw d φ' hc' hs' hD' (NumberField.StandardAddChar.stdAddChar K) hψ 1
      (g₀ * archRealGLAt hw h)).const_smul ((μ B)⁻¹).toReal
    have hfun : (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ' 1 (g₀ * archRealGLAt hw (h * archFlowMatrix d t))) =
        fun t : ℝ => ((μ B)⁻¹).toReal • ∫ x in B, φ' (unipotentGL2 x * (g₀ * archRealGLAt hw h) * archFlowAt hw d t) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ := by
      funext t; rw [hW]; simp only [hflow]
    rw [hfun, hW]
    exact hk
  refine ⟨fun d h => core φ hφc hφs d (hD1 d) h,
    fun d d' h => core (archDerivAt hw d' φ) (hD1 d') (hφs.archDerivAt d') d (hD2 d d') h, ?_⟩

  intro h
  set G : AdelicGL2 (𝓞 K) K := g₀ * archRealGLAt hw h with hG
  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset K
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top K
  have hBmeas : MeasurableSet B := measurableSet_adelicBox K
  have hint : ∀ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f →
      IntegrableOn (fun x => f (unipotentGL2 x * G) * NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) B μ := by
    intro f hf
    have hcf : Continuous (fun x => f (unipotentGL2 x * G) * NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) :=
      (hf.comp ((continuous_unipotentGL2 (AdeleRing (𝓞 K) K)).mul continuous_const)).mul
        (hψ.comp ((continuous_const.mul continuous_id).neg))
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (f := fun x => f (unipotentGL2 x * G) *
      NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) hcf.continuousOn
    exact Measure.integrableOn_of_bounded hBfin.ne hcf.aestronglyMeasurable
      (ae_restrict_of_forall_mem hBmeas fun x hx => hM x (hBC hx))
  have hA := hint _ (hD2 .H .H)
  have hBf := hint _ (hD1 .H)
  have hCf := hint _ (hD2 .E .Fm)
  rw [hW, hW, hW, hW]
  have hcas : (fun x => archCasimirAt hw φ (unipotentGL2 x * G) * NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) =
      fun x => -((1 / 4 : ℂ) * (archDerivAt hw .H (archDerivAt hw .H φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        - (1 / 2 : ℂ) * (archDerivAt hw .H φ (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        + archDerivAt hw .E (archDerivAt hw .Fm φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) := by
    funext x
    simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcas, integral_neg]
  have h1 : ∫ x in B, ((1 / 4 : ℂ) * (archDerivAt hw .H (archDerivAt hw .H φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        - (1 / 2 : ℂ) * (archDerivAt hw .H φ (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        + archDerivAt hw .E (archDerivAt hw .Fm φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) ∂μ =
      (1 / 4 : ℂ) * ∫ x in B, archDerivAt hw .H (archDerivAt hw .H φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ
      - (1 / 2 : ℂ) * ∫ x in B, archDerivAt hw .H φ (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ
      + ∫ x in B, archDerivAt hw .E (archDerivAt hw .Fm φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ := by
    have hfg : Integrable (fun x => (1 / 4 : ℂ) * (archDerivAt hw .H (archDerivAt hw .H φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        - (1 / 2 : ℂ) * (archDerivAt hw .H φ (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))) (μ.restrict B) :=
      (hA.const_mul _).sub (hBf.const_mul _)
    rw [integral_add hfg hCf, integral_sub (hA.const_mul _) (hBf.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [h1]
  simp only [Complex.real_smul]
  ring

end S_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt
end P2MW
export P2MW.S_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt (solution)
