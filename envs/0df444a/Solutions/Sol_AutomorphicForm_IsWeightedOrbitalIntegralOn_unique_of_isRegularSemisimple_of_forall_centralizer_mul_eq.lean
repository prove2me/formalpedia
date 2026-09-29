-- Prove2me | solution 1 for AutomorphicForm.IsWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6cbdd833-02f7-52af-ae93-c8787c211910

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Theorems.Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory TopologicalSpace

namespace P2mWeightedOrbitalUnique

section Algebra

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  have e11 := congr_fun (congr_fun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {s t : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : s * t = t * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ht
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  set g : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hg
  have hu' : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
    linear_combination hu
  have hsX : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by
    simpa [hg] using congrArg Units.val hs
  have htX : (t : Matrix (Fin 2) (Fin 2) A) * g = g * t := by
    simpa [hg] using congrArg Units.val ht
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g s hsX u hu'
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g t htX u hu'
  set X : Matrix (Fin 2) (Fin 2) A := (s : Matrix (Fin 2) (Fin 2) A)
  set Y : Matrix (Fin 2) (Fin 2) A := (t : Matrix (Fin 2) (Fin 2) A)
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  apply Units.ext
  change X * Y = Y * X
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  ·
    linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  ·
    linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

end Algebra

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Topology

section Main

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A]

theorem isInvInvariant_of_comm (T : Subgroup (GL (Fin 2) A)) (hT : IsClosed (T : Set (GL (Fin 2) A)))
    (hcomm : ∀ s t : T, s * t = t * s) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  haveI := t2Space_GL A
  haveI := secondCountableTopology_GL A
  haveI := locallyCompactSpace_GL A
  letI : CommGroup T := { mul_comm := hcomm }
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : T → GL (Fin 2) A)).secondCountableTopology
  haveI : PseudoMetrizableSpace T := PseudoMetrizableSpace.of_regularSpace_secondCountableTopology T
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : τ.InnerRegular := inferInstance
  exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

theorem main (μ : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μ)
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ)
    (wt : GL (Fin 2) A → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), ∀ x : GL (Fin 2) A,
      wt ((t : GL (Fin 2) A) * x) = wt x)
    (f : GL (Fin 2) A → ℂ) (hfm : Measurable[AutomorphicForm.glBorelOf A] f)
    (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C)
    {J₁ J₂ : ℂ} (h₁ : AutomorphicForm.IsWeightedOrbitalIntegralOn A μ wt γ τ f J₁)
    (h₂ : AutomorphicForm.IsWeightedOrbitalIntegralOn A μ wt γ τ f J₂) : J₁ = J₂ := by
  letI : MeasurableSpace (GL (Fin 2) A) := AutomorphicForm.glBorelOf A
  haveI : BorelSpace (GL (Fin 2) A) := AutomorphicForm.borelSpace_glBorelOf A
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :=
    AutomorphicForm.centralizerBorel A γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI := hμ
  haveI := hτ
  haveI := t2Space_GL A
  haveI := secondCountableTopology_GL A
  haveI := locallyCompactSpace_GL A
  have hTc : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : Set (GL (Fin 2) A)) := by
    show IsClosed (({γ} : Set (GL (Fin 2) A)).centralizer)
    exact Set.isClosed_centralizer _
  have hcomm : ∀ s t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), s * t = t * s := fun s t =>
    Subtype.ext (mul_comm_of_mem_centralizer hγ s.2 t.2)
  haveI : τ.IsInvInvariant := isInvInvariant_of_comm A _ hTc hcomm τ
  obtain ⟨w₁, hw₁, rfl⟩ := h₁
  obtain ⟨w₂, hw₂, rfl⟩ := h₂

  set S : Set (GL (Fin 2) A) := tsupport w₁ ∪ tsupport w₂ with hS_def
  have hS : IsCompact S := hw₁.2.2.1.union hw₂.2.2.1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ S, |wt x| ≤ M := by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hwtc.continuousOn
    exact ⟨C, fun x hx => by simpa only [Real.norm_eq_abs] using hC x hx⟩

  set wt' : GL (Fin 2) A → ℝ := fun x => max (-M) (min M (wt x)) with hwt'_def
  have hwt'T : ∀ (t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (x : GL (Fin 2) A),
      wt' ((t : GL (Fin 2) A) * x) = wt' x := by
    intro t x
    simp only [hwt'_def, hwt]
  have hwt'b : ∀ x, |wt' x| ≤ |M| := by
    intro x
    rw [abs_le]
    refine ⟨le_trans (neg_le_neg (le_abs_self M)) (le_max_left _ _), max_le ?_ ?_⟩
    · exact neg_le_abs M
    · exact le_trans (min_le_left _ _) (le_abs_self M)
  have hwt'eq : ∀ x ∈ S, wt' x = wt x := by
    intro x hx
    have h := abs_le.1 (hM x hx)
    show max (-M) (min M (wt x)) = wt x
    rw [min_eq_right h.2, max_eq_right h.1]
  have hwt'm : Measurable wt' :=
    measurable_const.max (measurable_const.min hwtc.measurable)

  set F : GL (Fin 2) A → ℂ := fun x => f (x⁻¹ * γ * x) * (wt' x : ℂ) with hF_def
  have hfcm : Measurable fun x : GL (Fin 2) A => f (x⁻¹ * γ * x) :=
    hfm.comp ((continuous_inv.mul continuous_const).mul continuous_id).measurable
  have hFm : Measurable F := hfcm.mul (Complex.continuous_ofReal.measurable.comp hwt'm)
  have hFb : ∃ C : ℝ, ∀ x : GL (Fin 2) A, ‖F x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hfb
    refine ⟨C * |M|, fun x => ?_⟩
    rw [hF_def, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hC _) (hwt'b x) (abs_nonneg _) (le_trans (norm_nonneg _) (hC (x⁻¹ * γ * x)))
  have hFT : ∀ (t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (x : GL (Fin 2) A),
      F ((t : GL (Fin 2) A) * x) = F x := by
    intro t x
    have ht : (t : GL (Fin 2) A) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
    have key : (t : GL (Fin 2) A)⁻¹ * γ * t = γ := by
      rw [mul_assoc, ← ht, inv_mul_cancel_left]
    have hconj : ((t : GL (Fin 2) A) * x)⁻¹ * γ * (t * x) = x⁻¹ * γ * x := by
      calc ((t : GL (Fin 2) A) * x)⁻¹ * γ * (t * x)
          = x⁻¹ * ((t : GL (Fin 2) A)⁻¹ * γ * t) * x := by simp only [mul_inv_rev, mul_assoc]
        _ = x⁻¹ * γ * x := by rw [key]
    simp only [hF_def, hconj, hwt'T]
  have hsec : ∀ w : GL (Fin 2) A → ℝ, AutomorphicForm.IsSectionFnOn A γ τ f w →
      (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
        ∀ x, F x ≠ 0 → ∫ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), w ((t : GL (Fin 2) A) * x) ∂τ = 1 :=
    fun w hw => ⟨hw.1, hw.2.1, hw.2.2.1, fun x hx => hw.2.2.2 x (mul_ne_zero_iff.1 hx).1⟩
  have key := MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) hTc μ τ F hFm hFb hFT w₁ w₂ (hsec w₁ hw₁) (hsec w₂ hw₂)

  have hswap : ∀ w : GL (Fin 2) A → ℝ, tsupport w ⊆ S →
      (fun x => f (x⁻¹ * γ * x) * (wt x : ℂ) * (w x : ℂ)) = fun x => F x * (w x : ℂ) := by
    intro w hw
    funext x
    by_cases hx : w x = 0
    · simp only [hx, hF_def, Complex.ofReal_zero, mul_zero]
    · have hxS : x ∈ S := hw (subset_tsupport w (Function.mem_support.2 hx))
      simp only [hF_def, hwt'eq x hxS]
  rw [hswap w₁ (Set.subset_union_left), hswap w₂ (Set.subset_union_right)]
  exact key

end Main

end P2mWeightedOrbitalUnique

theorem solution
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (μ : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μ)
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ)
    (wt : GL (Fin 2) A → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), ∀ x : GL (Fin 2) A,
      wt ((t : GL (Fin 2) A) * x) = wt x)
    (f : GL (Fin 2) A → ℂ) (hfm : Measurable[AutomorphicForm.glBorelOf A] f)
    (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C)
    {J₁ J₂ : ℂ} (h₁ : AutomorphicForm.IsWeightedOrbitalIntegralOn A μ wt γ τ f J₁)
    (h₂ : AutomorphicForm.IsWeightedOrbitalIntegralOn A μ wt γ τ f J₂) : J₁ = J₂ :=
  P2mWeightedOrbitalUnique.main A μ hμ γ hγ τ hτ wt hwtc hwt f hfm hfb h₁ h₂

end S_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
end P2MW
export P2MW.S_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq (solution)
