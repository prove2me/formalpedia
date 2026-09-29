-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/daa9a065-4591-5829-b244-74a84cc6deac

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace Blk408UniformTorus

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

scoped instance instSecondCountableCompletion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  show SecondCountableTopology ((w : InfinitePlace K) → w.Completion) from inferInstance

scoped instance instSecondCountableUnitsArch : SecondCountableTopology (InfiniteAdeleRing K)ˣ := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance instSigmaCompactUnitsArch : SigmaCompactSpace (InfiniteAdeleRing K)ˣ :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

abbrev Ginf : Type := GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)

def dinf (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) : Ginf K L :=
  AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)

theorem toTensorGL_val_apply (A : Type) [CommRing A] [Algebra K A] (g : GL (Fin 2) A) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ ((g : Matrix (Fin 2) (Fin 2) A) i j) := rfl

theorem includeRight_injective_arch :
    Function.Injective (fun a : InfiniteAdeleRing K => (1 : L) ⊗ₜ[K] a) := by
  have h := Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := InfiniteAdeleRing K)
    (FaithfulSMul.algebraMap_injective K L)
  intro a b hab
  exact h hab

theorem dinf_injective : Function.Injective (dinf K L) := by
  intro p q hpq
  have h00 := congrArg (fun g : Ginf K L => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0) hpq
  have h11 := congrArg (fun g : Ginf K L => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1) hpq
  simp only [dinf, toTensorGL_val_apply, LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val'] at h00 h11
  have h1 : (p.1 : InfiniteAdeleRing K) = q.1 := includeRight_injective_arch K L h00
  have h2 : (p.2 : InfiniteAdeleRing K) = q.2 := includeRight_injective_arch K L h11
  exact Prod.ext (Units.ext h1) (Units.ext h2)

theorem continuous_diagUnits2 (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun p : Aˣ × Aˣ => (diagUnits2 p.1 p.2 : GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa [Function.comp_def] using Units.continuous_val.comp continuous_fst
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa [Function.comp_def] using Units.continuous_val.comp continuous_snd
  · have h : ∀ p : Aˣ × Aˣ, ((diagUnits2 p.1 p.2 : GL (Fin 2) A)⁻¹ : GL (Fin 2) A).val =
        !![((p.1⁻¹ : Aˣ) : A), 0; 0, ((p.2⁻¹ : Aˣ) : A)] := fun p => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa [Function.comp_def] using Units.continuous_coe_inv.comp continuous_fst
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa [Function.comp_def] using Units.continuous_coe_inv.comp continuous_snd

theorem continuous_includeRight (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h : (fun a : A => (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      fun a : A => a • ((1 : L) ⊗ₜ[K] (1 : A)) := by
    funext a
    rw [Algebra.TensorProduct.includeRight_apply, AutomorphicForm.rightActions_smul_eq K L A a]
    simp
  show Continuous fun a : A => (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a
  rw [h]
  exact continuous_id.fun_smul continuous_const

theorem continuous_toTensorGL (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    Continuous (AutomorphicForm.toTensorGL K L A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  exact AutomorphicForm.continuous_glMap _ (continuous_includeRight K L A)

theorem continuous_dinf : Continuous (dinf K L) :=
  (continuous_toTensorGL K L (InfiniteAdeleRing K)).comp (continuous_diagUnits2 (InfiniteAdeleRing K))

variable [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
  (νA : Measure (InfiniteAdeleRing K)ˣ) [νA.IsHaarMeasure]

def C₁ : TopologicalSpace.PositiveCompacts (InfiniteAdeleRing K)ˣ := Classical.arbitrary _

def E : Set (Ginf K L) := dinf K L '' ((C₁ K : Set (InfiniteAdeleRing K)ˣ) ×ˢ (C₁ K : Set (InfiniteAdeleRing K)ˣ))

theorem isCompact_E : IsCompact (E K L) :=
  ((C₁ K).isCompact.prod (C₁ K).isCompact).image (continuous_dinf K L)

theorem isClosed_E : IsClosed (E K L) := by
  haveI := AutomorphicForm.t2Space_tensorGL K L (InfiniteAdeleRing K)
  exact (isCompact_E K L).isClosed

theorem preimage_E :
    dinf K L ⁻¹' E K L = (C₁ K : Set (InfiniteAdeleRing K)ˣ) ×ˢ (C₁ K : Set (InfiniteAdeleRing K)ˣ) :=
  (dinf_injective K L).preimage_image _

def Wa₀ : Ginf K L → ℂ := (E K L).indicator fun _ => (1 : ℂ)

def W₀ (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : ℂ :=
  open Classical in
  if ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v
  then Wa₀ K L (AutomorphicForm.tensorArch K L x) else 0

theorem Wa₀_comp_dinf (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) :
    Wa₀ K L (dinf K L p) =
      ((C₁ K : Set (InfiniteAdeleRing K)ˣ) ×ˢ (C₁ K : Set (InfiniteAdeleRing K)ˣ)).indicator
        (fun _ => (1 : ℂ)) p := by
  rw [Wa₀, ← preimage_E K L]
  rfl

theorem integral_Wa₀_dinf :
    ∫ p, Wa₀ K L (dinf K L p) ∂(νA.prod νA) = ((νA.real (C₁ K)) * (νA.real (C₁ K)) : ℝ) := by
  simp_rw [Wa₀_comp_dinf]
  rw [integral_indicator_const _ ((C₁ K).isCompact.measurableSet.prod (C₁ K).isCompact.measurableSet)]
  rw [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  simp [Measure.real]

theorem real_C₁_pos : 0 < νA.real (C₁ K) := by
  rw [Measure.real, ENNReal.toReal_pos_iff]
  exact ⟨Measure.measure_pos_of_nonempty_interior _ (C₁ K).interior_nonempty, (C₁ K).isCompact.measure_lt_top⟩

end Blk408UniformTorus
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal.Blk408UniformTorus"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal.Blk408UniformTorus"

open Blk408UniformTorus in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure]
    (cτ : ℝ) (hcτ : 0 < cτ) :
    ∃ cT : ℝ, 0 < cT ∧
    ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
    ∀ (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t →
    ∀ (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ →
      (∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
            g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ =
          cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νK.prod νK)) →
    ∀ (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ))
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ))),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)) τa →
      (∀ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ),
            g (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) ∂τa =
          ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            g (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)) ∂(νA.prod νA)) →
    ∀ (τf : ∀ v : HeightOneSpectrum (𝓞 K),
        @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ))
          (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ))),
      (∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)) (τf v)) →
      (∀ v : HeightOneSpectrum (𝓞 K),
        τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)] (fun t => WS v t) (τf v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by
  classical

  set A : ℂ := ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
      W₀ K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νK.prod νK) with hA
  set B : ℂ := ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
      Wa₀ K L (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)) ∂(νA.prod νA) with hB
  have hBval : B = ((νA.real (C₁ K)) * (νA.real (C₁ K)) : ℝ) := integral_Wa₀_dinf K L νA
  have hBre : B.re = νA.real (C₁ K) * νA.real (C₁ K) := by rw [hBval, Complex.ofReal_re]
  have hBpos : 0 < B.re := by rw [hBre]; exact mul_pos (real_C₁_pos K νA) (real_C₁_pos K νA)
  set c₀ : ℝ := cτ * A.re / B.re with hc₀
  refine ⟨if 0 < c₀ then c₀ else 1, by split_ifs with h; exacts [h, one_pos], ?_⟩
  intro t ht10 ht01 hreg δ hδ τ hτH hτ τa hτaH hτa τf hτfH hτf1 S W Wa WS hWa hWS hfac hvan

  obtain ⟨c, hc, hcid⟩ :=
    AutomorphicForm.exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
      K L σ δ τ hτH τa hτaH τf hτfH hτf1

  have hWa₀m : AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L δ)]
      (fun s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ) =>
        Wa₀ K L s) τa := by
    letI := AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
    haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
    letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ)
    haveI : BorelSpace
        (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ)) := ⟨rfl⟩
    haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
    have hEm : MeasurableSet (E K L) := (isClosed_E K L).measurableSet
    have hpre : MeasurableSet ((Subtype.val :
        AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ) →
          GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) ⁻¹' E K L) :=
      hEm.preimage continuous_subtype_val.measurable
    have heq : (fun s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ) => Wa₀ K L s) =
        ((Subtype.val ⁻¹' E K L)).indicator fun _ => (1 : ℂ) := by
      funext s
      simp only [Wa₀, Set.indicator_apply, Set.mem_preimage]
    rw [heq]
    exact (measurable_const.indicator hpre).aestronglyMeasurable
  have hWS₀ : ∀ v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 K))),
      AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ)]
        (fun s : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v δ) =>
          (fun (_ : HeightOneSpectrum (𝓞 K)) (_ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) => (0 : ℂ)) v s)
        (τf v) := fun v hv => absurd hv (Finset.notMem_empty v)
  have hfac₀ : ∀ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
      (∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K))),
        AutomorphicForm.tensorPlace K L v s ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
      W₀ K L s = Wa₀ K L (AutomorphicForm.tensorArch K L s) *
        ∏ v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 K))),
          (fun (v : HeightOneSpectrum (𝓞 K)) (_ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) => (0 : ℂ)) v
            (AutomorphicForm.tensorPlace K L v s) := by
    intro s hs
    have hall : ∀ v : HeightOneSpectrum (𝓞 K),
        AutomorphicForm.tensorPlace K L v s ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
      fun v => hs v (Finset.notMem_empty v)
    rw [Finset.prod_empty, mul_one, W₀, if_pos hall]
  have hvan₀ : ∀ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
      (∃ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K))),
        AutomorphicForm.tensorPlace K L v s ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
      W₀ K L s = 0 := by
    rintro s ⟨v, -, hv⟩
    have hnot : ¬ ∀ v : HeightOneSpectrum (𝓞 K),
        AutomorphicForm.tensorPlace K L v s ∈ AutomorphicForm.semiLocalIntegralSet K L v := fun h => hv (h v)
    rw [W₀, if_neg hnot]
  have htest := hcid ∅ (W₀ K L) (Wa₀ K L) (fun _ _ => 0) hWa₀m hWS₀ hfac₀ hvan₀
  rw [Finset.prod_empty, mul_one, hτ (W₀ K L), hτa (Wa₀ K L)] at htest

  have hre : cτ * A.re = c * B.re := by
    have h := congrArg Complex.re htest
    rwa [Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h
  have hc_eq : c = c₀ := by
    rw [hc₀, eq_div_iff hBpos.ne', hre]
  have hcT : (if 0 < c₀ then c₀ else 1) = c := by rw [if_pos (hc_eq ▸ hc), hc_eq]
  rw [hcT]
  exact hcid S W Wa WS hWa hWS hfac hvan

end S_AutomorphicForm_exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_integral_twistedCentralizer_eq_mul_integral_tensorArch_mul_prod_integral_tensorPlace_of_diagonal (solution)
