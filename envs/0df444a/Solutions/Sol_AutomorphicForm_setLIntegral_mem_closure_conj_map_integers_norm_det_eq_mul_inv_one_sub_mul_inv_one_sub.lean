-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_mem_closure_conj_map_integers_norm_det_eq_mul_inv_one_sub_mul_inv_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/bacf274f-af79-5199-99fd-16cc0c75bbdd

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_lintegral_comp_conj_twistedCentralizer_eq_mul_inv_one_sub_mul_inv_one_sub_of_map_eq_smul_map_toTensorGL_localHaar
import Theorems.Thm_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_mem_closure_conj_map_integers_norm_det_eq_mul_inv_one_sub_mul_inv_one_sub

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

namespace Ws46
namespace UM

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Topology

theorem indicator_one_mul_eq_indicator_preimage {α β : Type*} (s : Set β) (g : α → β) (f : α → ℝ≥0∞) (a : α) :
    s.indicator (fun _ => (1 : ℝ≥0∞)) (g a) * f a = (g ⁻¹' s).indicator f a := by
  by_cases h : g a ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.2 h), one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show a ∉ g ⁻¹' s from h), zero_mul]

theorem secondCountableTopology_gl (R : Type) [CommRing R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology (GL (Fin 2) R) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompactSpace_gl (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → R))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

section Local

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem continuous_norm_algebraNorm_det :
    Continuous fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => ‖Algebra.norm (v.adicCompletion K) (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  obtain ⟨-, -, h3⟩ :=
    HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm K L v
  have heq : (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => ‖Algebra.norm (v.adicCompletion K) (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖) =
      fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => ∏ w : v.Extension (𝓞 L), ‖semiLocalHomeomorph K L v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) w‖ := by
    funext g
    rw [h3, finprod_eq_prod_of_fintype]
    rfl
  rw [heq]
  exact continuous_finsetProd _ fun w _ =>
    ((continuous_apply w).comp ((semiLocalHomeomorph K L v).continuous.comp
      (Units.continuous_val.matrix_det))).norm

theorem norm_algebraNorm_includeRight (h2 : Module.finrank K L = 2) (s : v.adicCompletion K) :
    ‖Algebra.norm (v.adicCompletion K) ((Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s)‖ = ‖s‖ ^ 2 := by
  have hfr : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = 2 := by
    rw [TensorProduct.finrank_rightAlgebra, h2]
  have : (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) s := rfl
  rw [this, Algebra.norm_algebraMap, hfr, norm_pow]

omit [NumberField L] in
theorem toTensorGL_injective : Function.Injective (toTensorGL K L (v.adicCompletion K)) := by
  intro g g' h
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hij := congrArg (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) h
  exact Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective hij

omit [NumberField L] in
theorem coe_toTensorGL (g : GL (Fin 2) (v.adicCompletion K)) :
    ((toTensorGL K L (v.adicCompletion K) g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) := by
  ext i j; rfl

omit [NumberField L] in
theorem conj_cancel (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * ((y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * M * ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) * (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = M := by
  rw [mul_assoc (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) M, Units.inv_mul_cancel_left, Units.inv_mul_cancel_right]

omit [NumberField L] in
theorem conj_cancel' (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * (((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * M * (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) * ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = M := by
  rw [mul_assoc ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) M, Units.mul_inv_cancel_left, Units.mul_inv_cancel_right]

def conjIntegers (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) where
  carrier := {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
      X = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) * ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))}
  add_mem' := by
    rintro X Y ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, rfl⟩
    refine ⟨g₁ + g₂, fun i j => add_mem (hg₁ i j) (hg₂ i j), ?_⟩
    rw [Matrix.map_add _ (fun a b => map_add _ a b), Matrix.mul_add, Matrix.add_mul]
  zero_mem' := ⟨0, fun i j => zero_mem _, by rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]⟩
  neg_mem' := by
    rintro X ⟨g, hg, rfl⟩
    refine ⟨-g, fun i j => neg_mem (hg i j), ?_⟩
    rw [Matrix.map_neg _ (fun a => map_neg _ a), Matrix.mul_neg, Matrix.neg_mul]

omit [NumberField L] in
theorem mem_conjIntegers_iff (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    X ∈ conjIntegers K L v y ↔ ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
      X = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) * ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := Iff.rfl

def intSet : Set (GL (Fin 2) (v.adicCompletion K)) := {g | ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K}

def intImage : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := toTensorGL K L (v.adicCompletion K) '' intSet K v

omit [NumberField L] in
theorem mem_intImage_iff (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    x ∈ intImage K L v ↔ ∃ g : GL (Fin 2) (v.adicCompletion K), (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      toTensorGL K L (v.adicCompletion K) g = x := Iff.rfl

theorem measurableSet_intImage :
    letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    MeasurableSet (intImage K L v) := by
  letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := secondCountableTopology_gl _
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) := locallyCompactSpace_gl _
  have hO : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)).isClosed
  have hS : IsClosed (intSet K v) := by
    have : intSet K v = ⋂ i, ⋂ j, (fun g : GL (Fin 2) (v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      ext g; simp [intSet]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      hO.preimage ((Units.continuous_val : Continuous fun g : GL (Fin 2) (v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).matrix_elem i j)
  have hcont : Continuous (toTensorGL K L (v.adicCompletion K)) := by
    refine continuous_glMap _ ?_
    have : ((Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) : v.adicCompletion K → L ⊗[K] v.adicCompletion K) = fun a : v.adicCompletion K => a • (1 : L ⊗[K] v.adicCompletion K) := by
      funext a
      exact Algebra.algebraMap_eq_smul_one a
    show Continuous (fun a : v.adicCompletion K => (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) a)
    rw [this]
    exact Continuous.smul (f := fun a : v.adicCompletion K => a) (g := fun _ => (1 : L ⊗[K] v.adicCompletion K))
      continuous_id continuous_const
  obtain ⟨Kn, hKn, hU⟩ := (isSigmaCompact_univ.of_isClosed_subset hS (Set.subset_univ _)).image hcont
  show MeasurableSet (toTensorGL K L (v.adicCompletion K) '' intSet K v)
  rw [← hU]
  exact MeasurableSet.iUnion fun n => (hKn n).isClosed.measurableSet

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

omit [NumberField L] in

theorem mem_conj_iff (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ)) :
    (∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
      t.1.val = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) * ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) ↔
    y⁻¹ * t.1 * y ∈ intImage K L v := by
  rw [mem_intImage_iff]
  constructor
  · rintro ⟨g, hg, ht⟩
    have hconj : ((y⁻¹ * t.1 * y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) := by
      rw [Units.val_mul, Units.val_mul, ht]
      exact conj_cancel K L v y _
    have hdet : g.det ≠ 0 := by
      intro h0
      have hu : IsUnit (g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)).det := by
        rw [← hconj, ← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
      rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det, h0, map_zero] at hu
      exact not_isUnit_zero hu
    have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero g hdet : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = g := rfl
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hdet, fun i j => by rw [hcoe]; exact hg i j, ?_⟩
    refine Units.ext ?_
    rw [coe_toTensorGL, hcoe, hconj]
  · rintro ⟨g₀, hg₀, hι⟩
    refine ⟨(g₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)), hg₀, ?_⟩
    have hval : (g₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) = ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * t.1.val * (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
      rw [← coe_toTensorGL, hι, Units.val_mul, Units.val_mul]
    rw [hval]
    exact (conj_cancel' K L v y _).symm

end Local

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

theorem main (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ : Measure ↥(twistedCentralizer K L (v.adicCompletion K) σ δ)) (tv : ℝ≥0∞) (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hmap : letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       Measure.map (fun t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) => y⁻¹ * t.1 * y) τ =
          tv • Measure.map (toTensorGL K L (v.adicCompletion K)) (localHaar K v))
    (SM : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hSM : SM = (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
              X = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) * ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))})) :
    ∫⁻ t in {t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) | t.1.val ∈ (SM : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))},
        ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det t.1.val)‖ ∂τ =
      tv * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - (2 : ℝ)))⁻¹) := by
  classical
  letI iB := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : BorelSpace ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  have hImeas : MeasurableSet (intImage K L v) := measurableSet_intImage K L v

  have hSM' : SM = conjIntegers K L v y := by rw [hSM]; exact AddSubgroup.closure_eq (conjIntegers K L v y)
  have hset : {t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) | t.1.val ∈ (SM : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))} =
      (fun t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) => y⁻¹ * t.1 * y) ⁻¹' intImage K L v := by
    ext t
    rw [Set.mem_setOf_eq, hSM', SetLike.mem_coe, mem_conjIntegers_iff, Set.mem_preimage]
    exact mem_conj_iff K L v σ δ y t

  let Ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞ := fun x =>
    (intImage K L v).indicator (fun _ => (1 : ℝ≥0∞)) x * ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖
  have hΨm : Measurable Ψ :=
    (measurable_const.indicator hImeas).mul (continuous_norm_algebraNorm_det K L v).measurable.ennreal_ofReal
  have hΨ1 : ∀ g : GL (Fin 2) (v.adicCompletion K), (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) →
      Ψ (toTensorGL K L (v.adicCompletion K) g) =
        ((‖((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) := by
    intro g hg
    have hmem : toTensorGL K L (v.adicCompletion K) g ∈ intImage K L v := ⟨g, hg, rfl⟩
    show (intImage K L v).indicator (fun _ => (1 : ℝ≥0∞)) (toTensorGL K L (v.adicCompletion K) g) *
        ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((toTensorGL K L (v.adicCompletion K) g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ = _
    rw [Set.indicator_of_mem hmem, one_mul]
    have key : ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((toTensorGL K L (v.adicCompletion K) g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ =
        ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ^ 2 := by
      rw [coe_toTensorGL, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
      exact norm_algebraNorm_includeRight K L v h2 _
    rw [key, Matrix.GeneralLinearGroup.val_det_apply, ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, enorm_eq_nnnorm]
  have hΨ0 : ∀ g : GL (Fin 2) (v.adicCompletion K), ¬ (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) →
      Ψ (toTensorGL K L (v.adicCompletion K) g) = 0 := by
    intro g hng
    have hnot : toTensorGL K L (v.adicCompletion K) g ∉ intImage K L v := by
      rintro ⟨g', hg', h⟩
      rw [toTensorGL_injective K L v h] at hg'
      exact hng hg'
    show (intImage K L v).indicator (fun _ => (1 : ℝ≥0∞)) (toTensorGL K L (v.adicCompletion K) g) * _ = 0
    rw [Set.indicator_of_notMem hnot, zero_mul]

  have hE2 :=
    AutomorphicForm.lintegral_comp_conj_twistedCentralizer_eq_mul_inv_one_sub_mul_inv_one_sub_of_map_eq_smul_map_toTensorGL_localHaar
      K L σ v δ τ y tv hmap (2 : ℝ) Ψ hΨm hΨ1 hΨ0
  rw [← hE2]
  have hmeas : MeasurableSet ((fun t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) => y⁻¹ * t.1 * y) ⁻¹' intImage K L v) :=
    hImeas.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  rw [hset, ← lintegral_indicator hmeas]
  refine lintegral_congr fun t => ?_
  have hdet : Matrix.det ((y⁻¹ * t.1 * y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = Matrix.det t.1.val := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv,
      inv_mul_cancel_comm]
  show _ = (intImage K L v).indicator (fun _ => (1 : ℝ≥0∞)) (y⁻¹ * t.1 * y) *
    ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((y⁻¹ * t.1 * y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖
  rw [hdet]
  exact (indicator_one_mul_eq_indicator_preimage (intImage K L v) (fun t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ) => y⁻¹ * t.1 * y)
    (fun t => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det t.1.val)‖) t).symm

end Main

end Ws46.UM

set_option linter.unusedVariables false in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : HeightOneSpectrum (𝓞 K))
    (τ : Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτ : τ.IsHaarMeasure) (tv : ℝ≥0∞)
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y)
    (hmap : letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ =
          tv • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v))
    (SM : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hSM : SM = (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
              (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
              X = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
                g.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) *
                ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))})) :
    ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) |
        ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ (SM : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))}, ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ∂τ =
      tv * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - (2 : ℝ)))⁻¹) :=
  Ws46.UM.main K L h2 σ v _ τ tv y hmap SM hSM

end S_AutomorphicForm_setLIntegral_mem_closure_conj_map_integers_norm_det_eq_mul_inv_one_sub_mul_inv_one_sub
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_mem_closure_conj_map_integers_norm_det_eq_mul_inv_one_sub_mul_inv_one_sub (solution)
