-- Prove2me | solution 1 for AutomorphicForm.map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/687bd41c-ec3c-514f-a9e1-cb88df23e5fc

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open MeasureTheory NumberField AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal

noncomputable section

namespace P2mXiMeas

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev F : Type := InfiniteAdeleRing K

abbrev EK : Type := L ⊗[K] InfiniteAdeleRing K

abbrev EP : Type := (w : InfinitePlace K) → L ⊗[K] w.Completion

abbrev algRF : Algebra ℝ (F K) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra

attribute [local instance] algRF

abbrev algRE : Algebra ℝ (EK K L) :=
  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
    (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra

attribute [local instance] algRE

scoped instance instTopRingEK : IsTopologicalRing (EK K L) := isTopologicalRing_tensor K L (InfiniteAdeleRing K)

scoped instance instMeasEK : MeasurableSpace (Matrix (Fin 2) (Fin 2) (EK K L)) := borel _
scoped instance instBorelEK : BorelSpace (Matrix (Fin 2) (Fin 2) (EK K L)) := ⟨rfl⟩
scoped instance instMeasEP : MeasurableSpace (Matrix (Fin 2) (Fin 2) (EP K L)) := borel _
scoped instance instBorelEP : BorelSpace (Matrix (Fin 2) (Fin 2) (EP K L)) := ⟨rfl⟩

theorem continuous_includeRight :
    Continuous (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) := by
  have : ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) :
      InfiniteAdeleRing K → EK K L) = algebraMap (F K) (EK K L) := rfl
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (F K) (EK K L))

theorem continuous_ringEquiv_mixedSpace_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  apply continuous_pi
  intro v
  by_cases hv : InfinitePlace.IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : InfinitePlace.IsComplex v := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

theorem continuous_algebraMap_RF : Continuous (algebraMap ℝ (F K)) :=
  (continuous_ringEquiv_mixedSpace_symm K).comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace K))

scoped instance continuousSMul_RF : ContinuousSMul ℝ (F K) :=
  ⟨by
    have : (fun p : ℝ × F K => p.1 • p.2) = fun p => algebraMap ℝ (F K) p.1 * p.2 := by
      funext p; exact Algebra.smul_def p.1 p.2
    rw [this]
    exact ((continuous_algebraMap_RF K).comp continuous_fst).mul continuous_snd⟩

theorem continuous_algebraMap_RE : Continuous (algebraMap ℝ (EK K L)) :=
  (continuous_includeRight K L).comp (continuous_algebraMap_RF K)

scoped instance continuousSMul_RE : ContinuousSMul ℝ (EK K L) :=
  ⟨by
    have : (fun p : ℝ × EK K L => p.1 • p.2) = fun p => algebraMap ℝ (EK K L) p.1 * p.2 := by
      funext p; exact Algebra.smul_def p.1 p.2
    rw [this]
    exact ((continuous_algebraMap_RE K L).comp continuous_fst).mul continuous_snd⟩

scoped instance continuousSMul_matEK : ContinuousSMul ℝ (Matrix (Fin 2) (Fin 2) (EK K L)) := inferInstance

section Transport

variable (Ξ : EK K L ≃+* EP K L) (hΞ : Continuous Ξ) (hΞ' : Continuous Ξ.symm)
  [algE : ∀ w : InfinitePlace K, Algebra ℝ (L ⊗[K] w.Completion)]
  (hΞr : ∀ (r : ℝ) (z : EK K L), Ξ (r • z) = r • Ξ z)

include hΞr in

def ΞA : EK K L ≃ₐ[ℝ] EP K L :=
  AlgEquiv.ofRingEquiv (f := Ξ) fun r => by
    rw [Algebra.algebraMap_eq_smul_one, hΞr, map_one, ← Algebra.algebraMap_eq_smul_one]

theorem ΞA_apply (z : EK K L) : ΞA K L Ξ hΞr z = Ξ z := rfl

def ΦH : Matrix (Fin 2) (Fin 2) (EK K L) ≃ₜ Matrix (Fin 2) (Fin 2) (EP K L) where
  toFun X := X.map Ξ
  invFun Y := Y.map Ξ.symm
  left_inv X := by ext i j; simp
  right_inv Y := by ext i j; simp
  continuous_toFun := continuous_id.matrix_map hΞ
  continuous_invFun := continuous_id.matrix_map hΞ'

theorem ΦH_apply (X : Matrix (Fin 2) (Fin 2) (EK K L)) : ΦH K L Ξ hΞ hΞ' X = X.map Ξ := rfl

include hΞr in
theorem map_linComb {n : ℕ} (e : Fin n → Matrix (Fin 2) (Fin 2) (EK K L)) (c : Fin n → ℝ) :
    (∑ i, c i • e i).map Ξ = ∑ i, c i • (e i).map Ξ := by
  ext a b
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, map_sum, hΞr]

include hΞr in
theorem trace_map_map (X Y : Matrix (Fin 2) (Fin 2) (EK K L)) :
    Algebra.trace ℝ (EP K L) (Matrix.trace (X.map Ξ * Y.map Ξ)) =
      Algebra.trace ℝ (EK K L) (Matrix.trace (X * Y)) := by
  have hm : (X * Y).map Ξ = X.map Ξ * Y.map Ξ := Matrix.map_mul (f := Ξ.toRingHom)
  have ht : Matrix.trace ((X * Y).map Ξ) = Ξ (Matrix.trace (X * Y)) := by
    change ∑ i, (X * Y).map Ξ i i = Ξ (∑ i, (X * Y) i i)
    rw [map_sum]
    rfl
  rw [← hm, ht, ← ΞA_apply K L Ξ hΞr, Algebra.trace_eq_of_algEquiv]

include hΞr in
theorem density_map (X : Matrix (Fin 2) (Fin 2) (EK K L)) :
    (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det (X.map Ξ))|)⁻¹ =
      (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹ := by
  rw [show Matrix.det (X.map Ξ) = Ξ (Matrix.det X) from (RingHom.map_det Ξ.toRingHom X).symm,
    ← ΞA_apply K L Ξ hΞr, Algebra.norm_eq_of_algEquiv]

theorem withDensity_map_of_measurableEmbedding {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → ℝ≥0∞) :
    (Measure.map f μ).withDensity g = Measure.map f (μ.withDensity (g ∘ f)) := by
  ext s hs
  rw [withDensity_apply _ hs, hf.restrict_map, hf.lintegral_map, hf.map_apply,
    withDensity_apply _ (hf.measurable hs)]
  simp only [Function.comp_apply]

include hΞ hΞ' hΞr in

theorem transport {n : ℕ} (e : Fin n → Matrix (Fin 2) (Fin 2) (EK K L)) (s : ENNReal)
    (ν : Measure (Matrix (Fin 2) (Fin 2) (EK K L)))
    (hν : ν = s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                Algebra.trace ℝ (EK K L) (Matrix.trace (e i * e j))).det|)) •
              Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
            (fun X : Matrix (Fin 2) (Fin 2) (EK K L) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) :
    Measure.map (fun X : Matrix (Fin 2) (Fin 2) (EK K L) => X.map Ξ) ν =
      s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
              Algebra.trace ℝ (EP K L) (Matrix.trace ((e i).map Ξ * (e j).map Ξ))).det|)) •
            Measure.map (fun c : Fin n → ℝ => ∑ i, c i • (e i).map Ξ) volume).withDensity
          (fun X : Matrix (Fin 2) (Fin 2) (EP K L) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by
  have hemb : MeasurableEmbedding (fun X : Matrix (Fin 2) (Fin 2) (EK K L) => X.map Ξ) :=
    (ΦH K L Ξ hΞ hΞ').toMeasurableEquiv.measurableEmbedding
  have hlin : Measurable fun c : Fin n → ℝ => ∑ i, c i • e i :=
    (continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const).measurable
  have hdens : (fun X : Matrix (Fin 2) (Fin 2) (EK K L) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) =
      (fun X : Matrix (Fin 2) (Fin 2) (EP K L) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∘
        (fun X : Matrix (Fin 2) (Fin 2) (EK K L) => X.map Ξ) := by
    funext X; exact (density_map K L Ξ hΞr X).symm
  have hgram : (Matrix.of fun i j : Fin n => Algebra.trace ℝ (EP K L) (Matrix.trace ((e i).map Ξ * (e j).map Ξ))) =
      Matrix.of fun i j : Fin n => Algebra.trace ℝ (EK K L) (Matrix.trace (e i * e j)) := by
    ext i j; exact trace_map_map K L Ξ hΞr (e i) (e j)
  have hcomp : ((fun X : Matrix (Fin 2) (Fin 2) (EK K L) => X.map Ξ) ∘ fun c : Fin n → ℝ => ∑ i, c i • e i) =
      fun c : Fin n → ℝ => ∑ i, c i • (e i).map Ξ := by
    funext c; exact map_linComb K L Ξ hΞr e c
  rw [hν, Measure.map_smul, hdens, ← withDensity_map_of_measurableEmbedding hemb, Measure.map_smul,
    Measure.map_map hemb.measurable hlin, hcomp, hgram]

end Transport

end P2mXiMeas
p2m_reactivate "P2MW.S_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing.P2mXiMeas"

end
p2m_reactivate "P2MW.S_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing.P2mXiMeas"

open P2mXiMeas in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((w : InfinitePlace K) → L ⊗[K] w.Completion))
    (hΞ : Continuous Ξ) (hΞ' : Continuous Ξ.symm)
    [algE : ∀ w : InfinitePlace K, Algebra ℝ (L ⊗[K] w.Completion)]
    (hΞr : ∀ (r : ℝ) (z : L ⊗[K] InfiniteAdeleRing K),
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      Ξ (r • z) = r • Ξ z)
    (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal)
    (hL :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
          ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
        s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
              Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
            (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
              (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) :
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion)) := borel _
    letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
    Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
        (((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).map Ξ) τ' =
      s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
              Algebra.trace ℝ ((w : InfinitePlace K) → L ⊗[K] w.Completion)
                (Matrix.trace ((e₂ i).map Ξ * (e₂ j).map Ξ))).det|)) •
            Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • (e₂ i).map Ξ) volume).withDensity
          (fun X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion) =>
            (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by
  letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
  haveI : BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
  have hι : Measurable (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
      ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) :=
    (Units.continuous_val.comp continuous_subtype_val).measurable
  have hΦ : Measurable (fun X : Matrix (Fin 2) (Fin 2) (EK K L) => X.map Ξ) :=
    (continuous_id.matrix_map hΞ).measurable
  have hcomp : (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
        (((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))).map Ξ) =
      (fun X : Matrix (Fin 2) (Fin 2) (EK K L) => X.map Ξ) ∘
        (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
          ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := rfl
  rw [hcomp, ← Measure.map_map hΦ hι]
  exact transport K L Ξ hΞ hΞ' hΞr e₂ s _ hL

end S_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing
end P2MW
export P2MW.S_AutomorphicForm_map_twistedCentralizer_map_ringEquiv_pi_eq_smul_gram_of_infiniteAdeleRing (solution)
