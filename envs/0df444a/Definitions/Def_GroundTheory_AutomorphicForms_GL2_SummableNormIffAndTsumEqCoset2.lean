-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
-- name    : GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:47.921654+00:00
-- url     : https://prove2.me/theorems/01beb5c2-da59-487e-a860-718a518bfb17
-- title:
--   Summable Norm Iff And Tsum Eq Coset2
-- statement:
--   Definitions and structural lemmas for Summable Norm Iff And Tsum Eq Coset2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
def mixedPairing2 (x y : Fin 2 → mixedSpace K) : ℝ := ∑ i, mixedTraceForm K (x i) (y i)
def mixedMeasure2 : Measure (Fin 2 → mixedSpace K) := Measure.pi fun _ => selfDualMeasure K
instance : (mixedMeasure2 K).IsAddHaarMeasure := by
  unfold mixedMeasure2
  infer_instance
def toEuclid2 : (Fin 2 → mixedSpace K) ≃L[ℝ]
    WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) :=
  ((ContinuousLinearEquiv.finTwoArrow ℝ (mixedSpace K)).trans
    ((mixedToEuclidean K).prodCongr (mixedToEuclidean K))).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm
def toEuclid2Conj : (Fin 2 → mixedSpace K) ≃L[ℝ]
    WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) :=
  ((ContinuousLinearEquiv.finTwoArrow ℝ (mixedSpace K)).trans
    ((mixedToEuclideanConj K).prodCongr (mixedToEuclideanConj K))).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm
def mixedFourier2 (f : (Fin 2 → mixedSpace K) → ℂ) (y : Fin 2 → mixedSpace K) : ℂ :=
  ∫ x, 𝐞 (-mixedPairing2 K x y) • f x ∂mixedMeasure2 K
def mixedFourierInv2 (f : (Fin 2 → mixedSpace K) → ℂ) (x : Fin 2 → mixedSpace K) : ℂ :=
  ∫ y, 𝐞 (mixedPairing2 K x y) • f y ∂mixedMeasure2 K
def mixedFourier2Schwartz : 𝓢(Fin 2 → mixedSpace K, ℂ) →L[ℂ] 𝓢(Fin 2 → mixedSpace K, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2Conj K)).comp
    ((SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2 K).symm))
variable {K}
def idealLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (Fin 2 → mixedSpace K) :=
  Submodule.pi Set.univ fun i => idealLattice K (I i)
theorem mem_idealLattice2 {I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : Fin 2 → mixedSpace K} :
    x ∈ idealLattice2 I ↔ ∀ i, x i ∈ idealLattice K (I i) := by
  simp [idealLattice2, Submodule.mem_pi]
instance (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : DiscreteTopology (idealLattice2 I) := by
  let f : idealLattice2 I → ∀ i, idealLattice K (I i) :=
    fun x i => ⟨x.1 i, mem_idealLattice2.mp x.2 i⟩
  have hc : Continuous f := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h =>
    Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  exact DiscreteTopology.of_continuous_injective hc hi
instance (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : IsZLattice ℝ (idealLattice2 I) where
  span_top := by
    classical
    rw [eq_top_iff]
    rintro x -
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hsp : x i ∈ Submodule.span ℝ (idealLattice K (I i) : Set (mixedSpace K)) := by
      rw [IsZLattice.span_top]
      trivial
    have hmap : Pi.single i (x i) ∈ (Submodule.span ℝ (idealLattice K (I i) : Set (mixedSpace K))).map
        (LinearMap.single ℝ (fun _ : Fin 2 => mixedSpace K) i) := ⟨x i, hsp, rfl⟩
    rw [← Submodule.span_image] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_idealLattice2]
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using hy
    · simp [Pi.single_eq_of_ne hj]
abbrev euclidLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) :=
  ZLattice.comap ℝ (idealLattice2 I) (toEuclid2 K).symm.toLinearMap
abbrev euclidConjLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) :=
  ZLattice.comap ℝ (idealLattice2 I) (toEuclid2Conj K).symm.toLinearMap
variable (K) in

def emb2 (ξ : Fin 2 → K) : Fin 2 → mixedSpace K := fun i => mixedEmbedding K (ξ i)
variable (K) in

def coset2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : Fin 2 → K) : Set (Fin 2 → K) :=
  {ξ | ∀ i, ξ i - c i ∈ (I i : FractionalIdeal (𝓞 K)⁰ K)}
end
end GroundTheory.Automorphic.Adele2


