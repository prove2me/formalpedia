-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
-- name    : GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:10.371463+00:00
-- url     : https://prove2.me/theorems/3f1a515f-03c0-4058-9b50-ef53bf38cf12
-- title:
--   GJMatrix Infinite
-- statement:
--   Definitions and structural lemmas for GJMatrix Infinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean

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
namespace GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
def mixedPairingPi (x y : ι → mixedSpace K) : ℝ := ∑ i, mixedTraceForm K (x i) (y i)
def mixedMeasurePi : Measure (ι → mixedSpace K) := Measure.pi fun _ ↦ selfDualMeasure K
instance : (mixedMeasurePi K : Measure (ι → mixedSpace K)).IsAddHaarMeasure := by
  unfold mixedMeasurePi
  infer_instance
variable (ι) in

abbrev EuclidPi : Type _ := EuclideanSpace ℝ (ι × Fin (finrank ℝ (euclidean.mixedSpace K)))
def euclidPiEquiv : (ι → euclidean.mixedSpace K) ≃L[ℝ] EuclidPi K ι :=
  (((LinearEquiv.piCongrRight fun _ : ι ↦
      ((stdOrthonormalBasis ℝ (euclidean.mixedSpace K)).repr.toLinearEquiv.trans
        (WithLp.linearEquiv 2 ℝ (Fin (finrank ℝ (euclidean.mixedSpace K)) → ℝ)))).trans
    (LinearEquiv.curry ℝ ℝ ι (Fin (finrank ℝ (euclidean.mixedSpace K)))).symm).trans
    (WithLp.linearEquiv 2 ℝ _).symm).toContinuousLinearEquiv
def toEuclidPi : (ι → mixedSpace K) ≃L[ℝ] EuclidPi K ι :=
  (ContinuousLinearEquiv.piCongrRight fun _ : ι ↦ mixedToEuclidean K).trans (euclidPiEquiv K)
def toEuclidPiConj : (ι → mixedSpace K) ≃L[ℝ] EuclidPi K ι :=
  (ContinuousLinearEquiv.piCongrRight fun _ : ι ↦ mixedToEuclideanConj K).trans (euclidPiEquiv K)
def mixedFourierPi (f : (ι → mixedSpace K) → ℂ) (y : ι → mixedSpace K) : ℂ :=
  ∫ x, 𝐞 (-mixedPairingPi K x y) • f x ∂mixedMeasurePi K
def mixedFourierInvPi (f : (ι → mixedSpace K) → ℂ) (x : ι → mixedSpace K) : ℂ :=
  ∫ y, 𝐞 (mixedPairingPi K x y) • f y ∂mixedMeasurePi K
def mixedFourierPiSchwartz : 𝓢(ι → mixedSpace K, ℂ) →L[ℂ] 𝓢(ι → mixedSpace K, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPiConj K)).comp
    ((SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPi K).symm))
variable {K}
def idealLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (ι → mixedSpace K) :=
  Submodule.pi Set.univ fun i ↦ idealLattice K (I i)
omit [Fintype ι] in
theorem mem_idealLatticePi {I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : ι → mixedSpace K} :
    x ∈ idealLatticePi I ↔ ∀ i, x i ∈ idealLattice K (I i) := by
  simp [idealLatticePi, Submodule.mem_pi]
instance (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : DiscreteTopology (idealLatticePi I) := by
  let f : idealLatticePi I → ∀ i, idealLattice K (I i) :=
    fun x i ↦ ⟨x.1 i, mem_idealLatticePi.mp x.2 i⟩
  have hc : Continuous f := continuous_pi fun i ↦
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h ↦
    Subtype.ext (funext fun i ↦ congrArg Subtype.val (congrFun h i))
  exact DiscreteTopology.of_continuous_injective hc hi
instance (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : IsZLattice ℝ (idealLatticePi I) where
  span_top := by
    rw [eq_top_iff]
    rintro x -
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hsp : x i ∈ Submodule.span ℝ (idealLattice K (I i) : Set (mixedSpace K)) := by
      rw [IsZLattice.span_top]
      trivial
    have hmap : Pi.single i (x i) ∈
        (Submodule.span ℝ (idealLattice K (I i) : Set (mixedSpace K))).map
          (LinearMap.single ℝ (fun _ : ι ↦ mixedSpace K) i) := ⟨x i, hsp, rfl⟩
    rw [← Submodule.span_image] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_idealLatticePi]
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using hy
    · simp [Pi.single_eq_of_ne hj]
abbrev euclidLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (EuclidPi K ι) :=
  ZLattice.comap ℝ (idealLatticePi I) (toEuclidPi K).symm.toLinearMap
abbrev euclidConjLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (EuclidPi K ι) :=
  ZLattice.comap ℝ (idealLatticePi I) (toEuclidPiConj K).symm.toLinearMap
variable (K) in

def embPi (ξ : ι → K) : ι → mixedSpace K := fun i ↦ mixedEmbedding K (ξ i)
variable (K) in

def cosetPi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ι → K) : Set (ι → K) :=
  {ξ | ∀ i, ξ i - c i ∈ (I i : FractionalIdeal (𝓞 K)⁰ K)}
end
end GroundTheory.Automorphic.GJMatrix


