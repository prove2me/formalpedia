-- Prove2me | Definitions.Def_OAIHecke78B010
-- name    : OAIHecke78B010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T23:57:09.536217+00:00
-- url     : https://prove2.me/theorems/c04fec2f-a007-4d0f-a03b-169b9e4eb793
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 11 of 29
-- statement:
--   Definitions bundle 11 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B009` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `MeanSquare.UnitRows`, `Eisenstein.BarrierPotential`, `CubicSieve.CutoffOrders`, `Eisenstein.FredholmAlternative`, `Eisenstein.MeromorphicResolvent`, `Eisenstein.UnitNormalization`, `RowCompletion.CubicReopening`, `Eisenstein.SeedHeight`, `Eisenstein.CuspResidues`, `MeanSquare.ThetaDensity`, `RowCompletion.ThetaNonvanishing`, `Descent.FirstOriginalProfileAssembly`, `Descent.CanonicalRankMoments`, `Hecke.ReciprocalGrowth`, `Hecke.PrimeDyadicBuffered`, `PrimeCounting.RayAsymptotic`, `Dictionary.InverseMarkedReferenceOverlap`, `Dictionary.InverseMarkedReferenceRemaining`, `Dictionary.InverseMarkedReferenceEnergy`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B009

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B010

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  MeanSquare.UnitRows
  Eisenstein.BarrierPotential
  CubicSieve.CutoffOrders
  Eisenstein.FredholmAlternative
  Eisenstein.MeromorphicResolvent
  Eisenstein.UnitNormalization
  RowCompletion.CubicReopening
  Eisenstein.SeedHeight
  Eisenstein.CuspResidues
  MeanSquare.ThetaDensity
  RowCompletion.ThetaNonvanishing
  Descent.FirstOriginalProfileAssembly
  Descent.CanonicalRankMoments
  Hecke.ReciprocalGrowth
  Hecke.PrimeDyadicBuffered
  PrimeCounting.RayAsymptotic
  Dictionary.InverseMarkedReferenceOverlap
  Dictionary.InverseMarkedReferenceRemaining
  Dictionary.InverseMarkedReferenceEnergy
-/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

namespace CubicEisenstein

def euclideanAxisPath (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) : EuclideanSpatial :=
  WithLp.toLp 2 (Function.update p.ofLp j t)

lemma euclideanAxisPath_affine (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    euclideanAxisPath p j t=p+(t-p j)•euclideanCoordinateVector j := by
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext k
  by_cases hk : k=j
  · subst k
    simp [euclideanAxisPath,euclideanCoordinateVector]
  · simp [euclideanAxisPath,euclideanCoordinateVector,Function.update,hk]

lemma euclideanAxisPath_self (p : EuclideanSpatial) (j : Fin 3) :
    euclideanAxisPath p j (p j)=p := by
  rw [euclideanAxisPath_affine,sub_self,zero_smul,add_zero]

lemma euclideanAxisPath_hasDerivAt (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    HasDerivAt (euclideanAxisPath p j) (euclideanCoordinateVector j) t := by
  have he : euclideanAxisPath p j=(fun t => p+(t-p j)•euclideanCoordinateVector j) :=
    funext (euclideanAxisPath_affine p j)
  rw [he]
  simpa only [sub_zero,one_smul,zero_add,Pi.add_apply,id_eq] using!
    (hasDerivAt_const t p).add (((hasDerivAt_id t).sub_const (p j)).smul_const (euclideanCoordinateVector j))

lemma euclideanAxisSlice_deriv (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (j : Fin 3) (t : ℝ) (hf : DifferentiableAt ℝ f (euclideanAxisPath p j t)) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) t=
      fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j) :=
  (hf.hasFDerivAt.comp_hasDerivAt t (euclideanAxisPath_hasDerivAt p j t)).deriv

lemma euclideanAxisSlice_derivatives (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) (p j)=
      fderiv ℝ f p (euclideanCoordinateVector j) ∧
    deriv (deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)) (p j)=
      fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p (euclideanCoordinateVector j) := by
  constructor
  · simpa only [euclideanAxisPath_self] using euclideanAxisSlice_deriv f p j (p j)
      (by simpa only [euclideanAxisPath_self] using (hf p hp).differentiableAt (by simp))
  · have hc : ContinuousAt (fun t => euclideanAxisPath p j t 2) (p j) :=
      (by fun_prop : Continuous (fun q : EuclideanSpatial => q 2)).continuousAt.comp
        (euclideanAxisPath_hasDerivAt p j (p j)).continuousAt
    have hpos : 0<euclideanAxisPath p j (p j) 2 := by rw [euclideanAxisPath_self]; exact hp
    have he : deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)=ᶠ[𝓝 (p j)]
        (fun t => fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j)) := by
      filter_upwards [hc.eventually_const_lt hpos] with t ht
      exact euclideanAxisSlice_deriv f p j t ((hf _ ht).differentiableAt (by simp))
    rw [he.deriv_eq]
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p :=
      (((hf p hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hd' : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j))
        (euclideanAxisPath p j (p j)) := by rwa [euclideanAxisPath_self]
    have hh := hd'.hasFDerivAt.comp_hasDerivAt (p j) (euclideanAxisPath_hasDerivAt p j (p j))
    simpa only [euclideanAxisPath_self,Function.comp_def] using! hh.deriv

def positiveEuclideanLaplacian (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p
    (euclideanCoordinateVector j))+(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector 2)

lemma positiveEuclideanLaplacian_eq_axis (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian f p=-axisLaplacian (fun q => f (WithLp.toLp 2 q)) p.ofLp := by
  unfold positiveEuclideanLaplacian axisLaplacian
  simp only [(euclideanAxisSlice_derivatives f hf p hp _).1,(euclideanAxisSlice_derivatives f hf p hp _).2]
  ring

lemma positiveEuclideanLaplacian_congr (f g : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (he : f=ᶠ[𝓝 p]g) : positiveEuclideanLaplacian f p=positiveEuclideanLaplacian g p := by
  have hd (j : Fin 3) : (fun q => fderiv ℝ f q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  simp only [positiveEuclideanLaplacian,he.fderiv_eq,(hd _).fderiv_eq]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv Manifold

namespace CubicEisenstein

lemma kernelTestPartitionTerm_tsupport_right {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) :
    tsupport (kernelTestPartitionTerm ρ f i).1⊆tsupport f.1 :=
  tsupport_smul_subset_right _ _

lemma kernelSmoothTest_finite_chart_partition_subsupport (f : kernelSmoothTests) :
    ∃t : Finset KernelGoodCutoff,∃g : t→kernelSmoothTests,
      (∑i,g i)=f ∧ ∀i,tsupport (g i).1⊆kernelChartCoreImage i.1.1 ∧
        tsupport (g i).1⊆tsupport f.1 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover (tsupport f.1) f.2.2
  have hc : tsupport f.1⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,SpatialCoordinates)
    (isClosed_tsupport f.1) (fun χ : t => kernelChartCoreImage χ.1.1)
    (fun χ => kernelChartCoreImage_open χ.1.1) hc
  refine ⟨t,kernelTestPartitionTerm ρ f,kernelTestPartition_sum f ρ,fun i => ?_⟩
  exact ⟨(kernelTestPartitionTerm_tsupport ρ f i).trans (hρ i),
    kernelTestPartitionTerm_tsupport_right ρ f i⟩

lemma kernelDirichletForm_supported_equation_chart (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelEuclideanProjection p∈tsupport g.1→
      kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hi : Integrable (fun q => star (A q)*g.1 q) (integralQuotientVolume globalKubotaKernel) :=
    hA.star.integrable_mul (kernelSmoothTests_memLp g)
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  rw [kernelDirichletForm_eq_chart_laplacian χ hinj f g hg]
  calc
    _ = ∫p in S,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (kernelCoreLift_tsupport_outer χ g h))
      rw [hz,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)/(p 2:ℂ)^3 := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_eq_on_outer χ hinj g hg hp]
      by_cases hc : p∈kernelChartCore χ
      · by_cases hgp : kernelEuclideanProjection p∈tsupport g.1
        · rw [kernelCoreLift_laplacian χ f p hc,heq p (χ.positive hp) hgp]
          rfl
        · have hz : g.1 (kernelEuclideanProjection p)=0 := image_eq_zero_of_notMem_tsupport hgp
          change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
          rw [hz,mul_zero,zero_div,mul_zero,zero_div]
      · have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
          (fun h => hc (kernelCoreLift_tsupport χ hinj g hg h))
        rw [kernelCoreLift_eq_on_outer χ hinj g hg hp] at hz
        change g.1 (kernelEuclideanProjection p)=0 at hz
        change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
        rw [hz,mul_zero,zero_div,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (hyperbolicEuclidean_setIntegral_complex S hS χ.positive _).symm
    _ = ∫q in kernelEuclideanProjection '' S,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_integral_complex S hS χ.positive hinj _ hi.aestronglyMeasurable
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      have hz : g.1 q=0 := image_eq_zero_of_notMem_tsupport (fun h => hq (himg (hg h)))
      rw [hz,mul_zero]

theorem kernelDirichletForm_supported_equation (f g : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelEuclideanProjection p∈tsupport g.1→
      kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  obtain ⟨t,G,hG,hGsupp⟩ := kernelSmoothTest_finite_chart_partition_subsupport g
  calc
    _ = ∑i : t,kernelDirichletForm f (G i) := by
      rw [←hG,kernelDirichletForm_sum_right]
    _ = ∑i : t,∫q,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      apply Finset.sum_congr rfl
      intro i hi
      exact kernelDirichletForm_supported_equation_chart i.1.1 i.1.2 f (G i) (hGsupp i).1 A hA (fun p hp hgp => heq p hp ((hGsupp i).2 hgp))
    _ = ∫q,∑i : t,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      symm
      exact integral_finsetSum _ (fun i hi => hA.star.integrable_mul (kernelSmoothTests_memLp (G i)))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun q => by
        have hq := congrArg (fun k : kernelSmoothTests => k.1 q) hG
        simp only [Submodule.coe_sum,Finset.sum_apply] at hq
        dsimp only
        rw [←Finset.mul_sum,hq])

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma axisLaplacian_const_add (c : ℂ) (f : SpatialCoordinates→ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c+f q) p=axisLaplacian f p := by
  unfold axisLaplacian axisSlice
  simp only [deriv_const_add,deriv_const_add']

lemma fullCuspProfileField_summable (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    Summable (fun x => F (rowHeight (fullCuspRow x) p)) := by
  simpa only [fullCuspRow_height _ p hp] using
    fullCuspProfileSum_summable F hF (upperPoint (spatialHorizontal p) (p 2) hp)

lemma fullCuspProfileField_add (F G : ℝ→ℝ) (hF : ∀v≤1,F v=0) (hG : ∀v≤1,G v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    fullCuspProfileField (fun v => F v+G v) p=fullCuspProfileField F p+fullCuspProfileField G p :=
  (fullCuspProfileField_summable F hF p hp).tsum_add
    (fullCuspProfileField_summable G hG p hp)

lemma cuspBarrierProfile_laplacian_zero (a b v : ℝ) (ha : 1<a) (hab : a<b) (hv : v≤1) :
    positiveHeightLaplacian (cuspBarrierProfile a b) v=0 := by
  have hh := cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha)
  rw [cuspBarrierDefectProfile,cuspBarrierProfile_zero a b hab v (hv.trans ha.le),sub_zero] at hh
  exact hh

def cuspBarrierField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  1+fullCuspProfileField (cuspBarrierProfile a b) p

def cuspBarrierDefectField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  -1+fullCuspProfileField (cuspBarrierDefectProfile a b) p

lemma cuspBarrierField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierField a b p=cuspBarrier a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierField,cuspBarrier,fullCuspProfileField_eq _ p hp]

lemma cuspBarrierDefectField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierDefectField a b p=cuspBarrierDefect a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierDefectField,cuspBarrierDefect,fullCuspProfileField_eq _ p hp]

lemma cuspBarrierField_laplace_defect (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (cuspBarrierField a b q:ℂ)) p-(cuspBarrierField a b p:ℂ)=
      (cuspBarrierDefectField a b p:ℂ) := by
  have hF : ∀v≤1,cuspBarrierProfile a b v=0 :=
    fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha.le)
  have hD : ∀v≤1,cuspBarrierDefectProfile a b v=0 :=
    fun v hv => cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha)
  have hid : positiveHeightLaplacian (cuspBarrierProfile a b)=
      fun v => cuspBarrierDefectProfile a b v+cuspBarrierProfile a b v := by
    funext v
    rw [cuspBarrierDefectProfile,sub_add_cancel]
  have hh := fullCuspProfileField_laplacian _ (cuspBarrierProfile_smooth a b) hF
    (fun v hv => cuspBarrierProfile_laplacian_zero a b v ha hab hv) p hp
  simp only [cuspBarrierField,Complex.ofReal_add,Complex.ofReal_one,axisLaplacian_const_add]
  rw [hh,hid,fullCuspProfileField_add _ _ hD hF p hp]
  simp only [cuspBarrierDefectField,Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_one]
  ring

def kernelBarrierPotential (a b : ℝ) (q : KernelQuotient) : ℝ :=
  1+kernelQuotientBarrierDefect a b q/kernelQuotientBarrier a b q

lemma kernelBarrierPotential_lower (a b : ℝ) (ha : 1<a) (hab : a<b) :
    ∃K : Set KernelQuotient,IsCompact K ∧ ∃C : ℝ,0≤C ∧
      ∀q,1-C*(K.indicator (fun _ => (1:ℝ))) q≤kernelBarrierPotential a b q := by
  let D := kernelQuotientBarrierDefect a b
  let K := tsupport D
  have hK : IsCompact K := kernelQuotientBarrierDefect_hasCompactSupport a b ha hab
  obtain ⟨C,hC⟩ := (kernelQuotientBarrierDefect_hasCompactSupport a b ha hab).exists_bound_of_continuous
    (kernelQuotientBarrierDefect_continuous a b ha hab)
  refine ⟨K,hK,max C 0,le_max_right _ _,fun q => ?_⟩
  have hphi := kernelQuotientBarrier_one_le a b ha.le hab q
  have hpos : 0<kernelQuotientBarrier a b q := by linarith
  by_cases hq : q∈K
  · rw [Set.indicator_of_mem hq,mul_one,kernelBarrierPotential]
    have hD : -max C 0≤D q := by
      have hn : -‖D q‖≤D q := neg_abs_le (D q)
      exact (neg_le_neg ((hC q).trans (le_max_left C 0))).trans hn
    have hdiv : -max C 0≤D q/kernelQuotientBarrier a b q := by
      apply (le_div_iff₀ hpos).mpr
      have hm : -max C 0*kernelQuotientBarrier a b q≤-max C 0 := by
        nlinarith [mul_nonneg (le_max_right C 0) (sub_nonneg.mpr hphi)]
      exact hm.trans hD
    linarith
  · rw [Set.indicator_of_notMem hq,mul_zero,sub_zero,kernelBarrierPotential]
    have hz : D q=0 := image_eq_zero_of_notMem_tsupport hq
    change 1≤1+D q/kernelQuotientBarrier a b q
    rw [hz,zero_div,add_zero]

lemma cuspBarrier_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrier a b (euclideanToHyperbolic p)=cuspBarrierField a b p.ofLp := by
  rw [cuspBarrierField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]

lemma cuspBarrierDefect_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrierDefect a b (euclideanToHyperbolic p)=cuspBarrierDefectField a b p.ofLp := by
  rw [cuspBarrierDefectField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]

lemma kernelQuotientBarrier_laplace_defect (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelQuotientBarrier a b (kernelEuclideanProjection p)+
          kernelQuotientBarrierDefect a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  have hf : ∀q,0<q 2→ ContDiffAt ℝ ∞
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) q :=
    fun q hq => Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt a b ha.le hab q hq)
  rw [positiveEuclideanLaplacian_eq_axis _ hf p hp]
  have he : ∀q : SpatialCoordinates,0<q 2→
      (kernelQuotientBarrier a b (kernelEuclideanProjection (WithLp.toLp 2 q)):ℂ)=
        (cuspBarrierField a b q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq a b (WithLp.toLp 2 q) hq)
  rw [axisLaplacian_congr_positive _ _ he p.ofLp hp]
  have hh := cuspBarrierField_laplace_defect a b ha hab p.ofLp hp
  change -axisLaplacian _ p.ofLp=((cuspBarrier a b (euclideanToHyperbolic p)+
    cuspBarrierDefect a b (euclideanToHyperbolic p):ℝ):ℂ)
  rw [cuspBarrier_euclidean_eq a b p hp,cuspBarrierDefect_euclidean_eq a b p hp,Complex.ofReal_add]
  exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernelBarrierPotential_continuous (a b : ℝ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelBarrierPotential a b) := by
  apply continuous_const.add
  exact (kernelQuotientBarrierDefect_continuous a b ha hab).div
    (kernelQuotientBarrier_continuous a b ha.le hab) (fun q => by
      have hq := kernelQuotientBarrier_one_le a b ha.le hab q
      linarith)

lemma kernelBarrierPotential_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelBarrierPotential a b (kernelEuclideanProjection p)*
          kernelQuotientBarrier a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  rw [kernelQuotientBarrier_laplace_defect a b ha hab p hp]
  apply congrArg Complex.ofReal
  have hn : kernelQuotientBarrier a b (kernelEuclideanProjection p)≠0 := by
    have hq := kernelQuotientBarrier_one_le a b ha.le hab (kernelEuclideanProjection p)
    linarith
  rw [kernelBarrierPotential,add_mul,one_mul,div_mul_cancel₀ _ hn]

lemma kernelSmoothTest_weighted_mass_integrable (V : KernelQuotient→ℝ) (hV : Continuous V)
    (f : kernelSmoothTests) :
    Integrable (fun q => V q*‖f.1 q‖^2) (integralQuotientVolume globalKubotaKernel) := by
  apply (hV.mul (f.2.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact f.2.2
  intro q hq
  by_contra hn
  have hz : f.1 q=0 := image_eq_zero_of_notMem_tsupport hn
  apply hq
  change V q*‖f.1 q‖^2=0
  rw [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero]

end

open scoped ComplexConjugate

theorem ground_state_square_completion (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    ‖d‖^2 - b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) =
      ‖d - (b/a : ℝ)*z‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  field_simp
  ; ring

theorem ground_state_directional_inequality (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) ≤ ‖d‖^2 := by
  have hh := ground_state_square_completion a b ha z d
  nlinarith [sq_nonneg ‖d - (b/a : ℝ)*z‖]

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CompletedGauss (actualSextic)
open ConcreteTraceCRT (eisEmbedding)

theorem sixth_roots_reduce_injective (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) {x y : ActualEisensteinCubic.O}
    (hx : x^6=1) (hy : y^6=1)
    (hxy : Ideal.Quotient.mk P x=Ideal.Quotient.mk P y) : x=y := by
  let : Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
  have hs : x^2=y^2 := cubic_roots_reduce_injective P hg
    (by simpa only [←pow_mul] using hx)
    (by simpa only [←pow_mul] using hy)
    (by simpa only [map_pow] using congrArg (fun z : ActualEisensteinCubic.O⧸P=>z^2) hxy)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h|h
  · exact h
  · have hy0 : Ideal.Quotient.mk P y≠0 := by
      intro hz
      have he := congrArg (Ideal.Quotient.mk P) hy
      simp only [map_pow,map_one,hz,zero_pow (by decide : (6:ℕ)≠0)] at he
      exact zero_ne_one he
    have he : -(Ideal.Quotient.mk P y)=Ideal.Quotient.mk P y := by
      simpa only [h,map_neg] using hxy
    have htwo : (2 : ActualEisensteinCubic.O⧸P)*Ideal.Quotient.mk P y=0 := by linear_combination -he
    exact False.elim ((Ring.two_ne_zero hc) ((mul_eq_zero.mp htwo).resolve_right hy0))

lemma unit_pow_six (u : ActualEisensteinCubic.Oˣ) : (u.val : ActualEisensteinCubic.O)^6=1 := by
  have h := pow_card_eq_one' (x:=u)
  rw [PrimaryIdealUnitReindex.card_units_eq_six] at h
  exact congrArg Units.val h

theorem actualSextic_unit_euler (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) (u : ActualEisensteinCubic.Oˣ) :
    actualSextic P hg (Ideal.Quotient.mk P u.val) =
      eisEmbedding (u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6)) := by
  let : Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
  have hdata : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧ χ^6=1 ∧
      ∀v : (ActualEisensteinCubic.O⧸P)ˣ,Ideal.Quotient.mk P (χ v)=v.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6) := by
    refine ⟨_,rfl,(sexticChar_powers P hg).2.2,?_⟩
    exact sexticChar_reduce_unit P hg hc
  obtain ⟨χ,hχ,hχ6,hreduce⟩ := hdata
  let v : (ActualEisensteinCubic.O⧸P)ˣ := Units.map (Ideal.Quotient.mk P).toMonoidHom u
  have hx : χ v.val ^ 6=1 := by
    rw [←MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),hχ6]
    exact MulChar.one_apply v.isUnit
  have hy : (u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6))^6=1 := by
    rw [←pow_mul,Nat.mul_comm, pow_mul,unit_pow_six,one_pow]
  have he : χ v.val=u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6) :=
    sixth_roots_reduce_injective P hg hc hx hy (by simpa [v] using hreduce v)
  rw [hχ]
  change eisEmbedding (χ v.val)=_
  exact congrArg eisEmbedding he

end CanonicalUnitEuler

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

lemma kernel_mass_le_weighted_mass_add_core
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ)
    (V : KernelQuotient→ℝ) (hV : Continuous V)
    (hlow : ∀q,1-C*(K.indicator (fun _ => (1:ℝ))) q≤V q)
    (f : kernelSmoothTests) :
    ‖kernelSmoothTestsToL2 f‖^2≤
      (∫q,V q*‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)+
        C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2 := by
  have hi : Integrable (fun q => ‖f.1 q‖^2) (integralQuotientVolume globalKubotaKernel) :=
    (kernelSmoothTests_memLp f).norm.integrable_sq
  have hki := hi.indicator hK
  have hw := kernelSmoothTest_weighted_mass_integrable V hV f
  have hpoint : ∀q,‖f.1 q‖^2-C*(K.indicator (fun q => ‖f.1 q‖^2)) q≤V q*‖f.1 q‖^2 := by
    intro q
    have hh := mul_le_mul_of_nonneg_right (hlow q) (sq_nonneg ‖f.1 q‖)
    by_cases hq : q∈K
    · simp only [Set.indicator_of_mem hq] at hh ⊢
      nlinarith
    · simp only [Set.indicator_of_notMem hq,mul_zero,sub_zero,one_mul] at hh ⊢
      exact hh
  have hh := integral_mono (hi.sub (hki.const_mul C)) hw hpoint
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi (hki.const_mul C),integral_const_mul,integral_indicator hK,
    ←kernelSmoothTestsToL2_norm_sq,←kernelMassRestriction_smooth_norm_sq K hK] at hh
  linarith

lemma kernel_compact_coercivity_extend
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ)
    (hcore : ∀f : kernelSmoothTests,‖kernelSmoothTestsToL2 f‖^2≤kernelDirichletEnergy f+
      C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2)
    (u : KernelEnergyGraph) :
    ‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+C*‖kernelEnergyMassRestriction K hK u‖^2 := by
  exact kernelEnergyGraphCore_dense.induction_on u
    (isClosed_le (by fun_prop) (by fun_prop)) (fun f => by
      change ‖kernelSmoothTestsToL2 f‖^2≤‖kernelGradientToL2 f‖^2+
        C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2
      rw [kernelGradientToL2_norm_sq]
      exact hcore f)

lemma kernel_barrier_coercivity_of_ground_state
    (hground : ∀f : kernelSmoothTests,
      (∫q,kernelBarrierPotential 2 3 q*‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        kernelDirichletEnergy f) :
    ∃K : Set KernelQuotient,∃hK : IsCompact K,∃C : ℝ,0≤C ∧
      IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) ∧
      ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
        C*‖kernelEnergyMassRestriction K hK.measurableSet u‖^2 := by
  obtain ⟨K,hK,C,hC,hlow⟩ := kernelBarrierPotential_lower 2 3 (by norm_num) (by norm_num)
  refine ⟨K,hK,C,hC,kernelEnergyMassRestriction_isCompact K hK,?_⟩
  apply kernel_compact_coercivity_extend
  intro f
  exact (kernel_mass_le_weighted_mass_add_core K hK.measurableSet C
    (kernelBarrierPotential 2 3) (kernelBarrierPotential_continuous 2 3 (by norm_num) (by norm_num))
    hlow f).trans (add_le_add (hground f) le_rfl)

end

open scoped Topology ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ground_state_test_fderiv (f : E → ℂ) (u : E → ℝ) (x v : E)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (hux : u x ≠ 0) :
    fderiv ℝ (fun y => ‖f y‖^2/u y) x v =
      (2*(conj (f x)*fderiv ℝ f x v).re*u x - ‖f x‖^2*fderiv ℝ u x v)/(u x)^2 := by
  have hc : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
    simpa only [zero_add,one_smul,Pi.add_apply,id_eq] using!
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v)
  have hx : (fun t : ℝ => x+t•v) 0 = x := by simp
  have hfc : HasDerivAt (fun t : ℝ => f (x+t•v)) (fderiv ℝ f x v) 0 := by
    have hh : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ)•v) := by simpa using hf.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have huc : HasDerivAt (fun t : ℝ => u (x+t•v)) (fderiv ℝ u x v) 0 := by
    have hh : HasFDerivAt u (fderiv ℝ u x) (x+(0:ℝ)•v) := by simpa using hu.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have hzero : (fun t : ℝ => u (x+t•v)) 0 ≠ 0 := by simpa using hux
  have hq := hfc.norm_sq.div huc hzero
  have hdiff : DifferentiableAt ℝ (fun y => ‖f y‖^2/u y) x := by
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply] using! (hf.norm_sq (𝕜 := ℂ)).mul (hu.inv hux)
  have hqc : HasDerivAt (fun t : ℝ => ‖f (x+t•v)‖^2/u (x+t•v))
      (fderiv ℝ (fun y => ‖f y‖^2/u y) x v) 0 := by
    have hh : HasFDerivAt (fun y => ‖f y‖^2/u y)
        (fderiv ℝ (fun y => ‖f y‖^2/u y) x) (x+(0:ℝ)•v) := by simpa using hdiff.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have he := hqc.unique hq
  simpa only [zero_smul,add_zero,real_inner_eq_re_inner ℂ,RCLike.inner_apply',RCLike.re_to_complex] using he

theorem ground_state_fderiv_inequality (f : E → ℂ) (u : E → ℝ) (x v : E)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (hux : u x ≠ 0) :
    fderiv ℝ u x v * fderiv ℝ (fun y => ‖f y‖^2/u y) x v ≤ ‖fderiv ℝ f x v‖^2 := by
  rw [ground_state_test_fderiv f u x v hf hu hux]
  exact ground_state_directional_inequality (u x) (fderiv ℝ u x v) hux (f x) (fderiv ℝ f x v)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
namespace CubicEisenstein

section

def kernelGroundStateTest (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests) : kernelSmoothTests := by
  have hn : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (fun q => ‖f.1 q‖^2) :=
    (contDiff_norm_sq ℂ).contMDiff.comp f.2.1
  have hg := hn.div₀ hφ (fun q => (hpos q).ne')
  refine ⟨fun q => ((‖f.1 q‖^2/φ q : ℝ) : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp hg, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact f.2.2
  intro q hq
  by_contra hh
  have hz : f.1 q = 0 := image_eq_zero_of_notMem_tsupport hh
  exact hq (by simp [hz])

@[simp] theorem kernelGroundStateTest_apply (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests) (q : KernelQuotient) :
    (kernelGroundStateTest φ hφ hpos f).1 q = ((‖f.1 q‖^2/φ q : ℝ) : ℂ) := rfl

theorem kernelGroundStateTest_tsupport (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests) :
    tsupport (kernelGroundStateTest φ hφ hpos f).1 ⊆ tsupport f.1 := by
  apply closure_minimal _ (isClosed_tsupport f.1)
  intro q hq
  by_contra hh
  have hz : f.1 q = 0 := image_eq_zero_of_notMem_tsupport hh
  exact hq (by simp [hz])

def kernelTruncatedWeight (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ) : kernelSmoothTests := by
  refine ⟨fun q => ((χ q*φ q : ℝ) : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp (hχ.mul hφ), ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact hχK
  intro q hq
  by_contra hh
  have hz : χ q = 0 := image_eq_zero_of_notMem_tsupport hh
  exact hq (by simp [hz])

@[simp] theorem kernelTruncatedWeight_apply (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ) (q : KernelQuotient) :
    (kernelTruncatedWeight χ φ hχ hχK hφ).1 q = ((χ q*φ q : ℝ) : ℂ) := rfl

theorem kernelRealLift_contDiffAt (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt ℝ ∞ (fun p => φ (kernelEuclideanProjection p)) p :=
  (((hφ.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

theorem kernelEuclideanProjection_continuousAt (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContinuousAt kernelEuclideanProjection p :=
  (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
    (euclideanToHyperbolic_contMDiffAt p hp).continuousAt

theorem kernelTruncatedWeight_field_eq (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (p : EuclideanSpatial) (hp : 0 < p 2)
    (hχone : χ =ᶠ[𝓝 (kernelEuclideanProjection p)] (fun _ => 1)) :
    kernelTestField (kernelTruncatedWeight χ φ hχ hχK hφ) =ᶠ[𝓝 p]
      (fun q => (φ (kernelEuclideanProjection q) : ℂ)) := by
  have he := hχone.comp_tendsto (kernelEuclideanProjection_continuousAt p hp)
  filter_upwards [he] with q hq
  change χ (kernelEuclideanProjection q) = 1 at hq
  change ((χ (kernelEuclideanProjection q)*φ (kernelEuclideanProjection q) : ℝ) : ℂ) = _
  rw [hq,one_mul]

theorem kernelTruncatedPotential_memLp (χ φ V : KernelQuotient → ℝ)
    (hχ : Continuous χ) (hχK : HasCompactSupport χ) (hφ : Continuous φ) (hV : Continuous V) :
    MemLp (fun q => ((χ q*V q*φ q : ℝ) : ℂ)) 2 (integralQuotientVolume globalKubotaKernel) := by
  have hc : Continuous (fun q => ((χ q*V q*φ q : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((hχ.mul hV).mul hφ)
  apply hc.memLp_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact hχK
  intro q hq
  by_contra hh
  have hz : χ q = 0 := image_eq_zero_of_notMem_tsupport hh
  exact hq (by simp [hz])

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ComplexConjugate

theorem ground_state_ofReal_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x v : E) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => (u y : ℂ)) x v = (fderiv ℝ u x v : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ u) x v = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv]
  rfl

theorem ground_state_self_product (z : ℂ) : (star z*z).re = ‖z‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.star_def,Complex.mul_re,
    Complex.conj_re,Complex.conj_im]
  ring

theorem kernelEnergyDensity_euclidean (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    kernelQuotientEnergyDensity f (kernelEuclideanProjection p) =
      (p 2)^2 * ∑ j : Fin 3, ‖fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector j)‖^2 := by
  have hh := congrArg Complex.re (kernelDirichletPairDensity_euclidean f f p hp)
  rw [kernelDirichletPairDensity_self] at hh
  rw [← Complex.ofReal_pow,Complex.mul_re] at hh
  simpa only [Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum,ground_state_self_product] using hh

theorem kernelGroundState_pair_le_at
    (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0 < p 2)
    (hχone : χ =ᶠ[𝓝 (kernelEuclideanProjection p)] (fun _ => 1)) :
    (kernelDirichletPairDensity (kernelTruncatedWeight χ φ hχ hχK hφ)
      (kernelGroundStateTest φ hφ hpos f) (kernelEuclideanProjection p)).re ≤
      kernelQuotientEnergyDensity f (kernelEuclideanProjection p) := by
  let u : EuclideanSpatial → ℝ := fun q => φ (kernelEuclideanProjection q)
  let F : EuclideanSpatial → ℂ := kernelTestField f
  have hu : DifferentiableAt ℝ u p := (kernelRealLift_contDiffAt φ hφ p hp).differentiableAt (by simp)
  have hF : DifferentiableAt ℝ F p := (kernelTestField_contDiffAt f p hp).differentiableAt (by simp)
  have hu0 : u p ≠ 0 := (hpos _).ne'
  have hG : DifferentiableAt ℝ (fun q => ‖F q‖^2/u q) p := by
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply] using! (hF.norm_sq (𝕜 := ℂ)).mul (hu.inv hu0)
  have hh (j : Fin 3) :
      fderiv ℝ (kernelTestField (kernelTruncatedWeight χ φ hχ hχK hφ)) p (euclideanCoordinateVector j) =
        (fderiv ℝ u p (euclideanCoordinateVector j) : ℂ) := by
    rw [(kernelTruncatedWeight_field_eq χ φ hχ hχK hφ p hp hχone).fderiv_eq]
    exact ground_state_ofReal_fderiv u p _ hu
  have hg (j : Fin 3) :
      fderiv ℝ (kernelTestField (kernelGroundStateTest φ hφ hpos f)) p (euclideanCoordinateVector j) =
        (fderiv ℝ (fun q => ‖F q‖^2/u q) p (euclideanCoordinateVector j) : ℂ) := by
    change fderiv ℝ (fun q => ((‖F q‖^2/u q : ℝ) : ℂ)) p (euclideanCoordinateVector j) = _
    exact ground_state_ofReal_fderiv _ p _ hG
  rw [kernelDirichletPairDensity_euclidean _ _ p hp,kernelEnergyDensity_euclidean f p hp]
  simp only [hh,hg,Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,
    ← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  exact ground_state_fderiv_inequality F u p (euclideanCoordinateVector j) hF hu hu0

theorem kernelGroundState_pair_le
    (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests)
    (hχone : ∀ q ∈ tsupport f.1, χ =ᶠ[𝓝 q] (fun _ => 1)) (q : KernelQuotient) :
    (kernelDirichletPairDensity (kernelTruncatedWeight χ φ hχ hχK hφ)
      (kernelGroundStateTest φ hφ hpos f) q).re ≤ kernelQuotientEnergyDensity f q := by
  by_cases hq : q ∈ tsupport f.1
  · induction q using Quotient.inductionOn with
    | _ w =>
      have he : kernelEuclideanProjection (hyperbolicEuclideanCoordinates w) =
          integralOrbitProjection globalKubotaKernel w := by
        simp only [kernelEuclideanProjection,Function.comp_apply,euclideanToHyperbolic_coordinates]
      have hh := kernelGroundState_pair_le_at χ φ hχ hχK hφ hpos f
        (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
        (by rw [he]; exact hχone _ hq)
      rwa [he] at hh
  · rw [kernelDirichletPairDensity_zero_of_notMem _ _ q
      (fun h => hq (kernelGroundStateTest_tsupport φ hφ hpos f h)),Complex.zero_re]
    exact kernelQuotientEnergyDensity_nonneg f q

theorem kernel_ground_state_inequality (φ V : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (hV : Continuous V)
    (hPDE : ∀ p : EuclideanSpatial, 0 < p 2 →
      positiveEuclideanLaplacian (fun q => (φ (kernelEuclideanProjection q) : ℂ)) p =
        ((V (kernelEuclideanProjection p)*φ (kernelEuclideanProjection p) : ℝ) : ℂ))
    (f : kernelSmoothTests) :
    (∫ q, V q*‖f.1 q‖^2 ∂integralQuotientVolume globalKubotaKernel) ≤ kernelDirichletEnergy f := by
  obtain ⟨χ,hχ,hχK,hχone,hχrange⟩ := kernelCompact_smooth_cutoff (tsupport f.1) f.2.2
  let h := kernelTruncatedWeight χ φ hχ hχK hφ
  let g := kernelGroundStateTest φ hφ hpos f
  let A : KernelQuotient → ℂ := fun q => ((χ q*V q*φ q : ℝ) : ℂ)
  have hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel) :=
    kernelTruncatedPotential_memLp χ φ V hχ.continuous hχK hφ.continuous hV
  have hcoord : ∀ p : EuclideanSpatial, 0 < p 2 →
      kernelEuclideanProjection p ∈ tsupport g.1 →
      kernelCoordinateLaplacian h p = A (kernelEuclideanProjection p) := by
    intro p hp hpg
    have hfmem : kernelEuclideanProjection p ∈ tsupport f.1 :=
      kernelGroundStateTest_tsupport φ hφ hpos f hpg
    have hlocal := hχone (kernelEuclideanProjection p) hfmem
    change positiveEuclideanLaplacian (kernelTestField h) p = _
    rw [positiveEuclideanLaplacian_congr _ _ p
      (kernelTruncatedWeight_field_eq χ φ hχ hχK hφ p hp hlocal),hPDE p hp]
    dsimp only [A]
    rw [hlocal.eq_of_nhds,one_mul]
  have hprod (q : KernelQuotient) : star (A q)*g.1 q = ((V q*‖f.1 q‖^2 : ℝ) : ℂ) := by
    change star ((χ q*V q*φ q : ℝ) : ℂ) * ((‖f.1 q‖^2/φ q : ℝ) : ℂ) = _
    by_cases hfzero : f.1 q = 0
    · simp [hfzero]
    · have hq : q ∈ tsupport f.1 := subset_tsupport f.1 hfzero
      have hχq : χ q = 1 := (hχone q hq).eq_of_nhds
      have hφq : φ q ≠ 0 := (hpos q).ne'
      simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,hχq,one_mul]
      congr 1
      field_simp
  have hgreen : kernelDirichletForm h g =
      ((∫ q, V q*‖f.1 q‖^2 ∂integralQuotientVolume globalKubotaKernel : ℝ) : ℂ) := by
    rw [kernelDirichletForm_supported_equation h g A hA hcoord]
    simp_rw [hprod]
    exact integral_complex_ofReal
  have hbound : (∫ q, (kernelDirichletPairDensity h g q).re
      ∂integralQuotientVolume globalKubotaKernel) ≤ kernelDirichletEnergy f := by
    exact integral_mono (kernelDirichletPairDensity_integrable h g).re
      (kernelQuotientEnergyDensity_integrable f)
      (fun q => kernelGroundState_pair_le χ φ hχ hχK hφ hpos f hχone q)
  have hreal : (∫ q, (kernelDirichletPairDensity h g q).re
      ∂integralQuotientVolume globalKubotaKernel) = (kernelDirichletForm h g).re := by
    simpa only [kernelDirichletForm,RCLike.re_to_complex] using integral_re (kernelDirichletPairDensity_integrable h g)
  rw [hreal,hgreen,Complex.ofReal_re] at hbound
  exact hbound

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

theorem kernel_actual_barrier_ground_state (f : kernelSmoothTests) :
    (∫q,kernelBarrierPotential 2 3 q*‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
      kernelDirichletEnergy f :=
  kernel_ground_state_inequality (kernelQuotientBarrier 2 3) (kernelBarrierPotential 2 3)
    (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num))
    (fun q => lt_of_lt_of_le zero_lt_one (kernelQuotientBarrier_one_le 2 3 (by norm_num) (by norm_num) q))
    (kernelBarrierPotential_continuous 2 3 (by norm_num) (by norm_num))
    (kernelBarrierPotential_equation 2 3 (by norm_num) (by norm_num)) f

theorem kernel_global_exterior_coercivity :
    ∃K : Set KernelQuotient,∃hK : IsCompact K,∃C : ℝ,0≤C ∧
      IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) ∧
      ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
        C*‖kernelEnergyMassRestriction K hK.measurableSet u‖^2 :=
  kernel_barrier_coercivity_of_ground_state kernel_actual_barrier_ground_state

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

section

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma ker_orthogonal_restriction_injective (T : E→L[ℂ]F) :
    Function.Injective (T.domRestrict T.kerᗮ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  apply Subtype.ext
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact T.ker.inner_right_of_mem_orthogonal hu u.2

lemma ker_orthogonal_restriction_range (T : E→L[ℂ]F) :
    Set.range (T.domRestrict T.kerᗮ)=Set.range T := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  apply Set.Subset.antisymm
  · rintro _ ⟨u,rfl⟩
    exact ⟨u.1,rfl⟩
  · rintro _ ⟨u,rfl⟩
    refine ⟨⟨u-T.ker.starProjection u,T.ker.sub_starProjection_mem_orthogonal u⟩,?_⟩
    change T (u-T.ker.starProjection u)=T u
    rw [map_sub]
    have hz : T (T.ker.starProjection u)=0 := T.ker.starProjection_apply_mem u
    rw [hz,sub_zero]

lemma ker_orthogonal_restriction_antilipschitz (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    ∃D : NNReal,AntilipschitzWith D (T.domRestrict T.kerᗮ) := by
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  apply antilipschitz_of_injective_compact_estimate (T.domRestrict T.kerᗮ)
    (K.domRestrict T.kerᗮ) (hK.comp_clm T.kerᗮ.subtypeL) A B
      (fun u => hest u) (ker_orthogonal_restriction_injective T)

lemma closed_range_of_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : IsClosed (Set.range T) := by
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  rw [←ker_orthogonal_restriction_range T]
  exact hD.isClosed_range (T.domRestrict T.kerᗮ).uniformContinuous

lemma selfAdjoint_range_eq_ker_orthogonal (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (hrange : IsClosed (Set.range T)) : T.range=T.kerᗮ := by
  have hh := T.orthogonal_ker
  rw [hT.adjoint_eq] at hh
  rw [hrange.submodule_topologicalClosure_eq] at hh
  exact hh.symm

end

section
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma selfAdjoint_fredholm_of_compact_estimate (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (K : E→L[ℂ]G) (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : T.IsFredholm := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  let : FiniteDimensional ℂ T.ker := finiteDimensional_ker_of_compact_estimate T K hK A B hest
  let : T.kerᗮ.CoFG :=
    (T.kerᗮ.quotientEquivOfIsCompl T.ker T.ker.isCompl_orthogonal.symm).symm.finiteDimensional
  have hrange := closed_range_of_compact_estimate T K hK A B hest
  have heq := selfAdjoint_range_eq_ker_orthogonal T hT hrange
  let : T.range.CoFG := heq.symm ▸ (inferInstance : T.kerᗮ.CoFG)
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  
  
  have hce := hD.isClosedEmbedding (T.domRestrict T.kerᗮ).uniformContinuous
  have hsc := (T.isStrictMap_isClosed_range_iff_restrict T.kerᗮ T.ker.isClosed_orthogonal).mpr
    ⟨hce.isEmbedding.isStrictMap, hce.isClosed_range⟩
  exact ⟨hsc.1, hsc.2, inferInstance, inferInstance,
    Submodule.ClosedComplemented.of_isCompl_isClosed T.ker.isCompl_orthogonal T.isClosed_ker
      T.ker.isClosed_orthogonal⟩

end

def kernelSpectralFormOperator (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  ContinuousLinearMap.id ℂ KernelEnergyGraph-
    (z+1)•(kernelEnergyMass.adjoint.comp kernelEnergyMass)

lemma kernelSpectralFormOperator_inner (z : ℂ) (u : KernelEnergyGraph) :
    inner ℂ u (kernelSpectralFormOperator z u)=
      ((‖kernelEnergyGradient u‖^2:ℝ):ℂ)-z*((‖kernelEnergyMass u‖^2:ℝ):ℂ) := by
  change inner ℂ u (u-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass u))=_
  rw [inner_sub_right,inner_smul_right u (kernelEnergyMass.adjoint (kernelEnergyMass u)) (z + 1),kernelEnergyMass.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelEnergyGraph_norm_sq,Complex.ofReal_add]
  ring

lemma kernelSpectralFormOperator_selfAdjoint (spectralParam : ℝ) :
    IsSelfAdjoint (kernelSpectralFormOperator (spectralParam:ℂ)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply (LinearMap.isSymmetric_iff_inner_map_self_real _).mpr
  intro u
  have hh := kernelSpectralFormOperator_inner (spectralParam:ℂ) u
  have hr : inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u=
      (((‖kernelEnergyGradient u‖^2-spectralParam*‖kernelEnergyMass u‖^2):ℝ):ℂ) := by
    rw [show inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u=(starRingEnd ℂ) (inner ℂ u (kernelSpectralFormOperator (spectralParam:ℂ) u)) from by exact (inner_conj_symm (𝕜 := ℂ) (E := KernelEnergyGraph) (kernelSpectralFormOperator (spectralParam:ℂ) u) u).symm,kernelSpectralFormOperator_inner]
    simp only [map_sub,map_mul,Complex.conj_ofReal,Complex.ofReal_sub,Complex.ofReal_mul]
  change (starRingEnd ℂ) (inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u)=
    inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u
  rw [hr,Complex.conj_ofReal]

lemma scalar_compact_energy_estimate (m g n t k spectralParam C : ℝ)
    (_hn : 0≤n) (_ht : 0≤t) (hspectralParam : 0≤ spectralParam) (hspectralParamone : spectralParam<1) (hC : 0≤C)
    (hspace : n^2=m^2+g^2) (hcore : m^2≤g^2+C*k^2)
    (hform : g^2-spectralParam*m^2≤n*t) :
    n^2≤(4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2 := by
  have hd : 0<1-spectralParam := sub_pos.mpr hspectralParamone
  have hlow : (1-spectralParam)/2*n^2≤n*t+C*k^2 := by
    nlinarith [mul_nonneg (show 0≤1+spectralParam by linarith) (sub_nonneg.mpr hcore),
      mul_nonneg hd.le (mul_nonneg hC (sq_nonneg k))]
  have hlow' := mul_le_mul_of_nonneg_left hlow (show 0≤4*(1-spectralParam) by positivity)
  have hsq : (1-spectralParam)^2*n^2≤4*t^2+4*(1-spectralParam)*C*k^2 := by
    nlinarith [sq_nonneg ((1-spectralParam)*n-2*t)]
  have he : (4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2=
      (4*t^2+4*(1-spectralParam)*C*k^2)/(1-spectralParam)^2 := by
    field_simp [hd.ne']
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr (by nlinarith [hsq])

lemma kernelSpectralFormOperator_compact_estimate
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ) (hC : 0≤C)
    (hcore : ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
      C*‖kernelEnergyMassRestriction K hK u‖^2)
    (spectralParam : ℝ) (hspectralParam : 0≤ spectralParam) (hspectralParamone : spectralParam<1) (u : KernelEnergyGraph) :
    ‖u‖^2≤(4/(1-spectralParam)^2)*‖kernelSpectralFormOperator (spectralParam:ℂ) u‖^2+
      (4*C/(1-spectralParam))*‖kernelEnergyMassRestriction K hK u‖^2 := by
  apply scalar_compact_energy_estimate ‖kernelEnergyMass u‖ ‖kernelEnergyGradient u‖
    ‖u‖ ‖kernelSpectralFormOperator (spectralParam:ℂ) u‖ ‖kernelEnergyMassRestriction K hK u‖ spectralParam C
    (norm_nonneg _) (norm_nonneg _) hspectralParam hspectralParamone hC (kernelEnergyGraph_norm_sq u) (hcore u)
  have hh := re_inner_le_norm (𝕜 := ℂ) u (kernelSpectralFormOperator (spectralParam:ℂ) u)
  rw [kernelSpectralFormOperator_inner] at hh
  simpa only [RCLike.re_to_complex,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using hh

lemma kernelSpectralFormOperator_solution_graph (z : ℂ) (F : KernelQuotientL2)
    (v : KernelEnergyGraph) (hv : kernelSpectralFormOperator z v=kernelVariationalSolution F) :
    (kernelEnergyMass v,F+z•kernelEnergyMass v)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  have hh : v-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass v)=kernelEnergyMass.adjoint F := hv
  have hv' : kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v)=v := by
    rw [map_add,map_smul]
    exact (sub_eq_iff_eq_add.mp hh).symm
  have he : kernelEnergyMass v+(F+z•kernelEnergyMass v)=F+(z+1)•kernelEnergyMass v := by
    rw [add_smul,one_smul]
    abel
  rw [he]
  change kernelEnergyMass (kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v))=kernelEnergyMass v
  rw [hv']

lemma kernelSpectralFormOperator_of_domain (z : ℂ) (u : kernelEnergyLaplacian.domain) :
    kernelSpectralFormOperator z (kernelVariationalSolution (kernelEnergyLaplacian u+u))=
      kernelVariationalSolution (kernelEnergyLaplacian u-z•(u:KernelQuotientL2)) := by
  have hu : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  change kernelVariationalSolution (kernelEnergyLaplacian u+u)-
    (z+1)•kernelVariationalSolution (kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u)))=_
  rw [hu,←map_smul,←map_sub]
  congr 1
  rw [add_smul,one_smul]
  abel

theorem kernelSpectralFormOperator_isFredholm (spectralParam : ℝ)
    (hzero : 0≤ spectralParam) (hone : spectralParam<1) :
    (kernelSpectralFormOperator (spectralParam:ℂ)).IsFredholm := by
  obtain ⟨K,hK,C,hC,hcompact,hcoercive⟩ := kernel_global_exterior_coercivity
  exact selfAdjoint_fredholm_of_compact_estimate _
    (kernelSpectralFormOperator_selfAdjoint spectralParam)
    (kernelEnergyMassRestriction K hK.measurableSet) hcompact
    (4/(1-spectralParam)^2) (4*C/(1-spectralParam))
    (kernelSpectralFormOperator_compact_estimate K hK.measurableSet C hC hcoercive spectralParam hzero hone)

theorem kernel_theta_spectral_fredholm :
    (kernelSpectralFormOperator (8/9:ℂ)).IsFredholm := by
  convert (preTransparency := .instances) kernelSpectralFormOperator_isFredholm (8/9) (by norm_num) (by norm_num) using 1
  norm_num

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped Topology

lemma kernelSpectralFormOperator_analyticAt (z : ℂ) :
    AnalyticAt ℂ kernelSpectralFormOperator z := by
  let S : KernelEnergyGraph→L[ℂ]KernelEnergyGraph := kernelEnergyMass.adjoint.comp kernelEnergyMass
  have hc : AnalyticAt ℂ (fun w : ℂ => w • S) (z+1) := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply] using!
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
        (F := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) S) (z+1))
  have hz : AnalyticAt ℂ (fun w : ℂ => w+1) z := analyticAt_id.add analyticAt_const
  exact analyticAt_const.sub (hc.comp_of_eq hz rfl)

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelMassGram : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  kernelEnergyMass.adjoint.comp kernelEnergyMass

lemma selfAdjoint_adjoint_comp {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) : IsSelfAdjoint (A.adjoint.comp A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

lemma kernelMassGram_selfAdjoint : IsSelfAdjoint kernelMassGram :=
  selfAdjoint_adjoint_comp kernelEnergyMass

def kernelThetaNull : Submodule ℂ KernelEnergyGraph :=
  (kernelSpectralFormOperator (8/9:ℂ)).ker

def kernelThetaRegular : Submodule ℂ KernelEnergyGraph := kernelThetaNullᗮ

instance kernelThetaNull_complete : CompleteSpace kernelThetaNull :=
  (kernelSpectralFormOperator (8/9:ℂ)).isClosed_ker.completeSpace_coe

instance kernelThetaRegular_complete : CompleteSpace kernelThetaRegular :=
  kernelThetaNull.isClosed_orthogonal.completeSpace_coe

instance kernelThetaNull_finiteDimensional : FiniteDimensional ℂ kernelThetaNull :=
  kernel_theta_spectral_fredholm.finite_ker

lemma kernelThetaNull_gram_eq (u : KernelEnergyGraph) (hu : u∈kernelThetaNull) :
    kernelMassGram u=(9/17:ℂ)•u := by
  have hh : u-(8/9+1:ℂ)•kernelMassGram u=0 := hu
  have he : u=(17/9:ℂ)•kernelMassGram u := by
    simpa only [show (8/9+1:ℂ)=17/9 by norm_num] using sub_eq_zero.mp hh
  calc
    _ = (9/17:ℂ)•((17/9:ℂ)•kernelMassGram u) := by rw [smul_smul]; norm_num
    _ = _ := by rw [←he]

lemma kernelThetaNull_spectral_eq (z : ℂ) (u : KernelEnergyGraph) (hu : u∈kernelThetaNull) :
    kernelSpectralFormOperator z u=((8/9-z)*(9/17):ℂ)•u := by
  change u-(z+1)•kernelMassGram u=_
  rw [kernelThetaNull_gram_eq u hu,smul_smul]
  calc
    u-((z+1)*(9/17):ℂ)•u=(1-(z+1)*(9/17):ℂ)•u := by rw [sub_smul,one_smul]
    _ = _ := by congr 1; ring

lemma kernelMassGram_preserves_regular (u : KernelEnergyGraph) (hu : u∈kernelThetaRegular) :
    kernelMassGram u∈kernelThetaRegular := by
  apply (kernelThetaNull.mem_orthogonal _).mpr
  intro v hv
  have he : inner ℂ v (kernelMassGram u)=inner ℂ (kernelMassGram v) u := by
    simpa only [ContinuousLinearMap.coe_coe] using (kernelMassGram_selfAdjoint.isSymmetric v u).symm
  rw [he,kernelThetaNull_gram_eq v hv,inner_smul_left (𝕜 := ℂ) v u (9/17:ℂ)]
  rw [kernelThetaNull.inner_right_of_mem_orthogonal hv hu,mul_zero]

def kernelRegularGram : kernelThetaRegular→L[ℂ]kernelThetaRegular :=
  kernelMassGram.restrict kernelMassGram_preserves_regular

def kernelRegularPencil (z : ℂ) : kernelThetaRegular→L[ℂ]kernelThetaRegular :=
  ContinuousLinearMap.id ℂ kernelThetaRegular-(z+1)•kernelRegularGram

lemma kernelRegularPencil_apply (z : ℂ) (u : kernelThetaRegular) :
    (kernelRegularPencil z u:KernelEnergyGraph)=kernelSpectralFormOperator z u := rfl

lemma kernelRegularPencil_center_isUnit : IsUnit (kernelRegularPencil (8/9:ℂ)) := by
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := kernelThetaRegular)).mpr
  constructor
  · intro u v huv
    apply ker_orthogonal_restriction_injective (kernelSpectralFormOperator (8/9:ℂ))
    exact congrArg (fun w : kernelThetaRegular => (w:KernelEnergyGraph)) huv
  · intro v
    have he : (kernelSpectralFormOperator (8/9:ℂ)).range=kernelThetaRegular := by
      exact selfAdjoint_range_eq_ker_orthogonal _
        (by convert (preTransparency := .instances) kernelSpectralFormOperator_selfAdjoint (8/9) using 1 ; norm_num)
        kernel_theta_spectral_fredholm.isClosed_range
    have hv : (v:KernelEnergyGraph)∈(kernelSpectralFormOperator (8/9:ℂ)).range := by
      rw [he]
      exact v.2
    obtain ⟨u,hu⟩ := hv
    change kernelSpectralFormOperator (8/9:ℂ) u=(v:KernelEnergyGraph) at hu
    let w : kernelThetaRegular := ⟨u-kernelThetaNull.starProjection u,kernelThetaNull.sub_starProjection_mem_orthogonal u⟩
    refine ⟨w,Subtype.ext ?_⟩
    rw [kernelRegularPencil_apply]
    change kernelSpectralFormOperator (8/9:ℂ) (u-kernelThetaNull.starProjection u)=v
    rw [map_sub,hu]
    have hz : kernelSpectralFormOperator (8/9:ℂ) (kernelThetaNull.starProjection u)=0 :=
      kernelThetaNull.starProjection_apply_mem u
    rw [hz,sub_zero]

abbrev endomorphismNormedSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] : NormedSpace ℂ (E →L[ℂ] E) := inferInstance

local instance instNormedSpaceComplexContinuousLinearMapIdSubtypeKernelEnergyAmbientMemSubmoduleKernelEnergyGraphKernelThetaRegular : NormedSpace ℂ (kernelThetaRegular →L[ℂ] kernelThetaRegular) :=
  endomorphismNormedSpace kernelThetaRegular

lemma kernelRegularPencil_analyticAt (z : ℂ) :
    AnalyticAt ℂ kernelRegularPencil z := by
  have hc : AnalyticAt ℂ (fun w : ℂ => w • kernelRegularGram) (z+1) := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply] using!
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
        (F := kernelThetaRegular→L[ℂ]kernelThetaRegular)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) kernelRegularGram) (z+1))
  have hz : AnalyticAt ℂ (fun w : ℂ => w+1) z := analyticAt_id.add analyticAt_const
  exact analyticAt_const.sub (hc.comp_of_eq hz rfl)

lemma kernelRegularPencil_eventually_isUnit :
    ∀ᶠ z : ℂ in 𝓝 (8/9:ℂ), IsUnit (kernelRegularPencil z) :=
  (kernelRegularPencil_analyticAt (8/9)).continuousAt.eventually
    ((Units.isOpen (R := kernelThetaRegular→L[ℂ]kernelThetaRegular)).mem_nhds
      (show kernelRegularPencil (8/9)∈{x : kernelThetaRegular→L[ℂ]kernelThetaRegular | IsUnit x} from
        kernelRegularPencil_center_isUnit))

lemma kernelRegularInverse_analyticAt :
    AnalyticAt ℂ (fun z : ℂ => Ring.inverse (kernelRegularPencil z)) (8/9:ℂ) := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := kernelThetaRegular→L[ℂ]kernelThetaRegular))
    (kernelRegularPencil (8/9)) kernelRegularPencil_center_isUnit
  exact hi.comp_of_eq (kernelRegularPencil_analyticAt (8/9)) rfl

def continuousLinearSandwich {H G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : H →L[ℂ] G) (B : G →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (G →L[ℂ] G) :=
  (ContinuousLinearMap.compL ℂ G H G A).comp
    ((ContinuousLinearMap.compL ℂ G H H).flip B)

def kernelRegularLiftCLM :
    (kernelThetaRegular→L[ℂ]kernelThetaRegular)→L[ℂ](KernelEnergyGraph→L[ℂ]KernelEnergyGraph) :=
  continuousLinearSandwich (H := kernelThetaRegular) (G := KernelEnergyGraph)
    kernelThetaRegular.subtypeL
    kernelThetaRegular.orthogonalProjectionOnto

def kernelRegularInverseLift (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  kernelRegularLiftCLM (Ring.inverse (kernelRegularPencil z))

lemma kernelRegularInverseLift_apply (z : ℂ) (u : KernelEnergyGraph) :
    kernelRegularInverseLift z u =
      (Ring.inverse (kernelRegularPencil z) (kernelThetaRegular.orthogonalProjectionOnto u) :
        KernelEnergyGraph) := rfl

lemma kernelRegularInverseLift_analyticAt :
    AnalyticAt ℂ kernelRegularInverseLift (8/9:ℂ) := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := kernelThetaRegular→L[ℂ]kernelThetaRegular)
    (F := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    kernelRegularLiftCLM (Ring.inverse (kernelRegularPencil (8/9)))).comp_of_eq
      kernelRegularInverse_analyticAt rfl

def kernelLocalEnergyResolvent (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  ((17/9)/(8/9-z):ℂ) • kernelThetaNull.starProjection + kernelRegularInverseLift z

lemma kernelSpectralFormOperator_regularInverseLift (z : ℂ)
    (hz : IsUnit (kernelRegularPencil z)) (u : KernelEnergyGraph) :
    kernelSpectralFormOperator z (kernelRegularInverseLift z u)=
      kernelThetaRegular.starProjection u := by
  rw [kernelRegularInverseLift_apply,←kernelRegularPencil_apply]
  have he := congrArg (fun A : kernelThetaRegular→L[ℂ]kernelThetaRegular =>
    A (kernelThetaRegular.orthogonalProjectionOnto u))
      (Ring.mul_inverse_cancel (kernelRegularPencil z) hz)
  exact congrArg (fun v : kernelThetaRegular => (v:KernelEnergyGraph)) he

lemma kernelLocalEnergyResolvent_right_inverse (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) (u : KernelEnergyGraph) :
    kernelSpectralFormOperator z (kernelLocalEnergyResolvent z u)=u := by
  change kernelSpectralFormOperator z
    (((17/9)/(8/9-z):ℂ) • kernelThetaNull.starProjection u + kernelRegularInverseLift z u)=u
  rw [map_add,map_smul,kernelThetaNull_spectral_eq z _
    (kernelThetaNull.starProjection_apply_mem u),smul_smul]
  have hc : ((17/9)/(8/9-z):ℂ)*((8/9-z)*(9/17))=1 := by
    calc
      _ = (((17/9)/(8/9-z):ℂ)*(8/9-z))*(9/17) := by ring
      _ = (17/9:ℂ)*(9/17) := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hne.symm)]
      _ = 1 := by norm_num
  rw [hc,one_smul,kernelSpectralFormOperator_regularInverseLift z hz]
  exact kernelThetaNull.starProjection_add_starProjection_orthogonal u

lemma selfAdjoint_one_sub_smul_normal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : H→L[ℂ]H)
    (hS : IsSelfAdjoint S) (z : ℂ) : IsStarNormal (1-z•S) := by
  let : IsStarNormal S := hS.isStarNormal
  infer_instance

lemma kernelSpectralFormOperator_normal (z : ℂ) : IsStarNormal (kernelSpectralFormOperator z) := by
  exact selfAdjoint_one_sub_smul_normal kernelMassGram kernelMassGram_selfAdjoint (z+1)

lemma kernelSpectralFormOperator_isUnit_near (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) : IsUnit (kernelSpectralFormOperator z) := by
  have hsur : Function.Surjective (kernelSpectralFormOperator z) := fun u =>
    ⟨kernelLocalEnergyResolvent z u,kernelLocalEnergyResolvent_right_inverse z hne hz u⟩
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mpr
  refine ⟨?_,hsur⟩
  change Function.Injective (kernelSpectralFormOperator z).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  rw [←ContinuousLinearMap.IsStarNormal.orthogonal_range (kernelSpectralFormOperator_normal z)]
  have hr : (kernelSpectralFormOperator z).range=⊤ := LinearMap.range_eq_top.mpr hsur
  rw [hr,Submodule.top_orthogonal_eq_bot]

lemma kernelLocalEnergyResolvent_eq_inverse (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) :
    kernelLocalEnergyResolvent z = Ring.inverse (kernelSpectralFormOperator z) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ((ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mp
    (kernelSpectralFormOperator_isUnit_near z hne hz)).1
  rw [kernelLocalEnergyResolvent_right_inverse z hne hz]
  have hi := congrArg (fun A : KernelEnergyGraph→L[ℂ]KernelEnergyGraph => A u)
    (Ring.mul_inverse_cancel (kernelSpectralFormOperator z) (kernelSpectralFormOperator_isUnit_near z hne hz))
  exact hi.symm

end

open scoped Topology

lemma selfAdjoint_pencil_isUnit_nonreal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : H→L[ℂ]H)
    (hS : IsSelfAdjoint S) (z : ℂ) (hz : z.im≠0) : IsUnit (1-z•S) := by
  have hne : z≠0 := fun h => hz (by rw [h]; rfl)
  have hi : z⁻¹.im≠0 := by
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr hz) (mt Complex.normSq_eq_zero.mp hne)
  have hout : z⁻¹∉spectrum ℂ S := fun h => hi (hS.im_eq_zero_of_mem_spectrum h)
  have hu := (spectrum.notMem_iff (R := ℂ) (A := H→L[ℂ]H)).mp hout
  have hv := hu.smul (Units.mk0 z hne)
  simpa only [Units.smul_def,Units.val_mk0,Algebra.algebraMap_eq_smul_one,
    smul_sub,smul_smul,mul_inv_cancel₀ hne,one_smul] using hv

lemma kernelSpectralFormOperator_isUnit_nonreal (z : ℂ) (hz : z.im≠0) :
    IsUnit (kernelSpectralFormOperator z) := by
  exact selfAdjoint_pencil_isUnit_nonreal kernelMassGram kernelMassGram_selfAdjoint (z+1)
    (by simpa using hz)

lemma kernelSpectralFormInverse_analyticAt_of_isUnit (z : ℂ)
    (hz : IsUnit (kernelSpectralFormOperator z)) :
    AnalyticAt ℂ (fun w => Ring.inverse (kernelSpectralFormOperator w)) z := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)) (kernelSpectralFormOperator z) hz
  exact hi.comp_of_eq (kernelSpectralFormOperator_analyticAt z) rfl

lemma kernelSpectralFormInverse_analyticAt_nonreal (z : ℂ) (hz : z.im≠0) :
    AnalyticAt ℂ (fun w => Ring.inverse (kernelSpectralFormOperator w)) z :=
  kernelSpectralFormInverse_analyticAt_of_isUnit z (kernelSpectralFormOperator_isUnit_nonreal z hz)

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelL2SandwichCLM : (KernelEnergyGraph→L[ℂ]KernelEnergyGraph)→L[ℂ]
    (KernelQuotientL2→L[ℂ]KernelQuotientL2) :=
  continuousLinearSandwich kernelEnergyMass kernelEnergyMass.adjoint

def kernelSpectralResolvent (z : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM (Ring.inverse (kernelSpectralFormOperator z))

lemma kernelSpectralResolvent_apply (z : ℂ) (F : KernelQuotientL2) :
    kernelSpectralResolvent z F=
      kernelEnergyMass (Ring.inverse (kernelSpectralFormOperator z) (kernelVariationalSolution F)) := rfl

lemma kernelSpectralResolvent_analyticAt_nonreal (z : ℂ) (hz : z.im≠0) :
    AnalyticAt ℂ kernelSpectralResolvent z := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (Ring.inverse (kernelSpectralFormOperator z))).comp_of_eq
    (kernelSpectralFormInverse_analyticAt_nonreal z hz) rfl

lemma kernelSpectralResolvent_left_inverse (z : ℂ) (hz : IsUnit (kernelSpectralFormOperator z))
    (u : kernelEnergyLaplacian.domain) :
    kernelSpectralResolvent z (kernelEnergyLaplacian u-z•(u:KernelQuotientL2))=u := by
  rw [kernelSpectralResolvent_apply,←kernelSpectralFormOperator_of_domain z u]
  have hi := congrArg (fun A : KernelEnergyGraph→L[ℂ]KernelEnergyGraph =>
    A (kernelVariationalSolution (kernelEnergyLaplacian u+u)))
      (Ring.inverse_mul_cancel (kernelSpectralFormOperator z) hz)
  change Ring.inverse (kernelSpectralFormOperator z)
    (kernelSpectralFormOperator z (kernelVariationalSolution (kernelEnergyLaplacian u+u)))=
      kernelVariationalSolution (kernelEnergyLaplacian u+u) at hi
  rw [hi]
  exact kernelEnergyLaplacian_resolvent_relation u

lemma kernelSpectralResolvent_unique (z : ℂ) (hz : IsUnit (kernelSpectralFormOperator z))
    (u F : KernelQuotientL2) (hu : (u,F+z•u)∈kernelEnergyLaplacian.graph) :
    kernelSpectralResolvent z F=u := by
  let v : kernelEnergyLaplacian.domain := ⟨u,LinearPMap.mem_domain_of_mem_graph hu⟩
  have hv : kernelEnergyLaplacian v=F+z•u :=
    kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph v) hu rfl
  have hh := kernelSpectralResolvent_left_inverse z hz v
  rw [hv] at hh
  simpa only [v,add_sub_cancel_right] using hh

def kernelEisensteinSpectralParameter (s : ℂ) : ℂ := s*(2-s)

def kernelEisensteinResolvent (s : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelSpectralResolvent (kernelEisensteinSpectralParameter s)

lemma kernelEisensteinSpectralParameter_center :
    kernelEisensteinSpectralParameter (4/3)=8/9 := by
  norm_num [kernelEisensteinSpectralParameter]

lemma kernelEisensteinSpectralParameter_nonreal (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    (kernelEisensteinSpectralParameter s).im≠0 := by
  have he : (kernelEisensteinSpectralParameter s).im=2*(1-s.re)*s.im := by
    simp only [kernelEisensteinSpectralParameter,Complex.mul_im,Complex.sub_re,Complex.sub_im]
    norm_num
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hs.symm)) hi

lemma kernelEisensteinResolvent_analyticAt_nonreal (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ kernelEisensteinResolvent s := by
  exact (kernelSpectralResolvent_analyticAt_nonreal _
    (kernelEisensteinSpectralParameter_nonreal s hs hi)).comp_of_eq
      (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl

lemma kernelEisensteinPencil_eventually_isUnit :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ), IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s)) := by
  have hc : ContinuousAt kernelEisensteinSpectralParameter (4/3:ℂ) := by
    unfold kernelEisensteinSpectralParameter
    fun_prop
  have hp : ∀ᶠ s : ℂ in 𝓝 (4/3:ℂ), IsUnit (kernelRegularPencil (kernelEisensteinSpectralParameter s)) := by
    have hh : ∀ᶠ z : ℂ in 𝓝 (kernelEisensteinSpectralParameter (4/3)), IsUnit (kernelRegularPencil z) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularPencil_eventually_isUnit
    exact hc.eventually hh
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,
    eventually_ne_nhdsWithin (show (4/3:ℂ)≠2/3 by norm_num),self_mem_nhdsWithin] with s hs htwo hfour
  apply kernelSpectralFormOperator_isUnit_near _ _ hs
  intro he
  have hzero : (s-4/3)*(s-2/3)=0 := by
    have hid : (s-4/3)*(s-2/3)=(8/9:ℂ)-kernelEisensteinSpectralParameter s := by
      unfold kernelEisensteinSpectralParameter
      ring
    rw [hid,he,sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact hfour (sub_eq_zero.mp h)
  · exact htwo (sub_eq_zero.mp h)

def kernelEisensteinL2Correction (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  kernelEisensteinResolvent s (kernelL2Defect a b ha hab s)

lemma kernelEisensteinL2Correction_analyticAt_nonreal
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelEisensteinL2Correction a b ha hab) s := by
  exact ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
    (kernelL2Defect a b ha hab s,kernelEisensteinResolvent s)).comp₂
      ((kernelL2Defect_entire a b ha hab).analyticAt s)
      (kernelEisensteinResolvent_analyticAt_nonreal s hs hi)

lemma kernelEisensteinL2Correction_unique (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s)))
    (u : KernelQuotientL2)
    (hu : (u,kernelL2Defect a b ha hab s+kernelEisensteinSpectralParameter s•u)∈kernelEnergyLaplacian.graph) :
    kernelEisensteinL2Correction a b ha hab s=u :=
  kernelSpectralResolvent_unique _ hs _ _ hu

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelThetaMassProjection : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM kernelThetaNull.starProjection

def kernelRegularL2Resolvent (z : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM (kernelRegularInverseLift z)

lemma kernelRegularL2Resolvent_analyticAt :
    AnalyticAt ℂ kernelRegularL2Resolvent (8/9:ℂ) := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (kernelRegularInverseLift (8/9))).comp_of_eq kernelRegularInverseLift_analyticAt rfl

lemma kernelSpectralResolvent_decomposition (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) (F : KernelQuotientL2) :
    kernelSpectralResolvent z F=((17/9)/(8/9-z):ℂ)•kernelThetaMassProjection F+
      kernelRegularL2Resolvent z F := by
  unfold kernelSpectralResolvent
  rw [←kernelLocalEnergyResolvent_eq_inverse z hne hz]
  simp only [kernelLocalEnergyResolvent,map_add,map_smul,_root_.add_apply,
    _root_.smul_apply,kernelThetaMassProjection,kernelRegularL2Resolvent]

def kernelEisensteinCorrectionNumerator (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  ((17/9)/(s-2/3):ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab s)+
    (s-4/3)•kernelRegularL2Resolvent (kernelEisensteinSpectralParameter s)
      (kernelL2Defect a b ha hab s)

def kernelEisensteinResidueVector (a b : ℝ) (ha : 0<a) (hab : a<b) : KernelQuotientL2 :=
  (17/6:ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab (4/3))

lemma kernelEisensteinCorrectionNumerator_center (a b : ℝ) (ha : 0<a) (hab : a<b) :
    kernelEisensteinCorrectionNumerator a b ha hab (4/3)=kernelEisensteinResidueVector a b ha hab := by
  simp only [kernelEisensteinCorrectionNumerator,kernelEisensteinResidueVector,sub_self,zero_smul,add_zero]
  congr 1
  norm_num

lemma kernelEisensteinCorrectionNumerator_analyticAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    AnalyticAt ℂ (kernelEisensteinCorrectionNumerator a b ha hab) (4/3:ℂ) := by
  have hf := (kernelL2Defect_entire a b ha hab).analyticAt (4/3:ℂ)
  have hp := (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2)
    (F := KernelQuotientL2) kernelThetaMassProjection (kernelL2Defect a b ha hab (4/3))).comp_of_eq hf rfl
  have hr : AnalyticAt ℂ (fun s => kernelRegularL2Resolvent (kernelEisensteinSpectralParameter s)) (4/3:ℂ) := by
    have hreg : AnalyticAt ℂ kernelRegularL2Resolvent (kernelEisensteinSpectralParameter (4/3)) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularL2Resolvent_analyticAt
    exact hreg.comp_of_eq (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl
  have happ := ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
    (kernelL2Defect a b ha hab (4/3),kernelRegularL2Resolvent (kernelEisensteinSpectralParameter (4/3)))).comp₂ hf hr
  have hscalar : AnalyticAt ℂ (fun s : ℂ => (17/9)/(s-2/3)) (4/3:ℂ) := by
    apply AnalyticAt.div analyticAt_const (analyticAt_id.sub analyticAt_const)
    norm_num
  exact (hscalar.smul hp).add ((analyticAt_id.sub analyticAt_const).smul happ)

lemma kernelEisensteinCorrectionNumerator_eventually (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ),
      (s-4/3)•kernelEisensteinL2Correction a b ha hab s=
        kernelEisensteinCorrectionNumerator a b ha hab s := by
  have hc : ContinuousAt kernelEisensteinSpectralParameter (4/3:ℂ) := by
    unfold kernelEisensteinSpectralParameter
    fun_prop
  have hp : ∀ᶠ s : ℂ in 𝓝 (4/3:ℂ), IsUnit (kernelRegularPencil (kernelEisensteinSpectralParameter s)) := by
    have hh : ∀ᶠ z : ℂ in 𝓝 (kernelEisensteinSpectralParameter (4/3)), IsUnit (kernelRegularPencil z) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularPencil_eventually_isUnit
    exact hc.eventually hh
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,
    eventually_ne_nhdsWithin (show (4/3:ℂ)≠2/3 by norm_num),self_mem_nhdsWithin] with s hs htwo hfour
  have hfactor : (8/9:ℂ)-kernelEisensteinSpectralParameter s=(s-4/3)*(s-2/3) := by
    unfold kernelEisensteinSpectralParameter
    ring
  have hne : kernelEisensteinSpectralParameter s≠8/9 := by
    intro he
    have hh := mul_ne_zero (sub_ne_zero.mpr hfour) (sub_ne_zero.mpr htwo)
    rw [←hfactor,he,sub_self] at hh
    exact hh rfl
  change (s-4/3)•kernelSpectralResolvent (kernelEisensteinSpectralParameter s)
    (kernelL2Defect a b ha hab s)=_
  rw [kernelSpectralResolvent_decomposition _ hne hs,smul_add,smul_smul]
  have hscalar : (s-4/3)*((17/9)/(8/9-kernelEisensteinSpectralParameter s))=(17/9)/(s-2/3) := by
    rw [hfactor]
    have hcancel (x y c : ℂ) (hx : x≠0) : x*(c/(x*y))=c/y := by
      rw [div_eq_mul_inv,mul_inv_rev]
      calc
        _ = (x*x⁻¹)*(c*y⁻¹) := by ring
        _ = c/y := by rw [mul_inv_cancel₀ hx,one_mul,div_eq_mul_inv]
    exact hcancel _ _ _ (sub_ne_zero.mpr hfour)
  rw [hscalar]
  rfl

lemma kernelEisensteinResidueVector_limit (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)•kernelEisensteinL2Correction a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelEisensteinResidueVector a b ha hab)) := by
  apply (tendsto_congr' (kernelEisensteinCorrectionNumerator_eventually a b ha hab)).mpr
  rw [←kernelEisensteinCorrectionNumerator_center a b ha hab]
  exact (kernelEisensteinCorrectionNumerator_analyticAt a b ha hab).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

instance kernelThetaMassProjection_range_finiteDimensional :
    FiniteDimensional ℂ kernelThetaMassProjection.range := by
  let B : kernelThetaNull→L[ℂ]KernelQuotientL2 := kernelEnergyMass.comp kernelThetaNull.subtypeL
  have : FiniteDimensional ℂ B.range := LinearMap.finiteDimensional_range B.toLinearMap
  apply Submodule.finiteDimensional_of_le (S₂ := B.range)
  rintro y ⟨x,rfl⟩
  exact ⟨kernelThetaNull.orthogonalProjectionOnto (kernelEnergyMass.adjoint x),rfl⟩

lemma kernelEisensteinResidueVector_graph (a b : ℝ) (ha : 0<a) (hab : a<b) :
    (kernelEisensteinResidueVector a b ha hab,(8/9:ℂ)•kernelEisensteinResidueVector a b ha hab)
      ∈kernelEnergyLaplacian.graph := by
  let v : KernelEnergyGraph := (17/6:ℂ)•kernelThetaNull.starProjection
    (kernelVariationalSolution (kernelL2Defect a b ha hab (4/3)))
  have hv : kernelSpectralFormOperator (8/9) v=kernelVariationalSolution 0 := by
    change kernelSpectralFormOperator (8/9) ((17/6:ℂ)•kernelThetaNull.starProjection _)=_
    rw [map_smul]
    have hz : kernelSpectralFormOperator (8/9) (kernelThetaNull.starProjection
        (kernelVariationalSolution (kernelL2Defect a b ha hab (4/3))))=0 :=
      kernelThetaNull.starProjection_apply_mem _
    rw [hz,smul_zero,map_zero]
  have hh := kernelSpectralFormOperator_solution_graph (8/9) 0 v hv
  simpa only [v,map_smul,zero_add,kernelEisensteinResidueVector,kernelThetaMassProjection,
    kernelL2SandwichCLM,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,kernelVariationalSolution] using! hh

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CanonicalRowCompletion
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid

lemma good_prime_norm_mod_six (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) : Ideal.absNorm P%6=1 := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,orderOf χ=6 := ⟨_,sexticChar_order P hg hc⟩
  have hdiv:=χ.orderOf_dvd_card_sub_one
  rw [hχ] at hdiv
  have hcard : 1<Fintype.card (ActualEisensteinCubic.O⧸P):=Fintype.one_lt_card
  have hn : Ideal.absNorm P=Fintype.card (ActualEisensteinCubic.O⧸P) := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  rw [hn]
  omega

lemma unit_sixth_exponent_mul (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (ha : a%6=1) (hb : b%6=1) :
    u.val^((a*b-1)/6)=u.val^((a-1)/6)*u.val^((b-1)/6) := by
  have ha' : a=6*(a/6)+1:=by omega
  have hb' : b=6*(b/6)+1:=by omega
  have hab : a*b=6*(a/6+b/6+6*((a/6)*(b/6)))+1 := by
    calc
      a*b=(6*(a/6)+1)*(6*(b/6)+1):=congrArg₂ (·*·) ha' hb'
      _ = _ := by ring
  have hab' : (a*b-1)/6=a/6+b/6+6*((a/6)*(b/6)):=by omega
  have hda : (a-1)/6=a/6:=by omega
  have hdb : (b-1)/6=b/6:=by omega
  rw [hab',hda,hdb,pow_add,pow_add,pow_mul,unit_pow_six,one_pow,mul_one]

lemma multiset_unit_norm (u : ActualEisensteinCubic.Oˣ) (s : Multiset (Ideal ActualEisensteinCubic.O))
    (hs : ∀P∈s,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    (s.map (localRowValue u.val)).prod =
      eisEmbedding (u.val^(((s.map Ideal.absNorm).prod-1)/6)) ∧
      (s.map Ideal.absNorm).prod%6=1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons P s ih =>
    have hp:=hs P (Multiset.mem_cons_self _ _)
    let : P.IsMaximal:=hp.1
    have htail : ∀Q∈s,Q.IsMaximal ∧ lambda∉Q ∧ ringChar (ActualEisensteinCubic.O⧸Q)≠2:=
      fun Q hQ=>hs Q (Multiset.mem_cons_of_mem hQ)
    obtain ⟨hv,hn⟩:=ih htail
    have hP:=good_prime_norm_mod_six P hp.2.1 hp.2.2
    simp only [Multiset.map_cons,Multiset.prod_cons]
    refine ⟨?_,by rw [Nat.mul_mod,hP,hn]⟩
    rw [localRowValue_good _ P hp.2.1,actualSextic_unit_euler P hp.2.1 hp.2.2,hv]
    have hcard : Nat.card (ActualEisensteinCubic.O⧸P)=Ideal.absNorm P := by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
    rw [hcard,unit_sixth_exponent_mul u _ _ hP hn,map_mul]

theorem idealRowHom_unit_norm (u : ActualEisensteinCubic.Oˣ) (I : Ideal ActualEisensteinCubic.O) (hI : I≠0)
    (hgood : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    idealRowHom u.val I=eisEmbedding (u.val^((Ideal.absNorm I-1)/6)) := by
  have hn (s : Multiset (Ideal ActualEisensteinCubic.O)) : (s.map Ideal.absNorm).prod=Ideal.absNorm s.prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih => simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,ih]
  have hh:=(multiset_unit_norm u (normalizedFactors I) hgood).1
  rw [hn,Ideal.prod_normalizedFactors_eq_self hI] at hh
  change (if I=0 then 0 else _) = _
  rwa [if_neg hI]

lemma ideal_norm_mod_six_of_good (I : Ideal ActualEisensteinCubic.O) (hI : I≠0)
    (hgood : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    Ideal.absNorm I%6=1 := by
  have hn (s : Multiset (Ideal ActualEisensteinCubic.O)) : (s.map Ideal.absNorm).prod=Ideal.absNorm s.prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih => simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,ih]
  have hh:=(multiset_unit_norm (1:ActualEisensteinCubic.Oˣ) (normalizedFactors I) hgood).2
  rwa [hn,Ideal.prod_normalizedFactors_eq_self hI] at hh

theorem idealRowHom_unit_eq_of_norm_mod_thirty_six (u : ActualEisensteinCubic.Oˣ) (I J : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hJ : J≠0)
    (hgI : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (hgJ : ∀P∈normalizedFactors J,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (hmod : Ideal.absNorm I%36=Ideal.absNorm J%36) :
    idealRowHom u.val I=idealRowHom u.val J := by
  rw [idealRowHom_unit_norm u I hI hgI,idealRowHom_unit_norm u J hJ hgJ]
  have hmi:=ideal_norm_mod_six_of_good I hI hgI
  have hmj:=ideal_norm_mod_six_of_good J hJ hgJ
  have hm : (Ideal.absNorm I-1)/6 ≡ (Ideal.absNorm J-1)/6 [MOD 6] := by
    dsimp [Nat.ModEq]
    omega
  exact congrArg eisEmbedding (pow_eq_pow_of_modEq hm (unit_pow_six u))

end CanonicalUnitEuler

open scoped BigOperators Classical SchwartzMap ContDiff

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma rowCoordinates_zero : rowCoordinates (0 : Fin 2 → ActualEisensteinCubic.O)=0 := by
  apply norm_le_zero_iff.mp
  have h := coordinates_norm_bound (0 : Fin 2 → ActualEisensteinCubic.O)
  have he : (fun i : Fin 2 => eisEmbedding ((0 : Fin 2 → ActualEisensteinCubic.O) i))=0 := by
    funext i
    exact map_zero _
  rw [he,norm_zero,mul_zero] at h
  exact h

lemma rowCoordinates_norm_pos {u : Fin 2 → ActualEisensteinCubic.O} (hu : u≠0) :
    0<‖rowCoordinates u‖ := by
  apply norm_pos_iff.mpr
  intro h
  exact hu (rowCoordinates_injective (h.trans rowCoordinates_zero.symm))

lemma rowCoordinates_le_horizontal (u : Fin 2 → ActualEisensteinCubic.O) (z : ℂ) (hz : ‖z‖≤1) :
    ‖rowCoordinates u‖≤2*(‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖+
      ‖eisEmbedding (u 0)‖) := by
  apply (coordinates_norm_bound u).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · simp only [Fin.zero_eta]
    linarith [norm_nonneg (eisEmbedding (u 0)*z+eisEmbedding (u 1))]
  · have h : ‖eisEmbedding (u 1)‖≤
        ‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖+‖eisEmbedding (u 0)*z‖ := by
      simpa only [add_sub_cancel_left] using
        norm_sub_le (eisEmbedding (u 0)*z+eisEmbedding (u 1)) (eisEmbedding (u 0)*z)
    rw [norm_mul] at h
    have hm := mul_le_mul_of_nonneg_left hz (norm_nonneg (eisEmbedding (u 0)))
    rw [mul_one] at hm
    exact h.trans (add_le_add_right hm _)

lemma height_times_coordinate_bound (A c v N : ℝ)
    (_hA : 0≤A) (hc : 1≤ c) (hv : 1/2≤v) (hN : N≤2*(A+c)) :
    N*v≤5*(A^2+c^2*v^2) := by
  have hv0 : 0≤v := by linarith
  have hcv : v≤ c*v := by nlinarith
  have hcv0 : 1/2≤ c*v := by linarith
  have hv2 : v^2≤(c*v)^2 := by nlinarith
  have hcross : 2*v*A≤A^2+c^2*v^2 := by nlinarith [sq_nonneg (A-v)]
  have hlin : 2*c*v≤4*(c*v)^2 := by nlinarith
  have hNv := mul_le_mul_of_nonneg_right hN hv0
  nlinarith [sq_nonneg A]

lemma rowHeight_times_coordinates (u : Fin 2 → ActualEisensteinCubic.O) (hu : u 0≠0)
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    (v/(‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖^2+
       ‖eisEmbedding (u 0)‖^2*v^2))*‖rowCoordinates u‖≤5 := by
  have hc : 1≤‖eisEmbedding (u 0)‖ := by
    have hh := one_le_normSq_embedding (u 0) hu
    rw [Complex.normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg (eisEmbedding (u 0))]
  have hden : 0<‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖^2+
      ‖eisEmbedding (u 0)‖^2*v^2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  simpa only [mul_comm v] using
    height_times_coordinate_bound _ _ _ _ (norm_nonneg _) hc hv
      (rowCoordinates_le_horizontal u z hz)

lemma positive_rpow_of_product_bound (h N C σ : ℝ)
    (hh : 0≤h) (hN : 0<N) (hC : 0≤C) (hσ : 0≤σ) (hb : h*N≤C) :
    h^σ≤C ^σ*N^(-σ) := by
  have hdiv : h≤C/N := (le_div_iff₀ hN).mpr hb
  have hr := Real.rpow_le_rpow hh hdiv hσ
  rw [Real.div_rpow hC hN.le,div_eq_mul_inv] at hr
  simpa only [Real.rpow_neg hN.le] using hr

def cuspRemainderProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v-cuspSeedProfile a b s v

lemma cuspRemainderProfile_norm_le (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ‖cuspRemainderProfile a b s v‖≤v^s.re := by
  have hnon : 0≤1-cuspTransition a b v := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hle : 1-cuspTransition a b v≤1 := by
    have := Real.smoothTransition.nonneg ((v-a)/(b-a))
    change 0≤ cuspTransition a b v at this
    linarith
  have he : cuspRemainderProfile a b s v=
      ((1-cuspTransition a b v:ℝ):ℂ)*positiveHeightPower s v := by
    simp only [cuspRemainderProfile,cuspSeedProfile,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  rw [he,norm_mul,Complex.norm_of_nonneg hnon,positiveHeightPower_eq_cpow s v hv,
    Complex.norm_cpow_eq_rpow_re_of_pos hv]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hv.le _) hle

lemma cuspRemainderProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : 0<v) (hbv : b≤v) : cuspRemainderProfile a b s v=0 := by
  rw [cuspRemainderProfile,cuspSeedProfile_incoming a b s v hab hbv hv,
    positiveHeightPower_eq_cpow s v hv,sub_self]

lemma cuspRemainderProfile_norm_le_bound (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hb : 0≤b) (hv : 0<v) (hs : 0≤ s.re) :
    ‖cuspRemainderProfile a b s v‖≤b^s.re := by
  by_cases h : b≤v
  · rw [cuspRemainderProfile_zero a b s v hab hv h,norm_zero]
    exact Real.rpow_nonneg hb _
  · exact (cuspRemainderProfile_norm_le a b s v hv).trans
      (Real.rpow_le_rpow hv.le (le_of_not_ge h) hs)

end

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_row_embedding_ne_zero {u : Fin 2 → ActualEisensteinCubic.O} (hu : u≠0) :
    (eisEmbedding ∘ u)≠0 := by
  intro h
  apply hu
  funext i
  apply eisEmbedding_injective
  simpa only [Function.comp_apply,Pi.zero_apply,map_zero] using congrFun h i

lemma coprime_row_ne_zero {u : Fin 2 → ActualEisensteinCubic.O} (h : IsCoprime (u 0) (u 1)) : u≠0 := by
  intro hz
  have hh : (0 : ActualEisensteinCubic.O)=1 := by
    simpa only [hz,Pi.zero_apply,isCoprime_zero_left,isUnit_zero_iff] using h
  exact zero_ne_one hh

theorem cuspRemainderProfile_row_bound (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤ s.re)
    (u : Fin 2 → ActualEisensteinCubic.O) (hcop : IsCoprime (u 0) (u 1))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    ‖cuspRemainderProfile a b s (transformedHeight z v (eisEmbedding ∘ u))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates u‖^(-s.re) := by
  have hu := coprime_row_ne_zero hcop
  have hN := rowCoordinates_norm_pos hu
  have hv0 : 0<v := by linarith
  have hh : 0<transformedHeight z v (eisEmbedding ∘ u) :=
    div_pos hv0 (heightDenominator_pos z v hv0 _ (integral_row_embedding_ne_zero hu))
  have hC : 0≤ max 5 (2*b) := (by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)
  by_cases hc : u 0=0
  · have hunit : IsUnit (u 1) := by simpa only [hc,isCoprime_zero_left] using hcop
    obtain ⟨d,hd⟩ := hunit
    have hdnorm : ‖eisEmbedding (u 1)‖=1 := by
      rw [←hd]
      exact GaussGeneratorTransport.norm_eisEmbedding_unit d
    have hn : ‖rowCoordinates u‖≤2 := by
      apply (coordinates_norm_bound u).trans
      have hm : ‖fun i => eisEmbedding (u i)‖≤1 := by
        apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro i
        fin_cases i
        · change ‖eisEmbedding (u 0)‖≤1
          simp only [hc,map_zero,norm_zero,zero_le_one]
        · exact hdnorm.le
      nlinarith
    apply (cuspRemainderProfile_norm_le_bound a b s _ hab hb hh hs).trans
    exact positive_rpow_of_product_bound b _ _ _ hb hN hC hs
      (by nlinarith [mul_le_mul_of_nonneg_left hn hb,le_max_right (5 : ℝ) (2*b)])
  · apply (cuspRemainderProfile_norm_le a b s _ hh).trans
    apply positive_rpow_of_product_bound _ _ _ _ hh.le hN hC hs
    exact (rowHeight_times_coordinates u hc z hz v hv).trans (le_max_left _ _)

def translatedCuspRow (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets) : Fin 2 → ActualEisensteinCubic.O :=
  Matrix.vecMul (cosetRow r) (M : Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O)

lemma translatedCuspRow_injective (M : SL(2,ActualEisensteinCubic.O)) : Function.Injective (translatedCuspRow M) := by
  intro r t h
  apply cosetRow_injective
  have hh := congrArg (fun u : Fin 2 → ActualEisensteinCubic.O => Matrix.vecMul u
    ((M⁻¹ : SL(2,ActualEisensteinCubic.O)) : Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O)) h
  simpa only [translatedCuspRow,Matrix.vecMul_vecMul,←Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.vecMul_one] using hh

lemma integral_bottom_coprime (M : SL(2,ActualEisensteinCubic.O)) : IsCoprime (M 1 0) (M 1 1) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by
    simpa only [Matrix.det_fin_two] using M.property
  refine ⟨-M 0 1,M 0 0,?_⟩
  linear_combination hd

lemma translatedCuspRow_coprime (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets) :
    IsCoprime (translatedCuspRow M r 0) (translatedCuspRow M r 1) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change IsCoprime (translatedCuspRow M (cosetOf N) 0) (translatedCuspRow M (cosetOf N) 1)
    simpa only [translatedCuspRow,cosetRow_cosetOf,row,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Matrix.vecMul,dotProduct] using integral_bottom_coprime ((N : SL(2,ActualEisensteinCubic.O))*M)

lemma cosetHeight_integral_chart (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    cosetHeight r (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (eisEmbedding ∘ translatedCuspRow M r) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf N) (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (eisEmbedding ∘ translatedCuspRow M (cosetOf N))
    rw [cosetHeight_cosetOf,←integralComplexMatrix_levelThree,
      ←mul_smul,←map_mul,hyperbolicHeight_action_upperPoint]
    simp only [integralComplexMatrix_apply,transformedHeight,heightDenominator,
      Function.comp_apply,translatedCuspRow,cosetRow_cosetOf,row,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Matrix.vecMul,dotProduct]

lemma translated_remainder_majorant (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤ s.re)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v)
    (hv0 : 0<v) (r : CuspCosets) :
    ‖(cosetCharacter r)⁻¹*cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates (translatedCuspRow M r)‖^(-s.re) := by
  rw [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul,cosetHeight_integral_chart]
  exact cuspRemainderProfile_row_bound a b s hab hb hs _
    (translatedCuspRow_coprime M r) z hz v hv

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma cuspCutoffTerm_eq_seedProfile (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (r : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm 1 (cuspSeedProfile a b s) r w=
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
  unfold cuspCutoffTerm
  split_ifs with h
  · rfl
  · rw [cuspSeedProfile_zero a b s _ hab ((le_of_not_gt h).trans ha),mul_zero]

lemma cusp_seed_profile_summable (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => (cosetCharacter r)⁻¹*
      cuspSeedProfile a b s (cosetHeight r w)) :=
  (cuspCutoffTerm_summable 1 le_rfl _ w).congr
    (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)

theorem eisenstein_sub_seed_eq_series (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w-smoothCuspSeed a b s w=
      ∑'r : CuspCosets,(cosetCharacter r)⁻¹*
        cuspRemainderProfile a b s (cosetHeight r w) := by
  have hE := (height_series_summable_norm s hs w).of_norm
  have hS := cusp_seed_profile_summable a b ha hab s w
  have heq : smoothCuspSeed a b s w=∑'r : CuspCosets,
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
    unfold smoothCuspSeed cuspCutoffCorrection
    exact tsum_congr (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)
  rw [hyperbolicEisenstein_eq_height_series,heq,←hE.tsum_sub hS]
  apply tsum_congr
  intro r
  rw [cuspRemainderProfile,positiveHeightPower_eq_cpow s _ (cosetHeight_pos r w)]
  ring

def eisensteinRemainderBound (b : ℝ) (s : ℂ) : ℝ :=
  (max 5 (2*b))^s.re * ∑'n : (Fin 2×Fin 2)→ℤ,‖n‖^(-s.re)

lemma eisensteinRemainderBound_nonneg (b : ℝ) (s : ℂ) :
    0≤eisensteinRemainderBound b s :=
  mul_nonneg (Real.rpow_nonneg ((by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)) _)
    (tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _))

theorem eisenstein_sub_seed_chart_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (M : SL(2,ActualEisensteinCubic.O))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    ‖hyperbolicEisenstein s (integralComplexMatrix M • upperPoint z v hv0)-
      smoothCuspSeed a b s (integralComplexMatrix M • upperPoint z v hv0)‖≤
      eisensteinRemainderBound b s := by
  let G : ((Fin 2×Fin 2)→ℤ)→ℝ := fun n => (max 5 (2*b))^s.re*‖n‖^(-s.re)
  let f : CuspCosets→(Fin 2×Fin 2)→ℤ := fun r => rowCoordinates (translatedCuspRow M r)
  let R : CuspCosets→ℂ := fun r => (cosetCharacter r)⁻¹*cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))
  have hg : Summable G := (summable_integer_four_rpow s.re hs).mul_left _
  have hi : Function.Injective f := rowCoordinates_injective.comp (translatedCuspRow_injective M)
  have hb : ∀r,‖R r‖≤G (f r) :=
    translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0
  have hr : Summable (fun r => ‖R r‖) :=
    (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [eisenstein_sub_seed_eq_series a b ha hab s (by linarith)]
  change ‖∑'r,R r‖≤eisensteinRemainderBound b s
  apply (norm_tsum_le_tsum_norm hr).trans
  have hsum : (∑'r,‖R r‖)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

theorem eisenstein_sub_seed_bounded (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (w : HyperbolicSpace) :
    ‖hyperbolicEisenstein s w-smoothCuspSeed a b s w‖≤eisensteinRemainderBound b s := by
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  have hz1 : ‖z‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have hv1 : 1/2≤v := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hh0 := Real.sqrt_nonneg (2/3 : ℝ)
    nlinarith
  have hw : w=integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [←hMw,map_inv,inv_smul_smul]
  rw [hw]
  exact eisenstein_sub_seed_chart_bound a b ha hab s hs M⁻¹ z hz1 v hv1 hv

lemma cuspRemainderProfile_measurable (a b : ℝ) (s : ℂ) :
    Measurable (cuspRemainderProfile a b s) := by
  unfold cuspRemainderProfile cuspSeedProfile positiveHeightPower logRatioPower cuspTransition
  fun_prop

lemma eisenstein_sub_seed_measurable (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) :
    Measurable (fun w => hyperbolicEisenstein s w-smoothCuspSeed a b s w) := by
  simp_rw [eisenstein_sub_seed_eq_series a b ha hab s hs]
  apply Measurable.tsum
  intro r
  exact measurable_const.mul ((cuspRemainderProfile_measurable a b s).comp
    (cosetHeight_continuous r).measurable)

theorem kernel_eisenstein_sub_seed_memLp (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    MemLp (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) 2 (integralQuotientVolume globalKubotaKernel) := by
  have hmeas : Measurable (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) :=
    measurable_from_quotient.mpr (eisenstein_sub_seed_measurable a b ha hab s (by linarith))
  apply MemLp.of_bound hmeas.aestronglyMeasurable (eisensteinRemainderBound b s)
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact eisenstein_sub_seed_bounded a b ha hab s hs w

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
open UniqueFactorizationMonoid
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

def unitSupplement (u : ActualEisensteinCubic.Oˣ) : ActualEisensteinCubic.O→*ℂ where
  toFun n:=if Supported (Ideal.span {n}) then idealRowHom u.val (Ideal.span {n}) else 0
  map_one' := by
    have hs : Supported (1:Ideal ActualEisensteinCubic.O):=⟨one_ne_zero,by
      intro P hP
      rw [normalizedFactors_one] at hP
      exact False.elim (Multiset.notMem_zero P hP)⟩
    rw [show Ideal.span {(1:ActualEisensteinCubic.O)}=(1:Ideal ActualEisensteinCubic.O) by simp only [Ideal.span_singleton_one,Ideal.one_eq_top],if_pos hs,map_one]
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton, supported_mul_iff,map_mul]
    by_cases hx:Supported (Ideal.span {x}) <;> by_cases hy:Supported (Ideal.span {y}) <;> simp [hx,hy]

lemma supported_good (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) :
    ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2 := by
  intro P hP
  have hp:=prime_of_normalized_factor P hP
  exact ⟨(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero,hI.2 P hP⟩

lemma unitSupplement_norm (u : ActualEisensteinCubic.Oˣ) (n : ActualEisensteinCubic.O) : ‖unitSupplement u n‖≤1 := by
  change ‖if _ then _ else _‖≤_
  split_ifs
  · exact idealRowHom_norm _ _
  · simp

lemma norm_eval_residue (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}) : ZMod m)=
      (a : ZMod m)^2-(a : ZMod m)*(b : ZMod m)+(b : ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}) : ℤ)=a^2-a*b+b^2 := by
    rw [←qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (coords (eval a b))).toNat : ℤ)=_
    rw [Int.toNat_of_nonneg (qO_nonneg _),coords_eval]
    rfl
  have hz := congrArg (fun k : ℤ => (k : ZMod m)) hi
  push_cast at hz
  exact hz

lemma norm_residue_congruent (m : ℕ) (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(m:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    Ideal.absNorm (Ideal.span {x})%m=Ideal.absNorm (Ideal.span {y})%m := by
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c:=(coords y).1
  let d:=(coords y).2
  let e:=(coords z).1
  let f:=(coords z).2
  have hy : y=eval c d:=(eval_coords y).symm
  have hx : x=eval (c+(m:ℤ)*e) (d+(m:ℤ)*f) := by
    calc
      x=y+(m:ActualEisensteinCubic.O)*z:=by linear_combination hz
      _=eval (c+(m:ℤ)*e) (d+(m:ℤ)*f):=by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  apply (ZMod.natCast_eq_natCast_iff' _ _ m).mp
  rw [hx,hy,norm_eval_residue,norm_eval_residue]
  simp

lemma supported_span_congruent_mod_thirty_six (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(36:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    Supported (Ideal.span {x})↔Supported (Ideal.span {y}) := by
  have h36:(36:ActualEisensteinCubic.O)∣x-y:=Ideal.mem_span_singleton.mp hxy
  have hlam : lambda∣(36:ActualEisensteinCubic.O):=
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three).trans ⟨12,by norm_num⟩
  have htwo : (2:ActualEisensteinCubic.O)∣(36:ActualEisensteinCubic.O):=⟨18,by norm_num⟩
  have he (a : ActualEisensteinCubic.O) (ha : a∣x-y) : a∣x↔a∣y := by
    constructor
    · intro hx
      convert (preTransparency := .instances) dvd_sub hx ha using 1 ; ring
    · intro hy
      convert (preTransparency := .instances) dvd_add ha hy using 1 ; ring
  rw [supported_span_iff,supported_span_iff,he lambda (hlam.trans h36),he 2 (htwo.trans h36)]

theorem unitSupplement_periodic (u : ActualEisensteinCubic.Oˣ) (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(36:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    unitSupplement u x=unitSupplement u y := by
  have hs:=supported_span_congruent_mod_thirty_six x y hxy
  change (if _ then _ else _)=(if _ then _ else _)
  by_cases hx:Supported (Ideal.span {x})
  · have hy:=hs.mp hx
    rw [if_pos hx,if_pos hy]
    exact idealRowHom_unit_eq_of_norm_mod_thirty_six u _ _ hx.1 hy.1
      (supported_good _ hx) (supported_good _ hy) (norm_residue_congruent 36 x y hxy)
  · rw [if_neg hx,if_neg (fun hy=>hx (hs.mpr hy))]

lemma rowTwist_zero_of_common_prime (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z n : ActualEisensteinCubic.O)
    (P : Ideal ActualEisensteinCubic.O) (hp : Prime P) (hm : m∈P) (hn : n∈P) :
    rowTwist Ψ m f z n=0 := by
  have hPI:P∣Ideal.span {n}:=Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hn))
  have hm6:m^6∈P:=by
    rw [show m^6=m^5*m by ring]
    exact P.mul_mem_left _ hm
  have hx:m^6*f^4*z∈P:=P.mul_mem_right _ (P.mul_mem_right _ hm6)
  change Ψ n*idealRowHom _ (Ideal.span {n})=0
  rw [idealRowHom_zero_of_dvd _ hp hPI hx,mul_zero]

theorem rowTwist_unitSupplement (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ)
    (hmLam : lambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m) :
    rowTwist Ψ m f (u.val*z)=unitSupplement u*rowTwist Ψ m f z := by
  ext n
  by_cases hn:Supported (Ideal.span {n})
  · change Ψ n*idealRowHom (m^6*f^4*(u.val*z)) (Ideal.span {n})=
      (if Supported (Ideal.span {n}) then _ else 0)*(Ψ n*idealRowHom _ (Ideal.span {n}))
    rw [if_pos hn,show m^6*f^4*(u.val*z)=u.val*(m^6*f^4*z) by ring,idealRowHom_argument_mul]
    ring
  · have hz:rowTwist Ψ m f (u.val*z) n=0 := by
      have hbad : lambda∣n ∨ (2:ActualEisensteinCubic.O)∣n := by
        simpa only [supported_span_iff,not_and_or,not_not] using hn
      rcases hbad with hLam|h2
      · exact rowTwist_zero_of_common_prime Ψ m f _ n (Ideal.span {lambda})
          (Ideal.prime_of_isPrime (by
            rw [ne_eq,Ideal.span_singleton_eq_bot]
            exact PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero) lambdaIdeal_maximal.isPrime)
          (Ideal.mem_span_singleton.mpr hmLam) (Ideal.mem_span_singleton.mpr hLam)
      · exact rowTwist_zero_of_common_prime Ψ m f _ n (Ideal.span {(2:ActualEisensteinCubic.O)})
          (Ideal.prime_of_isPrime (by
            rw [ne_eq,Ideal.span_singleton_eq_bot]
            norm_num) twoIdeal_maximal.isPrime)
          (Ideal.mem_span_singleton.mpr hm2) (Ideal.mem_span_singleton.mpr h2)
    change rowTwist Ψ m f (u.val*z) n=(if Supported (Ideal.span {n}) then _ else 0)*_
    rw [hz,if_neg hn,zero_mul]

end CanonicalUnitEuler

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups

lemma kernelBarrier_sublevel_isCompact (T : ℝ) :
    IsCompact {q : KernelQuotient | kernelQuotientBarrier 2 3 q≤T} := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max 3 T)
  apply hcompact.of_isClosed_subset
    (isClosed_le (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)) continuous_const)
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max 3 T) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max 3 T) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    have hh : 3<p.1.2 := (le_max_left 3 T).trans_lt hp.2.2
    change kernelQuotientBarrier 2 3 (fordOrbitChart globalKubotaKernel r p)≤T at hq
    rw [kernelQuotientBarrier_fordCusp 2 3 (by norm_num) (by norm_num) r p hh] at hq
    exact (not_lt_of_ge hq) ((le_max_right 3 T).trans_lt hp.2.2)

def kernelExhaustionProfile (n : ℕ) (v : ℝ) : ℝ :=
  1-cuspTransition 1 2 (v/((n:ℝ)+1))

def kernelExhaustionCutoff (n : ℕ) (q : KernelQuotient) : ℝ :=
  kernelExhaustionProfile n (kernelQuotientBarrier 2 3 q)

lemma kernelExhaustionProfile_smooth (n : ℕ) :
    ContDiff ℝ ∞ (kernelExhaustionProfile n) := by
  unfold kernelExhaustionProfile cuspTransition
  fun_prop

lemma kernelExhaustionCutoff_smooth (n : ℕ) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (kernelExhaustionCutoff n) :=
  (kernelExhaustionProfile_smooth n).contMDiff.comp
    (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num))

lemma kernelExhaustionProfile_bounds (n : ℕ) (v : ℝ) :
    0≤kernelExhaustionProfile n v ∧ kernelExhaustionProfile n v≤1 := by
  have h0 := Real.smoothTransition.nonneg ((v/((n:ℝ)+1)-1)/(2-1))
  have h1 := Real.smoothTransition.le_one ((v/((n:ℝ)+1)-1)/(2-1))
  change 0≤1-Real.smoothTransition _ ∧ 1-Real.smoothTransition _≤1
  constructor <;> linarith

lemma kernelExhaustionProfile_one (n : ℕ) (v : ℝ) (hv : v≤(n:ℝ)+1) :
    kernelExhaustionProfile n v=1 := by
  rw [kernelExhaustionProfile,cuspTransition_zero 1 2 _ (by norm_num)
    ((div_le_one (by positivity)).mpr hv),sub_zero]

lemma kernelExhaustionProfile_zero (n : ℕ) (v : ℝ) (hv : 2*((n:ℝ)+1)≤v) :
    kernelExhaustionProfile n v=0 := by
  rw [kernelExhaustionProfile,cuspTransition_one 1 2 _ (by norm_num)
    ((le_div_iff₀ (by positivity)).mpr hv),sub_self]

lemma kernelExhaustionCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (kernelExhaustionCutoff n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (kernelBarrier_sublevel_isCompact (2*((n:ℝ)+1)))
  intro q hq
  change kernelQuotientBarrier 2 3 q≤2*((n:ℝ)+1)
  by_contra h
  exact hq (kernelExhaustionProfile_zero n _ (le_of_not_ge h))

lemma kernelExhaustionCutoff_bounds (n : ℕ) (q : KernelQuotient) :
    0≤kernelExhaustionCutoff n q ∧ kernelExhaustionCutoff n q≤1 :=
  kernelExhaustionProfile_bounds n _

lemma kernelExhaustionCutoff_eventually_one (q : KernelQuotient) :
    ∀ᶠn : ℕ in atTop,kernelExhaustionCutoff n q=1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (kernelQuotientBarrier 2 3 q)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply kernelExhaustionProfile_one
  have hh : (N:ℝ)≤n := by exact_mod_cast hn
  linarith

lemma kernelExhaustionCutoff_eventually_one_near (q : KernelQuotient) :
    ∀ᶠn : ℕ in atTop,kernelExhaustionCutoff n =ᶠ[𝓝 q] (fun _ => 1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (kernelQuotientBarrier 2 3 q)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hh : kernelQuotientBarrier 2 3 q<(n:ℝ)+1 := by
    have hcast : (N:ℝ)≤n := by exact_mod_cast hn
    linarith
  filter_upwards [(kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousAt.eventually_lt_const hh]
    with p hp
  exact kernelExhaustionProfile_one n _ hp.le

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma cuspTransition_euler_bounded (a b : ℝ) (hab : a<b) :
    ∃C : ℝ,0≤C ∧ ∀v,|v*deriv (cuspTransition a b) v|≤C := by
  have hc : HasCompactSupport (fun v => v*deriv (cuspTransition a b) v) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro v hv
    by_contra hnot
    have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hnot
    exact hv (by change v*deriv (cuspTransition a b) v=0; rw [(cuspTransition_derivatives a b v hab hout).1,mul_zero])
  have hcont : Continuous (fun v => v*deriv (cuspTransition a b) v) :=
    continuous_id.mul ((contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2.continuous)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hcont
  exact ⟨max C 0,le_max_right _ _,fun v => (hC v).trans (le_max_left _ _)⟩

lemma cuspRemainderProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspRemainderProfile a b s) v :=
  (positiveHeightPower_contDiffAt s v hv.ne').sub (cuspSeedProfile_contDiffAt a b s v hv)

lemma cuspRemainderProfile_euler (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    (v:ℂ)*deriv (cuspRemainderProfile a b s) v=
      positiveHeightPower s v *
        (((1-cuspTransition a b v:ℝ):ℂ)*s-((v*deriv (cuspTransition a b) v:ℝ):ℂ)) := by
  have h := (positiveHeightPower_hasDerivAt s v hv.ne').sub
    (cuspSeedProfile_hasDerivAt a b s v hv.ne')
  change HasDerivAt (cuspRemainderProfile a b s) _ v at h
  rw [h.deriv]
  simp only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  ; ring

lemma cuspRemainderProfile_euler_bound (a b : ℝ) (s : ℂ) (C : ℝ)
    (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C) (v : ℝ) (hv : 0<v) :
    ‖(v:ℂ)*deriv (cuspRemainderProfile a b s) v‖≤(‖s‖+C)*v^s.re := by
  rw [cuspRemainderProfile_euler a b s v hv,norm_mul,
    positiveHeightPower_eq_cpow s v hv,Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have hχ0 : 0≤1-cuspTransition a b v := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hχ1 : 1-cuspTransition a b v≤1 := by
    have h := Real.smoothTransition.nonneg ((v-a)/(b-a))
    change 0≤ cuspTransition a b v at h
    linarith
  have hfactor : ‖((1-cuspTransition a b v:ℝ):ℂ)*s-
      ((v*deriv (cuspTransition a b) v:ℝ):ℂ)‖≤‖s‖+C := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul,Complex.norm_of_nonneg hχ0,Complex.norm_real,Real.norm_eq_abs]
    have hm := mul_le_mul_of_nonneg_right hχ1 (norm_nonneg s)
    linarith [hC v]
  have hh := mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hv.le s.re)
  simpa only [mul_comm (v^s.re)] using hh

lemma cuspRemainderProfile_deriv_zero (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : 0<v) (hbv : b<v) : deriv (cuspRemainderProfile a b s) v=0 := by
  have he : cuspRemainderProfile a b s =ᶠ[𝓝 v] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hv,Ioi_mem_nhds hbv] with y hy hyb
    exact cuspRemainderProfile_zero a b s y hab hy hyb.le
  exact he.deriv_eq.trans (deriv_const v 0)

lemma rowLogD_hyperbolic_bound (u : Fin 2→ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) : |p 2*rowLogD u p j|≤1 := by
  have he := rowLog_eikonal u hu p hp
  have hsq : (p 2*rowLogD u p j)^2≤1 := by
    fin_cases j
    · change (p 2*rowLogD u p 0)^2≤1
      nlinarith [sq_nonneg (p 2*rowLogD u p 1),sq_nonneg (p 2*rowLogD u p 2)]
    · change (p 2*rowLogD u p 1)^2≤1
      nlinarith [sq_nonneg (p 2*rowLogD u p 0),sq_nonneg (p 2*rowLogD u p 2)]
    · change (p 2*rowLogD u p 2)^2≤1
      nlinarith [sq_nonneg (p 2*rowLogD u p 0),sq_nonneg (p 2*rowLogD u p 1)]
  exact (abs_le).mpr ⟨by nlinarith,by nlinarith⟩

lemma cuspRemainder_row_scaled_deriv_bound (a b : ℝ) (s : ℂ) (C : ℝ)
    (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (fun q => cuspRemainderProfile a b s (rowHeight u q)) p j) (p j)‖≤
      (‖s‖+C)*(rowHeight u p)^s.re := by
  have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
    (cuspRemainderProfile_contDiffAt a b s) u hu p hp j).1
  rw [hd.deriv]
  have he : (p 2:ℂ)*(deriv (cuspRemainderProfile a b s) (rowHeight u p)*
      (rowHeight u p:ℂ)*(rowLogD u p j:ℂ))=
      (((p 2*rowLogD u p j):ℝ):ℂ)*
        ((rowHeight u p:ℂ)*deriv (cuspRemainderProfile a b s) (rowHeight u p)) := by
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply (mul_le_of_le_one_left (norm_nonneg _) (rowLogD_hyperbolic_bound u hu p hp j)).trans
  exact cuspRemainderProfile_euler_bound a b s C hC _ (rowHeight_pos u hu p hp)

end CubicEisenstein

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups

lemma fullCuspHeight_le_barrier (x : FullCuspClasses) (w : HyperbolicSpace) :
    fullCuspHeight x w≤ max 3 (cuspBarrier 2 3 w) := by
  by_cases hx : fullCuspHeight x w≤3
  · exact hx.trans (le_max_left _ _)
  · have he : cuspBarrier 2 3 w=fullCuspHeight x w := by
      rw [cuspBarrier,fullCuspProfileSum_eq_single _
        (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) w x (by linarith),
        cuspBarrierProfile,cuspTransition_one 2 3 _ (by norm_num) (by linarith),one_mul]
      ring
    exact he ▸ le_max_right _ _

lemma cosetHeight_le_barrier (r : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight r w≤ max 3 (cuspBarrier 2 3 w) := by
  induction r using Quotient.inductionOn with
  | _ M =>
    change cosetHeight (cosetOf M) w≤ max 3 (cuspBarrier 2 3 w)
    rw [cosetHeight_cosetOf]
    exact fullCuspHeight_le_barrier (fullCuspOf M.1) w

lemma kernel_compact_seed_height_bound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    ∃B : ℝ,a≤B ∧ 3≤B ∧ ∀q∈S,kernelQuotientBarrier 2 3 q≤B := by
  obtain ⟨B,hB⟩ := (hS.image (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num)).continuous).bddAbove
  refine ⟨max a (max 3 B),le_max_left _ _,(le_max_left 3 B).trans (le_max_right _ _),?_⟩
  intro q hq
  exact (hB (Set.mem_image_of_mem _ hq)).trans ((le_max_right 3 B).trans (le_max_right _ _))

def kernelSeedHeightBound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) : ℝ :=
  Classical.choose (kernel_compact_seed_height_bound a S hS)

lemma kernelSeedHeightBound_spec (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    a≤kernelSeedHeightBound a S hS ∧ 3≤kernelSeedHeightBound a S hS ∧
      ∀q∈S,kernelQuotientBarrier 2 3 q≤kernelSeedHeightBound a S hS :=
  Classical.choose_spec (kernel_compact_seed_height_bound a S hS)

def compactSeedTransition (a b B : ℝ) : C(Set.Icc a B,ℂ) :=
  ⟨fun v => (cuspTransition a b (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    ((cuspTransition_contDiff a b).continuous.comp continuous_subtype_val)⟩

def compactSeedProfile (a b B : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a B,ℂ) :=
  compactSeedTransition a b B * NormedSpace.exp (s • compactLogProfile a B ha)

lemma compactSeedProfile_entire (a b B : ℝ) (ha : 0<a) :
    Differentiable ℂ (compactSeedProfile a b B ha) :=
  (differentiable_const _).mul (differentiable_exp_smul_const ℂ (compactLogProfile a B ha))

lemma compactSeedProfile_apply (a b B : ℝ) (ha : 0<a) (s : ℂ) (v : Set.Icc a B) :
    compactSeedProfile a b B ha s v=cuspSeedProfile a b s v := by
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (continuous_eval_const v) (s • compactLogProfile a B ha)
  change (NormedSpace.exp (s • compactLogProfile a B ha)) v=
    NormedSpace.exp ((s • compactLogProfile a B ha) v) at he
  change (cuspTransition a b (v:ℝ):ℂ)*(NormedSpace.exp (s • compactLogProfile a B ha)) v=_
  rw [he,←Complex.exp_eq_exp_ℂ]
  simp only [compactLogProfile,ContinuousMap.smul_apply,smul_eq_mul,cuspSeedProfile,
    positiveHeightPower,logRatioPower,Real.log_one,sub_zero,ContinuousMap.coe_mk]

lemma compactHeightProfile_seed (a b B : ℝ) (ha : 0<a) (hab : a<b) (hB : a≤B)
    (s : ℂ) (v : ℝ) (hv : v≤B) :
    compactHeightProfile a B hB (compactSeedProfile a b B ha s) v=cuspSeedProfile a b s v := by
  by_cases hva : a≤v
  · rw [compactHeightProfile,Set.indicator_of_mem (show v∈Set.Icc a B from ⟨hva,hv⟩),
      Set.projIcc_of_mem hB ⟨hva,hv⟩,compactSeedProfile_apply]
  · rw [compactHeightProfile,Set.indicator_of_notMem (by simp [Set.mem_Icc,hva]),
      cuspSeedProfile,cuspTransition_zero a b v hab (le_of_not_ge hva)]
    simp

lemma kernelCompactProfile_seed (a b B : ℝ) (ha : 0<a) (hab : a<b) (hB : a≤B)
    (hthree : 3≤B) (s : ℂ) (q : KernelQuotient) (hq : kernelQuotientBarrier 2 3 q≤B) :
    kernelCompactProfile a B hB (compactSeedProfile a b B ha s) q=kernelQuotientSeed a b s q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 (compactHeightProfile a B hB (compactSeedProfile a b B ha s)) w=
      cuspCutoffCorrection 1 (cuspSeedProfile a b s) w
    unfold cuspCutoffCorrection
    apply tsum_congr
    intro r
    unfold cuspCutoffTerm
    rw [compactHeightProfile_seed a b B ha hab hB s _
      ((cosetHeight_le_barrier r w).trans (max_le hthree hq))]

def kernelLocalSeedL2 (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (s : ℂ) : KernelQuotientL2 :=
  kernelMassRestrictionCLM S hS.measurableSet
    (compactProfileL2 a (kernelSeedHeightBound a S hS) (kernelSeedHeightBound_spec a S hS).1
      (compactSeedProfile a b (kernelSeedHeightBound a S hS) ha s))

lemma kernelLocalSeedL2_entire (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) : Differentiable ℂ (kernelLocalSeedL2 S hS a b ha) := by
  exact (kernelMassRestrictionCLM S hS.measurableSet).differentiable.comp
    ((compactProfileL2 a (kernelSeedHeightBound a S hS) (kernelSeedHeightBound_spec a S hS).1).differentiable.comp
      (compactSeedProfile_entire a b (kernelSeedHeightBound a S hS) ha))

lemma kernelLocalSeedL2_ae_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    (kernelLocalSeedL2 S hS a b ha s : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      S.indicator (kernelQuotientSeed a b s) := by
  let B := kernelSeedHeightBound a S hS
  have hB := kernelSeedHeightBound_spec a S hS
  filter_upwards [kernelMassRestriction_coe S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)),
    compactProfileL2_ae_eq a B hB.1 (compactSeedProfile a b B ha s)] with q hr hp
  change kernelMassRestriction S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)) q=S.indicator (kernelQuotientSeed a b s) q
  rw [hr]
  by_cases hq : q∈S
  · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq,hp]
    exact kernelCompactProfile_seed a b B ha hab hB.1 hB.2.1 s q (hB.2.2 q hq)
  · rw [Set.indicator_of_notMem hq,Set.indicator_of_notMem hq]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelCorrectedSeed (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotient→ℂ :=
  fun q => kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q

def kernelLocalCorrectedSeed (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  kernelLocalSeedL2 S hS a b ha s +
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)

lemma kernelLocalCorrectedSeed_analyticAt_nonreal (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelLocalCorrectedSeed S hS a b ha hab) s := by
  exact ((kernelLocalSeedL2_entire S hS a b ha).analyticAt s).add
    ((ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
      (kernelMassRestrictionCLM S hS.measurableSet) (kernelEisensteinL2Correction a b ha hab s)).comp_of_eq
        (kernelEisensteinL2Correction_analyticAt_nonreal a b ha hab s hs hi) rfl)

lemma kernelLocalCorrectedSeed_ae_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    (kernelLocalCorrectedSeed S hS a b ha hab s : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      S.indicator (kernelCorrectedSeed a b ha hab s) := by
  filter_upwards [Lp.coeFn_add (kernelLocalSeedL2 S hS a b ha s)
      (kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)),
    kernelLocalSeedL2_ae_eq S hS a b ha hab s,
    kernelMassRestriction_coe S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)]
    with q hsum hseed hcor
  change (kernelLocalSeedL2 S hS a b ha s+
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)) q=_
  rw [hsum]
  change kernelLocalSeedL2 S hS a b ha s q+
    kernelMassRestriction S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s) q=_
  rw [hseed,hcor]
  by_cases hq : q∈S
  · simp only [Set.indicator_of_mem hq,kernelCorrectedSeed]
  · simp only [Set.indicator_of_notMem hq,add_zero]

lemma kernelLocalCorrectedSeed_residue_limit (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)•kernelLocalCorrectedSeed S hS a b ha hab s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinResidueVector a b ha hab))) := by
  have hseed : Tendsto (fun s : ℂ => (s-4/3)•kernelLocalSeedL2 S hS a b ha s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 0) := by
    have hh : ContinuousAt (fun s : ℂ => (s-4/3)•kernelLocalSeedL2 S hS a b ha s) (4/3:ℂ) :=
      (continuousAt_id.sub continuousAt_const).smul
        ((kernelLocalSeedL2_entire S hS a b ha).continuous.continuousAt)
    simpa only [sub_self,zero_smul] using hh.tendsto.mono_left
      (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hcor := (kernelMassRestrictionCLM S hS.measurableSet).continuous.continuousAt.tendsto.comp
    (kernelEisensteinResidueVector_limit a b ha hab)
  have hh := hseed.add hcor
  simpa only [kernelLocalCorrectedSeed,smul_add,map_smul,Function.comp_def,zero_add] using hh

end

section
open Filter
open scoped BigOperators Classical Topology ContDiff

section PartialDerivatives
variable {A E G : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma partial_iteratedFDeriv_contDiffAt (F : A→E→G) (a : A) (x : E)
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (a,x)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (a,x) := by
  induction k with
  | zero =>
    exact hF.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E G).symm : G→L[ℝ] E [×0]→L[ℝ]G)
  | succ k ih =>
    have hpair : ContDiffAt ℝ ∞
        (fun p : (A×E)×E => (p.1.1,p.2)) ((a,x),x) :=
      (contDiffAt_fst.fst).prodMk contDiffAt_snd
    have hp := ih.comp ((a,x),x) hpair
    have hd : ContDiffAt ℝ ∞
        (fun p : A×E => fderiv ℝ (fun y => iteratedFDeriv ℝ k (F p.1) y) p.2) (a,x) :=
      hp.fderiv contDiffAt_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G).symm :
        (E→L[ℝ] E [×k]→L[ℝ]G)→L[ℝ] E [×(k+1)]→L[ℝ]G)

lemma compact_family_derivative_bound (F : A→E→G)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P) (k : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀a∈K,∀x,‖iteratedFDeriv ℝ k (F a) x‖≤C := by
  have hc : ContinuousOn (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (K×ˢP) := by
    intro p hp
    exact (partial_iteratedFDeriv_contDiffAt F p.1 p.2 (hF p.1 hp.1 p.2) k).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod hP).bddAbove_image hc.norm
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro a ha x
  by_cases hx : x∈P
  · exact (hC ⟨(a,x),⟨ha,hx⟩,rfl⟩).trans (le_max_left _ _)
  · have hz : iteratedFDeriv ℝ k (F a) x=0 := by
      by_contra hn
      exact hx (hsupp a ha (support_iteratedFDeriv_subset k hn))
    rw [hz,norm_zero]
    exact le_max_right _ _

end PartialDerivatives
section

variable {A E ι : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_smooth_family_tsum (F : A→E→ℂ)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P)
    (a : ι→A) (ha : ∀i,a i∈K) (b : ι→ℂ) (hb : Summable (fun i => ‖b i‖)) :
    ContDiff ℝ ∞ (fun x => ∑'i,b i*F (a i) x) := by
  choose C hC hbound using compact_family_derivative_bound F K P hK hP hF hsupp
  have hf (i : ι) : ContDiff ℝ ∞ (F (a i)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hF (a i) (ha i) x).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hprod (i : ι) : ContDiff ℝ ∞ (fun x => b i*F (a i) x) :=
    contDiff_const.mul (hf i)
  apply contDiff_tsum (v := fun k i => ‖b i‖*C k) hprod
  · intro k hk
    exact hb.mul_right (C k)
  · intro k i x hk
    have he : iteratedFDeriv ℝ k (fun x => b i*F (a i) x) x=
        b i • iteratedFDeriv ℝ k (F (a i)) x :=
      by simpa only [smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a := b i) (i := k) (x := x)
          ((hf i).contDiffAt.of_le (by simp)))
    rw [he,norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound k (a i) (ha i) x) (norm_nonneg _)

end

lemma rowEnergy_real_smul (r : ℝ) (u : Fin 2→ℂ) :
    rowEnergy (r • u)=r^2*rowEnergy u := by
  simp only [rowEnergy,Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

def normalizedComplexRow (u : Fin 2→ℂ) : Fin 2→ℂ := (Real.sqrt (rowEnergy u))⁻¹ • u

lemma normalizedComplexRow_energy (u : Fin 2→ℂ) (hu : u≠0) :
    rowEnergy (normalizedComplexRow u)=1 := by
  rw [normalizedComplexRow,rowEnergy_real_smul,inv_pow,
    Real.sq_sqrt (rowEnergy_nonneg u),inv_mul_cancel₀ (rowEnergy_pos u hu).ne']

lemma rowEnergy_continuous : Continuous rowEnergy := by
  unfold rowEnergy
  fun_prop

lemma rowEnergy_unit_isCompact : IsCompact {u : Fin 2→ℂ | rowEnergy u=1} := by
  apply (isCompact_closedBall (0 : Fin 2→ℂ) 1).of_isClosed_subset
    (isClosed_eq rowEnergy_continuous continuous_const)
  intro u hu
  change rowEnergy u=1 at hu
  rw [Metric.mem_closedBall,dist_zero_right]
  simpa only [hu,Real.sqrt_one] using norm_le_sqrt_rowEnergy u

lemma rowEnergy_unit_ne_zero (u : Fin 2→ℂ) (hu : rowEnergy u=1) : u≠0 := by
  intro h
  simp [h,rowEnergy] at hu

def regularSpatialHeight (deltaLoss : ℝ) (p : SpatialCoordinates) : ℝ :=
  deltaLoss*ConcreteCompactWeight.positiveExtension (p 2/deltaLoss)

lemma regularSpatialHeight_pos (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) :
    0< regularSpatialHeight deltaLoss p :=
  mul_pos hδ (ConcreteCompactWeight.positiveExtension_pos _)

lemma regularSpatialHeight_contDiff (deltaLoss : ℝ) : ContDiff ℝ ∞ (regularSpatialHeight deltaLoss) := by
  unfold regularSpatialHeight
  exact contDiff_const.mul (ConcreteCompactWeight.positiveExtension_smooth.comp
    ((contDiff_apply ℝ ℝ 2).div_const deltaLoss))

lemma regularSpatialHeight_eq (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    regularSpatialHeight deltaLoss p=p 2 := by
  rw [regularSpatialHeight,ConcreteCompactWeight.positiveExtension_eq _ ((le_div_iff₀ hδ).mpr (by simpa using hp))]
  field_simp

def regularRowKernel (s : ℂ) (deltaLoss : ℝ) (u : Fin 2→ℂ) (p : SpatialCoordinates) : ℂ :=
  logRatioPower s (regularSpatialHeight deltaLoss p)
    (heightDenominator (spatialHorizontal p) (regularSpatialHeight deltaLoss p) u)

lemma regularRowDenominator_contDiff (deltaLoss : ℝ) :
    ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates =>
      heightDenominator (spatialHorizontal p.2) (regularSpatialHeight deltaLoss p.2) p.1) := by
  have hc (j : Fin 2) : ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates => p.1 j) :=
    (contDiff_apply ℝ ℂ j).comp contDiff_fst
  have hz := spatialHorizontal_contDiff.comp (contDiff_snd (E := Fin 2→ℂ))
  have hv := (regularSpatialHeight_contDiff deltaLoss).comp (contDiff_snd (E := Fin 2→ℂ))
  have hw := ((hc 0).mul hz).add (hc 1)
  simp only [heightDenominator,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  exact (((Complex.reCLM.contDiff.comp hw).mul (Complex.reCLM.contDiff.comp hw)).add
    ((Complex.imCLM.contDiff.comp hw).mul (Complex.imCLM.contDiff.comp hw))).add
    ((((Complex.reCLM.contDiff.comp (hc 0)).mul (Complex.reCLM.contDiff.comp (hc 0))).add
      ((Complex.imCLM.contDiff.comp (hc 0)).mul (Complex.imCLM.contDiff.comp (hc 0)))).mul (hv.pow 2))

lemma regularRowKernel_contDiffAt (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) :
    ContDiffAt ℝ ∞ (Function.uncurry (regularRowKernel s deltaLoss)) (u,p) := by
  have hv : ContDiff ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => regularSpatialHeight deltaLoss q.2) :=
    (regularSpatialHeight_contDiff deltaLoss).comp contDiff_snd
  have hD := (regularRowDenominator_contDiff deltaLoss).contDiffAt (x := (u,p))
  have hv0 := regularSpatialHeight_pos deltaLoss hδ p
  have hD0 := heightDenominator_pos (spatialHorizontal p) (regularSpatialHeight deltaLoss p) hv0 u hu
  have hl := (hv.contDiffAt.log hv0.ne').sub (hD.log hD0.ne')
  exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (u,p) hl)).cexp

lemma heightDenominator_real_smul (z : ℂ) (v r : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (r•u)=r^2*heightDenominator z v u := by
  unfold heightDenominator
  have he : (r•u) 0*z+(r•u) 1=r•(u 0*z+u 1) := by
    simp only [Pi.smul_apply,smul_add,smul_mul_assoc]
  rw [he]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

lemma heightDenominator_normalized (z : ℂ) (v : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (normalizedComplexRow u)=heightDenominator z v u/rowEnergy u := by
  rw [normalizedComplexRow,heightDenominator_real_smul,inv_pow,Real.sq_sqrt (rowEnergy_nonneg u)]
  ring

lemma normalized_row_summand (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    summand 1 s r*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p=
      smoothSummand s r p := by
  have hu := embeddedRow_ne_zero r
  have hE := rowEnergy_pos _ hu
  have hv : 0<p 2 := hδ.trans_le hp
  have hD := heightDenominator_pos (spatialHorizontal p) (p 2) hv (embeddedRow r) hu
  rw [regularRowKernel,regularSpatialHeight_eq deltaLoss hδ p hp,heightDenominator_normalized]
  rw [summand,rowOperator_one,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hE.ne'),
    ←Complex.ofReal_log hE.le]
  unfold smoothSummand rowSmoothPower spatialHeightPower
  rw [←heightDenominator_eq_quadratic]
  unfold logRatioPower
  rw [Real.log_div hD.ne' hE.ne',mul_assoc,←Complex.exp_add]
  congr 2
  unfold spatialHorizontal
  push_cast
  ring

theorem regular_eisenstein_compact_smooth (s : ℂ) (hs : 2<s.re)
    (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ψ : SpatialCoordinates→ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (fun p => ∑'r : CuspCosets,
      summand 1 s r*(ψ p*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p)) := by
  apply compact_smooth_family_tsum (fun u p => ψ p*regularRowKernel s deltaLoss u p)
    {u : Fin 2→ℂ | rowEnergy u=1} (tsupport ψ) rowEnergy_unit_isCompact hcψ
  · intro u hu p
    have hψp : ContDiffAt ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => ψ q.2) (u,p) :=
      hψ.contDiffAt.comp (u,p) contDiffAt_snd
    exact hψp.mul (regularRowKernel_contDiffAt s deltaLoss hδ u (rowEnergy_unit_ne_zero u hu) p)
  · intro u hu
    exact tsupport_mul_subset_left
  · intro r
    exact normalizedComplexRow_energy _ (embeddedRow_ne_zero r)
  · exact summable_norm_summand 1 s hs

theorem smoothEisenstein_contDiffAt (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (smoothEisenstein s) p := by
  let deltaLoss : ℝ:=p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let χ : ContDiffBump p := ⟨1,2,by norm_num,by norm_num⟩
  let ψ : SpatialCoordinates→ℂ:=fun q => (χ q:ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hcψ : HasCompactSupport ψ := by
    have he : Function.support ψ=Function.support (fun q => χ q) := by
      ext q
      simp [Function.mem_support,ψ]
    change IsCompact (closure (Function.support ψ))
    rw [he]
    exact χ.hasCompactSupport
  have hsum := regular_eisenstein_compact_smooth s hs deltaLoss hδ ψ hψ hcψ
  apply hsum.contDiffAt.congr_of_eventuallyEq
  have hn : ∀ᶠq in 𝓝 p, deltaLoss<q 2 :=
    (isOpen_lt continuous_const (continuous_apply 2)).mem_nhds (by dsimp [deltaLoss]; linarith)
  filter_upwards [χ.eventuallyEq_one,hn] with q hχ hq
  unfold smoothEisenstein
  apply tsum_congr
  intro r
  have hψq : ψ q=1 := by simp [ψ,hχ]
  rw [hψq,one_mul]
  exact (normalized_row_summand s deltaLoss hδ r q hq.le).symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernel_contMDiff_of_spatial (f : KernelQuotient→ℂ) (F : SpatialCoordinates→ℂ)
    (hF : ∀p,0<p 2→ ContDiffAt ℝ ∞ F p)
    (hcoord : ∀q : KernelQuotient,∀p∈hyperbolicSpatialChart.target,
      f ((kernelQuotientChart q).symm p)=F p) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f := by
  intro q
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hc : ContinuousAt (kernelQuotientChart q) q :=
    (kernelQuotientChart q).continuousOn.continuousAt ((kernelQuotientChart q).open_source.mem_nhds hq)
  have heq : f=ᶠ[𝓝 q] (fun t => F (kernelQuotientChart q t)) := by
    filter_upwards [(kernelQuotientChart q).open_source.mem_nhds hq] with t ht
    rw [←hcoord q _ ((kernelQuotientChart q).map_source ht).1,
      (kernelQuotientChart q).left_inv ht]
  rw [contMDiffAt_iff]
  refine ⟨((hF _ (hyperbolicSpatialChart_target_positive hp)).continuousAt.comp hc).congr heq.symm,?_⟩
  have he : (fun p => f ((kernelQuotientChart q).symm p))=ᶠ[𝓝 (kernelQuotientChart q q)] F := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hp
    exact hcoord q p hp
  have hh := (hF _ (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq he
  have hh' := hh.contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'

lemma kernelQuotientEisenstein_coordinate (s : ℂ) (hs : 2<s.re) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientEisenstein s hs ((kernelQuotientChart q).symm p)=smoothEisenstein s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp,
    kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint,
    smoothEisenstein_eq_actual s p (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientEisenstein_contMDiff (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientEisenstein s hs) :=
  kernel_contMDiff_of_spatial _ _ (smoothEisenstein_contDiffAt s hs)
    (kernelQuotientEisenstein_coordinate s hs)

lemma kernelQuotientSeed_coordinate (a b : ℝ) (s : ℂ) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientSeed a b s ((kernelQuotientChart q).symm p)=smoothCuspSeedField a b s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp]
  change smoothCuspSeed a b s _=smoothCuspSeedField a b s p
  rw [smoothCuspSeedField,dif_pos (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientSeed_contMDiff (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientSeed a b s) :=
  kernel_contMDiff_of_spatial _ _ (actual_smoothCuspSeed_contDiffAt a b s ha hab)
    (kernelQuotientSeed_coordinate a b s)

end CubicEisenstein

open scoped BigOperators Classical ContDiff

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

lemma levelThree_integral_eq_translation (M : CubicKubota.levelThree)
    (hc : (M : SL(2,ActualEisensteinCubic.O)) 1 0=0) :
    integralComplexMatrix M.1=complexTranslation (ConcreteTraceCRT.eisEmbedding ((M : SL(2,ActualEisensteinCubic.O)) 0 1)) := by
  have hr := row_eq_one_of_lower_left_zero M hc
  have hd : (M : SL(2,ActualEisensteinCubic.O)) 1 1=1 := by
    simpa [row,Matrix.one_apply] using congrFun hr 1
  have ha : (M : SL(2,ActualEisensteinCubic.O)) 0 0=1 := by
    have hh : (M : SL(2,ActualEisensteinCubic.O)) 0 0 * (M : SL(2,ActualEisensteinCubic.O)) 1 1-
      (M : SL(2,ActualEisensteinCubic.O)) 0 1 * (M : SL(2,ActualEisensteinCubic.O)) 1 0=1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,ActualEisensteinCubic.O)).property
    simpa only [hc,hd,mul_zero,mul_one,sub_zero] using hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,ha,hc,hd]

lemma periodDomain_unique_translate (z w t : ℂ) (hz : z∈periodDomain) (hw : w∈periodDomain)
    (ht : t∈periodLattice) (he : z=w+t) : z=w := by
  have hf := ZSpan.fract_add_ZSpan periodBasis w ht
  rw [←he,(ZSpan.fract_eq_self (b := periodBasis)).mpr hz,
    (ZSpan.fract_eq_self (b := periodBasis)).mpr hw] at hf
  exact hf

def cuspPeriodRegion : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ 1<hyperbolicHeight w}

lemma kernelProjection_cuspPeriodRegion_injective :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) cuspPeriodRegion := by
  intro u hu v hv he
  obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff globalKubotaKernel u v).mp he
  have hMu : integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • v=u := hM
  have hc : (M:SL(2,ActualEisensteinCubic.O)) 1 0=0 := by
    by_contra hn
    have hb := integral_hyperbolicHeight_mul_le_one (M:SL(2,ActualEisensteinCubic.O)) hn v
    rw [hMu] at hb
    have huh : 1<hyperbolicHeight u := hu.2
    have hvh : 1<hyperbolicHeight v := hv.2
    nlinarith [mul_pos (sub_pos.mpr huh) (sub_pos.mpr hvh)]
  let N : CubicKubota.levelThree := ⟨M,globalKubotaKernel_le_levelThree M.2⟩
  have ht := levelThree_integral_eq_translation N hc
  obtain ⟨z,t,htpos,hvrep⟩ := upperPoint_surjective v
  have hua : u=upperPoint (z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)) t htpos := by
    rw [←hMu,←hvrep,ht,complexTranslation_action]
  have hvl : hyperbolicHorizontal v=z := by rw [←hvrep,hyperbolicHorizontal_upperPoint]
  have hul : hyperbolicHorizontal u=z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1) := by
    rw [hua,hyperbolicHorizontal_upperPoint]
  obtain ⟨k,hk⟩ := CubicKubota.levelThree_upper N
  have hper : ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)∈periodLattice := by
    change ConcreteTraceCRT.eisEmbedding ((N:CubicKubota.levelThree).1 0 1)∈periodLattice
    rw [hk,map_mul,map_ofNat]
    exact three_embedding_mem k
  have hehor : hyperbolicHorizontal u=hyperbolicHorizontal v :=
    periodDomain_unique_translate _ _ _ hu.1 hv.1 hper (by rw [hul,hvl])
  have hez : z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)=z := by
    simpa only [hul,hvl] using hehor
  rw [hua,hez,←hvrep]

def cuspPeriodStrip (a b : ℝ) : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ hyperbolicHeight w∈Set.Icc a b}

lemma cuspPeriodStrip_measurable (a b : ℝ) : MeasurableSet (cuspPeriodStrip a b) :=
  (periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable).inter
    (measurableSet_Icc.preimage hyperbolicHeight_continuous.measurable)

lemma kernelProjection_cuspPeriodStrip_injective (a b : ℝ) (ha : 1<a) :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) (cuspPeriodStrip a b) := by
  apply kernelProjection_cuspPeriodRegion_injective.mono
  intro w hw
  exact ⟨hw.1,ha.trans_le hw.2.1⟩

lemma kernelProjection_cuspPeriodStrip_measurePreserving (a b : ℝ) (ha : 1<a) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      ((integralQuotientVolume globalKubotaKernel).restrict
        (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip a b)) :=
  kernelProjection_measurePreserving_on _ (cuspPeriodStrip_measurable a b)
    (kernelProjection_cuspPeriodStrip_injective a b ha)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups

def kernelCuspStripSet : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6

lemma kernelCuspStripSet_measurable : MeasurableSet kernelCuspStripSet :=
  (cuspPeriodStrip_measurable 5 6).image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn
    (kernelProjection_cuspPeriodStrip_injective 5 6 (by norm_num))

def kernelCuspStripAverage : KernelQuotientL2→L[ℂ]ℂ :=
  innerSL ℂ (indicatorConstLp 2 kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) (1:ℂ))

lemma kernelCuspStripAverage_apply (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫q in kernelCuspStripSet,F q∂integralQuotientVolume globalKubotaKernel :=
  L2.inner_indicatorConstLp_one kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) F

lemma kernelCuspStripAverage_hyperbolic (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspStripAverage_apply]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hh := (Lp.aestronglyMeasurable F).mono_measure (Measure.restrict_le_self (s := kernelCuspStripSet))
  change AEStronglyMeasurable F ((integralQuotientVolume globalKubotaKernel).restrict
    (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6)) at hh
  change (∫q in integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6,
    F q∂integralQuotientVolume globalKubotaKernel)=_
  rw [←hm.map_eq] at hh ⊢
  exact integral_map hm.measurable.aemeasurable hh

def kernelCuspAverageCompact : Set KernelQuotient :=
  {q | kernelQuotientBarrier 2 3 q≤6}

lemma kernelCuspAverageCompact_isCompact : IsCompact kernelCuspAverageCompact :=
  kernelBarrier_sublevel_isCompact 6

lemma kernelCuspStripSet_subset_compact : kernelCuspStripSet⊆kernelCuspAverageCompact := by
  rintro q ⟨w,hw,rfl⟩
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  have hfive : 5≤v := by simpa only [hyperbolicHeight_upperPoint] using hw.2.1
  have hsix : v≤6 := by simpa only [hyperbolicHeight_upperPoint] using hw.2.2
  change cuspBarrier 2 3 (upperPoint z v hv)≤6
  have hh := cuspBarrier_high 2 3 (by norm_num) (by norm_num) 1 z v hv (by linarith)
  simpa only [map_one,one_smul] using hh.le.trans hsix

lemma kernelCuspStripAverage_restrict (F : KernelQuotientL2) :
    kernelCuspStripAverage (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspStripAverage F := by
  rw [kernelCuspStripAverage_apply,kernelCuspStripAverage_apply]
  apply setIntegral_congr_ae kernelCuspStripSet_measurable
  filter_upwards [kernelMassRestriction_coe kernelCuspAverageCompact
    kernelCuspAverageCompact_isCompact.measurableSet F] with q hq
  intro hmem
  exact hq.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact hmem) F)

def kernelCuspAverageFamily (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspStripAverage
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

lemma kernelCuspAverageFamily_residue_limit (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspAverageFamily a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := kernelCuspStripAverage.continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspStripAverage_restrict,kernelCuspAverageFamily] using hh

lemma kernelCuspAverageFamily_actual_integral (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelCuspAverageFamily a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspAverageFamily,kernelCuspStripAverage_hyperbolic]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hlocal := kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s
  have hrestr := ae_restrict_of_ae hlocal (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  apply integral_congr_ae
  filter_upwards [hp,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _)

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

def spatialComplexSplit : EuclideanSpatial ≃ᵐ ℝ × ℂ :=
  spatialHeightSplit.trans ((MeasurableEquiv.refl ℝ).prodCongr Complex.measurableEquivPi.symm)

lemma spatialComplexSplit_fst (p : EuclideanSpatial) : (spatialComplexSplit p).1=p 2 := rfl

lemma spatialComplexSplit_preserves_volume : MeasurePreserving spatialComplexSplit volume volume :=
  ((MeasurePreserving.id volume).prod Complex.volume_preserving_equiv_pi.symm).comp
    spatialHeightSplit_preserves_volume

lemma spatialComplexSplit_coordinates (w : HyperbolicSpace) :
    spatialComplexSplit (hyperbolicEuclideanCoordinates w)=
      (hyperbolicHeight w,hyperbolicHorizontal w) := by
  apply Prod.ext
  · rfl
  · change (hyperbolicHorizontal w).re+(hyperbolicHorizontal w).im*Complex.I=hyperbolicHorizontal w
    exact Complex.re_add_im _

def cuspCoordinateLift (q : ℝ × ℂ) : HyperbolicSpace :=
  euclideanToHyperbolic (spatialComplexSplit.symm q)

lemma cuspCoordinateLift_positive (v : ℝ) (z : ℂ) (hv : 0<v) :
    cuspCoordinateLift (v,z)=upperPoint z v hv := by
  have he : spatialComplexSplit (hyperbolicEuclideanCoordinates (upperPoint z v hv))=(v,z) := by
    simp only [spatialComplexSplit_coordinates,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  have he' := congrArg spatialComplexSplit.symm he
  rw [spatialComplexSplit.symm_apply_apply] at he'
  rw [cuspCoordinateLift,←he',euclideanToHyperbolic_coordinates]

def cuspEuclideanStrip : Set EuclideanSpatial :=
  spatialComplexSplit ⁻¹' (Set.Icc (5:ℝ) 6 ×ˢ periodDomain)

lemma cuspEuclideanStrip_measurable : MeasurableSet cuspEuclideanStrip :=
  spatialComplexSplit.measurable (measurableSet_Icc.prod periodDomain_measurable)

lemma cuspEuclideanStrip_positive : cuspEuclideanStrip⊆euclideanUpperHalf := by
  intro p hp
  have hh : 5≤p 2 := hp.1.1
  change 0<p 2
  linarith

lemma cuspEuclideanStrip_preimage :
    hyperbolicEuclideanCoordinates ⁻¹' cuspEuclideanStrip=cuspPeriodStrip 5 6 := by
  ext w
  change spatialComplexSplit (hyperbolicEuclideanCoordinates w)∈(Set.Icc (5:ℝ) 6 ×ˢ periodDomain) ↔ _
  rw [spatialComplexSplit_coordinates]
  exact and_comm

lemma cuspPeriodStrip_integral_coordinates (g : HyperbolicSpace→ℂ)
    (hg : AEStronglyMeasurable g hyperbolicVolume)
    (hint : IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume) :
    (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3 := by
  have hm := euclideanToHyperbolic_measurePreserving_on cuspEuclideanStrip
    cuspEuclideanStrip_measurable cuspEuclideanStrip_positive
  rw [cuspEuclideanStrip_preimage] at hm
  have hh := hg.mono_measure (Measure.restrict_le_self (s := cuspPeriodStrip 5 6))
  have he : (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
    rw [←hm.map_eq] at hh ⊢
    exact integral_map hm.measurable.aemeasurable hh
  rw [he,hyperbolicEuclidean_setIntegral_complex cuspEuclideanStrip
    cuspEuclideanStrip_measurable cuspEuclideanStrip_positive]
  have hsplit := spatialComplexSplit.measurableEmbedding.setIntegral_map
    (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
    (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) («μ» := (volume : Measure EuclideanSpatial))
  rw [spatialComplexSplit_preserves_volume.map_eq] at hsplit
  have heq : (∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)/(p 2:ℂ)^3)=
      ∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,g (cuspCoordinateLift q)/(q.1:ℂ)^3 := by
    rw [hsplit]
    simp only [cuspEuclideanStrip,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply,
      spatialComplexSplit_fst]
  rw [heq]
  change (∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,
    g (cuspCoordinateLift q)/(q.1:ℂ)^3 ∂((volume : Measure ℝ).prod volume))=_
  rw [setIntegral_prod _ hint]
  congr 1
  ext v
  exact integral_div ((v:ℂ)^3) (fun z => g (cuspCoordinateLift (v,z)))

lemma hyperbolicEisenstein_continuous (s : ℂ) (hs : 2<s.re) :
    Continuous (hyperbolicEisenstein s) := by
  have hcoord : Continuous (fun p : UpperCoordinates =>
      upperEisenstein p.1.1 p.1.2 p.2 s) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hin : ContinuousAt (fun q : UpperCoordinates => (q,s)) p :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp (f := fun q : UpperCoordinates => (q,s))
      (upperEisenstein_joint_continuousAt (p,s) hs) hin
  convert (preTransparency := .instances) hcoord.comp hyperbolicCoordinates_continuous using 1
  ext w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  simp only [Function.comp_def,hyperbolicEisenstein_upperPoint,hyperbolicCoordinates,
    hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]

lemma spatialComplexSplit_symm_eq (q : ℝ × ℂ) :
    spatialComplexSplit.symm q=WithLp.toLp 2 ![q.2.re,q.2.im,q.1] := by
  apply spatialComplexSplit.injective
  rw [spatialComplexSplit.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (Complex.re_add_im q.2).symm

lemma spatialComplexSplit_symm_continuous : Continuous spatialComplexSplit.symm := by
  change Continuous (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  fun_prop

lemma cuspCoordinateLift_continuousAt (q : ℝ × ℂ) (hq : 0<q.1) :
    ContinuousAt cuspCoordinateLift q := by
  have hp : 0<(spatialComplexSplit.symm q) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hq
  exact (euclideanToHyperbolic_contMDiffAt _ hp).continuousAt.comp
    spatialComplexSplit_symm_continuous.continuousAt

lemma cuspCoordinateLift_weighted_integrable (g : HyperbolicSpace→ℂ) (hg : Continuous g) :
    IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume := by
  let radiusBound : ℝ := ∑i,‖periodBasis i‖
  have hc : ContinuousOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ Metric.closedBall (0:ℂ) radiusBound) := by
    intro q hq
    have hpos : 0<q.1 := lt_of_lt_of_le (by norm_num) hq.1.1
    exact ((hg.continuousAt.comp (cuspCoordinateLift_continuousAt q hpos)).div
      ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.pow 3)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hpos.ne'))).continuousWithinAt
  apply (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
  intro q hq
  refine ⟨hq.1,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain q.2 hq.2

lemma hyperbolicEisenstein_cusp_average (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  rw [cuspPeriodStrip_integral_coordinates _
    (hyperbolicEisenstein_continuous s hs).aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable _ (hyperbolicEisenstein_continuous s hs))]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  have hh : (∫z in periodDomain,hyperbolicEisenstein s (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s 0*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint]
    rw [eisensteinFourierCoefficient]
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
      AddChar.map_zero_eq_one,mul_one]
    exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (by positivity))).symm
  dsimp only
  rw [hh,eisensteinConstantCoefficient_formula v hpos s hs]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def cuspMainHeightFactor (s : ℂ) : ℂ :=
  ((6:ℂ)^(s-2)-(5:ℂ)^(s-2))/(s-2)

def cuspScatterHeightFactor (s : ℂ) : ℂ :=
  ((5:ℂ)^(-s)-(6:ℂ)^(-s))/s

lemma cuspHeightPower_integrable (s : ℂ) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^s) (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s (Or.inr (by linarith [hv.1]))).continuousWithinAt

lemma cuspMainHeightFactor_integral (s : ℂ) (hs : s≠2) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(s-3))=cuspMainHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : s-3≠(-1:ℂ) := by intro h; apply hs; linear_combination h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(s-3+1)-(5:ℂ)^(s-3+1))/(s-3+1)=_
  have he : s-3+1=s-2 := by ring
  rw [he]
  rfl

lemma cuspScatterHeightFactor_integral (s : ℂ) (hs : s≠0) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1))=cuspScatterHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : -s-1≠(-1:ℂ) := by intro h; apply hs; linear_combination -h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(-s-1+1)-(5:ℂ)^(-s-1+1))/(-s-1+1)=_
  have he : -s-1+1=-s := by ring
  rw [he,cuspScatterHeightFactor]
  ring

lemma cuspMainHeightFactor_differentiableAt (s : ℂ) (hs : s≠2) :
    DifferentiableAt ℂ cuspMainHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => z-2) s := differentiableAt_id.sub_const 2
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div hd (sub_ne_zero.mpr hs)

lemma cuspScatterHeightFactor_differentiableAt (s : ℂ) (hs : s≠0) :
    DifferentiableAt ℂ cuspScatterHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div differentiableAt_id hs

def cuspConstantAverage (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(cuspMainHeightFactor s+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*cuspScatterHeightFactor s)

lemma hyperbolicEisenstein_cusp_average_eq (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      cuspConstantAverage s := by
  have hs2 : s≠2 := by intro he; subst s; norm_num at hs
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  rw [hyperbolicEisenstein_cusp_average s hs]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
        ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((v:ℂ)^(s-3)+(((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*(v:ℂ)^(-s-1)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [hv.1])
    have h1 : (v:ℂ)^(s-3)=(v:ℂ)^s/(v:ℂ)^3 := by
      rw [Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    have h2 : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [h1,h2]
    ring
  rw [heq,integral_const_mul,integral_add (cuspHeightPower_integrable _)
    ((cuspHeightPower_integrable _).const_mul _),integral_const_mul,
    cuspMainHeightFactor_integral s hs2,cuspScatterHeightFactor_integral s hs0]
  rfl

lemma cuspConstantAverage_differentiableAt (s : ℂ) (hs : 4/3<s.re) (hs2 : s≠2) :
    DifferentiableAt ℂ cuspConstantAverage s := by
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  have hs1 : s≠1 := by intro he; subst s; norm_num at hs
  have hsc : DifferentiableAt ℂ (fun z : ℂ => scatteringCoefficient z 0) s :=
    (arithmeticDirichletSeries_zero_differentiableAt s hs).div_const _
  exact ((cuspMainHeightFactor_differentiableAt s hs2).add
    ((((differentiableAt_const (Real.pi:ℂ)).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1)).mul hsc).mul
      (cuspScatterHeightFactor_differentiableAt s hs0))).const_mul _

lemma cuspScatterHeightFactor_center_re_pos :
    0<(cuspScatterHeightFactor (4/3:ℂ)).re := by
  have h5 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤5) (-(4/3:ℝ))
  have h6 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤6) (-(4/3:ℝ))
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] at h5 h6
  have he : cuspScatterHeightFactor (4/3:ℂ)=
      (((5:ℝ)^(-(4/3:ℝ))-(6:ℝ)^(-(4/3:ℝ)))/(4/3:ℝ):ℝ) := by
    rw [cuspScatterHeightFactor,←h5,←h6]
    push_cast
    rfl
  rw [he,Complex.ofReal_re]
  apply div_pos
  · exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by norm_num))
  · norm_num

def cuspConstantAverageResidue : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
    cuspScatterHeightFactor (4/3:ℂ)

lemma cuspConstantAverageResidue_ne_zero : cuspConstantAverageResidue≠0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero cusp_volume_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      constantArithmeticResidue_ne_zero
  · intro he
    have hh := cuspScatterHeightFactor_center_re_pos
    rw [he,Complex.zero_re] at hh
    exact lt_irrefl 0 hh

lemma cuspConstantAverage_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*cuspConstantAverage (x:ℂ))
      (𝓝[>] (4/3:ℝ)) (𝓝 cuspConstantAverageResidue) := by
  have harg : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝 (4/3:ℂ)) := by
    convert (preTransparency := .instances) Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hlinear := harg.sub_const (4/3:ℂ)
  norm_num only [sub_self] at hlinear
  have hm := (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hh := (cuspScatterHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hpi : Tendsto (fun x : ℝ => (Real.pi:ℂ)/((x:ℂ)-1))
      (𝓝[>] (4/3:ℝ)) (𝓝 (3*(Real.pi:ℂ))) := by
    convert (preTransparency := .instances) tendsto_const_nhds.div (harg.sub_const 1) (by norm_num : (4/3:ℂ)-1≠0) using 1 ; ring_nf
  have hall := ((hlinear.mul hm).add
    ((hpi.mul scatteringCoefficient_zero_oneSidedResidue).mul hh)).const_mul
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  convert (preTransparency := .instances) hall using 1
  · ext x
    dsimp only [cuspConstantAverage,Function.comp_def]
    ring
  · simp only [zero_mul,zero_add,cuspConstantAverageResidue]
    ring_nf

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma kernelSpectralResolvent_analyticAt_of_isUnit (z : ℂ)
    (hz : IsUnit (kernelSpectralFormOperator z)) :
    AnalyticAt ℂ kernelSpectralResolvent z := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (Ring.inverse (kernelSpectralFormOperator z))).comp_of_eq
    (kernelSpectralFormInverse_analyticAt_of_isUnit z hz) rfl

lemma kernelEisensteinResolvent_analyticAt_of_isUnit (s : ℂ)
    (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ kernelEisensteinResolvent s := by
  exact (kernelSpectralResolvent_analyticAt_of_isUnit _ hs).comp_of_eq
    (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl

lemma kernelCuspAverageFamily_analyticAt_of_isUnit (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s := by
  have hcor : AnalyticAt ℂ (kernelEisensteinL2Correction a b ha hab) s :=
    ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
      (kernelL2Defect a b ha hab s,kernelEisensteinResolvent s)).comp₂
      ((kernelL2Defect_entire a b ha hab).analyticAt s)
      (kernelEisensteinResolvent_analyticAt_of_isUnit s hs)
  have hlocal : AnalyticAt ℂ
      (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab) s :=
    ((kernelLocalSeedL2_entire kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha).analyticAt s).add
      ((ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
        (kernelMassRestrictionCLM kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet)
        (kernelEisensteinL2Correction a b ha hab s)).comp_of_eq hcor rfl)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    kernelCuspStripAverage _).comp_of_eq hlocal rfl

lemma kernelCuspAverageFamily_analyticAt_nonreal (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s :=
  kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab s
    (kernelSpectralFormOperator_isUnit_nonreal _ (kernelEisensteinSpectralParameter_nonreal s hs hi))

def cuspUpperParameterRegion : Set ℂ := {s | (4/3:ℝ)<s.re ∧ 0<s.im}

lemma cuspUpperParameterRegion_isOpen : IsOpen cuspUpperParameterRegion :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma cuspUpperParameterRegion_convex : Convex ℝ cuspUpperParameterRegion :=
  ((convex_Ioi (4/3:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)

lemma cuspConstantAverage_analyticOn_upper : AnalyticOnNhd ℂ cuspConstantAverage cuspUpperParameterRegion := by
  apply (Complex.analyticOnNhd_iff_differentiableOn cuspUpperParameterRegion_isOpen).mpr
  intro s hs
  apply (cuspConstantAverage_differentiableAt s hs.1 ?_).differentiableWithinAt
  intro he
  subst s
  norm_num [cuspUpperParameterRegion] at hs

lemma kernelCuspAverageFamily_eq_upper_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion := by
  have hleft : AnalyticOnNhd ℂ (kernelCuspAverageFamily a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelCuspAverageFamily_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hstart : (5+Complex.I:ℂ)∈cuspUpperParameterRegion := by
    norm_num [cuspUpperParameterRegion]
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : kernelCuspAverageFamily a b ha hab =ᶠ[𝓝 (5+Complex.I:ℂ)] cuspConstantAverage := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact (hoverlap s hs.1 hs.2).trans (hyperbolicEisenstein_cusp_average_eq s (by linarith [hs.1]))
  exact hleft.eqOn_of_preconnected_of_eventuallyEq cuspConstantAverage_analyticOn_upper
    cuspUpperParameterRegion_convex.isPreconnected hstart hevent

lemma kernelCuspAverageFamily_eq_real_of_upper (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hupper : Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion)
    (x : ℝ) (hx : (4/3:ℝ)<x) (hx2 : x≠2)
    (hunit : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter (x:ℂ)))) :
    kernelCuspAverageFamily a b ha hab (x:ℂ)=cuspConstantAverage (x:ℂ) := by
  have hpath : Tendsto (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have hcont : Continuous (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) :=
      (Complex.continuous_ofReal.mul_const Complex.I).const_add (x:ℂ)
    have hh := (hcont.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hh
  have hleft := (kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab (x:ℂ) hunit).continuousAt.tendsto.comp hpath
  have hx2' : (x:ℂ)≠2 := by exact_mod_cast hx2
  have hright := (cuspConstantAverage_differentiableAt (x:ℂ) hx hx2').continuousAt.tendsto.comp hpath
  have hevent : (fun t : ℝ => kernelCuspAverageFamily a b ha hab ((x:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => cuspConstantAverage ((x:ℂ)+(t:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    apply hupper
    simpa only [cuspUpperParameterRegion,Set.mem_ofPred_eq,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,
      Complex.mul_im,mul_zero,zero_mul,sub_zero,add_zero,zero_add,mul_one] using And.intro hx ht
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright hevent

lemma realAbove_tendsto_complex_punctured :
    Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · convert (preTransparency := .instances) Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (4/3:ℝ)<x at hx
    change (x:ℂ)≠(4/3:ℂ)
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith [hx]

lemma kernelEisensteinResidueVector_average_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab)=cuspConstantAverageResidue := by
  have hupper := kernelCuspAverageFamily_eq_upper_of_overlap a b ha hab hoverlap
  have hleft := (kernelCuspAverageFamily_residue_limit a b ha hab).comp realAbove_tendsto_complex_punctured
  have hunit := realAbove_tendsto_complex_punctured.eventually kernelEisensteinPencil_eventually_isUnit
  have hlt : ∀ᶠx : ℝ in 𝓝[>] (4/3:ℝ),x<2 := by
    have hh : ∀ᶠx : ℝ in 𝓝 (4/3:ℝ),x<2 := Iio_mem_nhds (by norm_num)
    exact hh.filter_mono nhdsWithin_le_nhds
  have hevent : (fun x : ℝ => ((x:ℂ)-4/3)*kernelCuspAverageFamily a b ha hab (x:ℂ))
      =ᶠ[𝓝[>] (4/3:ℝ)] (fun x : ℝ => ((x:ℂ)-4/3)*cuspConstantAverage (x:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,hunit,hlt] with x hx hux hxx
    rw [kernelCuspAverageFamily_eq_real_of_upper a b ha hab hupper x hx hxx.ne hux]
  exact tendsto_nhds_unique_of_eventuallyEq hleft cuspConstantAverage_oneSidedResidue hevent

lemma kernelEisensteinResidueVector_ne_zero_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelEisensteinResidueVector a b ha hab≠0 := by
  intro he
  have hh := kernelEisensteinResidueVector_average_of_overlap a b ha hab hoverlap
  rw [he,map_zero] at hh
  exact cuspConstantAverageResidue_ne_zero hh.symm

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma cuspBarrierField_local_model (p : SpatialCoordinates) (hp : 0<p 2) :
    (cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun _ => 1)) ∨
    ∃x : FullCuspClasses,1< rowHeight (fullCuspRow x) p ∧
      cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun q => 1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)) := by
  by_cases hx : ∃x : FullCuspClasses,1< rowHeight (fullCuspRow x) p
  · obtain ⟨x,hx⟩ := hx
    refine Or.inr ⟨x,hx,?_⟩
    have hc := (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt
    filter_upwards [hc.eventually_const_lt hx,(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq hpos
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=_
    rw [fullCuspProfileField_eq _ q hpos,fullCuspProfileSum_eq_single _
      (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) _ x
        (by rwa [←fullCuspRow_height x q hpos]),←fullCuspRow_height x q hpos]
  · left
    obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
    have hsmall : ∀ᶠq in 𝓝 p,∀x∈T,rowHeight (fullCuspRow x) q<2 := by
      rw [eventually_all_finset]
      intro x hxT
      apply (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt.eventually_lt_const
      have hn : rowHeight (fullCuspRow x) p≤1 := not_lt.mp (fun h => hx ⟨x,h⟩)
      linarith
    filter_upwards [hT,hsmall] with q hq hqT
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=1
    have hz : ∀x : FullCuspClasses,cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)=0 := by
      intro x
      apply cuspBarrierProfile_zero 2 3 (by norm_num)
      by_cases hmem : x∈T
      · exact (hqT x hmem).le
      · exact (hq x hmem).le.trans (by norm_num)
    simp only [fullCuspProfileField,hz,tsum_zero,add_zero]

lemma cuspBarrierProfile_log_derivative_bound :
    ∃D : ℝ,0≤D ∧ ∀v : ℝ,1<v→
      |v*deriv (cuspBarrierProfile 2 3) v|≤D*(1+cuspBarrierProfile 2 3 v) := by
  have hd := (contDiff_infty_iff_deriv.mp (cuspBarrierProfile_smooth 2 3)).2.continuous
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 3)).image hd.abs).bddAbove
  let D := max 1 (3*max C 0)
  have hD : 0≤D := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨D,hD,fun v hv => ?_⟩
  by_cases hhigh : 3<v
  · have he : cuspBarrierProfile 2 3 =ᶠ[𝓝 v] (fun x => x-1) := by
      filter_upwards [Ioi_mem_nhds hhigh] with x hx
      rw [cuspBarrierProfile,cuspTransition_one 2 3 x (by norm_num) hx.le,one_mul]
    have hder : deriv (cuspBarrierProfile 2 3) v=1 := by rw [he.deriv_eq]; simp
    rw [hder,mul_one,abs_of_pos (by linarith),he.self_of_nhds]
    have h := mul_le_mul_of_nonneg_right (le_max_left 1 (3*max C 0)) (show 0≤v by linarith)
    dsimp only [D]
    nlinarith
  · have hCv : |deriv (cuspBarrierProfile 2 3) v|≤ max C 0 :=
      (hC (Set.mem_image_of_mem _ (show v∈Set.Icc (1:ℝ) 3 from ⟨hv.le,not_lt.mp hhigh⟩))).trans (le_max_left _ _)
    have h1 : |v*deriv (cuspBarrierProfile 2 3) v|≤3*max C 0 := by
      rw [abs_mul,abs_of_pos (by linarith)]
      exact mul_le_mul (not_lt.mp hhigh) hCv (abs_nonneg _) (by positivity)
    have hphi := cuspBarrierProfile_nonneg 2 3 (by norm_num) (by norm_num) v
    exact (h1.trans (le_max_right _ _)).trans (by nlinarith)

lemma cuspBarrierField_scaled_deriv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j) (p j)‖≤
        D*cuspBarrierField 2 3 p := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierProfile_log_derivative_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [Function.update_eq_self] using ((continuous_axis_update p j).continuousAt (x := p j)).tendsto
  rcases cuspBarrierField_local_model p hp with hz | ⟨x,hx,he⟩
  · have hzCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p] (fun _ => (1:ℂ)) :=
      hz.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have hzC := hzCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)] (fun _ => (1:ℂ)) at hzC
    rw [hzC.deriv_eq,deriv_const,mul_zero,norm_zero,hz.self_of_nhds,mul_one]
    exact hD
  · have heCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p]
        (fun q => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℝ):ℂ)) :=
      he.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have heC := heCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)]
      (fun t => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) (Function.update p j t)):ℝ):ℂ)) at heC
    rw [heC.deriv_eq]
    simp only [Complex.ofReal_add,Complex.ofReal_one]
    rw [deriv_const_add]
    have hpF := (rowProfile_axis_derivatives (fun v => (cuspBarrierProfile 2 3 v:ℂ))
      (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspBarrierProfile_smooth 2 3).contDiffAt)
      (fullCuspRow x) (fullCuspRow_ne_zero x) p hp j).1
    change ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℂ)) p j) (p j)‖≤_
    rw [hpF.deriv,cast_profile_deriv _ ((cuspBarrierProfile_smooth 2 3).differentiable (by simp))]
    have hid : (p 2:ℂ)*(((deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ)*
        (rowHeight (fullCuspRow x) p:ℂ)*(rowLogD (fullCuspRow x) p j:ℂ))=
        ((p 2*rowLogD (fullCuspRow x) p j:ℝ):ℂ)*
        ((rowHeight (fullCuspRow x) p*deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ) := by
      push_cast
      ring
    rw [hid,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    apply (mul_le_of_le_one_left (abs_nonneg _) (rowLogD_hyperbolic_bound _ (fullCuspRow_ne_zero x) p hp j)).trans
    rw [he.self_of_nhds]
    exact hbound _ hx

lemma kernelBarrier_scaled_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierField_scaled_deriv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  let f : EuclideanSpatial→ℂ := fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)
  have hf : ∀q,0<q 2→ ContDiffAt ℝ ∞ f q := fun q hq =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) q hq)
  have he : ∀q : SpatialCoordinates,0<q 2→ f (WithLp.toLp 2 q)=(cuspBarrierField 2 3 q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq 2 3 (WithLp.toLp 2 q) hq)
  have ha := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤_
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,ha.deriv_eq]
  change _≤D*cuspBarrier 2 3 (euclideanToHyperbolic p)
  rw [cuspBarrier_euclidean_eq 2 3 p hp]
  exact hbound p.ofLp hp j

lemma kernelBarrier_scaled_real_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      |p 2*fderiv ℝ (fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)) p
        (euclideanCoordinateVector j)|≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := kernelBarrier_scaled_fderiv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have hphi := (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have he := (Complex.ofRealCLM.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  have hh := hbound p hp j
  change ‖(p 2:ℂ)*fderiv ℝ (Complex.ofRealCLM ∘ (fun q => cuspBarrier 2 3 (euclideanToHyperbolic q))) p
      (euclideanCoordinateVector j)‖≤_ at hh
  rw [he] at hh
  simpa only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,←Complex.ofReal_mul,
    Complex.norm_real,Real.norm_eq_abs] using! hh

lemma kernelExhaustionProfile_euler_bounded :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀v : ℝ,|v*deriv (kernelExhaustionProfile n) v|≤C := by
  obtain ⟨C,hC,hbound⟩ := cuspTransition_euler_bounded 1 2 (by norm_num)
  refine ⟨C,hC,fun n v => ?_⟩
  let c : ℝ := (n:ℝ)+1
  have hc : c≠0 := by dsimp [c]; positivity
  have hd := (hasDerivAt_const v (1:ℝ)).sub
    (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/c)).hasDerivAt.comp v
      ((hasDerivAt_id v).div_const c))
  change HasDerivAt (kernelExhaustionProfile n) (0-deriv (cuspTransition 1 2) (v/c)*(1/c)) v at hd
  rw [hd.deriv]
  have he : v*(0-deriv (cuspTransition 1 2) (v/c)*(1/c))= -(v/c*deriv (cuspTransition 1 2) (v/c)) := by ring
  rw [he,abs_neg]
  exact hbound (v/c)

lemma kernelExhaustionCutoff_scaled_fderiv_bound :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤C := by
  obtain ⟨D,hD,hgrad⟩ := kernelBarrier_scaled_real_fderiv_bound
  obtain ⟨B,hB,hprofile⟩ := kernelExhaustionProfile_euler_bounded
  refine ⟨D*B,mul_nonneg hD hB,fun n p hp j => ?_⟩
  let phi : EuclideanSpatial→ℝ := fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)
  have hphi : DifferentiableAt ℝ phi p :=
    (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have hP := ((kernelExhaustionProfile_smooth n).differentiable (by simp) (phi p)).hasDerivAt
  have hd := (hP.ofReal_comp.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  change ‖(p 2:ℂ)*fderiv ℝ ((fun v => (kernelExhaustionProfile n v:ℂ)) ∘ phi) p
    (euclideanCoordinateVector j)‖≤D*B
  rw [hd]
  change ‖(p 2:ℂ)*((fderiv ℝ phi p (euclideanCoordinateVector j):ℝ) •
    ((deriv (kernelExhaustionProfile n) (phi p):ℝ):ℂ))‖≤D*B
  rw [Complex.real_smul,←Complex.ofReal_mul,←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    |p 2*(fderiv ℝ phi p (euclideanCoordinateVector j)*deriv (kernelExhaustionProfile n) (phi p))|
      = |p 2*fderiv ℝ phi p (euclideanCoordinateVector j)| *|deriv (kernelExhaustionProfile n) (phi p)| := by rw [←abs_mul]; congr 1; ring
    _ ≤ (D*phi p)*|deriv (kernelExhaustionProfile n) (phi p)| :=
      mul_le_mul_of_nonneg_right (hgrad p hp j) (abs_nonneg _)
    _ = D*|phi p*deriv (kernelExhaustionProfile n) (phi p)| := by
      rw [abs_mul,abs_of_nonneg (le_trans zero_le_one (kernelQuotientBarrier_one_le 2 3 (by norm_num) (by norm_num) _))]
      ring
    _ ≤ D*B := mul_le_mul_of_nonneg_left (hprofile n (phi p)) hD

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical ContDiff Topology

open scoped BigOperators Classical
namespace QuadraticAllOddCRT

section
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open CanonicalQuadraticSieve hiding O

local instance instIsMaximalOSpanSingletonSetLambda : (Ideal.span {lambda} : Ideal ActualEisensteinCubic.O).IsMaximal:=lambdaIdeal_maximal

lemma lambda_odd : ringChar (ActualEisensteinCubic.O⧸Ideal.span {lambda})≠2:=
  ActualEisensteinSieve.lambda_residue_odd

lemma lambda_residue : residue lambda=((3:ZMod 4),(1:ZMod 4)) := by
  have h : lambda=eval (-1) 1 := by
    change (ActualEisensteinCubic.omega-1:ActualEisensteinCubic.O)=((-1:ℤ):ActualEisensteinCubic.O)+((1:ℤ):ActualEisensteinCubic.O)*ActualEisensteinCubic.omega
    push_cast
    ring
  rw [h,residue_eval]
  decide

lemma lambda_quadratic_ray_ne_zero : quadraticRayValue (residue lambda)≠0 := by
  apply quadraticRayValue_ne_zero_of_odd
  rw [lambda_residue]
  decide

lemma character_lambda_primary (p : ActualEisensteinCubic.O) (hp : lambda^2∣p-1) :
    character (Ideal.span {lambda}) (Ideal.Quotient.mk (Ideal.span {lambda}) p)=1 := by
  have hm : Ideal.Quotient.mk (Ideal.span {lambda}) p=Ideal.Quotient.mk (Ideal.span {lambda}) (1:ActualEisensteinCubic.O) :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hp))
  rw [hm,map_one,map_one]

def lambdaQuadraticRay (r : EisensteinEPrimaryPhase.Coord) : ℂ:=
  quadraticRayValue (EisensteinEPrimaryPhase.mul (residue lambda) r)/
    (quadraticRayValue (residue lambda)*quadraticRayValue r)

theorem character_lambda_eq_ray (p : ActualEisensteinCubic.O) (hp : p≠0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2)
    (hprimary : lambda^2∣p-1) :
    character (Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p}) lambda)=
      lambdaQuadraticRay (residue p) := by
  have hcop : IsCoprime (Ideal.span {lambda} : Ideal ActualEisensteinCubic.O) (Ideal.span {p}) := by
    apply Ideal.isCoprime_of_isMaximal
    intro he
    apply hg
    rw [←he]
    exact Ideal.subset_span (by simp)
  have h:=quadratic_ray_cross lambda p PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero hp hcop lambda_odd hc
  rw [character_lambda_primary p hprimary,one_mul] at h
  have hodd : EisensteinEPrimaryPhase.odd (residue p) := by
    have hn : ‖quadraticRayValue (residue p)‖=1 := by
      let pp : Unit→ActualEisensteinCubic.O:=fun _=>p
      have hpp : ∀i,pp i≠0:=fun _=>hp
      have hcp : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})):=by
        intro i j hij
        exact False.elim (hij (Subsingleton.elim _ _))
      have hh:=FiniteGaussPhase.norm_canonicalProductGauss pp hpp hcp (fun _=>hg) (fun _=>hc)
        (fun _=>3) (by intro i;decide) (by intro i;decide)
      rw [QuadraticGaussRay.canonicalProductGauss_three_eq_rayValue pp hpp hcp (fun _=>hg) (fun _=>hc)] at hh
      simpa [pp] using hh
    exact QuadraticUnitInvariance.odd_of_quadraticRayValue_norm_eq_one _ hn
  unfold lambdaQuadraticRay
  rw [←residue_mul]
  apply (eq_div_iff (mul_ne_zero lambda_quadratic_ray_ne_zero (quadraticRayValue_ne_zero_of_odd _ hodd))).mpr
  simpa only [mul_assoc] using h.symm

end

open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega

def lambdaQuadraticTable (r : EisensteinEPrimaryPhase.Coord) : ℤ :=
  if ¬EisensteinEPrimaryPhase.odd r then 0
  else if r∈({(0,1),(1,0),(1,2),(1,3),(2,3),(3,3)} : Finset EisensteinEPrimaryPhase.Coord)
    then 1 else -1

lemma lambdaQuadraticTable_mul (r s : EisensteinEPrimaryPhase.Coord) :
    lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
      lambdaQuadraticTable r*lambdaQuadraticTable s := by
  have h : ∀r s : EisensteinEPrimaryPhase.Coord,
      lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
        lambdaQuadraticTable r*lambdaQuadraticTable s := by decide
  exact h r s

lemma lambdaQuadraticTable_eq_ray (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    (lambdaQuadraticTable r:ℂ)=lambdaQuadraticRay r := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hn3 : (-3 : ZMod 4) = 1 := by decide
  rcases r with ⟨a,b⟩
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [lambdaQuadraticTable,lambdaQuadraticRay,lambda_residue,EisensteinEPrimaryPhase.mul,
      EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      Prod.mk.injEq,hcmp,hn3,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      ZMod.val_neg_one,ZMod.val_mul,ZMod.val_add,ZMod.val_sub,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_three]
  all_goals
    field_simp [Complex.I_ne_zero]
    change (-2 : ℂ) = Complex.I * (Complex.I ^ (1 : ℤ) + Complex.I ^ (2 - 1 : ℤ))
    norm_num [Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]

def lambdaQuadraticCharacter : ActualEisensteinCubic.O→*ℂ where
  toFun n:=(lambdaQuadraticTable (residue n):ℂ)
  map_one' := by
    have h : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0):=by
      have h1 : (1:ActualEisensteinCubic.O)=eval 1 0:=by simp [eval]
      rw [h1,residue_eval]
      norm_num
    rw [h]
    exact_mod_cast (show lambdaQuadraticTable ((1:ZMod 4),0)=1 from by decide)
  map_mul' x y := by
    rw [residue_mul,lambdaQuadraticTable_mul]
    push_cast
    rfl

lemma lambdaQuadraticCharacter_periodic (x y : ActualEisensteinCubic.O) (h : (4:ActualEisensteinCubic.O)∣x-y) :
    lambdaQuadraticCharacter x=lambdaQuadraticCharacter y := by
  change (lambdaQuadraticTable (residue x):ℂ)=(lambdaQuadraticTable (residue y):ℂ)
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y h]

end QuadraticAllOddCRT

open scoped BigOperators Classical
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open CubicJacobiGlobal hiding O
open QuadraticAllOddCRT
open CanonicalQuadraticSieve hiding O
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid

lemma localRowValue_square (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue x P^2=eisEmbedding (primeValue P x) := by
  unfold localRowValue primeValue
  split_ifs with h
  · let : P.IsMaximal:=h.1
    change (actualSextic P h.2 (Ideal.Quotient.mk P x))^2=_
    rw [←MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),canonicalSextic_pow_two]
    rfl
  · simp

theorem idealRowHom_square (x : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom x I ^2=eisEmbedding (idealSymbol I x) := by
  have hm (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue x)).prod^2=eisEmbedding ((s.map (fun P=>primeValue P x)).prod) := by
    induction s using Multiset.induction_on with
    | empty=>simp
    | @cons P s ih=>
      simp only [Multiset.map_cons,Multiset.prod_cons,mul_pow,map_mul,localRowValue_square,ih]
  by_cases hI : I=0
  · subst I
    simp only [map_zero,idealSymbol_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · change (if I=0 then 0 else _)^2=eisEmbedding (if I=0 then 0 else _)
    simp only [if_neg hI]
    exact hm _

lemma actualSextic_cube_quadratic (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    actualSextic P hg^3=character P := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ,hχ3⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧
      χ^3=(quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ActualEisensteinCubic.O) :=
    ⟨_,rfl,(sexticChar_powers P hg).2.1⟩
  rw [hχ,MulChar.ringHomComp_pow,hχ3]
  ext x
  change eisEmbedding ((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ActualEisensteinCubic.O)=((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ℂ)
  simp

lemma idealRowHom_lambda_prime_cube (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : lambda^2∣p-1) (hs : Supported (Ideal.span {p})) :
    idealRowHom lambda (Ideal.span {p})^3=lambdaQuadraticCharacter p := by
  let : (Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmem : Ideal.span {p}∈normalizedFactors (Ideal.span {p}) :=
    (Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩
  obtain ⟨hg,hc⟩:=hs.2 _ hmem
  rw [idealRowHom_prime lambda _ hg]
  change (actualSextic _ hg (Ideal.Quotient.mk _ lambda))^3=_
  rw [←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
  have he:=character_lambda_eq_ray p hp.ne_zero hg hc hprimary
  have ho:=ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p
  have hs' := (supported_span_iff p).mp hs
  change character _ (Ideal.Quotient.mk _ lambda)=_
  rw [he]
  exact (lambdaQuadraticTable_eq_ray _ (ho.mpr hs'.2)).symm

theorem idealRowHom_lambda_cube (y : ActualEisensteinCubic.O) (hy : lambda^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lambda (Ideal.span {y})^3=lambdaQuadraticCharacter y := by
  have hy0 : y≠0:=by
    intro he
    apply hs.1
    simp [he]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization y hy0 hy
  rw [←hprod] at hs ⊢
  clear hprod hy hy0 y
  induction s using Multiset.induction_on with
  | empty=>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_pow]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀q∈s,Prime q ∧ lambda^2∣q-1:=
      fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,mul_pow,
      idealRowHom_lambda_prime_cube p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

theorem idealRowHom_lambda_formula (y : ActualEisensteinCubic.O) (hy : lambda^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lambda (Ideal.span {y})=
      eisEmbedding (CubicRamified.linearRay 1 0 y)^2*lambdaQuadraticCharacter y := by
  have htwo:=idealRowHom_square lambda (Ideal.span {y})
  change idealRowHom lambda (Ideal.span {y})^2=eisEmbedding (symbol lambda y) at htwo
  rw [CubicRamified.symbol_lambda_eq_linearRay y hy] at htwo
  have hthree:=idealRowHom_lambda_cube y hy hs
  have hq : lambdaQuadraticCharacter y^2=1 := by
    change (lambdaQuadraticTable (ActualEisensteinCoordinates.residue y):ℂ)^2=1
    have ho := ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd y |>.mpr ((supported_span_iff y).mp hs).2
    unfold lambdaQuadraticTable
    rw [if_neg (not_not.mpr ho)]
    split_ifs <;> norm_num
  have hsix : idealRowHom lambda (Ideal.span {y})^6=1 := by
    calc
      _ = (idealRowHom lambda (Ideal.span {y})^3)^2:=by ring
      _ = 1:=by rw [hthree,hq]
  calc
    _ = (idealRowHom lambda (Ideal.span {y})^2)^2*(idealRowHom lambda (Ideal.span {y})^3):=by
      calc
        _ = idealRowHom lambda (Ideal.span {y})*idealRowHom lambda (Ideal.span {y})^6:=by rw [hsix,mul_one]
        _ = _:=by ring
    _ = _:=by rw [htwo,hthree]

theorem idealRowHom_lambda_mod_thirty_six (x y : ActualEisensteinCubic.O)
    (hx : lambda^2∣x-1) (hy : lambda^2∣y-1)
    (hsx : Supported (Ideal.span {x})) (hsy : Supported (Ideal.span {y}))
    (hxy : (36:ActualEisensteinCubic.O)∣x-y) :
    idealRowHom lambda (Ideal.span {x})=idealRowHom lambda (Ideal.span {y}) := by
  rw [idealRowHom_lambda_formula x hx hsx,idealRowHom_lambda_formula y hy hsy,
    CubicRamified.linearRay_congr_mod_nine 1 0 x y hx hy ((show (9:ActualEisensteinCubic.O)∣36 from ⟨4,by norm_num⟩).trans hxy),
    lambdaQuadraticCharacter_periodic x y ((show (4:ActualEisensteinCubic.O)∣36 from ⟨9,by norm_num⟩).trans hxy)]

end CanonicalRowCompletion

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma cuspRemainder_absolute_chart (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (hz : ‖z‖≤1)
    (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖)≤eisensteinRemainderBound b s := by
  let G : ((Fin 2×Fin 2)→ℤ)→ℝ := fun n => (max 5 (2*b))^s.re*‖n‖^(-s.re)
  let f : CuspCosets→(Fin 2×Fin 2)→ℤ := fun r => rowCoordinates (translatedCuspRow M r)
  let R : CuspCosets→ℝ := fun r => ‖cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖
  have hg : Summable G := (summable_integer_four_rpow s.re hs).mul_left _
  have hi : Function.Injective f := rowCoordinates_injective.comp (translatedCuspRow_injective M)
  have hb : ∀r,R r≤G (f r) := by
    intro r
    simpa only [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul] using
      translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0 r
  have hr : Summable R := (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hr,?_⟩
  have hsum : (∑'r,R r)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

theorem cuspRemainder_absolute_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s (cosetHeight r w)‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s (cosetHeight r w)‖)≤eisensteinRemainderBound b s := by
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  have hz1 : ‖z‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have hv1 : 1/2≤v := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hh0 := Real.sqrt_nonneg (2/3 : ℝ)
    nlinarith
  have hw : w=integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [←hMw,map_inv,inv_smul_smul]
  rw [hw]
  exact cuspRemainder_absolute_chart a b ha hab s hs M⁻¹ z hz1 v hv1 hv

lemma cuspRemainder_aux_norm (b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) (hvb : v≤b) :
    ‖cuspRemainderProfile (b+1) (b+2) s v‖=v^s.re := by
  rw [cuspRemainderProfile,cuspSeedProfile_zero (b+1) (b+2) s v (by linarith) (by linarith),
    sub_zero,positiveHeightPower_eq_cpow s v hv,Complex.norm_cpow_eq_rpow_re_of_pos hv]

lemma cuspRemainder_row_scaled_deriv_aux_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (fun q => cuspRemainderProfile a b s (rowHeight u q)) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight u p)‖ := by
  have hh := rowHeight_pos u hu p hp
  by_cases hb : rowHeight u p≤b
  · rw [cuspRemainder_aux_norm b s _ hh hb]
    exact cuspRemainder_row_scaled_deriv_bound a b s C hC u hu p hp j
  · have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
      (cuspRemainderProfile_contDiffAt a b s) u hu p hp j).1
    rw [hd.deriv,cuspRemainderProfile_deriv_zero a b s _ hab hh (lt_of_not_ge hb)]
    simp only [zero_mul,mul_zero,norm_zero]
    exact mul_nonneg (add_nonneg (norm_nonneg s) hC0) (norm_nonneg _)

end

open Filter
open scoped BigOperators Classical Topology ContDiff

def weightedHeightProfile (F : ℝ→ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma weightedHeightProfile_axis_differentiable (F : ℝ→ℂ)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (weightedHeightProfile F r) p j) (p j) :=
  ((rowProfile_axis_derivatives F hF (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1.const_mul _).differentiableAt

lemma heightPoincare_axis_termwise (F : ℝ→ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) ∧
    HasDerivAt (axisSlice (heightPoincareField F) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) (p j) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [ContinuousAt,Function.update_eq_self] using
      ((continuous_axis_update p j).continuousAt (x := p j))
  have hn : ∀ᶠt in 𝓝 (p j),Function.update p j t∈U := ht (hU.mem_nhds hpU)
  have hz (r : CuspCosets) (hr : r∉S) :
      deriv (axisSlice (weightedHeightProfile F r) p j) (p j)=0 := by
    have he : axisSlice (weightedHeightProfile F r) p j=ᶠ[𝓝 (p j)] (fun _ => 0) := by
      filter_upwards [hn] with t ht
      change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
      rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]
    exact he.deriv_eq.trans (deriv_const _ _)
  refine ⟨summable_of_ne_finset_zero hz,?_⟩
  rw [tsum_eq_sum hz]
  have hd := HasDerivAt.sum (u := S) (fun r hr =>
    (weightedHeightProfile_axis_differentiable F hF r p hp j).hasDerivAt)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  simp only [Finset.sum_apply]
  change (∑'r,weightedHeightProfile F r (Function.update p j t))=
    ∑r∈S,weightedHeightProfile F r (Function.update p j t)
  apply tsum_eq_sum
  intro r hr
  change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
  rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]

lemma weightedRemainder_axis_deriv (a b : ℝ) (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      deriv (axisSlice (smoothSummand s r) p j) (p j)-
        deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  have he : axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j=ᶠ[𝓝 (p j)]
      (fun t => axisSlice (smoothSummand s r) p j t-
        axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j t) := by
    filter_upwards [hn] with t ht
    simp only [axisSlice,weightedHeightProfile,cuspRemainderProfile,smoothSummand]
    rw [rowSmoothPower_eq_height s _ (embeddedRow_ne_zero r) _ ht,
      positiveHeightPower_eq_cpow s _ (rowHeight_pos _ (embeddedRow_ne_zero r) _ ht)]
    ring
  rw [he.deriv_eq]
  exact deriv_sub (smooth_axis_differentiable s r p hp j)
    (weightedHeightProfile_axis_differentiable _ (cuspSeedProfile_contDiffAt a b s) r p hp j)

def eisensteinRemainderField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  smoothEisenstein s p-smoothCuspSeedField a b s p

theorem eisensteinRemainder_axis_termwise (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) ∧
    HasDerivAt (axisSlice (eisensteinRemainderField a b s) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) (p j) := by
  have hE := eisenstein_axis_termwise s hs p hp j
  have hS := heightPoincare_axis_termwise (cuspSeedProfile a b s)
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp j
  have hcoeff : (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))=
      (∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j))-
        ∑'r,deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
    simp_rw [weightedRemainder_axis_deriv a b s _ p hp j]
    exact hE.1.tsum_sub hS.1
  refine ⟨(hE.1.sub hS.1).congr (fun r => (weightedRemainder_axis_deriv a b s r p hp j).symm),?_⟩
  rw [hcoeff]
  apply (hE.2.2.1.sub hS.2).congr_of_eventuallyEq
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  filter_upwards [hn] with t ht
  change smoothEisenstein s _-smoothCuspSeedField a b s _=
    smoothEisenstein s _-heightPoincareField (cuspSeedProfile a b s) _
  rw [smoothCuspSeedField_eq a b s ha hab _ ht]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

namespace CubicEisenstein

lemma weightedRemainder_scaled_deriv_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖ := by
  let g : SpatialCoordinates→ℂ:=fun q => cuspRemainderProfile a b s (rowHeight (embeddedRow r) q)
  have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
    (cuspRemainderProfile_contDiffAt a b s) (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1
  have hw := hd.const_mul (cosetCharacter r)⁻¹
  have he : deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      (cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j) := by
    change deriv (fun t => (cosetCharacter r)⁻¹*axisSlice g p j t) (p j)=_
    rw [hw.deriv,hd.deriv]
  rw [he]
  calc
    ‖(p 2:ℂ)*((cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j))‖
      = ‖(cosetCharacter r)⁻¹*((p 2:ℂ)*deriv (axisSlice g p j) (p j))‖ := by congr 1; ring
    _ = ‖(p 2:ℂ)*deriv (axisSlice g p j) (p j)‖ := by
      rw [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul]
    _ ≤ _ := cuspRemainder_row_scaled_deriv_aux_bound a b hab s C hC0 hC _ (embeddedRow_ne_zero r) p hp j

theorem eisensteinRemainder_scaled_axis_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (eisensteinRemainderField a b s) p j) (p j)‖≤B := by
  obtain ⟨C,hC0,hC⟩ := cuspTransition_euler_bounded a b hab
  refine ⟨(‖s‖+C)*eisensteinRemainderBound (b+2) s,
    mul_nonneg (add_nonneg (norm_nonneg s) hC0) (eisensteinRemainderBound_nonneg _ _),?_⟩
  intro p hp j
  have hA : Summable (fun r : CuspCosets =>
      ‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖) ∧
      (∑'r : CuspCosets,‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖)≤
        eisensteinRemainderBound (b+2) s := by
    simpa only [cosetHeight_upperPoint_rowHeight] using
      cuspRemainder_absolute_bound (b+1) (b+2) (by linarith) (by linarith) s hs
        (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)
  have hB := hA.1.mul_left (‖s‖+C)
  have hb (r : CuspCosets) := weightedRemainder_scaled_deriv_bound a b hab s C hC0 hC r p hp j
  have hnorm := hB.of_nonneg_of_le (fun r => norm_nonneg
    ((p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))) hb
  have ht := eisensteinRemainder_axis_termwise a b ha hab s (by linarith) p hp j
  rw [ht.2.deriv,←tsum_mul_left]
  apply (norm_tsum_le_tsum_norm hnorm).trans
  apply (Summable.tsum_le_tsum hb hnorm hB).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hA.2 (add_nonneg (norm_nonneg s) hC0)

def kernelEisensteinRemainder (a b : ℝ) (s : ℂ) (hs : 2<s.re) : KernelQuotient→ℂ :=
  fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q

lemma kernelEisensteinRemainder_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelEisensteinRemainder a b s hs) :=
  (kernelQuotientEisenstein_contMDiff s hs).sub (kernelQuotientSeed_contMDiff a b s ha hab)

lemma kernelEisensteinRemainder_euclidean_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun q => kernelEisensteinRemainder a b s hs (kernelEuclideanProjection q)) p :=
  ((((kernelEisensteinRemainder_smooth a b ha hab s hs).comp kernelProjection_contMDiff)
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

lemma kernelEisensteinRemainder_euclidean_eq (a b : ℝ) (s : ℂ) (hs : 2<s.re)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p)=eisensteinRemainderField a b s p.ofLp := by
  unfold kernelEisensteinRemainder kernelEuclideanProjection
  simp only [Function.comp_apply]
  rw [euclideanToHyperbolic_positive p hp,kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint]
  unfold eisensteinRemainderField
  rw [smoothEisenstein_eq_actual s p.ofLp hp,smoothCuspSeedField,dif_pos hp]
  simp only [mul_comm Complex.I]
  rfl

theorem kernelEisensteinRemainder_scaled_fderiv_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => kernelEisensteinRemainder a b s (by linarith)
        (kernelEuclideanProjection q)) p (euclideanCoordinateVector j)‖≤B := by
  obtain ⟨B,hB,hbound⟩ := eisensteinRemainder_scaled_axis_bound a b ha hab s hs
  refine ⟨B,hB,?_⟩
  intro p hp j
  let f : EuclideanSpatial→ℂ:=fun q => kernelEisensteinRemainder a b s (by linarith) (kernelEuclideanProjection q)
  have hf : ∀q,0<q 2→ ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s (by linarith)
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s (by linarith) (WithLp.toLp 2 q) hq
  have heq := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤B
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,heq.deriv_eq]
  exact hbound p.ofLp hp j

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows CompletedHeight
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def coefficient (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (negative : Bool)
    (x : OriginalIndex ι) : Finset ι→ℂ :=
  firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 negative Ψ m (divisorElement p x.1)
    (mark (if negative then x.1.1.rightExponent else x.1.1.leftExponent)) x.2

def weight (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Ψ : O→*ℂ) (m : O)
    (x : OriginalIndex ι) : ℂ :=
  retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
    (divisorElement p x.1) (firstOriginalWeight p β R x.1) x.2

def sourceSummand (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (x : OriginalIndex ι) (j : FirstCommonIndex ι) : ℂ :=
  weight p hp hcop hg β R Ψ m x *
    firstCommonWeight p hg (coefficient p hp hcop hg Ψ m mark true x)
      (coefficient p hp hcop hg Ψ m mark false x) x.2.2 j *
    firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialClippedColumns
open CanonicalCoefficientClass InverseMomentFirstLabelCell InverseMomentFirstChildWindows
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def CanonicalRankMoments (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  ∀(Ψ:O→*ℂ),IsBaseRayTwist base Ψ→∀(m:O),m≠0→∀N V M Qwidth:ℝ,
    0≤N→0≤V→0≤M→0≤Qwidth→M≤Mmax→N+V≤Fcap→
    CanonicalMargins (N+V) M Qwidth z c→
    ‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Qwidth→
    ∀(subslots:Finset σ),subslots⊆slots→∀labels:Finset (Ideal O),
      (∀I∈labels,Admissible I ∧ (Ideal.absNorm I:ℝ)≤Z^V)→∀s:ℝ,
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels
      (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z (N+V)≤
      A*Z^(N+V+eps)*(1+‖s‖)^(2*degree)

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeReciprocalGrowth
open HeckeFamily HeckeLogarithmic HeckeDeletionBounds

def presentationComplexity (χ : Character) (t : ℝ) : ℝ :=
  ((radical χ.modulus).absNorm : ℝ)*complexity χ t

end SevenEighths.HeckeReciprocalGrowth

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Metric MeasureTheory Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeLogarithmic HeckeDeletionBounds

def binCost (B : ℝ) (χ : Character) (H : ℝ) : ℝ :=
  B*Real.log (complexity χ H) + localBound (1/2)*Real.log ((radical χ.modulus).absNorm : ℝ)

end SevenEighths.HeckePrimeDyadic

end

end OAI
end

section

namespace OAI

namespace SevenEighths.PNT.RayAsymptotic

open ActualEisensteinCubic RayOrthogonality Filter
open scoped BigOperators Classical Topology

noncomputable section

variable (M : Ideal O) [Finite (O ⧸ M)]

def principalRegularization (F : ℂ → ℂ) (residue : ℂ) : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * F s) 1 residue

def regularizedFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ)
    (χ : rayCharacters M) : ℂ → ℂ :=
  if χ = 1 then principalRegularization (F χ) residue else F χ

structure AnalyticFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) : Prop where
  eq_series : ∀ (χ : rayCharacters M) (s : ℂ), 1 < s.re →
    F χ s = IdealEuler.series (idealCharacter M χ) s
  analytic : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → AnalyticAt ℂ (F χ) s
  nonzero : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → F χ s ≠ 0
  pole_analytic : AnalyticAt ℂ (principalRegularization (F 1) residue) 1
  residue_ne_zero : residue ≠ 0

section Quotient

variable (H : Subgroup (O ⧸ M)ˣ) (hH : globalUnits M ≤ H)

def quotientClassCoeff (n : ℕ) : ℝ := IdealMangoldt.classCoeff (RayQuotient.identityClass M H) n

def quotientRemainder (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) (s : ℂ) : ℂ :=
  (∑ χ : RayQuotient.Characters M H,
    -deriv (regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ)) s /
      regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ) s) /
        (RayQuotient.classNumber M H : ℂ)

end Quotient

end
end SevenEighths.PNT.RayAsymptotic

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingResidual (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)(a:Ideal O→ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,star ((∏i:{i:ι // i∉J},coeff i.val (y i).val)*
    (moebius (remainingIdeal L J y):ℂ))*
    conjugatedResidual S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) η a W Z r z G u

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic
open InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingPolynomial (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,(∏i:{i:ι // i∉J},star (coeff i.val (y i).val))*
    residualNormalizedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
      (fun v=>star (W v)) Z r z G u

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open UniqueFactorizationMonoid CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedMass (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→Ideal O→ℂ)(Z G:ℝ) : ℝ :=
  ‖∏i:↥J,coeff i.val (x i).val‖*Z^(-G)

def assignedTerm (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
    (Z^(-G):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
    star (remainingResidual S L J x coeff η (fun _=>1) W Z r z G u)

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end


