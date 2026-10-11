-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0148_parallel1
-- name    : PNT_ZeroFree_433_0148_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:13:57.421991+00:00
-- url     : https://prove2.me/theorems/1b7eea16-fbb1-45e7-a6ec-93a6ca4a4124
-- title:
--   Zero-free region foundations: MeanSquare.SourceTransfer [0148_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean#L308-L559

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0043
import Definitions.Def_PNT_ZeroFree_433_0050
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0083
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0136_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0144_parallel1
import Definitions.Def_PNT_ZeroFree_433_0161_parallel1
import Definitions.Def_PNT_ZeroFree_433_0184_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel1
import Definitions.Def_PNT_ZeroFree_433_0190_parallel1
import Definitions.Def_PNT_ZeroFree_433_0203_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel1
import Definitions.Def_PNT_ZeroFree_433_0332_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap ContDiff


namespace CubicEisenstein

section
open Filter MeasureTheory LineDeriv
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)
abbrev EuclideanGradientL2 := PiLp 2 (fun _ : Fin 3 => EuclideanL2)


abbrev EuclideanDistributions := TemperedDistribution EuclideanSpatial ℂ

def euclideanCoordinateVector (j : Fin 3) : EuclideanSpatial := WithLp.toLp 2 (Pi.single j 1)
def euclideanL2Distribution : EuclideanL2 →L[ℂ] EuclideanDistributions :=
  Lp.toTemperedDistributionCLM ℂ volume 2

lemma euclideanL2Distribution_injective : Function.Injective euclideanL2Distribution := by
  apply LinearMap.ker_eq_bot.mp
  exact Lp.ker_toTemperedDistributionCLM_eq_bot

def euclideanGradientEquations : EuclideanL2 × EuclideanGradientL2 →L[ℂ]
    (Fin 3 → EuclideanDistributions) :=
  ContinuousLinearMap.pi (fun j =>
    (lineDerivOpCLM ℂ EuclideanDistributions (euclideanCoordinateVector j)).comp
      (euclideanL2Distribution.comp (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2))-
    euclideanL2Distribution.comp ((PiLp.proj 2 (fun _ : Fin 3 => EuclideanL2) j).comp
      (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2)))

def euclideanWeakGradientGraph : Submodule ℂ (EuclideanL2 × EuclideanGradientL2) :=
  euclideanGradientEquations.ker

lemma mem_euclideanWeakGradientGraph (f : EuclideanL2) (g : EuclideanGradientL2) :
    (f,g)∈euclideanWeakGradientGraph ↔ ∀j,
      ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)=euclideanL2Distribution (g j) := by
  change (fun j => ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)-
    euclideanL2Distribution (g j))=0 ↔ _
  simp only [funext_iff,Pi.zero_apply,sub_eq_zero]

lemma euclideanWeakGradientGraph_unique (x : EuclideanL2 × EuclideanGradientL2)
    (hx : x∈euclideanWeakGradientGraph) (hzero : x.1=0) : x.2=0 := by
  have hh := (mem_euclideanWeakGradientGraph x.1 x.2).mp hx
  apply (WithLp.equiv 2 (Fin 3 → EuclideanL2)).injective
  funext j
  change x.2 j=(0:EuclideanL2)
  apply euclideanL2Distribution_injective
  simpa only [hzero,map_zero,lineDerivOp_zero,WithLp.ofLp_zero,Pi.zero_apply] using (hh j).symm

def euclideanWeakGradient : EuclideanL2 →ₗ.[ℂ] EuclideanGradientL2 :=
  euclideanWeakGradientGraph.toLinearPMap

lemma euclideanWeakGradient_graph : euclideanWeakGradient.graph=euclideanWeakGradientGraph :=
  Submodule.toLinearPMap_graph_eq _ euclideanWeakGradientGraph_unique

theorem euclideanWeakGradient_closed : euclideanWeakGradient.IsClosed := by
  rw [LinearPMap.IsClosed,euclideanWeakGradient_graph]
  exact euclideanGradientEquations.isClosed_ker

lemma schwartz_mem_euclideanWeakGradientGraph (f : 𝓢(EuclideanSpatial,ℂ)) :
    (f.toLp 2 volume,WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} f).toLp 2 volume))∈euclideanWeakGradientGraph := by
  apply (mem_euclideanWeakGradientGraph _ _).mpr
  intro j
  dsimp only [euclideanL2Distribution]
  simp only [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq («μ» := volume) f _

theorem euclideanWeakGradient_dense_domain : Dense (euclideanWeakGradient.domain : Set EuclideanL2) := by
  apply (SchwartzMap.denseRange_toLpCLM (E := EuclideanSpatial) (F := ℂ) (p := 2)
    («μ» := volume) (by norm_num)).mono
  rintro _ ⟨f,rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph
  rw [euclideanWeakGradient_graph]
  exact schwartz_mem_euclideanWeakGradientGraph f

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanH1Ambient := WithLp 2 (EuclideanL2 × EuclideanGradientL2)

def euclideanH1Submodule : Submodule ℂ EuclideanH1Ambient :=
  euclideanWeakGradientGraph.comap (WithLp.linearEquiv 2 ℂ (EuclideanL2 × EuclideanGradientL2)).toLinearMap

lemma euclideanH1Submodule_isClosed : IsClosed (euclideanH1Submodule : Set EuclideanH1Ambient) := by
  have hg : IsClosed (euclideanWeakGradientGraph : Set (EuclideanL2 × EuclideanGradientL2)) :=
    euclideanGradientEquations.isClosed_ker
  exact hg.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).continuous

abbrev EuclideanH1 := euclideanH1Submodule

instance euclideanH1Complete : CompleteSpace EuclideanH1 :=
  euclideanH1Submodule_isClosed.completeSpace_coe


def euclideanH1Embedding : EuclideanH1 →L[ℂ] EuclideanL2 :=
  (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

def euclideanH1Gradient : EuclideanH1 →L[ℂ] EuclideanGradientL2 :=
  (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

lemma euclideanH1Embedding_eq_zero (u : EuclideanH1) (hu : euclideanH1Embedding u=0) : u=0 := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (EuclideanL2 × EuclideanGradientL2)).injective
  apply Prod.ext
  · exact hu
  · exact euclideanWeakGradientGraph_unique u.1.ofLp u.2 hu

lemma euclideanH1Embedding_injective : Function.Injective euclideanH1Embedding := by
  intro u v huv
  apply sub_eq_zero.mp
  apply euclideanH1Embedding_eq_zero
  rw [map_sub,huv,sub_self]

lemma euclideanH1Embedding_dense : DenseRange euclideanH1Embedding := by
  apply euclideanWeakGradient_dense_domain.mono
  intro f hf
  obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
  rw [euclideanWeakGradient_graph] at hg
  refine ⟨⟨WithLp.toLp 2 (f,g),hg⟩,?_⟩
  rfl

lemma euclideanH1_norm_sq (u : EuclideanH1) :
    ‖u‖^2=‖euclideanH1Embedding u‖^2+‖euclideanH1Gradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

end CubicEisenstein

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge

def normCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : O→*ℂ where
  toFun a := χ (Ideal.absNorm (Ideal.span {a}))
  map_one' := by simp
  map_mul' a b := by
    rw [←Ideal.span_singleton_mul_span_singleton]
    simp

lemma normCharacter_prod {ι : Type*} (p : ι→O) (S : Finset ι)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normCharacter χ (∏i∈S,p i)=χ (Ideal.absNorm (∏i∈S,Ideal.span {p i})) := by
  change χ (Ideal.absNorm (Ideal.span {∏i∈S,p i}))=_
  rw [FiniteGaussPhase.span_finset_prod]

lemma pool_support_product (F : Finset (Ideal O)) (S : Finset (primePool F)) :
    idealSupport F (∏i∈S,i.val)=S := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏i∈S,i.val)≠(0:Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  ext i
  rw [mem_idealSupport_iff,UniqueFactorizationMonoid.mem_normalizedFactors_iff hn]
  simp only [family_prime_dvd_product_iff _ Subtype.val_injective S i,hp,true_and]

theorem sum_selected_ideals (F : Finset (Ideal O)) (hF : ∀I∈F,Squarefree I)
    (a : Ideal O→ℂ) :
    (∑I∈F,a I)=∑S∈(Finset.univ:Finset (primePool F)).powerset,
      if (∏i∈S,i.val)∈F then a (∏i∈S,i.val) else 0 := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun S _ => ∏i∈S,i.val)
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · intro S hS T hT he
    exact family_product_injective (fun i:primePool F => i.val) Subtype.val_injective he
  · intro I hI
    refine ⟨idealSupport F I,?_,idealSupport_product_eq F hI (hF I hI)⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),?_⟩
    rwa [idealSupport_product_eq F hI (hF I hI)]
  · intro S hS
    rfl

def selectedIdealTest (F : Finset (Ideal O)) (W : ℕ→ℂ) (S : Finset (primePool F)) : ℂ :=
  if (∏i∈S,i.val)∈F then W (Ideal.absNorm (∏i∈S,i.val)) else 0


end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def sourceChildEnergy (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑u∈T,‖fixedChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b testNegative)
    u.2 (if rowNegative then -u.1 else u.1)‖^2

def sourceEnergyMagnitude (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (testNegative rowNegative : Bool) : ℝ :=
  ∑u∈T,(rowMagnitude p hp hcop hg F Ψ m u.2 (if rowNegative then -u.1 else u.1)
    V X testNegative)^2

lemma sourceChildEnergy_le (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (tn rn : Bool) (a b : ℝ) :
    sourceChildEnergy p hp hcop hg F Ψ m T V X tn rn a b≤
      sourceEnergyMagnitude p hp hcop hg F Ψ m T V X tn rn := by
  unfold sourceChildEnergy sourceEnergyMagnitude
  apply Finset.sum_le_sum
  intro u hu
  exact pow_le_pow_left₀ (norm_nonneg _) (fixedRow_norm_le p hp hcop hg F Ψ m _ _ V X a b tn) 2

lemma sourceChildEnergy_continuous (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (tn rn : Bool) (τ σ : Frequency→ℝ)
    (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun q => sourceChildEnergy p hp hcop hg F Ψ m T V X tn rn (τ q) (σ q)) := by
  unfold sourceChildEnergy
  apply continuous_finsetSum
  intro u hu
  exact (fixedRow_continuous p hp hcop hg F Ψ m _ _ V X tn τ σ hτ hσ).norm.pow 2

def sourceGeometricMean (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℝ :=
  Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2)*
    Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2)


end


end InitialMeanSquare

end

end OAI

end


