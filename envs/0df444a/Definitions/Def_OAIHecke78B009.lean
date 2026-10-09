-- Prove2me | Definitions.Def_OAIHecke78B009
-- name    : OAIHecke78B009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T23:44:01.80069+00:00
-- url     : https://prove2.me/theorems/c7c3ea44-9e1b-40de-9324-1b60cbe8cd21
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 10 of 29
-- statement:
--   Definitions bundle 10 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B008` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `CubicSieve.PaddedPassage`, `CubicSieve.ReopenedFibers`, `Eisenstein.VariationalLaplacian`, `Eisenstein.CompactEnergyFamilies`, `RowCompletion.SupportBounds`, `CubicSieve.CanonicalLogEnergy`, `CubicSieve.RadialProfiles`, `Eisenstein.CoordinateLaplacian`, `CubicSieve.ReopeningBounds`, `CubicSieve.ClosedRecursion`, `Hecke.MobiusEulerCorrection`, `Inversion.InitialFibers`, `Descent.ReopenedBlocks`, `Descent.ReopenedPhysicalSplit`, `Descent.FirstGlobalSourceIndex`, `Descent.FirstGlobalSourceEnergy`, `Descent.FirstOriginalProfileData`, `Descent.ReopenedOriginalRow`, `Descent.CanonicalLongCoefficient`, `Detector.PairPhase`, `IdealEuler`, `Hecke.Boundary`, `Hecke.DeletionBounds`, `Detector.CentralAllSlots`, `Inversion.InitialPoissonBridge`, `Inversion.InitialConjugateEnergy`, `Moments.FirstAssembly`, `Moments.SecondScaled`, `Reflection.RowReindex`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B008

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B009

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  CubicSieve.PaddedPassage
  CubicSieve.ReopenedFibers
  Eisenstein.VariationalLaplacian
  Eisenstein.CompactEnergyFamilies
  RowCompletion.SupportBounds
  CubicSieve.CanonicalLogEnergy
  CubicSieve.RadialProfiles
  Eisenstein.CoordinateLaplacian
  CubicSieve.ReopeningBounds
  CubicSieve.ClosedRecursion
  Hecke.MobiusEulerCorrection
  Inversion.InitialFibers
  Descent.ReopenedBlocks
  Descent.ReopenedPhysicalSplit
  Descent.FirstGlobalSourceIndex
  Descent.FirstGlobalSourceEnergy
  Descent.FirstOriginalProfileData
  Descent.ReopenedOriginalRow
  Descent.CanonicalLongCoefficient
  Detector.PairPhase
  IdealEuler
  Hecke.Boundary
  Hecke.DeletionBounds
  Detector.CentralAllSlots
  Inversion.InitialPoissonBridge
  Inversion.InitialConjugateEnergy
  Moments.FirstAssembly
  Moments.SecondScaled
  Reflection.RowReindex
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def firstFrequencyDisk (R:ℝ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌈R⌉₊).filter (fun h=>‖eisEmbedding h‖^2≤R)

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

lemma euclideanCoordinateVector_eq_basis (j : Fin 3) :
    euclideanCoordinateVector j=EuclideanSpace.basisFun (Fin 3) ℝ j := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

lemma schwartz_toL2_norm_sq (g : 𝓢(EuclideanSpatial,ℂ)) :
    ‖g.toLp 2 volume‖^2=∫p,‖g p‖^2 := by
  calc
    ‖g.toLp 2 volume‖^2=inner ℝ (g.toLp 2 volume) (g.toLp 2 volume) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (g.toLp 2 volume p) (g.toLp 2 volume p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [g.coeFn_toLp 2 volume] with p hp
      rw [hp,real_inner_self_eq_norm_sq]

def kernelLocalizedDensity (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : ℝ :=
  ‖kernelLocalizedField χ f p‖^2+∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
    (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2

lemma kernelLocalizedDensity_eq_schwartz (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) :
    kernelLocalizedDensity χ f p=‖kernelLocalizedSchwartz χ f p‖^2+
      ∑j : Fin 3,‖(∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)) p‖^2 := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,euclideanCoordinateVector_eq_basis,
    kernelLocalizedSchwartz_coe]
  rfl

lemma kernelLocalizedDensity_integrable (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    Integrable (kernelLocalizedDensity χ f) volume := by
  change Integrable (fun p => kernelLocalizedDensity χ f p) volume
  simp_rw [kernelLocalizedDensity_eq_schwartz]
  exact ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq.add
    (integrable_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq))

lemma kernelLocalizedH1_norm_sq (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ‖kernelLocalizedH1 χ f‖^2=∫p,kernelLocalizedDensity χ f p := by
  rw [euclideanH1_norm_sq,kernelLocalizedH1_embedding,PiLp.norm_sq_eq_of_L2]
  simp_rw [kernelLocalizedH1_gradient,schwartz_toL2_norm_sq,kernelLocalizedDensity_eq_schwartz]
  rw [integral_add (((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq)
    (integrable_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq)),
    integral_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq)]

lemma kernelLocalizedDensity_zero (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∉tsupport χ.func) : kernelLocalizedDensity χ f p=0 := by
  have hz : kernelLocalizedField χ f=ᶠ[𝓝 p]0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    simp only [kernelLocalizedField,hq,Pi.zero_apply,zero_smul]
  simp only [kernelLocalizedDensity,hz.self_of_nhds,hz.fderiv_eq,fderiv_zero,
    Pi.zero_apply,_root_.zero_apply,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero]

lemma kernelLocalizedDensity_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) (M D A : ℝ)
    (hM : (χ.func p)^2≤M)
    (hD : (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hA : (χ.func p)^2≤A*(p 2)^2) :
    kernelLocalizedDensity χ f p≤
      (M+2*D)*‖kernelTestField f p‖^2+
        2*A*kernelTestEnergyDensity f (euclideanToHyperbolic p) := by
  have he := kernelLocalizedField_energy_bound χ f p hp
  have he' : (p 2)^2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤
      (p 2)^2*(2*A*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
        2*D*‖kernelTestField f p‖^2) := by
    refine he.trans ?_
    calc
      _ ≤ 2*(A*(p 2)^2)*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
          2*(p 2)^2*D*‖kernelTestField f p‖^2 := by
        gcongr
        · exact kernelTestEnergyDensity_nonneg _ _
      _ = _ := by ring
  have hs := le_of_mul_le_mul_left he' (sq_pos_of_pos hp)
  have hm : ‖kernelLocalizedField χ f p‖^2≤M*‖kernelTestField f p‖^2 := by
    simp only [kernelLocalizedField,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    exact mul_le_mul_of_nonneg_right hM (sq_nonneg _)
  unfold kernelLocalizedDensity
  nlinarith

lemma kernelEuclideanProjection_volume_integrable (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) (g : KernelQuotient→ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) :
    IntegrableOn (fun p => g (kernelEuclideanProjection p)) S volume := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := (hm.integrable_comp_of_integrable hg.integrableOn).smul_measure
    (c := ENNReal.ofReal (b^3)) ENNReal.ofReal_ne_top
  exact hh.mono_measure (euclideanVolume_le_heightCube_hyperbolic S hS hpos b hb hheight)

theorem kernelLocalizedH1_norm_sq_le (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (M D A b : ℝ) (hM0 : 0≤M) (hD0 : 0≤D) (hA0 : 0≤A) (hb : 0≤b)
    (hheight : ∀p∈tsupport χ.func,p 2≤b)
    (hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M)
    (hD : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hA : ∀p∈tsupport χ.func,(χ.func p)^2≤A*(p 2)^2)
    (f : kernelSmoothTests) :
    ‖kernelLocalizedH1 χ f‖^2≤b^3*((M+2*D)*‖kernelSmoothTestsToL2 f‖^2+
      2*A*kernelDirichletEnergy f) := by
  let G : KernelQuotient→ℝ := fun q =>
    (M+2*D)*‖f.1 q‖^2+2*A*kernelQuotientEnergyDensity f q
  have hG : Integrable G (integralQuotientVolume globalKubotaKernel) :=
    (((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul _).add
      ((kernelQuotientEnergyDensity_integrable f).const_mul _)
  have hGn : ∀q,0≤G q := by
    intro q
    dsimp only [G]
    positivity [kernelQuotientEnergyDensity_nonneg f q]
  have hS := χ.compact.measurableSet
  have hGI := kernelEuclideanProjection_volume_integrable (tsupport χ.func) hS χ.positive
    hinj b hb hheight G hG
  rw [kernelLocalizedH1_norm_sq]
  calc
    (∫p,kernelLocalizedDensity χ f p) =
        ∫p in tsupport χ.func,kernelLocalizedDensity χ f p :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (kernelLocalizedDensity_zero χ f)).symm
    _ ≤ ∫p in tsupport χ.func,G (kernelEuclideanProjection p) := by
      apply setIntegral_mono_on (kernelLocalizedDensity_integrable χ f).integrableOn hGI hS
      intro p hp
      exact kernelLocalizedDensity_le χ f p (χ.positive hp) M D A (hM p hp) (hD p hp) (hA p hp)
    _ ≤ b^3*∫q,G q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_volume_integral_le (tsupport χ.func) hS χ.positive hinj
        b hb hheight G hG hGn
    _ = _ := by
      dsimp only [G]
      rw [integral_add (((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul _)
        ((kernelQuotientEnergyDensity_integrable f).const_mul _),integral_const_mul,integral_const_mul,
        ←kernelSmoothTestsToL2_norm_sq]
      rfl

theorem kernelLocalizedH1_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelLocalizedH1 χ f‖^2≤C*(‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f) := by
  have hgrad : Continuous (fun p : EuclideanSpatial =>
      ∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) := by
    apply continuous_finsetSum
    intro j hj
    exact (((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hratio : ContinuousOn (fun p : EuclideanSpatial => (χ.func p)^2/(p 2)^2) (tsupport χ.func) :=
    (χ.smooth.continuous.pow 2).continuousOn.div (by fun_prop)
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.positive hp)))
  obtain ⟨m,hm⟩ := χ.compact.bddAbove_image (χ.smooth.continuous.pow 2).continuousOn
  obtain ⟨d,hd⟩ := χ.compact.bddAbove_image hgrad.continuousOn
  obtain ⟨a,ha⟩ := χ.compact.bddAbove_image hratio
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let M := max 0 m
  let D := max 0 d
  let A := max 0 a
  let B := max 0 b
  have hM0 : 0≤M := le_max_left _ _
  have hD0 : 0≤D := le_max_left _ _
  have hA0 : 0≤A := le_max_left _ _
  have hB0 : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M := fun p hp =>
    (hm ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hD : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D := fun p hp =>
    (hd ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hA : ∀p∈tsupport χ.func,(χ.func p)^2≤A*(p 2)^2 := fun p hp =>
    (div_le_iff₀ (sq_pos_of_pos (χ.positive hp))).mp
      ((ha ⟨p,hp,rfl⟩).trans (le_max_right _ _))
  refine ⟨B^3*(M+2*D+2*A),by positivity,fun f => ?_⟩
  refine (kernelLocalizedH1_norm_sq_le χ hinj M D A B hM0 hD0 hA0 hB0 hheight hM hD hA f).trans ?_
  rw [mul_assoc (B^3) (M+2*D+2*A)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB0 3)
  have hm0 := sq_nonneg ‖kernelSmoothTestsToL2 f‖
  have he0 := kernelDirichletEnergy_nonneg f
  nlinarith [mul_nonneg (by positivity : 0≤M+2*D) he0,mul_nonneg hA0 hm0]

def kernelLocalizedSchwartzLinear (χ : PositiveChartCutoff) :
    kernelSmoothTests →ₗ[ℂ] 𝓢(EuclideanSpatial,ℂ) where
  toFun := kernelLocalizedSchwartz χ
  map_add' f g := by
    ext p
    change χ.func p • (kernelTestField f p+kernelTestField g p)=_
    exact smul_add _ _ _
  map_smul' c f := by
    ext p
    change χ.func p • (c • kernelTestField f p)=c • (χ.func p • kernelTestField f p)
    exact smul_comm _ _ _

def kernelLocalizedH1Linear (χ : PositiveChartCutoff) : kernelSmoothTests →ₗ[ℂ] EuclideanH1 where
  toFun := kernelLocalizedH1 χ
  map_add' f g := by
    apply euclideanH1Embedding_injective
    simp only [map_add,kernelLocalizedH1_embedding]
    rw [show kernelLocalizedSchwartz χ (f+g)=kernelLocalizedSchwartz χ f+kernelLocalizedSchwartz χ g
      from (kernelLocalizedSchwartzLinear χ).map_add f g]
    rfl
  map_smul' c f := by
    apply euclideanH1Embedding_injective
    simp only [map_smul,kernelLocalizedH1_embedding,RingHom.id_apply]
    rw [show kernelLocalizedSchwartz χ (c•f)=c•kernelLocalizedSchwartz χ f
      from (kernelLocalizedSchwartzLinear χ).map_smul c f]
    rfl

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

namespace CubicEisenstein

abbrev KernelEnergyAmbient := WithLp 2 (KernelQuotientL2 × KernelGradientL2)

def kernelEnergyCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyAmbient :=
  (WithLp.linearEquiv 2 ℂ (KernelQuotientL2 × KernelGradientL2)).symm.toLinearMap.comp
    (kernelSmoothTestsToL2.prod kernelGradientLinear)

def kernelEnergyGraphSubmodule : Submodule ℂ KernelEnergyAmbient :=
  (LinearMap.range kernelEnergyCore).topologicalClosure

abbrev KernelEnergyGraph := kernelEnergyGraphSubmodule

instance kernelEnergyGraph_complete : CompleteSpace KernelEnergyGraph :=
  (LinearMap.range kernelEnergyCore).isClosed_topologicalClosure.completeSpace_coe

def kernelEnergyGraphCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyGraph :=
  kernelEnergyCore.codRestrict kernelEnergyGraphSubmodule
    (fun f => (LinearMap.range kernelEnergyCore).le_topologicalClosure ⟨f,rfl⟩)

lemma kernelEnergyGraphCore_dense : DenseRange kernelEnergyGraphCore := by
  rw [DenseRange,Subtype.dense_iff,←Set.range_comp]
  change closure (Set.range kernelEnergyCore)⊆closure (Set.range kernelEnergyCore)
  rfl

def kernelEnergyMass : KernelEnergyGraph →L[ℂ] KernelQuotientL2 :=
  (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

def kernelEnergyGradient : KernelEnergyGraph →L[ℂ] KernelGradientL2 :=
  (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

lemma kernelEnergyMass_core (f : kernelSmoothTests) :
    kernelEnergyMass (kernelEnergyGraphCore f)=kernelSmoothTestsToL2 f := rfl

lemma kernelEnergyGradient_core (f : kernelSmoothTests) :
    kernelEnergyGradient (kernelEnergyGraphCore f)=kernelGradientToL2 f := rfl

lemma kernelEnergyGraph_norm_sq (u : KernelEnergyGraph) :
    ‖u‖^2=‖kernelEnergyMass u‖^2+‖kernelEnergyGradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

lemma kernelEnergyGraphCore_norm_sq (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore f‖^2=‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f := by
  rw [kernelEnergyGraph_norm_sq,kernelEnergyMass_core,kernelEnergyGradient_core,
    kernelGradientToL2_norm_sq]

lemma kernelEnergyMass_dense : DenseRange kernelEnergyMass := by
  apply kernelSmoothTestsToL2_dense.mono
  rintro _ ⟨f,rfl⟩
  exact ⟨kernelEnergyGraphCore f,rfl⟩

lemma kernelLocalizedH1_graph_bound (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,∀f : kernelSmoothTests,
      ‖kernelLocalizedH1Linear χ f‖≤C*‖kernelEnergyGraphCore f‖ := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  refine ⟨Real.sqrt C,fun f => ?_⟩
  have hh := hbound f
  rw [←kernelEnergyGraphCore_norm_sq] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  change ‖kernelLocalizedH1 χ f‖^2≤(Real.sqrt C*‖kernelEnergyGraphCore f‖)^2
  rw [mul_pow,Real.sq_sqrt hC]
  exact hh

def kernelEnergyLocalize (χ : PositiveChartCutoff) : KernelEnergyGraph →L[ℂ] EuclideanH1 :=
  (kernelLocalizedH1Linear χ).extendOfNorm kernelEnergyGraphCore

lemma kernelEnergyLocalize_core (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (f : kernelSmoothTests) :
    kernelEnergyLocalize χ (kernelEnergyGraphCore f)=kernelLocalizedH1 χ f :=
  LinearMap.extendOfNorm_eq kernelEnergyGraphCore_dense (kernelLocalizedH1_graph_bound χ hinj) f

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

def kernelLocalizedL2Linear (χ : PositiveChartCutoff) : kernelSmoothTests →ₗ[ℂ] EuclideanL2 :=
  euclideanH1Embedding.toLinearMap.comp (kernelLocalizedH1Linear χ)

lemma kernelLocalizedL2Linear_apply (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    kernelLocalizedL2Linear χ f=(kernelLocalizedSchwartz χ f).toLp 2 volume := rfl

lemma kernelLocalizedL2_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelLocalizedL2Linear χ f‖^2≤C*‖kernelSmoothTestsToL2 f‖^2 := by
  obtain ⟨m,hm⟩ := χ.compact.bddAbove_image (χ.smooth.continuous.pow 2).continuousOn
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let M := max 0 m
  let B := max 0 b
  have hM0 : 0≤M := le_max_left _ _
  have hB0 : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M := fun p hp =>
    (hm ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  refine ⟨B^3*M,by positivity,fun f => ?_⟩
  let G : KernelQuotient→ℝ := fun q => M*‖f.1 q‖^2
  have hG : Integrable G (integralQuotientVolume globalKubotaKernel) :=
    ((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul M
  have hGn : ∀q,0≤G q := fun q => mul_nonneg hM0 (sq_nonneg _)
  have hS := χ.compact.measurableSet
  have hGI := kernelEuclideanProjection_volume_integrable (tsupport χ.func) hS χ.positive
    hinj B hB0 hheight G hG
  have hfi := ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq
  rw [kernelLocalizedL2Linear_apply,schwartz_toL2_norm_sq]
  calc
    (∫p,‖kernelLocalizedSchwartz χ f p‖^2) =
        ∫p in tsupport χ.func,‖kernelLocalizedSchwartz χ f p‖^2 := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro p hp
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).self_of_nhds
      change ‖χ.func p • kernelTestField f p‖^2=0
      simp only [hz,Pi.zero_apply,zero_smul,norm_zero,zero_pow (by decide : 2≠0)]
    _ ≤ ∫p in tsupport χ.func,G (kernelEuclideanProjection p) := by
      apply setIntegral_mono_on hfi.integrableOn hGI hS
      intro p hp
      change ‖χ.func p • kernelTestField f p‖^2≤M*‖kernelTestField f p‖^2
      simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
      exact mul_le_mul_of_nonneg_right (hM p hp) (sq_nonneg _)
    _ ≤ B^3*∫q,G q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_volume_integral_le (tsupport χ.func) hS χ.positive hinj
        B hB0 hheight G hG hGn
    _ = _ := by
      dsimp only [G]
      rw [integral_const_mul,←kernelSmoothTestsToL2_norm_sq,mul_assoc]

lemma kernelLocalizedL2_bound (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,∀f : kernelSmoothTests,
      ‖kernelLocalizedL2Linear χ f‖≤C*‖kernelSmoothTestsToL2 f‖ := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedL2_bounded χ hinj
  refine ⟨Real.sqrt C,fun f => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC]
  exact hbound f

def kernelL2Localize (χ : PositiveChartCutoff) : KernelQuotientL2 →L[ℂ] EuclideanL2 :=
  (kernelLocalizedL2Linear χ).extendOfNorm kernelSmoothTestsToL2

lemma kernelL2Localize_core (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (f : kernelSmoothTests) :
    kernelL2Localize χ (kernelSmoothTestsToL2 f)=(kernelLocalizedSchwartz χ f).toLp 2 volume :=
  LinearMap.extendOfNorm_eq kernelSmoothTestsToL2_dense (kernelLocalizedL2_bound χ hinj) f

lemma kernelEnergyLocalize_mass (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph) :
    euclideanH1Embedding (kernelEnergyLocalize χ u)=kernelL2Localize χ (kernelEnergyMass u) := by
  have heq : (fun v => euclideanH1Embedding (kernelEnergyLocalize χ v))=
      fun v => kernelL2Localize χ (kernelEnergyMass v) :=
    kernelEnergyGraphCore_dense.equalizer (by fun_prop) (by fun_prop) (by
      funext f
      simp only [Function.comp_apply,kernelEnergyLocalize_core χ hinj,
        kernelLocalizedH1_embedding,kernelEnergyMass_core,kernelL2Localize_core χ hinj])
  exact congrFun heq u

lemma kernelEnergyLocalize_eq_zero_of_mass_zero (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph)
    (hu : kernelEnergyMass u=0) : kernelEnergyLocalize χ u=0 := by
  apply euclideanH1Embedding_eq_zero
  rw [kernelEnergyLocalize_mass χ hinj u,hu,map_zero]

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
namespace SecondPassArithmetic

section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

def reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) : Finset (CubeCoordinates ι) :=
  (((v₁.support ∪ v₂.support).powerset).product
    ((v₁.support ∪ v₂.support).powerset)).image
    (fun A => ⟨v₁,v₂,A.2,A.1⟩)

def reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) : Finset (CubeCoordinates ι) :=
  (Q.product Q).biUnion (fun v => reopenedCubeFiber v.2 v.1)

def reopenedPairCoefficient (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (b : CubeCoordinates ι) (_C : Finset ι) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  star (β I b.rightExponent)*β I b.leftExponent

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

end SecondPassArithmetic

namespace CubicEisenstein
open MeasureTheory
open scoped SchwartzMap

lemma euclideanIntegral_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     ∫p,g p) =
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanIntegrable_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Integrable g volume) ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeIntegral_eq_borel (g : EuclideanSpatial→ℝ) :
    (∫p,g p)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) :=
  euclideanIntegral_borel_transport inferInstance inferInstance g

lemma euclideanNativeIntegrable_iff_borel (g : EuclideanSpatial→ℝ) :
    Integrable g volume ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) :=
  euclideanIntegrable_borel_transport inferInstance inferInstance g

def euclideanLp_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) := by
  have he := hm.measurable_eq
  subst m
  exact LinearIsometryEquiv.refl ℂ _

def euclideanNativeLpBorelEquiv : EuclideanL2 ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) :=
  euclideanLp_borel_transport inferInstance inferInstance

lemma euclideanLp_borel_transport_schwartz (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanLp_borel_transport m hm
      (letI : MeasurableSpace EuclideanSpatial := m
       letI : BorelSpace EuclideanSpatial := hm
       f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeLpBorelEquiv_schwartz (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanNativeLpBorelEquiv (f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) :=
  euclideanLp_borel_transport_schwartz inferInstance inferInstance f

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

namespace CubicEisenstein
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance instMeasurableSpaceEuclideanSpatial_1 : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance instBorelSpaceEuclideanSpatial_1 : BorelSpace EuclideanSpatial := ⟨rfl⟩

def kernelLocalizedRealTest (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) : C1c (E := EuclideanSpatial) :=
  ⟨fun p => projection (kernelLocalizedField χ f p),
    (projection.contDiff.comp (kernelLocalizedField_smooth χ f)).of_le (by simp),
    (kernelLocalizedField_compact χ f).comp_left (map_zero projection)⟩

lemma sourceC1c_toL2_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2 («μ» := volume) g‖^2=∫p,‖g.1 p‖^2 := by
  calc
    ‖toL2 («μ» := volume) g‖^2=inner ℝ (toL2 («μ» := volume) g) (toL2 («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2 («μ» := volume) g p) (toL2 («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)
        (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma sourceC1c_toL2Grad_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2Grad («μ» := volume) g‖^2=∫p,‖grad g.1 p‖^2 := by
  calc
    ‖toL2Grad («μ» := volume) g‖^2=inner ℝ (toL2Grad («μ» := volume) g) (toL2Grad («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2Grad («μ» := volume) g p) (toL2Grad («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_grad_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)
        (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma kernelLocalizedRealTest_grad_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) (p : EuclideanSpatial) :
    ‖grad (kernelLocalizedRealTest χ f projection).1 p‖^2≤
      ∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2 := by
  have hdiff : DifferentiableAt ℝ (kernelLocalizedField χ f) p :=
    ((kernelLocalizedField_smooth χ f).differentiable (by simp)).differentiableAt
  have hd := (projection.hasFDerivAt.comp p hdiff.hasFDerivAt).fderiv
  change fderiv ℝ (kernelLocalizedRealTest χ f projection).1 p=_ at hd
  unfold grad
  rw [LinearIsometryEquiv.norm_map,hd,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual]
  apply Finset.sum_le_sum
  intro j hj
  have hh := hprojection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
  change (projection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)))^2≤_
  simp only [Real.norm_eq_abs] at hh
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2

lemma kernelLocalizedRealTest_energy_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) :
    ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
      ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤
        ‖kernelLocalizedH1 χ f‖^2 := by
  let g := kernelLocalizedRealTest χ f projection
  rw [sourceC1c_toL2_norm_sq,sourceC1c_toL2Grad_norm_sq,kernelLocalizedH1_norm_sq,
    ←integral_add (memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq]
  rw [euclideanNativeIntegral_eq_borel]
  have hden := (euclideanNativeIntegrable_iff_borel (kernelLocalizedDensity χ f)).mp
    (kernelLocalizedDensity_integrable χ f)
  apply integral_mono
    ((memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq.add
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq)
    hden
  intro p
  have hm := hprojection (kernelLocalizedField χ f p)
  have hg := kernelLocalizedRealTest_grad_le χ f projection hprojection p
  change ‖projection (kernelLocalizedField χ f p)‖^2+_≤_
  unfold kernelLocalizedDensity
  nlinarith [norm_nonneg (projection (kernelLocalizedField χ f p)),norm_nonneg (kernelLocalizedField χ f p)]

lemma kernelLocalizedRealTest_support (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) :
    Function.support (kernelLocalizedRealTest χ f projection).1⊆tsupport χ.func := by
  intro p hp
  apply kernelLocalizedField_tsupport χ f
  apply subset_tsupport
  intro hz
  apply hp
  change projection (kernelLocalizedField χ f p)=0
  rw [hz,map_zero]

theorem kernelLocalizedReal_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖)
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)) '' family)) := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  have hCB : 0≤C*B := mul_nonneg hC hB
  have henergy : ∀f∈family,
      ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
        ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤C*B := by
    intro f hf
    exact (kernelLocalizedRealTest_energy_le χ f projection hprojection).trans
      ((hbound f).trans (mul_le_mul_of_nonneg_left (hfamily f hf) hC))
  have hh := euclidean_C1c_family_precompact (tsupport χ.func) χ.compact
    ((fun f => kernelLocalizedRealTest χ f projection) '' family) (Real.sqrt (C*B))
    (by
      rintro _ ⟨f,hf,rfl⟩
      exact kernelLocalizedRealTest_support χ f projection)
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection))])
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection))])
  simpa only [Set.image_image,Function.comp_def] using hh

abbrev RellichRealL2 := Lp ℝ 2 (volume : Measure EuclideanSpatial)
abbrev RellichComplexL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)

def kernelComplexL2Assemble : (RellichRealL2 × RellichRealL2) →L[ℝ] RellichComplexL2 :=
  (Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.fst ℝ RellichRealL2 RellichRealL2)+
  (Complex.I • Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.snd ℝ RellichRealL2 RellichRealL2)

lemma kernelComplexL2Assemble_localized (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    kernelComplexL2Assemble
      (toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
        toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM))=
      (kernelLocalizedSchwartz χ f).toLp 2 volume := by
  let r := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM)
  let i := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)
  let R := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) r
  let I := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) i
  have hr : (r : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).re :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM).2).coeFn_toLp
  have hi : (i : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).im :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM).2).coeFn_toLp
  change R+Complex.I•I=(kernelLocalizedSchwartz χ f).toLp 2 volume
  apply Lp.ext
  filter_upwards [hr,hi,Complex.ofRealCLM.coeFn_compLpL r,Complex.ofRealCLM.coeFn_compLpL i,
    Lp.coeFn_add R (Complex.I•I),Lp.coeFn_smul Complex.I I,
    (kernelLocalizedSchwartz χ f).coeFn_toLp 2 volume] with p hrp hip hR hI ha hs hf
  rw [ha,Pi.add_apply,hs,Pi.smul_apply,hR,hI,hrp,hip,hf]
  change ((kernelLocalizedField χ f p).re:ℂ)+Complex.I*((kernelLocalizedField χ f p).im:ℂ)=kernelLocalizedField χ f p
  simpa only [mul_comm] using Complex.re_add_im (kernelLocalizedField χ f p)

theorem kernelLocalizedComplex_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => (kernelLocalizedSchwartz χ f).toLp 2 volume) '' family)) := by
  have hr := kernelLocalizedReal_family_precompact χ hinj Complex.reCLM
    (fun z => by change ‖z.re‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z) family B hB hfamily
  have hi := kernelLocalizedReal_family_precompact χ hinj Complex.imCLM
    (fun z => by change ‖z.im‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm z) family B hB hfamily
  have hc := (hr.prod hi).image kernelComplexL2Assemble.continuous
  apply hc.closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
    toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)),?_,?_⟩
  · exact ⟨subset_closure ⟨f,hf,rfl⟩,subset_closure ⟨f,hf,rfl⟩⟩
  · exact kernelComplexL2Assemble_localized χ f

theorem kernelLocalizedNative_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)) := by
  have hc := kernelLocalizedComplex_family_precompact χ hinj family B hB hfamily
  apply (hc.image euclideanNativeLpBorelEquiv.symm.continuous).closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(kernelLocalizedSchwartz χ f).toLp 2 volume,subset_closure ⟨f,hf,rfl⟩,?_⟩
  apply euclideanNativeLpBorelEquiv.injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [kernelL2Localize_core χ hinj]
  exact (euclideanNativeLpBorelEquiv_schwartz _).symm

def kernelEnergyLocalizeL2 (χ : PositiveChartCutoff) : KernelEnergyGraph →L[ℂ] EuclideanL2 :=
  (kernelL2Localize χ).comp kernelEnergyMass

theorem kernelEnergyLocalizeL2_isCompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    IsCompactOperator (kernelEnergyLocalizeL2 χ) := by
  let family : Set kernelSmoothTests := {f | ‖kernelEnergyGraphCore f‖≤2}
  let C := closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)
  have hc : IsCompact C := kernelLocalizedNative_family_precompact χ hinj family 4 (by norm_num) (by
    intro f hf
    rw [←kernelEnergyGraphCore_norm_sq]
    change ‖kernelEnergyGraphCore f‖≤2 at hf
    nlinarith [norm_nonneg (kernelEnergyGraphCore f)])
  let T := kernelEnergyLocalizeL2 χ
  have hclosed : IsClosed (T ⁻¹' C) := hc.isClosed.preimage T.continuous
  have hsub : closure (kernelEnergyGraphCore ''
      (kernelEnergyGraphCore ⁻¹' Metric.ball (0 : KernelEnergyGraph) 2))⊆T ⁻¹' C := by
    apply hclosed.closure_subset_iff.mpr
    rintro _ ⟨f,hf,rfl⟩
    change kernelL2Localize χ (kernelEnergyMass (kernelEnergyGraphCore f))∈C
    rw [kernelEnergyMass_core]
    apply subset_closure
    refine ⟨f,?_,rfl⟩
    change ‖kernelEnergyGraphCore f‖≤2
    exact le_of_lt (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hf)
  have hball : Metric.ball (0 : KernelEnergyGraph) 2⊆T ⁻¹' C := by
    intro u hu
    exact hsub (kernelEnergyGraphCore_dense.subset_closure_image_preimage_of_isOpen
      Metric.isOpen_ball hu)
  refine ⟨C,hc,?_⟩
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : KernelEnergyGraph) (by norm_num : (0 : ℝ)<2)) hball

end CubicEisenstein

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

def kernelLiftedCutoff (χ : PositiveChartCutoff) (w : HyperbolicSpace) : ℝ :=
  χ.func (hyperbolicEuclideanCoordinates w)

lemma kernelLiftedCutoff_continuous (χ : PositiveChartCutoff) : Continuous (kernelLiftedCutoff χ) :=
  χ.smooth.continuous.comp hyperbolicEuclideanCoordinates_continuous

lemma kernelLiftedCutoff_compact (χ : PositiveChartCutoff) : HasCompactSupport (kernelLiftedCutoff χ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (χ.compact.image_of_continuousOn (fun p hp =>
      (euclideanToHyperbolic_contMDiffAt p (χ.positive hp)).continuousAt.continuousWithinAt))
  intro w hw
  refine ⟨hyperbolicEuclideanCoordinates w,?_,euclideanToHyperbolic_coordinates w⟩
  exact subset_tsupport χ.func hw

lemma kernelLiftedCutoff_bounded (χ : PositiveChartCutoff) :
    ∃C : ℝ,∀w,‖kernelLiftedCutoff χ w‖≤C := by
  obtain ⟨w,hw⟩ := (kernelLiftedCutoff_continuous χ).norm.exists_forall_ge_of_hasCompactSupport
    (kernelLiftedCutoff_compact χ).norm
  exact ⟨_,hw⟩

lemma kernelCutoffGradient_memLp (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    MemLp (fun w => kernelLiftedCutoff χ w • g w) 2 KernelFundamentalVolume := by
  obtain ⟨C,hC⟩ := kernelLiftedCutoff_bounded χ
  have hm : AEStronglyMeasurable (fun w => kernelLiftedCutoff χ w • g w) KernelFundamentalVolume :=
    (kernelLiftedCutoff_continuous χ).aestronglyMeasurable.smul (Lp.aestronglyMeasurable g)
  refine (Lp.memLp g).of_le_mul (c := C) hm (Eventually.of_forall (fun w => ?_))
  change ‖kernelLiftedCutoff χ w • g w‖≤C*‖g w‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC w) (norm_nonneg (g w))

def kernelCutoffGradient (χ : PositiveChartCutoff) (g : KernelGradientL2) : KernelGradientL2 :=
  (kernelCutoffGradient_memLp χ g).toLp (fun w => kernelLiftedCutoff χ w • g w)

lemma kernelCutoffGradient_coe (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    (kernelCutoffGradient χ g : HyperbolicSpace→EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelLiftedCutoff χ w • g w := (kernelCutoffGradient_memLp χ g).coeFn_toLp

def kernelCutoffGradientLinear (χ : PositiveChartCutoff) : KernelGradientL2 →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelCutoffGradient χ
  map_add' g h := by
    apply Lp.ext
    filter_upwards [kernelCutoffGradient_coe χ (g+h),kernelCutoffGradient_coe χ g,
      kernelCutoffGradient_coe χ h,Lp.coeFn_add g h,
      Lp.coeFn_add (kernelCutoffGradient χ g) (kernelCutoffGradient χ h)] with w hgh hg hh ha ha'
    simp only [hgh,ha',ha,Pi.add_apply,hg,hh,smul_add]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [kernelCutoffGradient_coe χ (c•g),kernelCutoffGradient_coe χ g,
      Lp.coeFn_smul c g,Lp.coeFn_smul c (kernelCutoffGradient χ g)] with w hcg hg ha ha'
    simp only [RingHom.id_apply,hcg,ha',ha,Pi.smul_apply,hg]
    exact smul_comm _ _ _

lemma kernelCutoffGradient_bound (χ : PositiveChartCutoff) :
    ∃C : ℝ,∀g : KernelGradientL2,‖kernelCutoffGradientLinear χ g‖≤C*‖g‖ := by
  obtain ⟨C,hC⟩ := kernelLiftedCutoff_bounded χ
  refine ⟨C,fun g => ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [kernelCutoffGradient_coe χ g] with w hw
  change ‖kernelCutoffGradient χ g w‖≤_
  rw [hw,norm_smul]
  exact mul_le_mul_of_nonneg_right (hC w) (norm_nonneg _)

def kernelCutoffGradientCLM (χ : PositiveChartCutoff) : KernelGradientL2 →L[ℂ] KernelGradientL2 :=
  (kernelCutoffGradientLinear χ).mkContinuousOfExistsBound (kernelCutoffGradient_bound χ)

lemma kernelCutoffGradient_norm_sq (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    ‖kernelCutoffGradientCLM χ g‖^2=
      ∫w,(kernelLiftedCutoff χ w)^2*‖g w‖^2∂KernelFundamentalVolume := by
  calc
    ‖kernelCutoffGradientCLM χ g‖^2=inner ℝ (kernelCutoffGradientCLM χ g) (kernelCutoffGradientCLM χ g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫w,inner ℝ (kernelCutoffGradient χ g w) (kernelCutoffGradient χ g w)∂KernelFundamentalVolume := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [kernelCutoffGradient_coe χ g] with w hw
      rw [hw,real_inner_self_eq_norm_sq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

lemma kernelCutoffGradient_core_norm_sq (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2=
      ∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂KernelFundamentalVolume := by
  rw [kernelCutoffGradient_norm_sq]
  apply integral_congr_ae
  filter_upwards [kernelGradientToL2_coe f] with w hw
  rw [hw,kernelGradientAt_norm_sq]

lemma kernelLocalizedField_reverse_energy (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)≤
      2*(p 2)^2*kernelLocalizedDensity χ f p+
      2*(p 2)^2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
  have hsum : (χ.func p)^2*(∑j : Fin 3,‖fderiv ℝ (kernelTestField f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤
      2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)+
      2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
    simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have he := kernelLocalizedField_fderiv χ f p hp (EuclideanSpace.basisFun (Fin 3) ℝ j)
    have he' : χ.func p • fderiv ℝ (kernelTestField f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)=
        fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)-
        fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p := by rw [he]; abel
    have hb := complex_norm_add_sq_le
      (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
      (- (fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p))
    rw [←sub_eq_add_neg,←he'] at hb
    simpa only [norm_smul,norm_neg,mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc] using hb
  have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
  have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
  rw [kernelTestEnergyDensity_eq_partials,hv]
  simp only [kernelTestPartial,hc]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (p 2))
  unfold kernelLocalizedDensity
  nlinarith [mul_nonneg (sq_nonneg (p 2)) (sq_nonneg ‖kernelLocalizedField χ f p‖)]

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal

lemma kernelLocalizedDensity_nonneg (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : 0≤kernelLocalizedDensity χ f p := by
  unfold kernelLocalizedDensity
  positivity

lemma hyperbolicVolume_le_densityBound (S : Set EuclideanSpatial) (hS : MeasurableSet S)
    (hpos : S⊆euclideanUpperHalf) (H : ℝ)
    (hH : ∀p∈S,((p 2)^3)⁻¹≤H) :
    hyperbolicEuclideanVolume.restrict S≤ENNReal.ofReal H • volume.restrict S := by
  rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
    Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos]
  have hh : hyperbolicDensity≤ᵐ[volume.restrict S] (fun _ => ENNReal.ofReal H) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    exact ENNReal.ofReal_le_ofReal (hH p hp)
  simpa only [MeasureTheory.withDensity_const] using MeasureTheory.withDensity_mono hh

instance hyperbolicVolume_finiteOnCompacts : IsFiniteMeasureOnCompacts hyperbolicVolume where
  lt_top_of_isCompact K hK := by
    let S := hyperbolicEuclideanCoordinates '' K
    have hSK : IsCompact S := hK.image hyperbolicEuclideanCoordinates_continuous
    have hS : MeasurableSet S := hSK.measurableSet
    have hpos : S⊆euclideanUpperHalf := by
      rintro p ⟨w,hw,rfl⟩
      exact hyperbolicHeight_pos w
    have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) S :=
      (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
        (fun p hp => pow_ne_zero _ (ne_of_gt (hpos hp)))
    obtain ⟨H,hH⟩ := hSK.bddAbove_image hrho
    have hb := hyperbolicVolume_le_densityBound S hS hpos H (fun p hp => hH ⟨p,hp,rfl⟩)
    have hm : hyperbolicEuclideanVolume S< (∞ : ℝ≥0∞) := by
      have hbu := Measure.le_iff.mp hb Set.univ MeasurableSet.univ
      simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Measure.smul_apply,
        smul_eq_mul] at hbu
      exact hbu.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSK.measure_lt_top)
    have heq : euclideanToHyperbolic ⁻¹' K=ᵐ[hyperbolicEuclideanVolume]S := by
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      apply propext
      constructor
      · intro h
        exact ⟨euclideanToHyperbolic p,h,hyperbolicEuclideanCoordinates_toHyperbolic p hp⟩
      · rintro ⟨w,hw,rfl⟩
        show hyperbolicEuclideanCoordinates w ∈ euclideanToHyperbolic ⁻¹' K
        simpa only [Set.mem_preimage,euclideanToHyperbolic_coordinates] using hw
    rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable hK.measurableSet,
      measure_congr heq]
    exact hm

lemma integrable_sq_mul_of_compact (a b : HyperbolicSpace → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : HasCompactSupport a) :
    Integrable (fun w => (a w)^2*b w) hyperbolicVolume := by
  have hs : HasCompactSupport (fun w => (a w)^2) :=
    hc.comp_left (g := fun x : ℝ => x^2) (by simp)
  exact ((ha.pow 2).mul hb).integrable_of_hasCompactSupport hs.mul_right

lemma kernelLiftedCutoffEnergy_integrable (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    Integrable (fun w => (kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w) hyperbolicVolume :=
  integrable_sq_mul_of_compact (kernelLiftedCutoff χ) (kernelTestEnergyDensity f)
    (kernelLiftedCutoff_continuous χ) (kernelTestEnergyDensity_continuous f)
    (kernelLiftedCutoff_compact χ)

lemma kernelLiftedCutoffEnergy_integral (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    (∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂hyperbolicVolume)=
      ∫p,(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
  rw [hyperbolicVolume,integral_map euclideanToHyperbolic_measurable.aemeasurable
    (kernelLiftedCutoffEnergy_integrable χ f).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
  simp only [kernelLiftedCutoff,hyperbolicEuclideanCoordinates_toHyperbolic p hp]

lemma kernelCutoffGradient_core_estimate (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (B D H : ℝ) (_hB : 0≤B) (hD : 0≤D) (hH : 0≤H)
    (hheight : ∀p∈tsupport χ.func,p 2≤B)
    (hderiv : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H)
    (f : kernelSmoothTests) :
    ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2≤
      2*B^2*(H*‖kernelLocalizedH1 χ f‖^2+D*‖kernelSmoothTestsToL2 f‖^2) := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hpos : S⊆euclideanUpperHalf := χ.positive
  have hmeasure := hyperbolicVolume_le_densityBound S hS hpos H hdensity
  have hloc : IntegrableOn (kernelLocalizedDensity χ f) S hyperbolicEuclideanVolume :=
    (((kernelLocalizedDensity_integrable χ f).integrableOn).smul_measure
      (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top).mono_measure hmeasure
  have hmass : IntegrableOn (fun p => ‖kernelTestField f p‖^2) S hyperbolicEuclideanVolume := by
    exact (kernelEuclideanProjection_measurePreserving_on S hS hpos hinj).integrable_comp_of_integrable
      ((kernelSmoothTests_memLp f).norm.integrable_sq.integrableOn)
  have hweight : IntegrableOn (fun p => (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p))
      S hyperbolicEuclideanVolume := by
    have hh := (kernelLiftedCutoffEnergy_integrable χ f).comp_measurable euclideanToHyperbolic_measurable
    have heq : (fun p => (kernelLiftedCutoff χ (euclideanToHyperbolic p))^2*
        kernelTestEnergyDensity f (euclideanToHyperbolic p))=ᵐ[hyperbolicEuclideanVolume]
        fun p => (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p) := by
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      simp only [kernelLiftedCutoff,hyperbolicEuclideanCoordinates_toHyperbolic p hp]
    exact (hh.congr heq).integrableOn
  have hlocBound : (∫p in S,kernelLocalizedDensity χ f p∂hyperbolicEuclideanVolume)≤
      H*‖kernelLocalizedH1 χ f‖^2 := by
    have hh := integral_mono_measure hmeasure
      (Eventually.of_forall (kernelLocalizedDensity_nonneg χ f))
      (((kernelLocalizedDensity_integrable χ f).integrableOn).smul_measure
        (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top)
    rw [integral_smul_measure,ENNReal.toReal_ofReal hH] at hh
    rw [kernelLocalizedH1_norm_sq]
    exact hh.trans (mul_le_mul_of_nonneg_left
      (setIntegral_le_integral (kernelLocalizedDensity_integrable χ f)
        (Eventually.of_forall (kernelLocalizedDensity_nonneg χ f))) hH)
  rw [kernelCutoffGradient_core_norm_sq]
  calc
    _ ≤ ∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂hyperbolicVolume :=
      setIntegral_le_integral (kernelLiftedCutoffEnergy_integrable χ f)
        (Eventually.of_forall (fun w => mul_nonneg (sq_nonneg _) (kernelTestEnergyDensity_nonneg f w)))
    _ = ∫p in S,(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
      rw [kernelLiftedCutoffEnergy_integral]
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro p hp
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).self_of_nhds
      simp only [hz,Pi.zero_apply,zero_pow (by decide : 2≠0),zero_mul]
    _ ≤ ∫p in S,(2*B^2*kernelLocalizedDensity χ f p+2*B^2*D*‖kernelTestField f p‖^2)
        ∂hyperbolicEuclideanVolume := by
      apply setIntegral_mono_on hweight ((hloc.const_mul _).add (hmass.const_mul _)) hS
      intro p hp
      refine (kernelLocalizedField_reverse_energy χ f p (hpos hp)).trans ?_
      simp only [Pi.add_apply]
      gcongr
      · exact kernelLocalizedDensity_nonneg _ _ _
      · exact (hpos hp).le
      · exact hheight p hp
      · exact (hpos hp).le
      · exact hheight p hp
      · exact hderiv p hp
    _ = 2*B^2*((∫p in S,kernelLocalizedDensity χ f p∂hyperbolicEuclideanVolume)+
        D*(∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)) := by
      rw [integral_add (hloc.const_mul _) (hmass.const_mul _),integral_const_mul,integral_const_mul]
      ring
    _ ≤ _ := by
      gcongr
      exact kernelLocalMass_le S hS hpos hinj f

lemma kernelCutoffGradient_core_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2≤
        C*(‖kernelLocalizedH1 χ f‖^2+‖kernelSmoothTestsToL2 f‖^2) := by
  have hgrad : Continuous (fun p : EuclideanSpatial =>
      ∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) := by
    apply continuous_finsetSum
    intro j hj
    exact (((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) (tsupport χ.func) :=
    (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.positive hp)))
  obtain ⟨d,hd⟩ := χ.compact.bddAbove_image hgrad.continuousOn
  obtain ⟨r,hr⟩ := χ.compact.bddAbove_image hrho
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let D := max 0 d
  let H := max 0 r
  let B := max 0 b
  have hD : 0≤D := le_max_left _ _
  have hH : 0≤H := le_max_left _ _
  have hB : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hderiv : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D := fun p hp =>
    (hd ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H := fun p hp =>
    (hr ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  refine ⟨2*B^2*(H+D),by positivity,fun f => ?_⟩
  refine (kernelCutoffGradient_core_estimate χ hinj B D H hB hD hH hheight hderiv hdensity f).trans ?_
  rw [mul_assoc (2*B^2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [mul_nonneg hH (sq_nonneg ‖kernelSmoothTestsToL2 f‖),
    mul_nonneg hD (sq_nonneg ‖kernelLocalizedH1 χ f‖)]

lemma kernelEnergyCutoffGradient_eq_zero (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph)
    (hu : kernelEnergyMass u=0) : kernelCutoffGradientCLM χ (kernelEnergyGradient u)=0 := by
  obtain ⟨C,hC,hbound⟩ := kernelCutoffGradient_core_bounded χ hinj
  have hh : ‖kernelCutoffGradientCLM χ (kernelEnergyGradient u)‖^2≤
      C*(‖kernelEnergyLocalize χ u‖^2+‖kernelEnergyMass u‖^2) :=
    kernelEnergyGraphCore_dense.induction_on u (isClosed_le (by fun_prop) (by fun_prop))
      (fun f => by simpa only [kernelEnergyGradient_core,kernelEnergyMass_core,
        kernelEnergyLocalize_core χ hinj] using hbound f)
  rw [kernelEnergyLocalize_eq_zero_of_mass_zero χ hinj u hu,hu] at hh
  have hz : ‖kernelCutoffGradientCLM χ (kernelEnergyGradient u)‖=0 := by simpa using hh
  exact norm_eq_zero.mp hz

lemma kernelCutoffGradient_faithful (g : KernelGradientL2)
    (hg : ∀χ : PositiveChartCutoff,
      Set.InjOn kernelEuclideanProjection (tsupport χ.func) → kernelCutoffGradientCLM χ g=0) : g=0 := by
  let Cutoff := {χ : PositiveChartCutoff // Set.InjOn kernelEuclideanProjection (tsupport χ.func)}
  let U : Cutoff→Set HyperbolicSpace := fun χ => {w | kernelLiftedCutoff χ.1 w≠0}
  have hU : ∀χ,IsOpen (U χ) := fun χ =>
    isOpen_ne.preimage (kernelLiftedCutoff_continuous χ.1)
  have hcover : (Set.univ : Set HyperbolicSpace)⊆⋃χ,U χ := by
    intro w hw
    obtain ⟨χ,hχ,hrange,hinj⟩ :=
      kernelChartCutoff_exists (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
    refine Set.mem_iUnion.mpr ⟨⟨χ,hinj⟩,?_⟩
    change χ.func (hyperbolicEuclideanCoordinates w)≠0
    rw [hχ]
    norm_num
  obtain ⟨r,hr,hcov⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let : Countable r := hr.to_subtype
  have heach (χ : Cutoff) : ∀ᵐw∂KernelFundamentalVolume,kernelLiftedCutoff χ.1 w • g w=0 := by
    have hzero := hg χ.1 χ.2
    change kernelCutoffGradient χ.1 g=0 at hzero
    filter_upwards [kernelCutoffGradient_coe χ.1 g,
      (Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 3)) (p := (2:ℝ≥0∞)) («μ» := KernelFundamentalVolume))]
      with w hw hz
    rw [hzero] at hw
    exact hw.symm.trans hz
  have hall : ∀ᵐw∂KernelFundamentalVolume,∀χ : r,kernelLiftedCutoff χ.1.1 w • g w=0 :=
    ae_all_iff.mpr (fun χ => heach χ.1)
  apply Lp.ext
  filter_upwards [hall,
    (Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 3)) (p := (2:ℝ≥0∞)) («μ» := KernelFundamentalVolume))]
    with w hw hz
  obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ w))
  obtain ⟨hχr,hχw⟩ := Set.mem_iUnion.mp hχ
  have hsm := hw ⟨χ,hχr⟩
  have hne : kernelLiftedCutoff χ.1 w≠0 := hχw
  exact ((smul_eq_zero.mp hsm).resolve_left hne).trans hz.symm

theorem kernelEnergyMass_eq_zero (u : KernelEnergyGraph) (hu : kernelEnergyMass u=0) : u=0 := by
  have hgrad : kernelEnergyGradient u=0 :=
    kernelCutoffGradient_faithful _ (fun χ hinj => kernelEnergyCutoffGradient_eq_zero χ hinj u hu)
  apply norm_eq_zero.mp
  have hn := kernelEnergyGraph_norm_sq u
  simp only [hu,hgrad,norm_zero,zero_pow (by decide : 2≠0),add_zero] at hn
  nlinarith [norm_nonneg u]

theorem kernelEnergyMass_injective : Function.Injective kernelEnergyMass := by
  intro u v huv
  apply sub_eq_zero.mp
  apply kernelEnergyMass_eq_zero
  rw [map_sub,huv,sub_self]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff InnerProductSpace

lemma kernelEnergyGraph_inner (u v : KernelEnergyGraph) :
    inner ℂ u v=inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v) := rfl

def kernelVariationalSolution : KernelQuotientL2 →L[ℂ] KernelEnergyGraph :=
  kernelEnergyMass.adjoint

lemma kernelVariationalSolution_equation (F : KernelQuotientL2) (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyMass (kernelVariationalSolution F)) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient (kernelVariationalSolution F)) (kernelEnergyGradient v)=
        inner ℂ F (kernelEnergyMass v) := by
  rw [←kernelEnergyGraph_inner]
  exact kernelEnergyMass.adjoint_inner_left v F

lemma kernelVariationalSolution_unique (F : KernelQuotientL2) (u : KernelEnergyGraph)
    (hu : ∀v : KernelEnergyGraph,
      inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ F (kernelEnergyMass v)) :
    u=kernelVariationalSolution F := by
  apply ext_inner_right ℂ
  intro v
  rw [kernelEnergyGraph_inner,kernelEnergyGraph_inner]
  exact (hu v).trans (kernelVariationalSolution_equation F v).symm

def kernelVariationalResolvent : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  kernelEnergyMass.comp kernelVariationalSolution

lemma kernelVariationalResolvent_injective : Function.Injective kernelVariationalResolvent := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro F hF
  change kernelEnergyMass (kernelVariationalSolution F)=0 at hF
  have hu : kernelVariationalSolution F=0 := kernelEnergyMass_injective (by
    rw [map_zero]
    exact hF)
  have he : (fun g : KernelQuotientL2 => inner ℂ F g)=(fun _ => (0 : ℂ)) :=
    kernelEnergyMass_dense.equalizer (by fun_prop) continuous_const (by
      funext v
      change inner ℂ F (kernelEnergyMass v)=0
      rw [←kernelEnergyMass.adjoint_inner_left]
      change inner ℂ (kernelVariationalSolution F) v=0
      rw [hu,inner_zero_left])
  exact inner_self_eq_zero.mp (congrFun he F)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelLaplacianEquation : (KernelQuotientL2 × KernelQuotientL2) →L[ℂ] KernelQuotientL2 :=
  kernelVariationalResolvent.comp ((ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)+
    (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelQuotientL2))-
      (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)

def kernelLaplacianGraph : Submodule ℂ (KernelQuotientL2 × KernelQuotientL2) :=
  kernelLaplacianEquation.ker

lemma mem_kernelLaplacianGraph (u f : KernelQuotientL2) :
    (u,f)∈kernelLaplacianGraph ↔ kernelVariationalResolvent (u+f)=u := by
  change kernelVariationalResolvent (u+f)-u=0 ↔ _
  exact sub_eq_zero

lemma kernelLaplacianGraph_unique (x : KernelQuotientL2 × KernelQuotientL2)
    (hx : x∈kernelLaplacianGraph) (hz : x.1=0) : x.2=0 := by
  have hh := (mem_kernelLaplacianGraph x.1 x.2).mp hx
  rw [hz,zero_add] at hh
  apply kernelVariationalResolvent_injective
  rw [map_zero]
  exact hh

def kernelEnergyLaplacian : KernelQuotientL2 →ₗ.[ℂ] KernelQuotientL2 :=
  kernelLaplacianGraph.toLinearPMap

lemma kernelEnergyLaplacian_graph : kernelEnergyLaplacian.graph=kernelLaplacianGraph :=
  Submodule.toLinearPMap_graph_eq _ kernelLaplacianGraph_unique

lemma kernelEnergyLaplacian_resolvent_relation (u : kernelEnergyLaplacian.domain) :
    kernelVariationalResolvent (kernelEnergyLaplacian u+u)=u := by
  have hh := kernelEnergyLaplacian.mem_graph u
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hh
  simpa only [add_comm] using hh

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

section

lemma compact_of_norm_le_compact {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : E→L[ℂ]F) (g : E→L[ℂ]G) (hg : IsCompactOperator g)
    (hbound : ∃C : ℝ,∀x,‖f x‖≤C*‖g x‖) : IsCompactOperator f := by
  let S := (LinearMap.range g.toLinearMap).topologicalClosure
  have hS : IsClosed (S : Set G) := (LinearMap.range g.toLinearMap).isClosed_topologicalClosure
  have hmem : ∀x,g x∈S := fun x => (LinearMap.range g.toLinearMap).le_topologicalClosure ⟨x,rfl⟩
  let e : E→L[ℂ]S := g.codRestrict S hmem
  have he : DenseRange e := by
    rw [DenseRange,Subtype.dense_iff,←Set.range_comp]
    change closure (Set.range g)⊆closure (Set.range g)
    exact Set.Subset.rfl
  have hec : IsCompactOperator e := hg.codRestrict hmem hS
  let q : S→L[ℂ]F := f.toLinearMap.extendOfNorm e.toLinearMap
  have hfq : f=q.comp e := by
    ext x
    exact (LinearMap.extendOfNorm_eq he hbound x).symm
  rw [hfq]
  exact hec.clm_comp q

lemma compact_finite_pi {E G ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T : ι→E→L[ℂ]G) (hT : ∀i,IsCompactOperator (T i)) :
    IsCompactOperator (ContinuousLinearMap.pi T) := by
  let K : ι→Set G := fun i => closure ((T i) '' Metric.ball (0 : E) 1)
  have hK : ∀i,IsCompact (K i) := fun i => (hT i).isCompact_closure_image_ball 1
  refine ⟨Set.pi Set.univ K,isCompact_univ_pi hK,?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ)<1))
  intro x hx
  exact fun i hi => subset_closure ⟨x,hx,rfl⟩

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

def kernelChartCore (χ : PositiveChartCutoff) : Set EuclideanSpatial :=
  {p | (1/2 : ℝ)<χ.func p}

def kernelChartCoreImage (χ : PositiveChartCutoff) : Set KernelQuotient :=
  kernelEuclideanProjection '' kernelChartCore χ

lemma kernelChartCore_open (χ : PositiveChartCutoff) : IsOpen (kernelChartCore χ) :=
  isOpen_lt continuous_const χ.smooth.continuous

lemma kernelChartCore_subset (χ : PositiveChartCutoff) : kernelChartCore χ⊆tsupport χ.func := by
  intro p hp
  apply subset_tsupport
  change χ.func p≠0
  have hh : (1/2 : ℝ)<χ.func p := hp
  linarith

lemma kernelChartCoreImage_open (χ : PositiveChartCutoff) : IsOpen (kernelChartCoreImage χ) := by
  have hp : kernelChartCore χ⊆euclideanUpperHalf := (kernelChartCore_subset χ).trans χ.positive
  have he : kernelChartCoreImage χ=integralOrbitProjection globalKubotaKernel ''
      (hyperbolicEuclideanCoordinates ⁻¹' kernelChartCore χ) := by
    rw [←euclideanToHyperbolic_image_positive _ hp,Set.image_image]
    rfl
  rw [he]
  exact (integralOrbitProjection_openQuotient globalKubotaKernel
    globalKubotaKernel_le_levelThree).isOpenMap _
      ((kernelChartCore_open χ).preimage hyperbolicEuclideanCoordinates_continuous)

abbrev KernelGoodCutoff := {χ : PositiveChartCutoff //
  Set.InjOn kernelEuclideanProjection (tsupport χ.func)}

lemma kernelChartCoreImage_cover : (Set.univ : Set KernelQuotient)⊆
    ⋃χ : KernelGoodCutoff,kernelChartCoreImage χ.1 := by
  intro q hq
  obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
  obtain ⟨χ,hχ,hrange,hinj⟩ := kernelChartCutoff_exists
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
  refine Set.mem_iUnion.mpr ⟨⟨χ,hinj⟩,hyperbolicEuclideanCoordinates w,?_,?_⟩
  · change (1/2 : ℝ)<χ.func (hyperbolicEuclideanCoordinates w)
    rw [hχ]
    norm_num
  · simp only [kernelEuclideanProjection,Function.comp_apply,euclideanToHyperbolic_coordinates]
    rfl

lemma kernelCompact_finite_chart_cover (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃t : Finset KernelGoodCutoff,K⊆⋃χ∈t,kernelChartCoreImage χ.1 := by
  exact hK.elim_finite_subcover (fun χ : KernelGoodCutoff => kernelChartCoreImage χ.1)
    (fun χ => kernelChartCoreImage_open χ.1)
    (Set.subset_univ K |>.trans kernelChartCoreImage_cover)

lemma kernelChartCore_mass_estimate (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (H : ℝ) (hH : 0≤H) (hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H)
    (f : kernelSmoothTests) :
    (∫q in kernelChartCoreImage χ,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
      4*H*‖kernelL2Localize χ (kernelSmoothTestsToL2 f)‖^2 := by
  let S := kernelChartCore χ
  have hS : MeasurableSet S := (kernelChartCore_open χ).measurableSet
  have hpos : S⊆euclideanUpperHalf := (kernelChartCore_subset χ).trans χ.positive
  have hi : Set.InjOn kernelEuclideanProjection S := hinj.mono (kernelChartCore_subset χ)
  have hm := hyperbolicVolume_le_densityBound S hS hpos H
    (fun p hp => hdensity p (kernelChartCore_subset χ hp))
  have hloc : Integrable (fun p => ‖kernelLocalizedField χ f p‖^2) volume := by
    exact ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq
  have hlocHyp : IntegrableOn (fun p => ‖kernelLocalizedField χ f p‖^2) S hyperbolicEuclideanVolume :=
    (hloc.integrableOn.smul_measure (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top).mono_measure hm
  have hmass : IntegrableOn (fun p => ‖kernelTestField f p‖^2) S hyperbolicEuclideanVolume :=
    (kernelEuclideanProjection_measurePreserving_on S hS hpos hi).integrable_comp_of_integrable
      (kernelSmoothTests_memLp f).norm.integrable_sq.integrableOn
  rw [kernelL2Localize_core χ hinj,schwartz_toL2_norm_sq]
  have hEq := kernelEuclideanProjection_integral S hS hpos hi
    (fun q => ‖f.1 q‖^2) (kernelSmoothTests_memLp f).norm.integrable_sq.aestronglyMeasurable
  change (∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)=_ at hEq
  change (∫q in kernelEuclideanProjection '' S,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
    4*H*(∫p,‖kernelLocalizedField χ f p‖^2)
  rw [←hEq]
  calc
    _ ≤ ∫p in S,4*‖kernelLocalizedField χ f p‖^2∂hyperbolicEuclideanVolume := by
      apply setIntegral_mono_on hmass (hlocHyp.const_mul 4) hS
      intro p hp
      have hc : (1/2 : ℝ)<χ.func p := hp
      rw [kernelLocalizedField,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      have hn := sq_nonneg ‖kernelTestField f p‖
      have hx : 1≤4*(χ.func p)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hx hn]
    _ = 4*(∫p in S,‖kernelLocalizedField χ f p‖^2∂hyperbolicEuclideanVolume) := integral_const_mul _ _
    _ ≤ 4*(H*(∫p in S,‖kernelLocalizedField χ f p‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hh := integral_mono_measure hm
        (Eventually.of_forall (fun p => sq_nonneg ‖kernelLocalizedField χ f p‖))
        (hloc.integrableOn.smul_measure (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top)
      simpa only [integral_smul_measure,ENNReal.toReal_ofReal hH,smul_eq_mul] using hh
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_le_integral hloc (Eventually.of_forall (fun p => sq_nonneg ‖kernelLocalizedField χ f p‖))

lemma kernelChartCore_mass_bound (χ : KernelGoodCutoff) : ∃C : ℝ,0≤C ∧
    ∀f : kernelSmoothTests,
      (∫q in kernelChartCoreImage χ.1,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        C*‖kernelL2Localize χ.1 (kernelSmoothTestsToL2 f)‖^2 := by
  have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) (tsupport χ.1.func) :=
    (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.1.positive hp)))
  obtain ⟨r,hr⟩ := χ.1.compact.bddAbove_image hrho
  refine ⟨4*max 0 r,by positivity,fun f => ?_⟩
  exact kernelChartCore_mass_estimate χ.1 χ.2 (max 0 r) (le_max_left _ _)
    (fun p hp => (hr ⟨p,hp,rfl⟩).trans (le_max_right _ _)) f

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def kernelMassRestriction (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) : KernelQuotientL2 :=
  ((Lp.memLp f).indicator hK).toLp (K.indicator f)

lemma kernelMassRestriction_coe (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) :
    (kernelMassRestriction K hK f : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      K.indicator f := ((Lp.memLp f).indicator hK).coeFn_toLp

def kernelMassRestrictionLinear (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelQuotientL2→ₗ[ℂ]KernelQuotientL2 where
  toFun := kernelMassRestriction K hK
  map_add' f g := by
    apply Lp.ext
    filter_upwards [kernelMassRestriction_coe K hK (f+g),kernelMassRestriction_coe K hK f,
      kernelMassRestriction_coe K hK g,Lp.coeFn_add f g,
      Lp.coeFn_add (kernelMassRestriction K hK f) (kernelMassRestriction K hK g)] with q hfg hf hg ha hb
    rw [hfg,hb,Pi.add_apply,hf,hg]
    by_cases hq : q∈K
    · simp only [Set.indicator_of_mem hq,ha,Pi.add_apply]
    · simp only [Set.indicator_of_notMem hq,add_zero]
  map_smul' c f := by
    change kernelMassRestriction K hK (c•f)=c•kernelMassRestriction K hK f
    apply Lp.ext
    filter_upwards [kernelMassRestriction_coe K hK (c•f),kernelMassRestriction_coe K hK f,
      Lp.coeFn_smul c f,Lp.coeFn_smul c (kernelMassRestriction K hK f)] with q hcf hf ha hb
    rw [hcf,hb,Pi.smul_apply,hf]
    by_cases hq : q∈K
    · simp only [Set.indicator_of_mem hq,ha,Pi.smul_apply]
    · simp only [Set.indicator_of_notMem hq,smul_zero]

lemma kernelMassRestriction_norm_le (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) : ‖kernelMassRestriction K hK f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [kernelMassRestriction_coe K hK f] with q hq
  rw [hq]
  by_cases hm : q∈K
  · simp only [Set.indicator_of_mem hm,le_refl]
  · simp only [Set.indicator_of_notMem hm,norm_zero,norm_nonneg]

def kernelMassRestrictionCLM (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  (kernelMassRestrictionLinear K hK).mkContinuous 1 (by
    intro f
    change ‖kernelMassRestriction K hK f‖≤1*‖f‖
    simpa only [one_mul] using kernelMassRestriction_norm_le K hK f)

lemma kernelMassRestriction_norm_sq (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) :
    ‖kernelMassRestrictionCLM K hK f‖^2=
      ∫q in K,‖f q‖^2∂integralQuotientVolume globalKubotaKernel := by
  rw [←integral_indicator hK]
  calc
    _ = inner ℝ (kernelMassRestriction K hK f) (kernelMassRestriction K hK f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫q,inner ℝ (kernelMassRestriction K hK f q) (kernelMassRestriction K hK f q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [kernelMassRestriction_coe K hK f] with q hq
      rw [hq,real_inner_self_eq_norm_sq]
      by_cases hqK : q∈K
      · simp only [Set.indicator_of_mem hqK]
      · simp only [Set.indicator_of_notMem hqK,norm_zero,zero_pow (by decide : 2≠0)]

lemma kernelMassRestriction_smooth_norm_sq (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : kernelSmoothTests) :
    ‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2=
      ∫q in K,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel := by
  rw [kernelMassRestriction_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (kernelSmoothTests_memLp f).coeFn_toLp] with q hq
  change ‖((kernelSmoothTests_memLp f).toLp f.1) q‖^2=‖f.1 q‖^2
  rw [hq]

def kernelEnergyMassRestriction (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelEnergyGraph→L[ℂ]KernelQuotientL2 :=
  (kernelMassRestrictionCLM K hK).comp kernelEnergyMass

lemma integral_le_finite_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) (K : Set X) (hK : MeasurableSet K) (U : ι→Set X)
    (hU : ∀i,MeasurableSet (U i)) (hcover : K⊆⋃i,U i)
    (g : X→ℝ) (hg : Integrable g ν) (hn : ∀x,0≤g x) :
    (∫x in K,g x∂ν)≤∑i,∫x in U i,g x∂ν := by
  have hi : ∀i,Integrable ((U i).indicator g) ν := fun i => hg.indicator (hU i)
  calc
    _ = ∫x,K.indicator g x∂ν := (integral_indicator hK).symm
    _ ≤ ∫x,∑i,(U i).indicator g x∂ν := by
      apply integral_mono (hg.indicator hK) (integrable_finsetSum _ (fun i himem => hi i))
      intro x
      have hnon : ∀i,0≤(U i).indicator g x := fun i => Set.indicator_nonneg (fun y hy => hn y) x
      by_cases hx : x∈K
      · rw [Set.indicator_of_mem hx]
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover hx)
        calc
          g x=(U i).indicator g x := (Set.indicator_of_mem hi g).symm
          _ ≤ ∑j,(U j).indicator g x := Finset.single_le_sum (fun j hj => hnon j) (Finset.mem_univ i)
      · rw [Set.indicator_of_notMem hx]
        exact Finset.sum_nonneg (fun i hi => hnon i)
    _ = _ := by
      rw [integral_finsetSum _ (fun i himem => hi i)]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_indicator (hU i)

def kernelEnergyChartFamily (t : Finset KernelGoodCutoff) :
    KernelEnergyGraph→L[ℂ](t→EuclideanL2) :=
  ContinuousLinearMap.pi (fun χ : t => kernelEnergyLocalizeL2 χ.1.1)

lemma kernelEnergyChartFamily_isCompact (t : Finset KernelGoodCutoff) :
    IsCompactOperator (kernelEnergyChartFamily t) :=
  compact_finite_pi _ (fun χ => kernelEnergyLocalizeL2_isCompact χ.1.1 χ.1.2)

lemma finite_sum_weighted_norm_sq_le {G ι : Type*} [Fintype ι]
    [NormedAddCommGroup G] (C : ι→ℝ) (hC : ∀i,0≤C i) (x : ι→G) :
    (∑i,C i*‖x i‖^2)≤(∑i,C i)*‖x‖^2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2) (hC i)

lemma kernelEnergyChartFamily_core_apply (t : Finset KernelGoodCutoff)
    (f : kernelSmoothTests) (χ : t) :
    kernelEnergyChartFamily t (kernelEnergyGraphCore f) χ=
      kernelL2Localize χ.1.1 (kernelSmoothTestsToL2 f) := by
  change kernelL2Localize χ.1.1 (kernelEnergyMass (kernelEnergyGraphCore f))=_
  rw [kernelEnergyMass_core]

lemma kernelCompact_mass_bound (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃t : Finset KernelGoodCutoff,∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      (∫q in K,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        C*‖kernelEnergyChartFamily t (kernelEnergyGraphCore f)‖^2 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover K hK
  have hcov : K⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  choose C hC hbound using fun χ : t => kernelChartCore_mass_bound χ.1
  refine ⟨t,∑χ,C χ,Finset.sum_nonneg (fun χ hχ => hC χ),fun f => ?_⟩
  calc
    _ ≤ ∑χ : t,∫q in kernelChartCoreImage χ.1.1,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel :=
      integral_le_finite_cover _ K hK.measurableSet _
        (fun χ : t => (kernelChartCoreImage_open χ.1.1).measurableSet) hcov _
        (kernelSmoothTests_memLp f).norm.integrable_sq (fun _ => sq_nonneg _)
    _ ≤ ∑χ : t,C χ*‖kernelL2Localize χ.1.1 (kernelSmoothTestsToL2 f)‖^2 :=
      Finset.sum_le_sum (fun χ hχ => hbound χ f)
    _ = ∑χ : t,C χ*‖kernelEnergyChartFamily t (kernelEnergyGraphCore f) χ‖^2 := by
      simp only [kernelEnergyChartFamily_core_apply]
    _ ≤ _ := finite_sum_weighted_norm_sq_le C hC _

theorem kernelEnergyMassRestriction_isCompact (K : Set KernelQuotient) (hK : IsCompact K) :
    IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) := by
  obtain ⟨t,C,hC,hbound⟩ := kernelCompact_mass_bound K hK
  have hsq : ∀u : KernelEnergyGraph,
      ‖kernelEnergyMassRestriction K hK.measurableSet u‖^2≤
        C*‖kernelEnergyChartFamily t u‖^2 := by
    intro u
    exact kernelEnergyGraphCore_dense.induction_on u
      (isClosed_le (by fun_prop : Continuous (fun v => ‖kernelEnergyMassRestriction K hK.measurableSet v‖^2))
        (by fun_prop : Continuous (fun v => C*‖kernelEnergyChartFamily t v‖^2)))
      (fun f => by
        change ‖kernelMassRestrictionCLM K hK.measurableSet
          (kernelEnergyMass (kernelEnergyGraphCore f))‖^2≤_
        rw [kernelEnergyMass_core,kernelMassRestriction_smooth_norm_sq]
        exact hbound f)
  apply compact_of_norm_le_compact _ (kernelEnergyChartFamily t)
    (kernelEnergyChartFamily_isCompact t)
  refine ⟨Real.sqrt C,fun u => ?_⟩
  have hs := hsq u
  have hc := Real.sq_sqrt hC
  have hn := mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (kernelEnergyChartFamily t u))
  have he : (Real.sqrt C*‖kernelEnergyChartFamily t u‖)^2=C*‖kernelEnergyChartFamily t u‖^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
  nlinarith [norm_nonneg (kernelEnergyMassRestriction K hK.measurableSet u)]

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss (actualSextic)

def primeValueHom (w : Ideal ActualEisensteinCubic.O → ℂ) : Ideal ActualEisensteinCubic.O →*₀ ℂ where
  toFun I := if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map w).prod
  map_zero' := by simp
  map_one' := by
    rw [if_neg one_ne_zero,UniqueFactorizationMonoid.normalizedFactors_one]
    rfl
  map_mul' I J := by
    by_cases hI : I=0
    · simp [hI]
    by_cases hJ : J=0
    · simp [hJ]
    simp only [if_neg hI,if_neg hJ,if_neg (mul_ne_zero hI hJ),
      UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,Multiset.map_add,Multiset.prod_add]

theorem primeValueHom_prime (w : Ideal ActualEisensteinCubic.O → ℂ) (P : Ideal ActualEisensteinCubic.O) (hP : Prime P) :
    primeValueHom w P = w P := by
  change (if P=0 then 0 else _) = w P
  rw [if_neg hP.ne_zero,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hP.irreducible]
  simp only [normalize_eq,Multiset.map_singleton,Multiset.prod_singleton]

theorem primeValueHom_norm_le_one (w : Ideal ActualEisensteinCubic.O → ℂ) (hw : ∀ P,‖w P‖≤1)
    (I : Ideal ActualEisensteinCubic.O) : ‖primeValueHom w I‖≤1 := by
  by_cases hI : I=0
  · rw [hI,map_zero,norm_zero]
    exact zero_le_one
  change ‖if I=0 then 0 else _‖≤1
  rw [if_neg hI]
  have hprod (s : Multiset (Ideal ActualEisensteinCubic.O)) : ‖(s.map w).prod‖≤1 := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw P)).trans ih
  exact hprod _

def principalIdealHom : ActualEisensteinCubic.O →*₀ Ideal ActualEisensteinCubic.O where
  toFun n := Ideal.span {n}
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := (Ideal.span_singleton_mul_span_singleton a b).symm

def localRowValue (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) : ℂ :=
  if h : P.IsMaximal ∧ lambda∉P then
    letI : P.IsMaximal := h.1
    actualSextic P h.2 (Ideal.Quotient.mk P x)
  else 0

theorem localRowValue_good (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    localRowValue x P = actualSextic P hg (Ideal.Quotient.mk P x) := by
  simp only [localRowValue,dif_pos (show P.IsMaximal ∧ lambda∉P from ⟨inferInstance,hg⟩)]

theorem localRowValue_norm (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) : ‖localRowValue x P‖≤1 := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    let : Fintype (ActualEisensteinCubic.O⧸P) := Fintype.ofFinite _
    exact FiniteRayExpansion.norm_char_le_one _ _
  · simp

def idealRowHom (x : ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O →*₀ ℂ := primeValueHom (localRowValue x)

def rowTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) : ActualEisensteinCubic.O →* ℂ :=
  Ψ * (idealRowHom (m^6*f^4*z)).toMonoidHom.comp principalIdealHom.toMonoidHom

theorem idealRowHom_prime (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    idealRowHom x P = actualSextic P hg (Ideal.Quotient.mk P x) := by
  rw [idealRowHom,primeValueHom_prime _ P
    (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance),localRowValue_good]

theorem idealRowHom_norm (x : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) : ‖idealRowHom x I‖≤1 :=
  primeValueHom_norm_le_one _ (localRowValue_norm x) I

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open SecondPassArithmetic hiding O

end CanonicalRowCompletion

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
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem localRowValue_zero_of_mem (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) (hx : x∈P) :
    localRowValue x P = 0 := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact MulChar.map_nonunit _ (not_isUnit_zero)
  · rfl

theorem idealRowHom_zero_of_dvd (x : ActualEisensteinCubic.O) {P I : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPI : P∣I) (hx : x∈P) : idealRowHom x I = 0 := by
  obtain ⟨J,rfl⟩ := hPI
  rw [map_mul]
  have hz : idealRowHom x P = 0 := by
    rw [idealRowHom,primeValueHom_prime _ P hP,localRowValue_zero_of_mem x P hx]
  rw [hz,zero_mul]

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open FirstPassCubeLabels hiding O

theorem localRowValue_mul (a b : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue (a*b) P = localRowValue a P * localRowValue b P := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    simp only [map_mul]
  · simp

theorem idealRowHom_argument_mul (a b : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom (a*b) I = idealRowHom a I * idealRowHom b I := by
  by_cases hI : I=0
  · rw [hI,map_zero,map_zero,map_zero,zero_mul]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _) * (if I=0 then 0 else _)
  simp only [if_neg hI]
  have hprod (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue (a*b))).prod =
        (s.map (localRowValue a)).prod * (s.map (localRowValue b)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons]
      rw [localRowValue_mul,ih]
      ring
  exact hprod _

end

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

def excludedGenerator (S : Finset (Ideal ActualEisensteinCubic.O)) : ActualEisensteinCubic.O := idealGenerator (∏P∈S,P)

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open CompletedGauss hiding O

def cubeIndex (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) : primePool F →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i=>(UniqueFactorizationMonoid.normalizedFactors B).count i.val)

@[simp] theorem cubeIndex_apply (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) (i : primePool F) :
    cubeIndex F B i = (UniqueFactorizationMonoid.normalizedFactors B).count i.val := by
  simp [cubeIndex]

def cubeIdeal (F : Finset (Ideal ActualEisensteinCubic.O)) (v : primePool F →₀ ℕ) : Ideal ActualEisensteinCubic.O :=
  ∏i:primePool F,i.val^v i

end CanonicalRowCompletion

open scoped BigOperators Classical
open MeasureTheory

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

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

def activeCubeExponents (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) :
    Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  ((outsideIdealsUpTo S D).image (cubeIndex F)).filter
    (fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)^3 ≤ b*X)

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

def cubeLogIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) : ℕ :=
  normLogBin (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)

def cubeLogRange (b X : ℝ) : Finset ℕ :=
  Finset.range (normLogBin (max 1 (b*X)) + 1)

def activeCubeLogBin (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) (j : ℕ) :
    Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) :=
  (activeCubeExponents S D b X).filter (fun v => cubeLogIndex S D v = j)

end CanonicalRowCompletion

open scoped BigOperators Classical

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

namespace SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter

def positiveRadialProfile (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0<x then V (Real.log x) else 0

theorem positiveRadialProfile_support (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : positiveRadialProfile V x≠0) :
    x∈Set.Icc (Real.exp (-A)) (Real.exp A) := by
  have hpos : 0<x := by
    by_contra hn
    exact hx (by simp [positiveRadialProfile,hn])
  have hlog : |Real.log x|≤A := hV _ (by simpa [positiveRadialProfile,hpos] using hx)
  constructor
  · calc
      Real.exp (-A) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (abs_le.mp hlog).1
      _ = x := Real.exp_log hpos
  · calc
      x = Real.exp (Real.log x) := (Real.exp_log hpos).symm
      _ ≤ Real.exp A := Real.exp_le_exp.mpr (abs_le.mp hlog).2

theorem positiveRadialProfile_compact (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : HasCompactSupport (positiveRadialProfile V) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun x hx=>positiveRadialProfile_support V A hV x hx)

theorem positiveRadialProfile_smooth (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V)
    (A : ℝ) (hV : ∀s,V s≠0→|s|≤A) : ContDiff ℝ ∞ (positiveRadialProfile V) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hpos : 0<x
  · have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun y=>V (Real.log y)) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      change 0<y at hy
      simp only [positiveRadialProfile,if_pos hy]
    exact (hVs.contDiffAt.comp x (Real.contDiffAt_log.mpr hpos.ne')).congr_of_eventuallyEq he
  · have hx : x<Real.exp (-A) := (le_of_not_gt hpos).trans_lt (Real.exp_pos _)
    have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun _=>0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      by_contra hn
      have hb := (positiveRadialProfile_support V A hV y hn).1
      exact (not_le_of_gt hy) hb
    exact (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq he

def radialFromLog (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : 𝓢(ℝ,ℂ) :=
  (positiveRadialProfile_compact V A hV).toSchwartzMap (positiveRadialProfile_smooth V hVs A hV)

@[simp] theorem radialFromLog_apply_pos (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : 0<x) :
    radialFromLog V hVs A hV x=V (Real.log x) := by
  change positiveRadialProfile V x=_
  simp only [positiveRadialProfile,if_pos hx]

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

def kernelTestPartitionTerm {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) : kernelSmoothTests :=
  ⟨fun q => ρ i q • f.1 q,(ρ i).contMDiff.smul f.2.1,
    HasCompactSupport.smul_left (f := fun q => ρ i q) (f' := f.1) f.2.2⟩

lemma kernelTestPartitionTerm_tsupport {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) :
    tsupport (kernelTestPartitionTerm ρ f i).1⊆tsupport (ρ i) :=
  tsupport_smul_subset_left _ _

lemma kernelTestPartition_sum {ι : Type*} [Fintype ι]
    (f : kernelSmoothTests)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient (tsupport f.1)) :
    ∑i,kernelTestPartitionTerm ρ f i=f := by
  apply Subtype.ext
  funext q
  simp only [Submodule.coe_sum,Finset.sum_apply,kernelTestPartitionTerm]
  rw [←Finset.sum_smul]
  by_cases hq : q∈tsupport f.1
  · have hs := ρ.sum_eq_one hq
    rw [finsum_eq_sum_of_fintype] at hs
    rw [hs,one_smul]
  · have hz : f.1 q=0 := image_eq_zero_of_notMem_tsupport hq
    rw [hz,smul_zero]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

def kernelFullCutoffFun (χ : PositiveChartCutoff) (p : EuclideanSpatial) : ℝ :=
  Real.smoothTransition (4*χ.func p-1)

lemma kernelFullCutoffFun_smooth (χ : PositiveChartCutoff) :
    ContDiff ℝ ∞ (kernelFullCutoffFun χ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul χ.smooth).sub contDiff_const)

lemma kernelFullCutoffFun_tsupport (χ : PositiveChartCutoff) :
    tsupport (kernelFullCutoffFun χ)⊆tsupport χ.func := by
  apply closure_mono
  intro p hp
  change kernelFullCutoffFun χ p≠0 at hp
  change χ.func p≠0
  intro hz
  apply hp
  simp only [kernelFullCutoffFun,hz,mul_zero,zero_sub]
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)

lemma kernelFullCutoffFun_compact (χ : PositiveChartCutoff) :
    HasCompactSupport (kernelFullCutoffFun χ) :=
  χ.compact.of_isClosed_subset (isClosed_tsupport _) (kernelFullCutoffFun_tsupport χ)

def kernelFullCutoff (χ : PositiveChartCutoff) : PositiveChartCutoff where
  func := kernelFullCutoffFun χ
  smooth := kernelFullCutoffFun_smooth χ
  compact := kernelFullCutoffFun_compact χ
  positive := (kernelFullCutoffFun_tsupport χ).trans χ.positive

lemma kernelFullCutoff_one (χ : PositiveChartCutoff) (p : EuclideanSpatial)
    (hp : p∈kernelChartCore χ) : (kernelFullCutoff χ).func p=1 := by
  apply Real.smoothTransition.one_of_one_le
  change (1/2 : ℝ)<χ.func p at hp
  linarith

lemma kernelFullCutoff_eventually_one (χ : PositiveChartCutoff) (p : EuclideanSpatial)
    (hp : p∈kernelChartCore χ) : (kernelFullCutoff χ).func =ᶠ[𝓝 p] fun _ => 1 := by
  filter_upwards [(kernelChartCore_open χ).mem_nhds hp] with q hq
  exact kernelFullCutoff_one χ q hq

def kernelCoreLift (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    𝓢(EuclideanSpatial,ℂ) := kernelLocalizedSchwartz (kernelFullCutoff χ) f

lemma kernelCoreLift_eventually_eq (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    (kernelCoreLift χ f : EuclideanSpatial→ℂ)=ᶠ[𝓝 p] kernelTestField f := by
  filter_upwards [kernelFullCutoff_eventually_one χ p hp] with q hq
  change (kernelFullCutoff χ).func q • kernelTestField f q=kernelTestField f q
  rw [hq,one_smul]

lemma kernelCoreLift_tsupport_outer (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    tsupport (kernelCoreLift χ f)⊆tsupport χ.func :=
  (kernelLocalizedField_tsupport (kernelFullCutoff χ) f).trans (kernelFullCutoffFun_tsupport χ)

lemma kernelCoreLift_tsupport (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ) :
    tsupport (kernelCoreLift χ f)⊆kernelChartCore χ := by
  intro p hp
  have houter := kernelCoreLift_tsupport_outer χ f hp
  by_contra hn
  have hfp : kernelEuclideanProjection p∉tsupport f.1 := by
    intro hfp
    obtain ⟨q,hq,heq⟩ := hf hfp
    have hqp := hinj (kernelChartCore_subset χ hq) houter heq
    exact hn (hqp ▸ hq)
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p (χ.positive houter)).continuousAt
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hfp).comp_tendsto hc
  have hzero : (kernelCoreLift χ f : EuclideanSpatial→ℂ)=ᶠ[𝓝 p] 0 := by
    filter_upwards [hz] with q hq
    change (kernelFullCutoff χ).func q • f.1 (kernelEuclideanProjection q)=0
    change f.1 (kernelEuclideanProjection q)=0 at hq
    rw [hq,smul_zero]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hp

lemma kernelCoreLift_eq_on_outer (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ) :
    Set.EqOn (kernelCoreLift χ f) (kernelTestField f) (tsupport χ.func) := by
  intro p hp
  by_cases hc : p∈kernelChartCore χ
  · exact (kernelCoreLift_eventually_eq χ f p hc).self_of_nhds
  · have hz : kernelTestField f p=0 := by
      change f.1 (kernelEuclideanProjection p)=0
      apply image_eq_zero_of_notMem_tsupport
      intro hfp
      obtain ⟨q,hq,heq⟩ := hf hfp
      have hqp := hinj (kernelChartCore_subset χ hq) hp heq
      exact hc (hqp ▸ hq)
    change (kernelFullCutoff χ).func p • kernelTestField f p=kernelTestField f p
    rw [hz,smul_zero]

def euclideanHeightCLM : EuclideanSpatial→L[ℝ]ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2)

lemma euclideanHeightCLM_apply (p : EuclideanSpatial) : euclideanHeightCLM p=(p 2:ℂ) := rfl

lemma upperHeightDivide_smooth (f : 𝓢(EuclideanSpatial,ℂ))
    (hpos : tsupport f⊆euclideanUpperHalf) :
    ContDiff ℝ ∞ (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p 2=0
  · have hn : p∉tsupport f := by
      intro hf
      have hh := hpos hf
      change 0<p 2 at hh
      linarith
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [hq,Pi.zero_apply,zero_div]
  · simpa only [div_eq_mul_inv,Pi.inv_apply,euclideanHeightCLM_apply] using
      (f.smooth ⊤).contDiffAt.mul (euclideanHeightCLM.contDiff.contDiffAt.fun_inv
        (Complex.ofReal_ne_zero.mpr hp))

lemma upperHeightDivide_compact (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) :
    HasCompactSupport (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hcompact ⊢
  exact hcompact.mono (fun p hp => by simp only [hp,Pi.zero_apply,zero_div])

def upperHeightDivide (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  (upperHeightDivide_compact f hcompact).toSchwartzMap (upperHeightDivide_smooth f hpos)

lemma upperHeightDivide_apply (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) : upperHeightDivide f hcompact hpos p=f p/(p 2:ℂ) := rfl

lemma upperHeightDivide_tsupport (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    tsupport (upperHeightDivide f hcompact hpos)⊆tsupport f := by
  apply closure_mono
  intro p hp
  change f p/(p 2:ℂ)≠0 at hp
  change f p≠0
  exact fun hz => hp (by rw [hz,zero_div])

lemma upperHeightDivide_lineDeriv (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p u : EuclideanSpatial) (hp : p 2≠0) :
    (∂_{u} (upperHeightDivide f hcompact hpos)) p=
      ((∂_{u} f) p*(p 2:ℂ)-f p*(u 2:ℂ))/(p 2:ℂ)^2 := by
  have hf := (f.hasFDerivAt p).hasLineDerivAt u
  have hv := (euclideanHeightCLM.hasFDerivAt (x := p)).hasLineDerivAt u
  change HasDerivAt (fun t : ℝ => f (p+t•u)) ((∂_{u} f) p) 0 at hf
  change HasDerivAt (fun t : ℝ => ((p+t•u) 2:ℂ)) (u 2:ℂ) 0 at hv
  have hd := hf.div hv (by simpa using Complex.ofReal_ne_zero.mpr hp)
  have hline : HasLineDerivAt ℝ (upperHeightDivide f hcompact hpos)
      (((∂_{u} f) p*(p 2:ℂ)-f p*(u 2:ℂ))/(p 2:ℂ)^2) p u := by
    simpa only [HasLineDerivAt,upperHeightDivide_apply,Pi.div_apply,zero_smul,add_zero] using! hd
  exact ((upperHeightDivide f hcompact hpos).hasFDerivAt p).hasLineDerivAt u |>.unique hline

lemma upperSchwartz_derivative_compact (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (u : EuclideanSpatial) :
    HasCompactSupport (∂_{u} f : 𝓢(EuclideanSpatial,ℂ)) :=
  hcompact.fderiv_apply ℝ u

def upperWeightedPartial (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) (j : Fin 3) :
    𝓢(EuclideanSpatial,ℂ) :=
  upperHeightDivide (∂_{euclideanCoordinateVector j} f)
    (upperSchwartz_derivative_compact f hcompact _)
    ((SchwartzMap.tsupport_lineDerivOp_subset _ f).trans hpos)

def upperWeightedDivergence (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  -∑j : Fin 3,∂_{euclideanCoordinateVector j} (upperWeightedPartial f hcompact hpos j)

def complexHermitianBilin : ℂ→L[ℝ]ℂ→L[ℝ]ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap

lemma schwartz_hermitian_integrable (f g : 𝓢(EuclideanSpatial,ℂ)) :
    Integrable (fun p => star (f p)*g p) volume :=
  (SchwartzMap.bilinLeftCLM complexHermitianBilin g.hasTemperateGrowth f).integrable

lemma schwartz_hermitian_lineGreen (f g : 𝓢(EuclideanSpatial,ℂ)) (u : EuclideanSpatial) :
    (∫p,star (f p)*(∂_{u} g) p)=-∫p,star ((∂_{u} f) p)*g p :=
  SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left f g complexHermitianBilin u

lemma upperWeighted_green (f g : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    (∫p,∑j : Fin 3,star (upperWeightedPartial f hcompact hpos j p)*
      (∂_{euclideanCoordinateVector j} g) p)=
      ∫p,star (upperWeightedDivergence f hcompact hpos p)*g p := by
  calc
    _ = ∑j : Fin 3,∫p,star (upperWeightedPartial f hcompact hpos j p)*
        (∂_{euclideanCoordinateVector j} g) p :=
      integral_finsetSum _ (fun j hj => schwartz_hermitian_integrable _ _)
    _ = -∑j : Fin 3,∫p,star ((∂_{euclideanCoordinateVector j}
        (upperWeightedPartial f hcompact hpos j)) p)*g p := by
      simp only [schwartz_hermitian_lineGreen,Finset.sum_neg_distrib]
    _ = _ := by
      rw [←integral_finsetSum _ (fun j hj => schwartz_hermitian_integrable _ _),←integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        simp only [upperWeightedDivergence,_root_.neg_apply,_root_.sum_apply,star_neg,star_sum,
          Finset.sum_mul,neg_mul])

def upperPositiveLaplacian (f : 𝓢(EuclideanSpatial,ℂ)) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,(∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} f)) p)+
    (p 2:ℂ)*(∂_{euclideanCoordinateVector 2} f) p

lemma upperWeightedDivergence_apply_ne_zero (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) (hp : p 2≠0) :
    upperWeightedDivergence f hcompact hpos p=upperPositiveLaplacian f p/(p 2:ℂ)^3 := by
  have hd (j : Fin 3) : (∂_{euclideanCoordinateVector j} (upperWeightedPartial f hcompact hpos j)) p=
      ((∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} f)) p*(p 2:ℂ)-
        (∂_{euclideanCoordinateVector j} f) p*(euclideanCoordinateVector j 2:ℂ))/(p 2:ℂ)^2 :=
    upperHeightDivide_lineDeriv _ _ _ p _ hp
  simp only [upperWeightedDivergence,Fin.sum_univ_three,_root_.neg_apply,_root_.add_apply]
  rw [hd 0,hd 1,hd 2]
  simp only [upperPositiveLaplacian,Fin.sum_univ_three]
  ((try simp [euclideanCoordinateVector]) <;> norm_num [euclideanCoordinateVector])
  field_simp [Complex.ofReal_ne_zero.mpr hp]
  ring

lemma upperWeightedDivergence_apply (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) :
    upperWeightedDivergence f hcompact hpos p=upperPositiveLaplacian f p/(p 2:ℂ)^3 := by
  by_cases hp : p 2=0
  · have hz : ∀j : Fin 3,(∂_{euclideanCoordinateVector j}
        (upperWeightedPartial f hcompact hpos j)) p=0 := by
      intro j
      have hn : p∉tsupport (upperWeightedPartial f hcompact hpos j) := by
        intro hm
        have ht := hpos ((SchwartzMap.tsupport_lineDerivOp_subset _ f)
          (upperHeightDivide_tsupport _ _ _ hm))
        change 0<p 2 at ht
        linarith
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,fderiv_of_notMem_tsupport ℝ hn]
      rfl
    simp only [upperWeightedDivergence,_root_.neg_apply,_root_.sum_apply,hz,Finset.sum_const_zero,neg_zero,
      upperPositiveLaplacian,hp,Complex.ofReal_zero,zero_pow (by decide : 2≠0),
      zero_pow (by decide : 3≠0),zero_mul,zero_add,zero_div]
  · exact upperWeightedDivergence_apply_ne_zero f hcompact hpos p hp

theorem upperHyperbolic_green (f g : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    (∫p,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} f) p)*
      (∂_{euclideanCoordinateVector j} g) p/(p 2:ℂ))=
      ∫p,star (upperPositiveLaplacian f p)*g p/(p 2:ℂ)^3 := by
  have hh := upperWeighted_green f g hcompact hpos
  simpa only [upperWeightedPartial,upperHeightDivide_apply,upperWeightedDivergence_apply,
    star_div₀,star_pow,Complex.star_def,Complex.conj_ofReal,div_mul_eq_mul_div] using hh

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

lemma kernelEuclideanProjection_integral_complex (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient→ℂ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := hg.mono_measure (Measure.restrict_le_self (s := kernelEuclideanProjection '' S))
  rw [←hm.map_eq] at hh ⊢
  exact (integral_map hm.measurable.aemeasurable hh).symm

lemma hyperbolicEuclidean_setIntegral_complex (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf) (g : EuclideanSpatial→ℂ) :
    (∫p in S,g p∂hyperbolicEuclideanVolume)=∫p in S,g p/(p 2:ℂ)^3 := by
  rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
    Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos,
    integral_withDensity_eq_integral_toReal_smul hyperbolicDensity_measurable
      (Eventually.of_forall (fun p => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hS] with p hp
  have hpositive : 0<p 2 := hpos hp
  rw [hyperbolicDensity,ENNReal.toReal_ofReal (by positivity)]
  rw [Complex.real_smul]
  change (↑(((p 2)^3)⁻¹) : ℂ)*g p=g p/(p 2:ℂ)^3
  simp only [Complex.ofReal_inv,Complex.ofReal_pow,div_eq_mul_inv,mul_comm]

lemma kernelDirichletPairDensity_zero_of_notMem (f g : kernelSmoothTests) (q : KernelQuotient)
    (hq : q∉tsupport g.1) : kernelDirichletPairDensity f g q=0 := by
  have hz : kernelQuotientEnergyDensity g q=0 := by
    by_contra hn
    exact hq (kernelQuotientEnergyDensity_support g hn)
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)=0
    rw [kernelDirichletPairDensity_coordinate]
    have hg : kernelGradientAt w g=0 := by
      apply norm_eq_zero.mp
      have h := kernelGradientAt_norm_sq w g
      change kernelTestEnergyDensity g w=0 at hz
      rw [hz] at h
      nlinarith [norm_nonneg (kernelGradientAt w g)]
    rw [hg,inner_zero_right]

lemma kernelDirichletPairDensity_euclidean (f g : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelDirichletPairDensity f g (kernelEuclideanProjection p)=
      (p 2:ℂ)^2*∑j : Fin 3,star (fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector j))*
        fderiv ℝ (kernelTestField g) p (euclideanCoordinateVector j) := by
  have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
  have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
  change kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))=_
  rw [kernelDirichletPairDensity_coordinate,PiLp.inner_apply]
  change (∑j : Fin 3,inner ℂ ((hyperbolicHeight (euclideanToHyperbolic p):ℂ)*kernelTestPartial f (euclideanToHyperbolic p) j)
    ((hyperbolicHeight (euclideanToHyperbolic p):ℂ)*kernelTestPartial g (euclideanToHyperbolic p) j))=_
  rw [hv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [kernelTestPartial,hc,←euclideanCoordinateVector_eq_basis,RCLike.inner_apply,
    map_mul,Complex.conj_ofReal,Complex.star_def]
  ring

lemma kernelCoreLift_fderiv_eq_on_outer (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ)
    (p : EuclideanSpatial) (hp : p∈tsupport χ.func) :
    fderiv ℝ (kernelCoreLift χ f) p=fderiv ℝ (kernelTestField f) p := by
  by_cases hc : p∈kernelChartCore χ
  · exact (kernelCoreLift_eventually_eq χ f p hc).fderiv_eq
  · have hl : p∉tsupport (kernelCoreLift χ f) := fun h => hc (kernelCoreLift_tsupport χ hinj f hf h)
    have hfp : kernelEuclideanProjection p∉tsupport f.1 := by
      intro hfp
      obtain ⟨q,hq,heq⟩ := hf hfp
      exact hc ((hinj (kernelChartCore_subset χ hq) hp heq) ▸ hq)
    have hcont : ContinuousAt kernelEuclideanProjection p :=
      (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
        (euclideanToHyperbolic_contMDiffAt p (χ.positive hp)).continuousAt
    have hz : kernelTestField f=ᶠ[𝓝 p]0 := (notMem_tsupport_iff_eventuallyEq.mp hfp).comp_tendsto hcont
    rw [fderiv_of_notMem_tsupport ℝ hl,hz.fderiv_eq,fderiv_zero]
    rfl

lemma kernelCoreLift_pair_on_outer (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (p : EuclideanSpatial) (hp : p∈tsupport χ.func) :
    kernelDirichletPairDensity f g (kernelEuclideanProjection p)=
      (p 2:ℂ)^2*∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p := by
  rw [kernelDirichletPairDensity_euclidean f g p (χ.positive hp)]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [←kernelCoreLift_fderiv_eq_on_outer χ hinj g hg p hp]
  by_cases hc : p∈kernelChartCore χ
  · rw [(kernelCoreLift_eventually_eq χ f p hc).fderiv_eq]
  · have hn : p∉tsupport (kernelCoreLift χ g) := fun h => hc (kernelCoreLift_tsupport χ hinj g hg h)
    rw [fderiv_of_notMem_tsupport ℝ hn]
    simp only [_root_.zero_apply,mul_zero,Finset.sum_const_zero]

theorem kernelDirichletForm_eq_chart_pairing (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ) :
    kernelDirichletForm f g=
      ∫p,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p/(p 2:ℂ) := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  calc
    _ = ∫q in kernelEuclideanProjection '' S,kernelDirichletPairDensity f g q
        ∂integralQuotientVolume globalKubotaKernel := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      exact kernelDirichletPairDensity_zero_of_notMem f g q (fun h => hq (himg (hg h)))
    _ = ∫p in S,kernelDirichletPairDensity f g (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (kernelEuclideanProjection_integral_complex S hS χ.positive hinj _
        (kernelDirichletPairDensity_integrable f g).aestronglyMeasurable).symm
    _ = ∫p in S,kernelDirichletPairDensity f g (kernelEuclideanProjection p)/(p 2:ℂ)^3 :=
      hyperbolicEuclidean_setIntegral_complex S hS χ.positive _
    _ = ∫p in S,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p/(p 2:ℂ) := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_pair_on_outer χ hinj f g hg p hp,←Finset.sum_div]
      have hv : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (χ.positive hp).ne'
      field_simp [hv]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hn : p∉tsupport (kernelCoreLift χ g) := fun h => hp (kernelCoreLift_tsupport_outer χ g h)
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,fderiv_of_notMem_tsupport ℝ hn,
        _root_.zero_apply,mul_zero,zero_div,Finset.sum_const_zero]

theorem kernelDirichletForm_eq_chart_laplacian (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ) :
    kernelDirichletForm f g=
      ∫p,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
  rw [kernelDirichletForm_eq_chart_pairing χ hinj f g hg]
  exact upperHyperbolic_green _ _ (kernelLocalizedField_compact (kernelFullCutoff χ) f)
    ((kernelCoreLift_tsupport_outer χ f).trans χ.positive)

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
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

def kernelCoordinateLaplacian (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,
    fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j))+
    (p 2:ℂ)*fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector 2)

lemma kernelCoreLift_laplacian (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    upperPositiveLaplacian (kernelCoreLift χ f) p=kernelCoordinateLaplacian f p := by
  have he := kernelCoreLift_eventually_eq χ f p hp
  have hd (j : Fin 3) : (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  have hdd (j : Fin 3) :
      (∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} (kernelCoreLift χ f))) p=
        fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
          (euclideanCoordinateVector j) := by
    change fderiv ℝ (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j)=_
    rw [(hd j).fderiv_eq]
  simp only [upperPositiveLaplacian,kernelCoordinateLaplacian,hdd,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,he.fderiv_eq]

lemma kernelDirichletForm_sum_right {ι : Type*} (f : kernelSmoothTests)
    (t : Finset ι) (g : ι→kernelSmoothTests) :
    kernelDirichletForm f (∑i∈t,g i)=∑i∈t,kernelDirichletForm f (g i) := by
  induction t using Finset.induction_on with
  | empty =>
    have hz := kernelDirichletForm_smul_right 0 f (0 : kernelSmoothTests)
    simpa only [Finset.sum_empty,zero_smul,zero_mul] using hz
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi,kernelDirichletForm_add_right,ih]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

lemma kernelL2_inner_toLp_smooth (A : KernelQuotient→ℂ)
    (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel)) (g : kernelSmoothTests) :
    inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g)=
      ∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  calc
    _ = ∫q,inner ℂ ((hA.toLp A) q) (kernelSmoothTestsToL2 g q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hA.coeFn_toLp,(kernelSmoothTests_memLp g).coeFn_toLp] with q hq hg
      change inner ℂ ((hA.toLp A) q) (((kernelSmoothTests_memLp g).toLp g.1) q)=_
      rw [hq,hg,RCLike.inner_apply]
      simp only [RCLike.star_def,mul_comm]

end CubicEisenstein

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalCoefficientClass

section
open ActualEisensteinCubic
open SecondPassArithmetic (rayMonoid conjugateRayMonoid rayMonoid_apply conjugateRayMonoid_apply
  FirstCoreIndex firstCoreTwist sideRayMonoid SecondRayIndex secondRayMinus secondRayPlus)
open RayFourExpansion (RayCharacter)

def IsBaseRayTwist (base Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  Ψ=base ∨ ∃χ : RayCharacter, Ψ=rayMonoid χ*base

def FactorsModulo (Q : Ideal ActualEisensteinCubic.O) (Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  ∀x y : ActualEisensteinCubic.O,x-y∈Q → Ψ x=Ψ y

end

open ActualEisensteinCubic
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

lemma norm_eval_mod (m : ℕ) (a b : ℤ) :
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

theorem normCharacter_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (InitialMeanSquare.normCharacter χ) := by
  intro x y hxy
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c := (coords y).1
  let d := (coords y).2
  let e := (coords z).1
  let f := (coords z).2
  have hy : y=eval c d := (eval_coords y).symm
  have hx : x=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
    calc
      x=y+(m : ActualEisensteinCubic.O)*z := by linear_combination hz
      _=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  change χ (Ideal.absNorm (Ideal.span {x}))=χ (Ideal.absNorm (Ideal.span {y}))
  congr 1
  rw [hx,hy,norm_eval_mod,norm_eval_mod]
  simp

def fixedBaseConductor (m : ℕ) : Ideal ActualEisensteinCubic.O := Ideal.span {(m : ActualEisensteinCubic.O)}*Ideal.span {(4 : ActualEisensteinCubic.O)}

end CanonicalCoefficientClass

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

namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation

def progressingCubes (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (H₀ : ℝ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)) :=
  Q.filter (fun v=>H₀≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))

end CanonicalRowCompletion

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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic UniqueFactorizationMonoid

theorem nonresidual_count_eq_on_fiber (I J Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    (normalizedFactors I).count P=(normalizedFactors J).count P := by
  have ha := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hA
  simp only [normalizedFactors_rowPowerfulPart,Multiset.count_filter] at ha
  have ht := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hT
  simp only [rowMaskPart,normalizedFactors_squarefreeMaskPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at ht
  have hr0 : (normalizedFactors (rowResidualPart I Q)).count P=0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp hm).2
  simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at hr0
  by_cases hpq : P∣Q
  · simp only [hpq,ite_true] at ht
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha ht <;> omega
  · have hpi : P∣I := (hP.dvd_mul.mp hpool).resolve_right hpq
    have hci : 0<(normalizedFactors I).count P :=
      Multiset.count_pos.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hpi⟩)
    simp only [hpq,not_false_eq_true,ite_true] at hr0
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha hr0 <;> omega

theorem nonresidual_prime_transport (I J F Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hJ : J≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    P∣J*Q ∧ ¬P∣rowResidualPart J Q ∧ completedLocalExponent I F P=completedLocalExponent J F P := by
  have hc := nonresidual_count_eq_on_fiber I J Q P hI hP hA hT hpool hr
  have hpoolJ : P∣J*Q := by
    rcases hP.dvd_mul.mp hpool with hi|hq
    · have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hi⟩
      have hcj : 0<(normalizedFactors J).count P := hc ▸ Multiset.count_pos.mpr hm
      exact dvd_mul_of_dvd_left ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hJ).mp (Multiset.count_pos.mp hcj)).2 Q
    · exact dvd_mul_of_dvd_right hq J
  have hrc : (normalizedFactors (rowResidualPart I Q)).count P=
      (normalizedFactors (rowResidualPart J Q)).count P := by
    simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
      normalizedFactors_rowSimplePart,Multiset.count_filter,hc]
  refine ⟨hpoolJ,?_,?_⟩
  · intro hd
    have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart J) Q)).mpr ⟨hP,hd⟩
    have hp : 0<(normalizedFactors (rowResidualPart I Q)).count P := hrc.symm ▸ Multiset.count_pos.mpr hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
      (Multiset.count_pos.mp hp)).2
  · simp only [completedLocalExponent,hc]

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma compact_estimate_prod_antilipschitz (T : E→L[ℂ]F) (K : E→L[ℂ]G) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    ∃D : NNReal,AntilipschitzWith D (T.prod K) := by
  let R := max A 0+max B 0
  have hR : 0≤R := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨⟨Real.sqrt R,Real.sqrt_nonneg _⟩,(T.prod K).antilipschitz_of_bound (fun u => ?_)⟩
  have hT : ‖T u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_fst_le (T u,K u))
  have hK : ‖K u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_snd_le (T u,K u))
  have hh : ‖u‖^2≤R*‖(T.prod K) u‖^2 := calc
    _ ≤A*‖T u‖^2+B*‖K u‖^2 := hest u
    _ ≤ max A 0*‖T u‖^2+max B 0*‖K u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    _ ≤ max A 0*‖(T.prod K) u‖^2+max B 0*‖(T.prod K) u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hT (le_max_right _ _))
        (mul_le_mul_of_nonneg_left hK (le_max_right _ _))
    _ = _ := by dsimp only [R]; ring
  change ‖u‖≤Real.sqrt R*‖(T.prod K) u‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow,Real.sq_sqrt hR] using hh

lemma finiteDimensional_ker_of_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    FiniteDimensional ℂ T.ker := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  have hc : IsCompactOperator (K.comp T.ker.subtypeL) := hK.comp_clm T.ker.subtypeL
  have hid : IsCompactOperator (ContinuousLinearMap.id ℂ T.ker) := by
    apply compact_of_norm_le_compact _ _ hc
    refine ⟨Real.sqrt (max B 0),fun u => ?_⟩
    have ht : T (u:E)=0 := u.2
    have hh := hest (u:E)
    rw [ht,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_add] at hh
    have hh' : ‖u‖^2≤ max B 0*‖K (u:E)‖^2 :=
      hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    change ‖u‖≤Real.sqrt (max B 0)*‖K (u:E)‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt (le_max_right B 0)] using hh'
  exact FiniteDimensional.of_isCompactOperator_id hid

lemma antilipschitz_of_injective_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) (hT : Function.Injective T) :
    ∃D : NNReal,AntilipschitzWith D T := by
  by_contra hanti
  have hex (ε : ℝ) (hε : 0<ε) : ∃u : E,‖u‖=1 ∧ ‖T u‖<ε := by
    by_contra! hn
    apply hanti
    refine ⟨⟨ε⁻¹,inv_nonneg.mpr hε.le⟩,antilipschitz_of_bound_of_norm_one T (fun u hu => ?_)⟩
    change 1≤ε⁻¹*‖T u‖
    have hh := mul_le_mul_of_nonneg_left (hn u hu) (inv_nonneg.mpr hε.le)
    simpa only [inv_mul_cancel₀ hε.ne'] using hh
  obtain ⟨eps,hepsAnti,hepsPos,heps⟩ := exists_seq_strictAnti_tendsto (0:ℝ)
  choose u hunorm huT using fun n : ℕ => hex (eps n) (hepsPos n)
  have huTlim : Tendsto (fun n => T (u n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (huT n).le) heps
  obtain ⟨S,hS,hsub⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨k,hk,seq,hseq,hklim⟩ := hS.tendsto_subseq
    (fun n => hsub ⟨u n,by simp only [Metric.mem_closedBall,dist_zero_right,hunorm,le_refl],rfl⟩)
  let P := T.prod K
  obtain ⟨D,hD⟩ := compact_estimate_prod_antilipschitz T K A B hest
  have hlim : Tendsto (fun n => P (u (seq n))) atTop (𝓝 (0,k)) :=
    (huTlim.comp hseq.tendsto_atTop).prodMk_nhds hklim
  have hmem : (0,k)∈Set.range P :=
    (hD.isClosed_range P.uniformContinuous).mem_of_tendsto hlim
      (Eventually.of_forall (fun n => ⟨u (seq n),rfl⟩))
  obtain ⟨v,hv⟩ := hmem
  have hvlim : Tendsto (fun n => u (seq n)) atTop (𝓝 v) := by
    apply (hD.isInducing P.continuous).tendsto_nhds_iff.mpr
    change Tendsto (fun n => P (u (seq n))) atTop (𝓝 (P v))
    rw [hv]
    exact hlim
  have hvzero : v=0 := hT (by
    have hh := congrArg Prod.fst hv
    change T v=0 at hh
    simpa only [map_zero] using hh)
  have hnorm : ‖v‖=1 := tendsto_nhds_unique hvlim.norm (by simpa only [hunorm] using tendsto_const_nhds)
  rw [hvzero,norm_zero] at hnorm
  norm_num at hnorm

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

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

section
open ActualEisensteinCubic
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

abbrev PrimeIdeal := {P : Ideal ActualEisensteinCubic.O // Prime P}

def primeProduct (s : Finset PrimeIdeal) : Ideal ActualEisensteinCubic.O := ∏ P ∈ s, P.val

def primeSet (I : Ideal ActualEisensteinCubic.O) : Finset PrimeIdeal :=
  (primeSupport I).attach.image (fun P => ⟨P.val, support_prime P.property⟩)

@[simp] theorem mem_primeSet (I : Ideal ActualEisensteinCubic.O) (P : PrimeIdeal) :
    P ∈ primeSet I ↔ P.val ∈ primeSupport I := by
  simp only [primeSet, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨Q,hQ⟩
    have hv := congrArg Subtype.val hQ
    simpa only [←hv] using Q.property
  · intro h
    exact ⟨⟨P.val,h⟩,rfl⟩

def mobiusPrimeCoeff (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  (moebius I : ℂ) * primeValueHom w I

end

section
open ActualEisensteinCubic
open Filter

def primeNormPower (P : PrimeIdeal) (s : ℂ) : ℂ := (Ideal.absNorm P.val : ℂ)^(-s)

end

open ActualEisensteinCubic

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

end SmoothMobiusCorrection

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseInitialFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical
noncomputable section

@[ext] structure InitialTuple (J : ℕ) where
  common : Ideal O
  divisor : Ideal O
  residual : Ideal O
  frequency : O
  assigned : Fin J → SmoothMobiusCorrection.PrimeIdeal

structure Valid {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O) : Prop where
  common_eq : t * x.divisor = x.common
  label_eq : x.divisor * x.residual = f
  divisor_good : primaryGenerator x.divisor ≠ 0
  row_eq : primaryGenerator x.divisor * x.frequency = k
  assigned_dvd : ∀ i, (x.assigned i).val ∣ t * f

lemma divisor_dvd {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) : x.divisor ∣ f := ⟨x.residual, hx.label_eq.symm⟩

end
end SevenEighths.InverseInitialFibers

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def varyingCanonicalSourceTotal {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (H : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑b∈reopenedCubeFamily Q,∑C∈(pool\b.support).powerset,∑I∈labels,
    reopenedPairCoefficient β b C I *
      canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (H I b.rightExponent) (H I b.leftExponent) W K

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def reopenedPhysicalSourceSum (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (source : CubeCoordinates ι→Finset ι→Ideal O→ℂ) : ℂ :=
  ∑ b∈reopenedCubeFamily Q,∑ C∈(pool\b.support).powerset,∑ I∈labels,
    reopenedPairCoefficient β b C I*source b C I

def reopenedPhysicalCutoff (b : CubeCoordinates ι) (I : Ideal O)
    (R : Finset ι→ℝ) (D : Finset ι) : Finset O :=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit I) (R D)

def reopenedPhysicalRetained (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ : O→*ℂ) (m : O) (I : Ideal O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (R : Finset ι→ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ Ψ m m (idealGenerator I)*
    ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i∈D,Ideal.span {p i}):ℂ)*
      ∑ h∈(reopenedPhysicalCutoff p b I R D).erase 0,
        firstCubePhysicalMode p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
          (mark b.rightExponent) (mark b.leftExponent) W W Φ K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

abbrev FirstOriginalOuter (ι : Type*) := Σ _ : CubeCoordinates ι,Σ _ : Finset ι,Finset ι

def firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (FirstOriginalOuter ι) :=
  (reopenedCubeFamily Q).sigma (fun b=>(pool\b.support).powerset.sigma
    (fun C=>(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset))

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstOriginalWeight (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (k : FirstOriginalOuter ι) (x : Ideal O×O) : ℂ :=
  reopenedPairCoefficient β k.1 k.2.1 x.1 *
    (UniqueFactorizationMonoid.moebius (∏i∈k.2.2,Ideal.span {p i}):ℂ) *
    (if x.2∈reopenedPhysicalCutoff p k.1 x.1 (R k.1 k.2.1 x.1) k.2.2 then 1 else 0)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def originalRetainedFamily
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y) pool
      (fun _ _=>1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 true Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.rightExponent) x.2)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 false Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.leftExponent) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (firstOriginalWeight p β R x.1) x.2)
      (fun y=>star (W ((s 0*s 2*s 5*s 7)*y))) (fun y=>W ((s 1*s 2*s 5*s 8)*y)) Φ
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2)
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2)
      (fun x=>primeProductNorm p x.1.2.1)
      (fun x=>primeProductNorm p (cubeActiveSupport x.1.1.support
        (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)) K
      (fun x=>primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (fun x=>x.2.2) s

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open CompletedHeight FourierBridge
local notation "O" => ActualEisensteinCubic.O
abbrev OriginalIndex (ι : Type*) := Σ _ : FirstOriginalOuter ι,Ideal O×O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def leftNorm (x : OriginalIndex ι) : ℝ := ‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2
def rightNorm (x : OriginalIndex ι) : ℝ := ‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2
def commonNorm (x : OriginalIndex ι) : ℝ := primeProductNorm p x.1.2.1
def activeNorm (x : OriginalIndex ι) : ℝ := primeProductNorm p (cubeActiveSupport x.1.1.support
  (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)
def divisorElement (k : FirstOriginalOuter ι) : O := primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def markedReopenedCubeBin {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (X H₀ : ℝ)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
  ∑ v∈Q,(largeCubeCoefficient H₀ (cubeIdeal F v)*cubeWeight Ψrow (cubeIdeal F v)*
    (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹)*
    ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

def actualLongCoefficient {ι:Type*}(p:ι→O)(Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)
    (I:Ideal O)(v:ι→₀ℕ) : ℂ :=
  separatedCubeCoefficient
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ v

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def sexticPair (p q : O) : ℂ :=
  idealRowHom q (Ideal.span {p}) * idealRowHom p (Ideal.span {q})

end SevenEighths.ProbePhase
end

end OAI
end

section

namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)
open SmoothMobiusCorrection (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

def normWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun := CubicEisenstein.fullIdealWeight s
  map_zero' := by simp [CubicEisenstein.fullIdealWeight]
  map_one' := by simp [CubicEisenstein.fullIdealWeight]
  map_mul' I J := by
    by_cases hI : I = 0
    · simp [CubicEisenstein.fullIdealWeight, hI]
    by_cases hJ : J = 0
    · simp [CubicEisenstein.fullIdealWeight, hJ]
    simp only [CubicEisenstein.fullIdealWeight, hI, hJ, mul_ne_zero hI hJ,
      ite_false, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

def weighted (a : Ideal O →*₀ ℂ) (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := a I * normWeight s I
  map_zero' := by rw [map_zero, map_zero, zero_mul]
  map_one' := by rw [map_one, map_one, one_mul]
  map_mul' I J := by simp only [map_mul]; ring

def series (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := ∑' I : Ideal O, weighted a s I

def inverseSeries (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I : ℂ) * weighted a s I

theorem weighted_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => ‖weighted a s I‖) := by
  apply (CubicEisenstein.fullIdealWeight_summable_norm s hs).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem inverse_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal O => ‖(moebius I : ℂ) * weighted a s I‖) := by
  apply (weighted_summable_norm a ha s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)

theorem inverseSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s * series a s = 1 := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (moebius p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (inverse_summable_norm a ha s hs).mul_norm (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.1) = if B = 1 then 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have hz (p : MulFiber 0) : F p.1 = 0 := by simp only [F, p.2, map_zero, mul_zero]
      simp only [hz, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = (∑' p : MulFiber B, (moebius p.1.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.2])
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B
            simp only [map_one, one_mul]
          · exact zero_mul _
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.1) (∑' p, F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p, F p) = 1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O, ((moebius p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (inverse_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = 1 := hFone

theorem series_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : series a s ≠ 0 := by
  intro hz
  have h := inverseSeries_mul_series a ha s hs
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem primeValueHom_eq (f : Ideal O →*₀ ℂ) : CanonicalRowCompletion.primeValueHom f = f := by
  ext I
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
  · change (if I = 0 then 0 else ((normalizedFactors I).map f).prod) = f I
    simp only [hI, ite_false]
    rw [← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]

def deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) : Ideal O →*₀ ℂ :=
  CanonicalRowCompletion.primeValueHom
    (fun I => if I ∈ S.image Subtype.val then 0 else a I)

end

end SevenEighths.IdealEuler

end OAI
end

section

namespace OAI

namespace SevenEighths.HeckeBoundary

open ActualEisensteinCubic Complex
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)
open Asymptotics Filter
open scoped BigOperators Classical Topology

noncomputable section

def PrimeTriple (a₀ a₁ a₂ : Ideal O →*₀ ℂ) : Prop :=
  ∀ P : PrimeIdeal,
    (a₀ P.val = 0 ∧ a₁ P.val = 0 ∧ a₂ P.val = 0) ∨
    (a₀ P.val = 1 ∧ ‖a₁ P.val‖ = 1 ∧ a₂ P.val = a₁ P.val ^ 2)

theorem square_unitInvariant (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : UnitInvariant M (χ ^ 2) := by
  intro u
  rw [χ.pow_apply' two_ne_zero, hχ u, one_pow]

section Quadratic

open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open UniqueFactorizationMonoid
open scoped ComplexOrder

def zetaConvolutionCoeff (a : Ideal O →*₀ ℂ) (B : Ideal O) : ℂ :=
  if B = 0 then 0 else ∑ D ∈ idealDivisors B, a D

def regularizedIdealZeta (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 1 s *
    (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s

end Quadratic

end

end SevenEighths.HeckeBoundary

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionBounds
open HeckeFamily

def localBound (σ : ℝ) : ℝ := (1-(2 : ℝ)^(-σ))⁻¹

def radical (M : Ideal O) : Ideal O :=
  SmoothMobiusCorrection.primeProduct (SmoothMobiusCorrection.primeSet M)

end SevenEighths.HeckeDeletionBounds

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralAllSlots
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def phaseSlot (u : FreeRow) (T : Finset PrimeIdeal) (W : ℝ→ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑P:T,W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*(-star (idealRowHom u.val P.val.val))

end SevenEighths.ProbeCentralAllSlots

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialPoissonBridge
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open UniqueFactorizationMonoid InverseInitialOverlap
local notation "Eis" => ActualEisensteinCubic.O

def rowPolynomial (F : Finset (Ideal Eis)) (A : Ideal Eis → ℂ) (u : Eis) : ℂ :=
  ∑ I ∈ F, A I * idealRowHom u I

lemma pool_positive (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I) :
    ∀ I ∈ F, I ≠ 0 := fun I hI => (hF I hI).1

lemma pool_good (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I) :
    ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q :=
  fun I hI Q hQ => ((hF I hI).2.2 Q hQ).1

def heckeIdealCharacter (η : Ideal Eis →* ℂ) (u : Eis) : Ideal Eis →* ℂ :=
  η * (idealRowHom u).toMonoidHom

def originalFixedPolynomial (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    (Z r z : ℝ) (u : Eis) : ℂ :=
  (Z^(-(r+z)/2) : ℝ) * ∑ n ∈ original S P j,
    (moebius n : ℂ) * heckeIdealCharacter η u n * heckeIdealCharacter η u P *
      a n * W ((Ideal.absNorm n : ℝ)/Z^r)

def overlapResidualCoefficient (P j : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (c : Ideal Eis) : ℂ :=
  (moebius c : ℂ) * η c * a (reconstruct P j c) *
    W ((((Ideal.absNorm j : ℝ)/Z^G)*((Ideal.absNorm c : ℝ)/Z^(r+z-2*G))) /
      ((Ideal.absNorm (residual P j) : ℝ)/Z^(z-G)))

def overlapPrefactor (P j : Ideal Eis) (η : Ideal Eis →* ℂ) (Z r z G : ℝ) : ℂ :=
  (moebius j : ℂ)*(moebius (residual P j) : ℂ)*(Z^(-G) : ℝ)*η j^2*
    (Z^(-(r+z-2*G)/2) : ℝ)

def residualNormalizedPolynomial (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : Eis) : ℂ :=
  (Z^(-(r+z-2*G)/2) : ℝ) * ∑ c ∈ columns S P j,
    overlapResidualCoefficient P j η a W Z r z G c * star (idealRowHom u c)

end SevenEighths.InverseInitialPoissonBridge

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialConjugateEnergy
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss ConcreteTraceCRT
open InverseInitialOverlap InverseInitialPoissonBridge
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def conjugateIdealCharacter (η : Ideal O →* ℂ) : Ideal O →* ℂ where
  toFun I := star (η I)
  map_one' := by rw [map_one,star_one]
  map_mul' I J := by simp [map_mul]

@[simp] theorem conjugateIdealCharacter_apply (η : Ideal O →* ℂ) (I : Ideal O) :
    conjugateIdealCharacter η I = star (η I) := rfl

def conjugatedResidual (S : Finset (Ideal O)) (P j : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) : ℂ :=
  residualNormalizedPolynomial S P j (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) Z r z G u

def radialWeight (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (u : O) : ℝ :=
  (Φ (‖eisEmbedding u‖^2/Y)).re

def smoothedEnergy (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (f : O → ℂ) : ℝ :=
  ∑' u,radialWeight Φ Y u*‖f u‖^2

def originalTotalPolynomial (S : Finset (Ideal O)) (P : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (u : O) : ℂ :=
  (Z^(-(r+z)/2) : ℝ) * ∑ n∈S,(moebius n : ℂ)*heckeIdealCharacter η u n*
    heckeIdealCharacter η u P*a n*W ((Ideal.absNorm n : ℝ)/Z^r)

end SevenEighths.InverseInitialConjugateEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentMobiusRegroup CenteredMomentChildAssembly
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def originalPhase (e r : O) (ρ : O → ℂ) (a b : O) : ℂ :=
  (idealRowHom e (Ideal.span {a})*star (idealRowHom e (Ideal.span {b}))*ρ e)*
    (idealRowHom (b*r) (Ideal.span {a})*star (idealRowHom (a*r) (Ideal.span {b}))*ρ (a*b))

end SevenEighths.CenteredMomentFirstAssembly

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondScaled
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentSmooth RayFourExpansion
open CenteredMomentProductCRT CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

def movingCoefficient {α : Type*} (A : O) (a : α → O) (c : α → ℂ) (i : α) : ℂ :=
  c i*idealRowHom A (Ideal.span {a i})

end SevenEighths.CenteredMomentSecondScaled

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def originalResidualRows (rows : Finset (Ideal Eis)) (R Q : Ideal Eis) : Finset (Ideal Eis) :=
  (representativeRowFiber rows R Q).image (fun I => rowResidualPart I Q)

lemma originalResidualRows_reconstruct (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (K : Ideal Eis) (hK : K∈originalResidualRows rows R Q) :
    reconstructFiberRow R Q K∈representativeRowFiber rows R Q ∧
      rowResidualPart (reconstructFiberRow R Q K) Q=K := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  have he := reconstructFiberRow_of_original rows R Q I hI (hrows I (Finset.mem_filter.mp hI).1)
  rw [he]
  exact ⟨hI,rfl⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
end


