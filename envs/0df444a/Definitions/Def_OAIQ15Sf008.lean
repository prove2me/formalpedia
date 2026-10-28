-- Prove2me | Definitions.Def_OAIQ15Sf008
-- name    : OAIQ15Sf008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:25:03.841348+00:00
-- url     : https://prove2.me/theorems/3f398f5f-610d-4ba9-9e40-2b92f5f2b354
-- title:
--   Definitions bundle OAIQ15Sf008 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 161 declarations of OpenAI's Lean: 72 definitions, 17 instances and 72 theorems. The definitions and types are `OAI.Kaplansky.RetainedGroupedSlot`, `OAI.Kaplansky.SemigroupDifference.flip`, `OAI.Kaplansky.complexDiagonalRelativeMap`, `OAI.Kaplansky.coordinateLineProjection`, `OAI.Kaplansky.evalStarWordPolynomial`, `OAI.Kaplansky.finiteLineFrameEquiv`, `OAI.Kaplansky.finiteLineFrameHomeomorph`, `OAI.Kaplansky.finiteLineFrameNormalization`, `OAI.Kaplansky.finiteLineFrameRelativeIso`, `OAI.Kaplansky.generatedWordPolynomial`, `OAI.Kaplansky.hyperplaneFunctionalSection`, `OAI.Kaplansky.lineFrameHomeomorph`, `OAI.Kaplansky.lineSumChartPullbackHomeomorph`, `OAI.Kaplansky.matrixPolynomialDegree`, `OAI.Kaplansky.matrixPolynomialTerm`, `OAI.Kaplansky.nonzeroBundle`, `OAI.Kaplansky.openChartCoordinateLocalHomologyIso`, `OAI.Kaplansky.openChartLocalExcisionIso`, `OAI.Kaplansky.operatorMatrixAction`, `OAI.Kaplansky.ordinarySectionClassMap`, `OAI.Kaplansky.productPairBaseSubsetIso`, `OAI.Kaplansky.productPairChartFiberMap`, `OAI.Kaplansky.productPairCoordinateMap`, `OAI.Kaplansky.productPairFiberMap`, `OAI.Kaplansky.productPairProjection`, `OAI.Kaplansky.productPairProjectionIso`, `OAI.Kaplansky.relativeChainSequenceMap`, `OAI.Kaplansky.relativeCoverChainComparison`, `OAI.Kaplansky.relativeCoverChainSequence`, `OAI.Kaplansky.relativeCoverLeftChainsIso`, `OAI.Kaplansky.relativeCoverLeftHomologyIso`, `OAI.Kaplansky.relativeCoverMiddleChainsIso`, `OAI.Kaplansky.relativeCoverMiddleHomologyIso`, `OAI.Kaplansky.relativeCoverQuotientSequence`, `OAI.Kaplansky.relativeCoverQuotientSequenceComparison`, `OAI.Kaplansky.relativeMayerVietorisBoundary`, `OAI.Kaplansky.relativeMayerVietorisSumSequence`, `OAI.Kaplansky.relativeMayerVietorisSumSequenceIso`, `OAI.Kaplansky.relativeOpenCoverGlue`, `OAI.Kaplansky.relativeOpenCoverHomologyIso` and 32 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Base`, `BundleTests_Normalization`, `BundleTests_Retained`, `BundleTests_Smooth`, `BundleTests_Twisted`, `ComplexBundle_CoordinatesMetric`, `ComplexBundle_Hyperplane`, `ComplexBundle_HyperplaneProduct`, `ComplexBundle_LineStage`, `ComplexBundle_Pullback`, `ComplexBundle_RealModel`, `ComplexBundle_Tensor`, `Cuntz_Monoid`, `Cuntz_Quasitrace`, `Cuntz_Translation`, `IntegralHomology_Compactification`, `IntegralHomology_Connected`, `IntegralHomology_Equivalence`, `IntegralHomology_Excision`, `IntegralHomology_FiniteCover`, `IntegralHomology_FrameNormalization`, `IntegralHomology_MayerVietoris`, `IntegralHomology_OpenUnion`, `IntegralHomology_Product`, `IntegralHomology_ProductCover`, `IntegralHomology_ProjectiveLocal`, `IntegralHomology_Relative`, `IntegralHomology_Simplex`, `IntegralHomology_SmallChains`, `IntegralHomology_SmallExcision`, `IntegralHomology_Sphere`, `Kaplansky_BundlePolynomials`, `Kaplansky_BundleWords`, `Kaplansky_Operators`, `Kaplansky_Polynomials`, `Kaplansky_Products`, `Kaplansky_Quotient_ClosedStarQuotient`, `Kaplansky_Regular_FreeNormal`, `Kaplansky_Regular_PowersAverages`, `Kaplansky_Regular_ReducedPolynomials`, `Kaplansky_Regular_ReducedTrace`, `Kaplansky_Regular_RegularOperators`, `OrderedStates_Semigroup`, `Quasitrace_Extension`.
--
--   **Imports.** It imports the published bundle `Def_KaplanskyStableFiniteness`; the bundles `OAIQ15Sf000`, `OAIQ15Sf001`, `OAIQ15Sf002`, `OAIQ15Sf003` and `OAIQ15Sf004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ15Sf010` and `OAIQ15Sf011`; the statements `OAI.KaplanskyConsequences.Regular.average_conjugated_partition_bound`, `OAI.KaplanskyConsequences.Regular.polynomial_average_small` and `OAI.KaplanskyConsequences.Regular.polynomial_dense_zero`; the proof of `OAI.KaplanskyConsequences.Regular.average_conjugated_partition_bound`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf000
import Definitions.Def_OAIQ15Sf001
import Definitions.Def_OAIQ15Sf002
import Definitions.Def_OAIQ15Sf003
import Definitions.Def_OAIQ15Sf004

section
-- module Solutions.OAIQ15_Sf.BundleTests_Base
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact bundle-test base, prefix dimensions, and retained multiplicities. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky

/-- A concrete basepoint in every projective factor. -/
def coordinateLineProjection (k : ℕ) : projectionSpace (k+1) 1 := by
  let f : Fin (k+1) → ℂ := fun j => if j = 0 then 1 else 0
  refine ⟨Matrix.diagonal f, ?_, ?_, ?_⟩
  · apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext j
    simp [f]
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp [f]
  · simp [Matrix.trace_diagonal, f]

end Kaplansky

end

namespace Kaplansky
open scoped BigOperators

/-- Count all copies of L_(i+1) in m copies of E_0⊕...⊕E_R.
The stages are enumerated in descending order. -/
def retainedHyperplaneMultiplicity (m R : ℕ) (i : Fin R) : ℕ :=
  m * ∑ t : Fin (R-i.val), testMultiplicity m R (R-t.val) ⟨i.val+1,by omega⟩

theorem retainedHyperplaneMultiplicity_eq (m R : ℕ) (i : Fin R) :
    retainedHyperplaneMultiplicity m R i = testProjectiveDimension m R i := by
  have ht : ∀ t : Fin (R-i.val),
      testMultiplicity m R (R-t.val) ⟨i.val+1,by omega⟩ =
        960*m*4^(2*i.val)*4^t.val := by
    intro t
    unfold testMultiplicity
    rw [ite_eq_right (by simp)]
    have he : R+2*(i.val+1)-(R-t.val)-2=2*i.val+t.val := by omega
    dsimp only
    rw [he,pow_add]
    ring
  unfold retainedHyperplaneMultiplicity
  simp_rw [ht]
  rw [← Finset.mul_sum]
  have hg : 3*(∑ t : Fin (R-i.val),4^t.val)=4^(R-i.val)-1 := by
    have h := three_sum_pow_four (R-i.val)
    omega
  unfold testProjectiveDimension
  rw [← hg]
  ring

/-- The exact rank of the retained trivial block, in descending stage order. -/
def retainedTrivialMultiplicity (m R : ℕ) : ℕ :=
  m * ∑ t : Fin (R+1), testMultiplicity m R (R-t.val) 0

end Kaplansky

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Tensor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Tensor line bundles, metrics, and finite frames. -/

section
open Bundle Topology
namespace Kaplansky

variable {B J : Type} [TopologicalSpace B]
  (C : VectorBundleCore ℂ B ℂ J) (u : ∀ b, C.Fiber b)
  (hu : ∀ b, u b ≠ 0)

variable (hc : Continuous (fun b => TotalSpace.mk' ℂ b (u b)))

/-- A nonzero continuous frame gives a homeomorphism for the original
line-core topology, with complex-linear fibers. -/
def lineFrameHomeomorph : TotalSpace ℂ C.Fiber ≃ₜ B × ℂ where
  toFun z := (z.proj,lineFrameEquiv C u hu z.proj z.2)
  invFun z := ⟨z.1,(lineFrameEquiv C u hu z.1).symm z.2⟩
  left_inv z := by
    obtain ⟨b,z⟩ := z
    exact congrArg (TotalSpace.mk' ℂ b) ((lineFrameEquiv C u hu b).symm_apply_apply z)
  right_inv z := Prod.ext rfl ((lineFrameEquiv C u hu z.1).apply_symm_apply z.2)
  continuous_toFun := by
    apply (FiberBundle.continuous_proj _ _).prodMk
    apply continuous_iff_continuousAt.mpr
    intro z
    let i := C.indexAt z.proj
    have hp := FiberBundle.continuous_proj ℂ C.Fiber
    have hv := ((C.localTriv i).continuousAt
      ((C.localTriv i).mem_source.mpr (C.mem_baseSet_at z.proj))).snd
    have hw : ContinuousAt (fun w : TotalSpace ℂ C.Fiber =>
        (C.localTriv i ⟨w.proj,u w.proj⟩).2) z :=
      ((FiberBundle.continuousAt_section ℂ z.proj).mp hc.continuousAt).comp hp.continuousAt
    have hn : (C.localTriv i ⟨z.proj,u z.proj⟩).2 ≠ 0 := by
      change C.coordChange (C.indexAt z.proj) i z.proj (u z.proj) ≠ 0
      intro h
      exact hu z.proj ((C.coordChange_self _ _ (C.mem_baseSet_at z.proj) (u z.proj)).symm.trans h)
    apply (hv.div hw hn).congr_of_eventuallyEq
    filter_upwards [hp.continuousAt ((C.isOpen_baseSet i).mem_nhds
      (C.mem_baseSet_at z.proj))] with w hw
    exact lineFrameEquiv_chart C u hu w.proj w.2 i hw
  continuous_invFun := by
    exact continuous_bundle_smul_over Prod.fst continuous_fst Prod.snd continuous_snd
      (fun z : B × ℂ => u z.1) (hc.comp continuous_fst)

variable {S : Type} [Fintype S] {I : S → Type}
  (D : ∀ s, VectorBundleCore ℂ B ℂ (I s))
  (v : ∀ s b, (D s).Fiber b) (hn : ∀ s b, v s b ≠ 0)
  (hv : ∀ s, Continuous (fun b => TotalSpace.mk' ℂ b (v s b)))

def finiteLineFrameEquiv (b : B) :
    (finiteLineSumCore D).Fiber b ≃ₗ[ℂ] (S → ℂ) :=
  (EuclideanSpace.equiv S ℂ).toLinearEquiv.trans
    (LinearEquiv.piCongrRight (fun s => lineFrameEquiv (D s) (v s) (hn s) b))

def finiteLineFrameHomeomorph :
    TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore D).Fiber ≃ₜ B × (S → ℂ) where
  toFun z := (z.proj,finiteLineFrameEquiv D v hn z.proj z.2)
  invFun z := ⟨z.1,(finiteLineFrameEquiv D v hn z.1).symm z.2⟩
  left_inv z := by
    obtain ⟨b,w⟩ := z
    exact congrArg (TotalSpace.mk' _ b) ((finiteLineFrameEquiv D v hn b).symm_apply_apply w)
  right_inv z := Prod.ext rfl ((finiteLineFrameEquiv D v hn z.1).apply_symm_apply z.2)
  continuous_toFun := by
    apply (FiberBundle.continuous_proj _ _).prodMk
    apply continuous_pi
    intro s
    exact continuous_snd.comp ((lineFrameHomeomorph (D s) (v s) (hn s) (hv s)).continuous.comp
      (continuous_finiteLineSumComponent D s))
  continuous_invFun := by
    apply (continuous_finiteLineSum_iff _ _).mpr
    refine ⟨continuous_fst,fun s => ?_⟩
    exact (lineFrameHomeomorph (D s) (v s) (hn s) (hv s)).symm.continuous.comp
      (continuous_fst.prodMk ((continuous_apply s).comp continuous_snd))

theorem finiteLineFrameHomeomorph_zero_iff
    (z : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore D).Fiber) :
    (finiteLineFrameHomeomorph D v hn hv z).2 = 0 ↔ z.2 = 0 :=
  (finiteLineFrameEquiv D v hn z.proj).map_eq_zero_iff

end Kaplansky

end

open Bundle Topology
open scoped InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Relative
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSingularChainsIntoSmallRight _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSmallSingularChainInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Integral relative singular chains, homology, and relative section maps. -/

section
open CategoryTheory Limits AlgebraicTopology

theorem relativeChainMap_comp {A X B Y C Z : TopCat.{0}}
    (i : A ⟶ X) (j : B ⟶ Y) (k : C ⟶ Z)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j)
    (b : B ⟶ C) (g : Y ⟶ Z) (h' : j ≫ g = b ≫ k) :
    relativeChainMap i j a f h ≫ relativeChainMap j k b g h' =
      relativeChainMap i k (a ≫ b) (f ≫ g) (by rw [← Category.assoc, h,
        Category.assoc, h', Category.assoc]) := by
  apply (cancel_epi (relativeChainProjection i)).mp
  simp [Functor.map_comp, Category.assoc]

end

section
open CategoryTheory Limits

theorem relativeHomologyBoundary_inclusion {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (n : ℕ) : relativeHomologyBoundary i n ≫ (integralSingularHomology n).map i = 0 :=
  (relativeChainSequence_shortExact i).δ_comp (n+1) n rfl

theorem inclusion_absoluteToRelative {A X : TopCat.{0}} (i : A ⟶ X) (n : ℕ) :
    (integralSingularHomology n).map i ≫ absoluteToRelative i n = 0 := by
  have hp : integralSingularChains.map i ≫ relativeChainProjection i = 0 :=
    cokernel.condition (integralSingularChains.map i)
  calc
    _ = HomologicalComplex.homologyMap
        (integralSingularChains.map i ≫ relativeChainProjection i) n :=
      (HomologicalComplex.homologyMap_comp (integralSingularChains.map i)
        (relativeChainProjection i) n).symm
    _ = 0 := by rw [hp]; exact HomologicalComplex.homologyMap_zero _ _ _

/-- All three positions in the relative singular homology long exact sequence. -/
theorem relativeHomology_exact_at_absolute {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (n : ℕ) : (ShortComplex.mk _ _ (inclusion_absoluteToRelative i n)).Exact :=
  (relativeChainSequence_shortExact i).homology_exact₂ n

theorem relativeHomology_exact_at_relative {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (n : ℕ) : (ShortComplex.mk _ _ (absoluteToRelative_boundary i n)).Exact :=
  (relativeChainSequence_shortExact i).homology_exact₃ (n+1) n rfl

def relativeChainSequenceMap {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) :
    relativeChainSequence i ⟶ relativeChainSequence j where
  τ₁ := integralSingularChains.map a
  τ₂ := integralSingularChains.map f
  τ₃ := relativeChainMap i j a f h
  comm₁₂ := by
    change integralSingularChains.map a ≫ integralSingularChains.map j =
      integralSingularChains.map i ≫ integralSingularChains.map f
    rw [← Functor.map_comp, ← h, Functor.map_comp]
  comm₂₃ := (relativeChainProjection_map i j a f h).symm

end

open Bundle Topology CategoryTheory OnePoint
section

variable {B V : Type} {E : B → Type} [∀ b, NormedAddCommGroup (E b)]

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace V E)]

/-- A class annihilated by the relative boundary lifts to absolute homology.
This is a consequence of the proved long exact sequence, not a lifting axiom. -/
theorem relativeClass_lifts_iff {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] (n : ℕ)
    (c : relativeSingularHomology i (n+1)) :
    relativeHomologyBoundary i n c = 0 ↔
      ∃ b : (integralSingularHomology (n+1)).obj X, absoluteToRelative i (n+1) b = c := by
  have h := (relativeHomology_exact_at_relative i n).moduleCat_range_eq_ker
  change c ∈ LinearMap.ker (relativeHomologyBoundary i n).hom ↔
    c ∈ LinearMap.range (absoluteToRelative i (n+1)).hom
  rw [h]

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Equivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSingularChainsIntoSmallRight _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSmallSingularChainInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Contractible-pair homology, equivalences, and relative map extensionality. -/

open CategoryTheory Limits HomologicalComplex ContinuousMap
section

/-- Singular chains of an actual homotopy equivalence form a quasi-isomorphism. -/
theorem integralChains_homotopyEquiv_quasiIso {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    QuasiIso (integralSingularChains.map (TopCat.ofHom e.toFun)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (integralHomologyHomotopyIso e n).hom
  infer_instance

/-- A map of genuine pairs whose ambient and subspace maps are homotopy
equivalences induces an isomorphism on relative homology in every degree. -/
theorem relativeHomologyMap_isIso_of_equivalences
    {A X B Y : Type} [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace B] [TopologicalSpace Y]
    (i : TopCat.of A ⟶ TopCat.of X) (j : TopCat.of B ⟶ TopCat.of Y)
    [Mono i] [Mono j] (a : A ≃ₕ B) (f : X ≃ₕ Y)
    (h : i ≫ TopCat.ofHom f.toFun = TopCat.ofHom a.toFun ≫ j) (n : ℕ) :
    IsIso (relativeHomologyMap i j (TopCat.ofHom a.toFun) (TopCat.ofHom f.toFun) h n) := by
  have hq : QuasiIso (relativeChainMap i j (TopCat.ofHom a.toFun)
      (TopCat.ofHom f.toFun) h) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃
      (relativeChainSequenceMap i j _ _ h)
      (relativeChainSequence_shortExact i) (relativeChainSequence_shortExact j)
      (integralChains_homotopyEquiv_quasiIso a) (integralChains_homotopyEquiv_quasiIso f)
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp ((quasiIso_iff _).mp hq n)

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_SmallChains
attribute [-instance] _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Simplicial gluing, small singular subcomplexes, and cover meshes. -/

open CategoryTheory Topology Filter
section
variable {P X : Type} [PseudoMetricSpace P] [CompactSpace P] [TopologicalSpace X]

open Simplicial
variable {X : Type} [TopologicalSpace X]

instance standardSimplexMetricSpace (Index : Type*) [Fintype Index] :
    MetricSpace (OAI.SStd ℝ Index) :=
  (OAI.SStd.isEmbedding_toFun_comp_weights ℝ Index).comapMetricSpace
    (fun simplex => (simplex.weights : Index → ℝ))

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_SmallExcision
attribute [-instance] _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Small relative excision, Mayer-Vietoris, and naturality. -/

open CategoryTheory Limits
section
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (U V : Set X) (U' V' : Set Y) (f : C(X,Y))
  (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')

theorem smallSingularChainsContinuousMap_mono (hf : Function.Injective f) :
    Mono (smallSingularChainsContinuousMap U V U' V' f hU hV) := by
  have : Mono (TopCat.ofHom f) := (TopCat.mono_iff_injective _).mpr hf
  have : Mono (integralSingularChains.map (TopCat.ofHom f)) := by
    unfold integralSingularChains
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
  exact mono_of_mono_fac (smallSingularChainsContinuousMap_inclusion U V U' V' f hU hV)

/-- Naturality includes the intersection term and the signs of the
Mayer–Vietoris differential. -/
def smallMayerVietorisContinuousMap :
    smallMayerVietorisSequence U V ⟶ smallMayerVietorisSequence U' V' where
  τ₁ := integralSingularChains.map
    (subspaceMap (U ∩ V) (U' ∩ V') f (fun _ hx => ⟨hU hx.1, hV hx.2⟩))
  τ₂ := biprod.map (integralSingularChains.map (subspaceMap U U' f hU))
    (integralSingularChains.map (subspaceMap V V' f hV))
  τ₃ := smallSingularChainsContinuousMap U V U' V' f hU hV
  comm₁₂ := by
    apply biprod.hom_ext <;>
      simp [smallMayerVietorisSequence, CommSq.shortComplex, Category.assoc,
        ← Functor.map_comp] <;> rfl
  comm₂₃ := by
    apply biprod.hom_ext' <;>
      simp [smallMayerVietorisSequence, CommSq.shortComplex]

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Simplex
attribute [-instance] _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Affine simplex chains, mesh geometry, and universal subdivision. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial Convexity

instance simplexMetricSpace {κ : Type} [Fintype κ] : MetricSpace (OAI.SStd ℝ κ) :=
  Topology.IsEmbedding.comapMetricSpace
    (fun point : OAI.SStd ℝ κ => (point.weights : κ → ℝ))
    (OAI.SStd.isEmbedding_toFun_comp_weights ℝ κ)

end

open CategoryTheory Limits AlgebraicTopology Simplicial Convexity

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_MayerVietoris
attribute [-instance] _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Relative Mayer-Vietoris comparison, exactness, and gluing. -/

section
open CategoryTheory Limits HomologicalComplex

section
variable {X : Type} [TopologicalSpace X] (U V A : Set X)

/-- The inclusion of the removed subspace, with its induced two-set cover. -/
def removedCoverSequenceMap :
    smallMayerVietorisSequence (Subtype.val ⁻¹' U : Set A) (Subtype.val ⁻¹' V : Set A) ⟶
      smallMayerVietorisSequence U V :=
  smallMayerVietorisContinuousMap _ _ U V
    ⟨Subtype.val, continuous_subtype_val⟩ (fun _ h => h) (fun _ h => h)

theorem removedCoverSequenceMap_mono : Mono (removedCoverSequenceMap U V A).τ₃ :=
  smallSingularChainsContinuousMap_mono _ _ _ _ _ _ _ Subtype.val_injective

/-- The relative gluing sequence formed using the actual singular chains
of A. Its right term compares directly with C(X)/C(A). -/
def relativeCoverChainSequence := quotientShortComplex (removedCoverSequenceMap U V A)

theorem relativeCoverChainSequence_shortExact :
    (relativeCoverChainSequence U V A).ShortExact := by
  have := removedCoverSequenceMap_mono U V A
  exact quotientShortComplex_shortExact _
    (smallMayerVietorisSequence_shortExact _ _) (smallMayerVietorisSequence_shortExact _ _)

def relativeCoverChainComparison : (relativeCoverChainSequence U V A).X₃ ⟶
    relativeSingularChains (subspaceInclusion A) :=
  cokernel.map _ _ (smallSingularChainInclusion _ _) (smallSingularChainInclusion U V)
    (smallSingularChainsContinuousMap_inclusion _ _ _ _ _ _ _)

def relativeCoverQuotientSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (removedCoverSequenceMap U V A).τ₃ (cokernel.π _)
    (cokernel.condition _)

theorem relativeCoverQuotientSequence_shortExact :
    (relativeCoverQuotientSequence U V A).ShortExact := by
  have := removedCoverSequenceMap_mono U V A
  exact {
    exact := ShortComplex.exact_cokernel _
    mono_f := removedCoverSequenceMap_mono U V A
    epi_g := coequalizer.π_epi (f := (removedCoverSequenceMap U V A).τ₃) (g := 0) }

def relativeCoverQuotientSequenceComparison : relativeCoverQuotientSequence U V A ⟶
    relativeChainSequence (subspaceInclusion A) where
  τ₁ := smallSingularChainInclusion _ _
  τ₂ := smallSingularChainInclusion U V
  τ₃ := relativeCoverChainComparison U V A
  comm₁₂ := (smallSingularChainsContinuousMap_inclusion _ _ _ _ _ _ _).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- Subdivision on both X and A proves comparison with full relative
singular chains. No openness of A is needed. -/
theorem relativeCoverChainComparison_quasiIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) : QuasiIso (relativeCoverChainComparison U V A) := by
  have hA : (Subtype.val ⁻¹' U : Set A) ∪ (Subtype.val ⁻¹' V : Set A) = Set.univ := by
    rw [← Set.preimage_union, hcover, Set.preimage_univ]
  exact HomologySequence.quasiIso_τ₃
    (relativeCoverQuotientSequenceComparison U V A)
    (relativeCoverQuotientSequence_shortExact U V A)
    (relativeChainSequence_shortExact (subspaceInclusion A))
    (smallSingularChainInclusion_quasiIso _ _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) hA)
    (smallSingularChainInclusion_quasiIso U V hU hV hcover)

def relativeOpenCoverHomologyIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (relativeCoverChainSequence U V A).X₃.homology n ≅
      relativeSingularHomology (subspaceInclusion A) n := by
  have := relativeCoverChainComparison_quasiIso U V A hU hV hcover
  exact isoOfQuasiIsoAt (relativeCoverChainComparison U V A) n

end

section
variable {X : Type} [TopologicalSpace X]

def removedRestrictionMap (U A : Set X) :
    TopCat.of (Subtype.val ⁻¹' U : Set A) ⟶ TopCat.of U :=
  subspaceMap _ U ⟨Subtype.val, continuous_subtype_val⟩ (fun _ h => h)

/-- The relative chain group in a chart uses its actual removed subspace. -/
def removedRestrictionChainsIso (U A : Set X) :
    cokernel (integralSingularChains.map (removedRestrictionMap U A)) ≅
      relativeSingularChains (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) :=
  cokernel.mapIso _ _
    (integralSingularChains.mapIso (TopCat.isoOfHomeo (intersectionSubtypeSwap U A)))
    (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom]
      rw [← Functor.map_comp]
      rfl)

@[reassoc (attr := simp)]
theorem removedRestrictionChainsIso_projection (U A : Set X) :
    cokernel.π (integralSingularChains.map (removedRestrictionMap U A)) ≫
      (removedRestrictionChainsIso U A).hom =
        relativeChainProjection (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) := by
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

def relativeCoverLeftChainsIso (U V A : Set X) :
    (relativeCoverChainSequence U V A).X₁ ≅
      relativeSingularChains (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) :=
  removedRestrictionChainsIso (U ∩ V) A

def relativeCoverMiddleChainsIso (U V A : Set X) :
    (relativeCoverChainSequence U V A).X₂ ≅
      relativeSingularChains (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) ⊞
        relativeSingularChains (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) :=
  cokernelBiprodIso _ _ ≪≫
    biprod.mapIso (removedRestrictionChainsIso U A) (removedRestrictionChainsIso V A)

def relativeCoverLeftHomologyIso (U V A : Set X) (n : ℕ) :
    (relativeCoverChainSequence U V A).X₁.homology n ≅
      relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n :=
  (homologyFunctor _ _ n).mapIso (relativeCoverLeftChainsIso U V A)

attribute [local instance] OAI.Kaplansky.instPreservesBinaryBiproductsHomologicalComplexNatModuleCatIntDownHomologyFunctor_solutions
def relativeCoverMiddleHomologyIso (U V A : Set X) (n : ℕ) :
    (relativeCoverChainSequence U V A).X₂.homology n ≅
      relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n ⊞
        relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) n :=
  (homologyFunctor _ _ n).mapIso (relativeCoverMiddleChainsIso U V A) ≪≫
    (homologyFunctor _ _ n).mapBiprod _ _

end

section
variable {X : Type} [TopologicalSpace X]

/-- Inclusion of restricted pairs (U,U∩A) into (V,V∩A). -/
def restrictedPairChainMap {U V : Set X} (h : U ⊆ V) (A : Set X) :=
  relativeChainMap (subspaceInclusion (Subtype.val ⁻¹' A : Set U))
    (subspaceInclusion (Subtype.val ⁻¹' A : Set V))
    (subspaceMap _ _ (subspaceInclusionOfLE h).hom (fun _ hx => hx))
    (subspaceInclusionOfLE h) (by rfl)

/-- Inclusion of the actual chart pair into the whole pair. -/
def restrictedPairToAmbientChainMap (U A : Set X) :=
  relativeChainMap (subspaceInclusion (Subtype.val ⁻¹' A : Set U))
    (subspaceInclusion A)
    (subspaceMap _ _ ⟨Subtype.val,continuous_subtype_val⟩ (fun _ hx => hx))
    (subspaceInclusion U) (by rfl)

def restrictedPairHomologyMap {U V : Set X} (h : U ⊆ V) (A : Set X) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n ⟶
      relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) n :=
  homologyMap (restrictedPairChainMap h A) n

def restrictedPairToAmbientHomologyMap (U A : Set X) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n ⟶
      relativeSingularHomology (subspaceInclusion A) n :=
  homologyMap (restrictedPairToAmbientChainMap U A) n

theorem restrictedPairChainMap_toAmbient {U V : Set X} (h : U ⊆ V) (A : Set X) :
    restrictedPairChainMap h A ≫ restrictedPairToAmbientChainMap V A =
      restrictedPairToAmbientChainMap U A := by
  unfold restrictedPairChainMap restrictedPairToAmbientChainMap
  erw [relativeChainMap_comp]
  rfl

theorem restrictedPairHomologyMap_toAmbient {U V : Set X} (h : U ⊆ V)
    (A : Set X) (n : ℕ) :
    restrictedPairHomologyMap h A n ≫ restrictedPairToAmbientHomologyMap V A n =
      restrictedPairToAmbientHomologyMap U A n := by
  unfold restrictedPairHomologyMap restrictedPairToAmbientHomologyMap
  erw [← homologyMap_comp, restrictedPairChainMap_toAmbient]

theorem relativeCoverMiddleChainsIso_projection (U V A : Set X) :
    cokernel.π (removedCoverSequenceMap U V A).τ₂ ≫
      (relativeCoverMiddleChainsIso U V A).hom =
    biprod.map (relativeChainProjection (subspaceInclusion (Subtype.val ⁻¹' A : Set U)))
      (relativeChainProjection (subspaceInclusion (Subtype.val ⁻¹' A : Set V))) := by
  change cokernel.π (biprod.map _ _) ≫
    ((cokernelBiprodIso _ _).hom ≫
      (biprod.mapIso (removedRestrictionChainsIso U A) (removedRestrictionChainsIso V A)).hom) = _
  erw [← Category.assoc, cokernelBiprodIso_projection, biprod.mapIso_hom]
  apply biprod.hom_ext
  · erw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.map_fst,
      Category.assoc, removedRestrictionChainsIso_projection, biprod.map_fst]
  · erw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.map_snd,
      Category.assoc, removedRestrictionChainsIso_projection, biprod.map_snd]

/-- Identification of the left gluing map, including its minus sign, with
the two actual inclusions of intersection pairs. -/
theorem relativeCoverLeftChainsIso_map (U V A : Set X) :
    (relativeCoverLeftChainsIso U V A).hom ≫
      biprod.lift (restrictedPairChainMap (Set.inter_subset_left : U ∩ V ⊆ U) A)
        (-restrictedPairChainMap (Set.inter_subset_right : U ∩ V ⊆ V) A) =
    (relativeCoverChainSequence U V A).f ≫ (relativeCoverMiddleChainsIso U V A).hom := by
  apply (cancel_epi (cokernel.π (removedCoverSequenceMap U V A).τ₁)).mp
  have hl := removedRestrictionChainsIso_projection (U ∩ V) A
  change cokernel.π (removedCoverSequenceMap U V A).τ₁ ≫
    (relativeCoverLeftChainsIso U V A).hom = _ at hl
  erw [← Category.assoc, hl]
  erw [cokernel.π_desc_assoc, Category.assoc, relativeCoverMiddleChainsIso_projection]
  change _ = biprod.lift
    (integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)))
    (-integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V))) ≫ _
  apply biprod.hom_ext
  · erw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst,
      ← Category.assoc (biprod.lift _ _) biprod.fst, biprod.lift_fst]
    exact relativeChainProjection_map _ _ _ _ _
  · erw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd,
      ← Category.assoc (biprod.lift _ _) biprod.snd, biprod.lift_snd,
      Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg (relativeChainProjection_map _ _ _ _ _)

/-- Identification of the right gluing map with the sum of the actual
inclusions into (X,A), after the proved small-to-full chain comparison. -/
theorem relativeCoverMiddleChainsIso_map (U V A : Set X) :
    (relativeCoverMiddleChainsIso U V A).hom ≫
      biprod.desc (restrictedPairToAmbientChainMap U A) (restrictedPairToAmbientChainMap V A) =
    (relativeCoverChainSequence U V A).g ≫ relativeCoverChainComparison U V A := by
  apply (cancel_epi (cokernel.π (removedCoverSequenceMap U V A).τ₂)).mp
  erw [← Category.assoc, relativeCoverMiddleChainsIso_projection]
  erw [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc]
  change _ = biprod.desc (singularChainsIntoSmallLeft U V) (singularChainsIntoSmallRight U V) ≫
    smallSingularChainInclusion U V ≫ _
  apply biprod.hom_ext'
  · erw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc,
      ← Category.assoc (singularChainsIntoSmallLeft U V), singularChainsIntoSmallLeft_inclusion]
    exact relativeChainProjection_map _ _ _ _ _
  · erw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc,
      ← Category.assoc (singularChainsIntoSmallRight U V), singularChainsIntoSmallRight_inclusion]
    exact relativeChainProjection_map _ _ _ _ _

end

section
variable {X : Type} [TopologicalSpace X] (U V A : Set X)

attribute [local instance] OAI.Kaplansky.instPreservesBinaryBiproductsHomologicalComplexNatModuleCatIntDownHomologyFunctor_solutions_1
theorem relativeCoverLeftHomologyIso_map (n : ℕ) :
    (relativeCoverLeftHomologyIso U V A n).hom ≫
      biprod.lift (restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A n)
        (-restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A n) =
    homologyMap (relativeCoverChainSequence U V A).f n ≫
      (relativeCoverMiddleHomologyIso U V A n).hom := by
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  change F.map (relativeCoverLeftChainsIso U V A).hom ≫
    biprod.lift (F.map (restrictedPairChainMap _ A)) (-F.map (restrictedPairChainMap _ A)) =
      F.map (relativeCoverChainSequence U V A).f ≫
        (F.map (relativeCoverMiddleChainsIso U V A).hom ≫ (F.mapBiprod _ _).hom)
  rw [← F.map_neg, ← biprod.map_lift_mapBiprod F, ← Category.assoc,
    ← F.map_comp, relativeCoverLeftChainsIso_map, F.map_comp, Category.assoc]

theorem relativeCoverMiddleHomologyIso_map (n : ℕ) :
    (relativeCoverMiddleHomologyIso U V A n).hom ≫
      biprod.desc (restrictedPairToAmbientHomologyMap U A n) (restrictedPairToAmbientHomologyMap V A n) =
    homologyMap (relativeCoverChainSequence U V A).g n ≫
      homologyMap (relativeCoverChainComparison U V A) n := by
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  change (F.map (relativeCoverMiddleChainsIso U V A).hom ≫ (F.mapBiprod _ _).hom) ≫
    biprod.desc (F.map (restrictedPairToAmbientChainMap U A))
      (F.map (restrictedPairToAmbientChainMap V A)) =
    F.map (relativeCoverChainSequence U V A).g ≫ F.map (relativeCoverChainComparison U V A)
  rw [Category.assoc, biprod.mapBiprod_hom_desc, ← F.map_comp,
    relativeCoverMiddleChainsIso_map, F.map_comp]

/-- The exact relative Mayer–Vietoris sequence at the direct sum, with
the standard signed intersection map and actual pair inclusions. -/
def relativeMayerVietorisSumSequence (n : ℕ) : ShortComplex (ModuleCat.{0} ℤ) where
  f := biprod.lift (restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A n)
    (-restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A n)
  g := biprod.desc (restrictedPairToAmbientHomologyMap U A n) (restrictedPairToAmbientHomologyMap V A n)
  zero := by simp [restrictedPairHomologyMap_toAmbient]

def relativeMayerVietorisSumSequenceIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    ((relativeCoverChainSequence U V A).map (homologyFunctor _ _ n)) ≅
      relativeMayerVietorisSumSequence U V A n :=
  ShortComplex.isoMk (relativeCoverLeftHomologyIso U V A n)
    (relativeCoverMiddleHomologyIso U V A n)
    (relativeOpenCoverHomologyIso U V A hU hV hcover n)
    (relativeCoverLeftHomologyIso_map U V A n)
    (relativeCoverMiddleHomologyIso_map U V A n)

theorem relativeMayerVietoris_exact_at_sum (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (relativeMayerVietorisSumSequence U V A n).Exact :=
  ShortComplex.exact_of_iso (relativeMayerVietorisSumSequenceIso U V A hU hV hcover n)
    ((relativeCoverChainSequence_shortExact U V A).homology_exact₂ n)

/-- The connecting map on the actual full relative homology groups. -/
def relativeMayerVietorisBoundary (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :=
  (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1)).inv ≫
    (relativeCoverChainSequence_shortExact U V A).δ (n+1) n rfl ≫
      (relativeCoverLeftHomologyIso U V A n).hom

theorem relativeMayerVietoris_sum_boundary (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (relativeMayerVietorisSumSequence U V A (n+1)).g ≫
      relativeMayerVietorisBoundary U V A hU hV hcover n = 0 := by
  exact comp_zero_of_iso
    (relativeCoverMiddleHomologyIso U V A (n+1))
    (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1))
    (relativeCoverLeftHomologyIso U V A n) _ _ _ _
    (relativeCoverMiddleHomologyIso_map U V A (n+1))
    ((relativeOpenCoverHomologyIso U V A hU hV hcover (n+1)).hom_inv_id_assoc _)
    ((relativeCoverChainSequence_shortExact U V A).comp_δ (n+1) n rfl)

theorem relativeMayerVietoris_exact_at_relative (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk _ _ (relativeMayerVietoris_sum_boundary U V A hU hV hcover n)).Exact := by
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (relativeCoverMiddleHomologyIso U V A (n+1))
      (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1))
      (relativeCoverLeftHomologyIso U V A n)
      (relativeCoverMiddleHomologyIso_map U V A (n+1)) ?_)
    ((relativeCoverChainSequence_shortExact U V A).homology_exact₃ (n+1) n rfl)
  exact (relativeOpenCoverHomologyIso U V A hU hV hcover (n+1)).hom_inv_id_assoc _

end

variable {X : Type} [TopologicalSpace X] (U V A : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
include hU hV hcover

/-- Below the overlap degree, the two actual chart maps jointly generate
the full relative homology group. -/
theorem relativeOpenCover_sum_epi (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n)) :
    Epi (relativeMayerVietorisSumSequence U V A (n+1)).g := by
  have hex := relativeMayerVietoris_exact_at_relative U V A hU hV hcover n
  exact (ShortComplex.exact_iff_epi _ (hi.eq_of_tgt _ _)).mp hex

/-- Compatible local linear normalizations glue to a genuine global
normalization when the preceding overlap group vanishes. -/
def relativeOpenCoverGlue (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (u : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1) ⟶ Z)
    (v : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1) ⟶ Z)
    (hcompat : restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A (n+1) ≫ u =
      restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A (n+1) ≫ v) :
    relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z := by
  have := relativeOpenCover_sum_epi U V A hU hV hcover n hi
  exact (relativeMayerVietoris_exact_at_sum U V A hU hV hcover (n+1)).desc
    (biprod.desc u v) (by
      dsimp only [relativeMayerVietorisSumSequence]
      erw [biprod.lift_desc, Preadditive.neg_comp, hcompat, add_neg_cancel]
      rfl)

end

open CategoryTheory Limits HomologicalComplex

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Pullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Pullback line bundles and their continuous chart identifications. -/

section
open Bundle Topology
namespace Kaplansky

variable {B A X J : Type} [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace X]

/-- Continuity into the core pullback is exactly continuity in the base
and continuity of the induced map to the original total space. -/
theorem continuous_pullbackLineCore_total_iff (C : VectorBundleCore ℂ B ℂ J)
    (f : C(A,B)) (g : X → A) (v : X → ℂ) :
    Continuous (fun x => TotalSpace.mk' ℂ (g x)
      (show (pullbackLineCore C f).Fiber (g x) from v x)) ↔
    Continuous g ∧ Continuous (fun x => TotalSpace.mk' ℂ (f (g x))
      (show C.Fiber (f (g x)) from v x)) := by
  constructor
  · intro h
    have hg := (FiberBundle.continuous_proj ℂ (pullbackLineCore C f).Fiber).comp h
    refine ⟨hg, continuous_iff_continuousAt.mpr (fun x => ?_)⟩
    rw [FiberBundle.continuousAt_totalSpace]
    exact ⟨(f.continuous.comp hg).continuousAt,
      ((FiberBundle.continuousAt_totalSpace ℂ _).mp h.continuousAt).2⟩
  · rintro ⟨hg,hv⟩
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    exact ⟨hg.continuousAt,
      ((FiberBundle.continuousAt_totalSpace ℂ _).mp hv.continuousAt).2⟩

variable {S : Type} [Fintype S] {J : S → Type}

/-- The same assertion for the actual finite Hermitian sum. -/
theorem continuous_pullbackLineSum_total_iff (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))
    (f : C(A,B)) (g : X → A) (v : X → EuclideanSpace ℂ S) :
    Continuous (fun x => TotalSpace.mk' (EuclideanSpace ℂ S) (g x)
      (show (finiteLineSumCore (fun s => pullbackLineCore (C s) f)).Fiber (g x) from v x)) ↔
    Continuous g ∧ Continuous (fun x => TotalSpace.mk' (EuclideanSpace ℂ S) (f (g x))
      (show (finiteLineSumCore C).Fiber (f (g x)) from v x)) := by
  rw [continuous_finiteLineSum_iff, continuous_finiteLineSum_iff]
  constructor
  · rintro ⟨hg,hv⟩
    exact ⟨hg, f.continuous.comp hg, fun s =>
      (continuous_pullbackLineCore_total_iff (C s) f g (fun x => v x s)).mp (hv s) |>.2⟩
  · rintro ⟨hg,_,hv⟩
    exact ⟨hg, fun s =>
      (continuous_pullbackLineCore_total_iff (C s) f g (fun x => v x s)).mpr ⟨hg,hv s⟩⟩

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
variable {B A S : Type} [TopologicalSpace B] [TopologicalSpace A]
  [Fintype S] {J : S → Type}
  (C : ∀ s, VectorBundleCore ℂ B ℂ (J s)) (U : Set B) (e : U ≃ₜ A)

/-- Pulling the actual sum into full chart coordinates gives exactly the
restriction of its original total space, with its inherited topology. -/
def lineSumChartPullbackHomeomorph :
    TotalSpace (EuclideanSpace ℂ S)
      (finiteLineSumCore (fun s => pullbackLineCore (C s) (chartBaseMap U e))).Fiber ≃ₜ
    {z : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber | z.proj ∈ U} where
  toFun z := ⟨⟨chartBaseMap U e z.proj,z.2⟩,(e.symm z.proj).2⟩
  invFun z := ⟨e ⟨z.1.proj,z.2⟩,z.1.2⟩
  left_inv z := by
    obtain ⟨a,v⟩ := z
    change TotalSpace.mk' _ (e (e.symm a)) v = TotalSpace.mk' _ a v
    rw [e.apply_symm_apply]
  right_inv z := by
    apply Subtype.ext
    obtain ⟨⟨b,v⟩,hb⟩ := z
    change TotalSpace.mk' _ (e.symm (e ⟨b,hb⟩)).val v = TotalSpace.mk' _ b v
    rw [e.symm_apply_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_pullbackLineSum_total_iff C (chartBaseMap U e)
      (fun z : TotalSpace (EuclideanSpace ℂ S)
        (finiteLineSumCore (fun s => pullbackLineCore (C s) (chartBaseMap U e))).Fiber => z.proj)
      (fun z => z.2)).mp continuous_id |>.2
  continuous_invFun := by
    apply (continuous_pullbackLineSum_total_iff C (chartBaseMap U e) _ _).mpr
    constructor
    · exact e.continuous.comp
        (((FiberBundle.continuous_proj _ _).comp continuous_subtype_val).subtype_mk _)
    · convert continuous_subtype_val using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      change TotalSpace.mk' _ (e.symm (e ⟨z.1.proj,z.2⟩)).val z.1.2 = z.1
      rw [e.symm_apply_apply]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_RealModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real models of complex bundles and smooth finite line sums. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky

section
variable {B F J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] (C : VectorBundleCore ℂ B F J)

instance complexCoreRealFiberComplexModule (x : B) : Module ℂ ((complexCoreReal C).Fiber x) :=
  inferInstanceAs (Module ℂ F)

instance complexCoreRealFiberComplexVectorBundle : VectorBundle ℂ F (complexCoreReal C).Fiber :=
  inferInstanceAs (VectorBundle ℂ F C.Fiber)

end

end Kaplansky

end

open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
variable {B F G J : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  (C : VectorBundleCore ℂ B F J) (e : F ≃L[ℂ] G)

instance changeModelFiberNorm (x : B) : NormedAddCommGroup ((changeModelCore C e).Fiber x) :=
  inferInstanceAs (NormedAddCommGroup G)
instance changeModelFiberNormedSpace (x : B) : NormedSpace ℂ ((changeModelCore C e).Fiber x) :=
  inferInstanceAs (NormedSpace ℂ G)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_LineStage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Doubling stages of line bundles and their Hilbert direct sums. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

attribute [instance] LineStage.finiteSlot

end Kaplansky

end

namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} [Fintype ι] {K : ι → ℕ}

/-- The actual stage fibers have their finite-dimensional Hilbert-space
instances directly from the finite orthogonal sum model. -/
instance lineStage_finite (a : LineStage K) (y : ProjectiveProduct K) :
    FiniteDimensional ℂ (a.Fiber y) :=
  inferInstanceAs (FiniteDimensional ℂ (EuclideanSpace ℂ a.Slot))
instance lineStage_complete (a : LineStage K) (y : ProjectiveProduct K) :
    CompleteSpace (a.Fiber y) :=
  inferInstanceAs (CompleteSpace (EuclideanSpace ℂ a.Slot))

end Kaplansky

open scoped BigOperators
namespace Kaplansky.LineStage
open ComplexGrassmann
variable {ι : Type*} {J : Type} [Fintype J] {K : ι → ℕ}

theorem sum_inner (a : J → LineStage K) (y : ProjectiveProduct K)
    (v w : (sum a).Fiber y) :
    inner ℂ v w = ∑ j, inner ℂ (sumProj a j y v) (sumProj a j y w) := by
  change (∑ s : Σ j : J, (a j).Slot,
    inner ℂ ((show (sum a).Model from v) s) ((show (sum a).Model from w) s)) =
    ∑ j : J, ∑ s : (a j).Slot,
      inner ℂ ((show (sum a).Model from v) ⟨j,s⟩) ((show (sum a).Model from w) ⟨j,s⟩)
  exact Fintype.sum_sigma _

end Kaplansky.LineStage

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Hyperplane
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hyperplane sections, dual evaluation, graph coordinates, and their zero. -/

section
open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {d : ℕ}

/-- Restrict an ambient linear functional to each actual tautological line,
viewed as a section of its dual, the hyperplane bundle. -/
def hyperplaneFunctionalSection (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ)
    (p : projectionSpace d 1) : (projectionDualLineCore d).Fiber p :=
  L (unitProjectionColumn p ((projectionLineCore d).indexAt p))

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky

theorem vector_eq_firstCoordinate_of_positive_zero {k : ℕ}
    (v : EuclideanSpace ℂ (Fin (1+k))) (hv : ∀ i : Fin k, v (positiveCoordinate k i)=0) :
    v=(v 0) • firstCoordinateVector k := by
  ext j
  by_cases hj : j=0
  · subst j
    simp [firstCoordinateVector]
  · have hpos : 0<j.val := by
      have : j.val≠0 := fun h => hj (Fin.ext h)
      omega
    let i : Fin k := ⟨j.val-1,by omega⟩
    have hi : positiveCoordinate k i=j := Fin.ext (by dsimp [positiveCoordinate,i]; omega)
    have hzero := hv i
    rw [hi] at hzero
    simp [firstCoordinateVector,hj,hzero]

end Kaplansky

open Bundle Topology
open scoped InnerProductSpace

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_HyperplaneProduct
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hyperplane product sections and regular zeros. -/

section
open Bundle Topology
namespace Kaplansky

/-- Pullback of a genuine continuous section through the actual line-core
pullback construction. -/
theorem continuous_pullbackLineCore_section {B X J : Type*} [TopologicalSpace B] [TopologicalSpace X]
    (C : VectorBundleCore ℂ B ℂ J) (g : C(X,B)) (s : ∀ b, C.Fiber b)
    (hs : Continuous (fun b => TotalSpace.mk' ℂ b (s b))) :
    Continuous (fun x => TotalSpace.mk' ℂ x (show (pullbackLineCore C g).Fiber x from s (g x))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_section]
  exact ((FiberBundle.continuousAt_section ℂ (g x)).mp (hs.continuousAt (x := g x))).comp g.continuous.continuousAt

open ComplexGrassmann

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Excision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Excision for chart-small chains, open covers, and open embeddings. -/

open CategoryTheory Limits HomologicalComplex
section
variable {X : Type} [TopologicalSpace X] [T1Space X]

/-- Excision at any point of an open chart, using the preserved chain-level
comparison and the proved open-cover small-chain theorem. -/
def openChartLocalExcisionIso (U : Set X) (hU : IsOpen U) (x : X) (hx : x ∈ U) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion ({⟨x,hx⟩}ᶜ : Set U)) n ≅
      relativeSingularHomology (subspaceInclusion ({x}ᶜ : Set X)) n := by
  haveI := smallRelativeComparison_quasiIso U ({x}ᶜ : Set X)
    (smallSingularChainInclusion_quasiIso U _ hU isClosed_singleton.isOpen_compl
      (chart_punctured_cover U x hx))
  exact (homologyFunctor _ _ n).mapIso (chartSmallRelativeChainsIso U x hx) ≪≫
    isoOfQuasiIsoAt (smallRelativeComparison U ({x}ᶜ : Set X)) n

/-- Local homology in a full open vector-space chart, at an arbitrary point. -/
def openChartCoordinateLocalHomologyIso {E : Type} [NormedAddCommGroup E]
    (U : Set X) (hU : IsOpen U) (x : X) (hx : x ∈ U) (e : U ≃ₜ E) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion ({x}ᶜ : Set X)) n ≅
      relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set E)) n :=
  (openChartLocalExcisionIso U hU x hx n).symm ≪≫
    relativeHomologyHomeomorphIso (centeredChartHomeomorph U x hx e) _ _
      (fun y => by
        change y ≠ ⟨x,hx⟩ ↔ centeredChartHomeomorph U x hx e y ≠ 0
        rw [← centeredChartHomeomorph_center U x hx e]
        exact (not_congr (centeredChartHomeomorph U x hx e).injective.eq_iff).symm) n

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_OpenUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Vanishing of homology under open unions and finite covers. -/

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X]

/-- Actual open-cover Mayer–Vietoris vanishing, with all three adjacent
groups explicit. No contractibility hypothesis is required. -/
theorem openCoverHomology_isZero (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hu : IsZero ((integralSingularHomology (n+1)).obj (TopCat.of U)))
    (hv : IsZero ((integralSingularHomology (n+1)).obj (TopCat.of V)))
    (hi : IsZero ((integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)))) :
    IsZero ((integralSingularHomology (n+1)).obj (TopCat.of X)) := by
  have hs := homology_biprod_isZero _ _ (n+1) hu hv
  have he := (smallMayerVietorisSequence_shortExact U V).homology_exact₃ (n+1) n rfl
  exact (he.isZero_of_both_isZero hs hi).of_iso
    (openCoverSmallHomologyIso U V hU hV hUV (n+1)).symm

/-- Mayer–Vietoris for an open union viewed as a subspace of the ambient space. -/
theorem openUnionHomology_isZero (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ)
    (hu : IsZero ((integralSingularHomology (n+1)).obj (TopCat.of U)))
    (hv : IsZero ((integralSingularHomology (n+1)).obj (TopCat.of V)))
    (hi : IsZero ((integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)))) :
    IsZero ((integralSingularHomology (n+1)).obj (TopCat.of ↥(U ∪ V))) := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact x.property
  apply openCoverHomology_isZero U' V' (hU.preimage continuous_subtype_val)
    (hV.preimage continuous_subtype_val) hcov n
  · exact hu.of_iso (integralHomologyHomotopyIso
      (subspaceSubsetHomeomorph U (U ∪ V) Set.subset_union_left).toHomotopyEquiv (n+1))
  · exact hv.of_iso (integralHomologyHomotopyIso
      (subspaceSubsetHomeomorph V (U ∪ V) Set.subset_union_right).toHomotopyEquiv (n+1))
  · exact hi.of_iso (integralHomologyHomotopyIso
      (subspaceSubsetHomeomorph (U ∩ V) (U ∪ V)
        (fun x hx => Or.inl hx.1)).toHomotopyEquiv n)

end

open CategoryTheory Limits Set
section
variable {X ι : Type} [TopologicalSpace X]

/-- Finite open-cover homology vanishing from explicit bounds on every
nonempty intersection. The degree shift is the number of intersected sets. -/
theorem finiteOpenUnionHomology_isZero (S : Finset ι) (U : ι → Set X)
    (hS : S.Nonempty) (hopen : ∀ i ∈ S, IsOpen (U i)) (n : ℕ) (hcard : S.card ≤ n+1)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q : ℕ, n < q + T.card →
      IsZero ((integralSingularHomology q).obj (TopCat.of (⋂ i ∈ T, U i)))) :
    IsZero ((integralSingularHomology n).obj (TopCat.of (⋃ i ∈ S, U i))) := by
  classical
  induction S using Finset.induction_on generalizing U n with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert a S ha ih =>
    by_cases hs : S.Nonempty
    · have hn : 0 < n := by
        rw [Finset.card_insert_of_notMem ha] at hcard
        have := Finset.card_pos.mpr hs
        omega
      have hU := hinter {a} (by simp) (by simp) n (by simp)
      have hea : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
      rw [hea] at hU
      have hV : IsZero ((integralSingularHomology n).obj (TopCat.of (⋃ i ∈ S, U i))) :=
        ih U hs (fun i hi => hopen i (Finset.mem_insert_of_mem hi)) n
          (by rw [Finset.card_insert_of_notMem ha] at hcard; omega)
          (fun T ht hts q hq => hinter T ht (hts.trans (Finset.subset_insert a S)) q hq)
      have hI : IsZero ((integralSingularHomology (n-1)).obj
          (TopCat.of (⋃ i ∈ S, U a ∩ U i))) := by
        apply ih (fun i => U a ∩ U i) hs
          (fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi)))
          (n-1) (by rw [Finset.card_insert_of_notMem ha] at hcard; omega)
        intro T ht hts q hq
        have hat : a ∉ T := fun h => ha (hts h)
        have hb := hinter (insert a T) (by simp)
          (Finset.insert_subset_insert a hts) q (by
            rw [Finset.card_insert_of_notMem hat]
            omega)
        have he : (⋂ i ∈ T, U a ∩ U i) = ⋂ i ∈ insert a T, U i := by
          ext x
          simp only [mem_iInter, Finset.mem_insert]
          constructor
          · intro hx i hi
            rcases hi with rfl | hi
            · obtain ⟨j, hj⟩ := ht
              exact (hx j hj).1
            · exact (hx i hi).2
          · intro hx i hi
            exact ⟨hx a (Or.inl rfl), hx i (Or.inr hi)⟩
        rw [he]
        exact hb
      have heI : (⋃ i ∈ S, U a ∩ U i) = U a ∩ (⋃ i ∈ S, U i) := by
        ext x
        simp only [mem_iUnion, mem_inter_iff]
        constructor
        · rintro ⟨i, hi, hxa, hxi⟩
          exact ⟨hxa, i, hi, hxi⟩
        · rintro ⟨hxa, i, hi, hxi⟩
          exact ⟨i, hi, hxa, hxi⟩
      rw [heI] at hI
      have heN : (n-1)+1 = n := by omega
      have hz := openUnionHomology_isZero (U a) (⋃ i ∈ S, U i)
        (hopen a (by simp))
        (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi))))
        (n-1) (heN.symm ▸ hU) (heN.symm ▸ hV) hI
      have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by
        ext x; simp
      rw [heW]
      simpa only [heN] using hz
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst S
      have hz := hinter {a} (by simp) (by simp) n (by simp)
      have hea : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
      have heb : (⋃ i ∈ insert a (∅ : Finset ι), U i) = U a := by ext x; simp
      rw [hea] at hz
      rw [heb]
      exact hz

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_FiniteCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Relative maps and vanishing and gluing over finite open covers. -/

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X]

/-- Nested restrictions give the same actual pair, with ambient subspace
topology and the same removed set. -/
def restrictedPairSubsetIso (U W A : Set X) (h : U ⊆ W) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' (Subtype.val ⁻¹' A : Set W) : Set (Subtype.val ⁻¹' U : Set W))) n ≅
    relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n :=
  relativeHomologyHomeomorphIso (subspaceSubsetHomeomorph U W h)
    (Subtype.val ⁻¹' (Subtype.val ⁻¹' A : Set W) : Set (Subtype.val ⁻¹' U : Set W))
    (Subtype.val ⁻¹' A : Set U) (fun _ => Iff.rfl) n

end

open CategoryTheory Limits Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Compactification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Compactification excision and ordinary relative section classes. -/

section
open Bundle Topology CategoryTheory OnePoint
variable {B V : Type} {E : B → Type} [∀ b, NormedAddCommGroup (E b)]

/-- The ordinary total space with its entire zero section removed. -/
def nonzeroBundle : Set (TotalSpace V E) :=
  ((↑) : TotalSpace V E → OnePoint (TotalSpace V E)) ⁻¹'
    compactifiedNonzeroBundle

theorem mem_nonzeroBundle (z : TotalSpace V E) : z ∈ nonzeroBundle ↔ z.2 ≠ 0 :=
  coe_mem_compactifiedNonzeroBundle z.proj z.2

end

open Bundle Topology CategoryTheory
section
variable {B V : Type} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : B → Type} [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℂ (E b)]
  [TopologicalSpace (TotalSpace V E)] [FiberBundle V E] [VectorBundle ℂ V E]

/-- The section's absolute class followed by localization away from the
whole zero section, in the original total space. -/
def ordinarySectionClassMap (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b))) (n : ℕ) :=
  (integralSingularHomology n).map (TopCat.ofHom ⟨_,hs⟩) ≫
    absoluteToRelative (subspaceInclusion (nonzeroBundle (V := V) (E := E))) n

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Product
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair homology, pair homotopies, and diagonal normalization. -/

section
open CategoryTheory Limits ContinuousMap
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

def productPairProjection (W : Set V) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion {z : B × V | z.2 ∈ W})
    (subspaceInclusion W)
    (subspaceMap _ _ ⟨Prod.snd, continuous_snd⟩ (fun _ h => h))
    (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (by rfl) n

/-- Genuine relative homology normalization for a trivial bundle over any
contractible base, with no homology or orientation assumption. -/
theorem productPairProjection_isIso [ContractibleSpace B] (W : Set V) (n : ℕ) :
    IsIso (productPairProjection (B := B) W n) := by
  let a := (productSubspaceHomeomorph (B := B) W).toHomotopyEquiv.trans
    (contractibleProductProjection (B := B) W)
  exact relativeHomologyMap_isIso_of_equivalences _ _ a
    (contractibleProductProjection (B := B) V) (by rfl) n

def productPairProjectionIso [ContractibleSpace B] (W : Set V) (n : ℕ) :=
  @asIso _ _ _ _ (productPairProjection (B := B) W n) (productPairProjection_isIso W n)

end

section
open CategoryTheory ContinuousMap
section
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

/-- Inclusion of one genuine fiber of a product pair. -/
def productPairFiberMap (b : B) (W : Set V) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion W)
    (subspaceInclusion {z : B × V | z.2 ∈ W})
    (subspaceMap _ _ ⟨fun v => (b,v), continuous_const.prodMk continuous_id⟩ (fun _ h => h))
    (TopCat.ofHom ⟨fun v => (b,v), continuous_const.prodMk continuous_id⟩) (by rfl) n

end

open CategoryTheory ContinuousMap
open scoped unitInterval

end

section
open CategoryTheory ContinuousMap
open scoped unitInterval
variable {ι : Type}

def complexDiagonalRelativeMap (a : ι → ℂˣ) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion ({0}ᶜ : Set (ι → ℂ)))
    (subspaceInclusion ({0}ᶜ : Set (ι → ℂ)))
    (subspaceMap _ _ (complexDiagonalMap a) (complexDiagonalMap_nonzero a))
    (TopCat.ofHom (complexDiagonalMap a)) (by rfl) n

end

open CategoryTheory ContinuousMap
section
variable {B ι : Type} [TopologicalSpace B]

/-- A map from a product pair to its fiber pair. -/
def productPairCoordinateMap (f : C(B × (ι → ℂ),(ι → ℂ)))
    (hf : ∀ z, z.2 ≠ 0 → f z ≠ 0) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion {z : B × (ι → ℂ) | z.2 ≠ 0})
    (subspaceInclusion ({0}ᶜ : Set (ι → ℂ)))
    (subspaceMap _ _ f (fun z hz => hf z hz)) (TopCat.ofHom f) (by rfl) n

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Connected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Connected-cover homology, degree-zero components, and degree-one generators. -/

section
open CategoryTheory Limits HomologicalComplex

/-- An inclusion (indeed any map) from a path-connected space is injective
on integral H₀. The augmentation provides an explicit left inverse. -/
theorem integralHomologyZero_map_injective {A X : TopCat.{0}}
    [PathConnectedSpace A] (f : A ⟶ X) :
    Function.Injective ((integralSingularHomology 0).map f) := by
  let a : A := Classical.choice (inferInstance : Nonempty A)
  have hs : (integralSingularHomology 0).map f ≫
      pointAugmentation X ≫ pointHomology A a = 𝟙 _ := by
    apply pointHomology_hom_ext A
    intro x
    simp only [← Category.assoc, pointHomology_map, pointHomology_augmentation,
      Category.id_comp, Category.comp_id]
    exact pointHomology_eq_of_joined A (PathConnectedSpace.joined a x)
  intro x y h
  have hx := ConcreteCategory.congr_hom hs x
  have hy := ConcreteCategory.congr_hom hs y
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hx hy
  rw [h] at hx
  exact hx.symm.trans hy

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Two contractible open sets with path-connected intersection have zero
integral H₁. The connected-intersection hypothesis is essential. -/
theorem openCover_homologyOne_isZero [ContractibleSpace U] [ContractibleSpace V]
    [PathConnectedSpace ↥(U ∩ V)]
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    IsZero ((integralSingularHomology 1).obj (TopCat.of X)) := by
  let δ := smallMayerVietorisBoundary U V 0
  let : Mono δ := (smallMayerVietorisSequence_shortExact U V).mono_δ 1 0 rfl
    (smallMayerVietoris_sum_isZero U V 1 (by decide))
  have hf : homologyMap (smallMayerVietorisSequence U V).f 0 ≫ homologyMap biprod.fst 0 =
      (integralSingularHomology 0).map
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) := by
    erw [← homologyMap_comp]
    congr 1
    exact biprod.lift_fst _ _
  have hz : IsZero ((smallSingularChains U V).homology 1) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro z
    have hk : homologyMap (smallMayerVietorisSequence U V).f 0 (δ z) = 0 :=
      ConcreteCategory.congr_hom
        ((smallMayerVietorisSequence_shortExact U V).δ_comp 1 0 rfl) z
    have hi : (integralSingularHomology 0).map
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) (δ z) = 0 := by
      erw [← hf, ModuleCat.comp_apply]
      erw [hk]
      exact map_zero _
    have hd : δ z = 0 := integralHomologyZero_map_injective _ (hi.trans (map_zero _).symm)
    exact (ModuleCat.mono_iff_injective δ).mp inferInstance (hd.trans (map_zero _).symm)
  exact hz.of_iso (openCoverSmallHomologyIso U V hU hV hUV 1).symm

end

open CategoryTheory Limits
section

/-- A connected removed subspace makes the degree-one connecting map zero. -/
theorem relativeHomologyBoundary_zero_connected {A X : TopCat.{0}}
    (i : A ⟶ X) [Mono i] [PathConnectedSpace A] :
    relativeHomologyBoundary i 0 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply integralHomologyZero_map_injective i
  exact (ConcreteCategory.congr_hom (relativeHomologyBoundary_inclusion i 0) z).trans
    (map_zero _).symm

/-- A connected subspace of a contractible ambient space has zero relative H₁. -/
theorem relativeHomologyOne_isZero {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    [PathConnectedSpace A] [ContractibleSpace X] :
    IsZero (relativeSingularHomology i 1) := by
  let : Mono (relativeHomologyBoundary i 0) :=
    (relativeChainSequence_shortExact i).mono_δ 1 0 rfl
      (integralSingularHomology_isZero_contractible X 1 (by decide))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro z
  apply (ModuleCat.mono_iff_injective (relativeHomologyBoundary i 0)).mp inferInstance
  rw [relativeHomologyBoundary_zero_connected]
  rfl

/-- Relative H₀ vanishes if the ambient space is path connected and the
removed subspace is nonempty. -/
theorem relativeHomologyZero_isZero {A X : TopCat.{0}} (i : A ⟶ X)
    [PathConnectedSpace X] [Nonempty A] :
    IsZero (relativeSingularHomology i 0) := by
  let a : A := Classical.choice (inferInstance : Nonempty A)
  have hz : absoluteToRelative i 0 = 0 := by
    apply pointHomology_hom_ext X
    intro x
    rw [pointHomology_eq_of_joined X (PathConnectedSpace.joined x (i a))]
    rw [← pointHomology_map i a, Category.assoc, inclusion_absoluteToRelative]
    simp
  let : Epi (absoluteToRelative i 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (relativeChainProjection i) 0
      (by intro j; simp)
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi (absoluteToRelative i 0)).mp
  rw [hz, zero_comp, zero_comp]

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Suspension homology and integral top generators of spheres. -/

open CategoryTheory Limits Metric
section

/-- The actual real zero-sphere has no positive integral homology. -/
theorem realSphere_positiveHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero ((integralSingularHomology n).obj (TopCat.of (sphere (0 : ℝ) 1))) := by
  have hf : (sphere (0 : ℝ) 1).Finite := by
    rw [Real.sphere_eq_pair 0 (by norm_num)]
    exact Set.toFinite _
  let := hf.fintype
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (sphere (0 : ℝ) 1)) hn

/-- The pole-chart intersection is connected in real ambient dimension at least three. -/
theorem sphere_homologyOne_isZero {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (d : ℕ) (hd : 2 ≤ d)
    [Fact (Module.finrank ℝ E = d+1)] (v : sphere (0 : E) 1) :
    IsZero ((integralSingularHomology 1).obj (TopCat.of (sphere (0 : E) 1))) := by
  let := spherePole_contractible v
  let := spherePole_contractible (-v)
  obtain ⟨hU,hV,hUV⟩ := sphere_poles_open_cover v
  let e := (spherePoleOverlapHomeomorph v).trans
    (continuousLinearEquivPuncturedHomeomorph
      (OrthonormalBasis.fromOrthogonalSpanSingleton d
        (show (v : E) ≠ 0 by
          intro h
          have := norm_eq_of_mem_sphere v
          simp [h] at this)).repr.toContinuousLinearEquiv)
  have hc : PathConnectedSpace ({0}ᶜ : Set (EuclideanSpace ℝ (Fin d))) := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    apply isPathConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank]
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
    rw [hfin]
    exact_mod_cast (show 1 < d by omega)
  let := hc
  let : PathConnectedSpace ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  exact openCover_homologyOne_isZero _ _ hU hV hUV

/-- Integral sphere homology vanishes in every positive degree other than
the sphere dimension. This includes both above- and below-dimension vanishing. -/
theorem euclideanSphereHomology_isZero (d n : ℕ) (hn : n ≠ 0) (hne : n ≠ d) :
    IsZero ((integralSingularHomology n).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1))) := by
  induction d generalizing n with
  | zero =>
      let e := integralHomologyHomotopyIso
        (continuousLinearEquivSphereHomotopyEquiv
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))) n
      exact (realSphere_positiveHomology_isZero n hn).of_iso e
  | succ d ih =>
      let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d+1+1))) = (d+1)+1) :=
        ⟨by simp⟩
      cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
          by_cases hzero : n = 0
          · subst n
            exact sphere_homologyOne_isZero (d+1) (by omega) (euclideanSpherePole (d+1))
          · exact (ih n hzero (by omega)).of_iso
              (sphereEuclideanHomologyStep (d+1) (euclideanSpherePole (d+1)) n hzero)

theorem finiteDimensionalSphereHomology_isZero (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d n : ℕ) (hd : Module.finrank ℝ E = d+1) (hn : n ≠ 0) (hne : n ≠ d) :
    IsZero ((integralSingularHomology n).obj (TopCat.of (sphere (0 : E) 1))) :=
  (euclideanSphereHomology_isZero d n hn hne).of_iso
    (integralHomologyHomotopyIso (continuousLinearEquivSphereHomotopyEquiv
      (ContinuousLinearEquiv.ofFinrankEq (by simpa using hd) :
        E ≃L[ℝ] EuclideanSpace ℝ (Fin (d+1)))) n)

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProjectiveLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Nonzero local classes and local homology of projective spaces and products. -/

section
open CategoryTheory Limits

section

/-- Actual local relative homology of a real vector space vanishes in every
non-top degree, including the low degrees zero and one. -/
theorem localVectorHomology_isZero (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : 2 ≤ Module.finrank ℝ E) (n : ℕ) (hn : n ≠ Module.finrank ℝ E) :
    IsZero (relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set E)) n) := by
  let := puncturedVector_pathConnected_of_finrank E hd
  cases n with
  | zero => exact relativeHomologyZero_isZero _
  | succ n =>
      cases n with
      | zero => exact relativeHomologyOne_isZero _
      | succ n =>
          exact (finiteDimensionalSphereHomology_isZero E (Module.finrank ℝ E-1) (n+1)
            (by omega) (by omega) (by omega)).of_iso
              (localVectorSphereHomologyIso E (n+1) (by omega))

open ComplexGrassmann

end

open ComplexGrassmann

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_ProductCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair fiber normalization, punctured products, and overlap generators. -/

section
open CategoryTheory Limits
variable {B V : Type} [TopologicalSpace B] [TopologicalSpace V]

/-- Relative product coordinates over an arbitrary subset of the base. -/
def productPairBaseSubsetIso (C : Set B) (W : Set V) (n : ℕ) :=
  relativeHomologyHomeomorphIso (firstCoordinateSubspaceHomeomorph C)
    (Subtype.val ⁻¹' {z : B × V | z.2 ∈ W})
    {z : C × V | z.2 ∈ W} (fun _ => Iff.rfl) n

/-- A fiber inside a restricted product chart. -/
def productPairChartFiberMap (C : Set B) (b : C) (W : Set V) (n : ℕ) :=
  relativeHomologyMap (subspaceInclusion W)
    (subspaceInclusion (Subtype.val ⁻¹' {z : B × V | z.2 ∈ W} : Set {z : B × V | z.1 ∈ C}))
    (subspaceMap _ _
      ⟨fun v => ⟨(b.1,v),b.2⟩,(continuous_const.prodMk continuous_id).subtype_mk _⟩
      (fun _ h => h))
    (TopCat.ofHom
      ⟨fun v => ⟨(b.1,v),b.2⟩,(continuous_const.prodMk continuous_id).subtype_mk _⟩) (by rfl) n

end

open Bundle Topology CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Twisted
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted hyperplane bundles, zeros, graph coordinates, and frame sections. -/

section
open Bundle Topology
namespace Kaplansky

section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedOldLabel : TwistedHyperplaneSlot K h → Option (Option ι)
  | .inl _ => none
  | .inr s => some (some s.1)

/-- The summands of (trivial(h) ⊕ H) tensored with the hyperplane line
from the auxiliary factor. This is an explicit vector-bundle core. -/
def twistedHyperplaneLineCore (s : TwistedHyperplaneSlot K h) :=
  tensorLineCore
    (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s))
    (productLineCore (twistedProjectiveDimensions K h) (some none))

def twistedHyperplaneSumCore := finiteLineSumCore (twistedHyperplaneLineCore K h)

end

open ComplexGrassmann

end Kaplansky

end

section
open Bundle Topology Set CategoryTheory
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type}
  [Fintype ι]
  [TopologicalSpace A]
  (K : ι → ℕ)
  (h : ℕ)
  (U : Set (ProjectiveProduct (twistedProjectiveDimensions K h)))
  (e : U ≃ₜ A)
  (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))

instance twistedHyperplaneFiberNormedAddCommGroup
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    NormedAddCommGroup ((twistedHyperplaneSumCore K h).Fiber P) :=
  finiteLineSumFiberNormedAddCommGroup (twistedHyperplaneLineCore K h) P

instance twistedHyperplaneFiberInnerProductSpace
    (P : ProjectiveProduct (twistedProjectiveDimensions K h)) :
    InnerProductSpace ℂ ((twistedHyperplaneSumCore K h).Fiber P) :=
  finiteLineSumFiberInnerProductSpace (twistedHyperplaneLineCore K h) P

abbrev twistedGraphBundleDomain :=
  {z : TotalSpace (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
    (twistedHyperplaneSumCore K h).Fiber | z.proj ∈ U}

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedSlotEquiv : TwistedHyperplaneSlot K h ≃
    (Σ i, Fin (twistedProjectiveDimensions K h i)) where
  toFun
    | .inl j => ⟨none,j⟩
    | .inr s => ⟨some s.1,s.2⟩
  invFun
    | ⟨none,j⟩ => .inl j
    | ⟨some i,j⟩ => .inr ⟨i,j⟩
  left_inv s := by cases s <;> rfl
  right_inv s := by obtain ⟨i,j⟩ := s; cases i <;> rfl

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedSourceLabel : TwistedHyperplaneSlot K h → Option ι
  | .inl _ => none
  | .inr s => some s.1

def twistedSourceStage : LineStage K :=
  ⟨TwistedHyperplaneSlot K h,inferInstance,twistedSourceLabel K h⟩

def twistedOldBase : C(ProjectiveProduct (twistedProjectiveDimensions K h),ProjectiveProduct K) :=
  ⟨fun P i => P (some i),continuous_pi (fun i => continuous_apply (some i))⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_FrameNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Integral normalization of finite-line frames over affine-avoidance covers. -/

section
open Bundle Topology CategoryTheory Set
variable {A S : Type} [TopologicalSpace A] [Fintype S] {I : S → Type}
  (C : ∀ s, VectorBundleCore ℂ A ℂ (I s))
  (v : ∀ s a, (C s).Fiber a) (hn : ∀ s a, v s a ≠ 0)
  (hc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (v s a)))

/-- Relative coordinates of any finite sum with genuine continuous line frames. -/
def finiteLineFrameRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (finiteLineFrameHomeomorph C v hn hc)
    {z : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber | z.2 ≠ 0}
    {z : A × (S → ℂ) | z.2 ≠ 0}
    (fun z => (not_congr (finiteLineFrameHomeomorph_zero_iff C v hn hc z)).symm) n

def finiteLineFrameNormalization (n : ℕ) :=
  (finiteLineFrameRelativeIso C v hn hc n).hom ≫
    productPairProjection (B := A) ({0}ᶜ : Set (S → ℂ)) n

end

open Bundle Topology CategoryTheory Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Normalization
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted bundle graph normalization and its naturality. -/

section
open Bundle Topology CategoryTheory Limits Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ) (h : ℕ)
  (U : Set (ProjectiveProduct (twistedProjectiveDimensions K h))) (e : U ≃ₜ A)

def twistedGraphBundlePullbackRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso
    (lineSumChartPullbackHomeomorph (twistedHyperplaneLineCore K h) U e).symm
    (Subtype.val ⁻¹' nonzeroBundle)
    {z : TotalSpace (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
      (finiteLineSumCore (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s)
        (chartBaseMap U e))).Fiber | z.2 ≠ 0}
    (fun z => mem_nonzeroBundle z.1) n

end Kaplansky

end

open Bundle Topology CategoryTheory Limits Set

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Smooth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth bases and test bundles with replacement maps. -/

section
open Topology
open scoped Manifold ContDiff BigOperators
namespace Kaplansky
open ComplexGrassmann

def testFactorProjectiveHomeomorph (m R : ℕ) (i : Fin R) :
    projectionSpace (testProjectiveDimension m R i+1) 1 ≃ₜ
      Grassmann 1 (testProjectiveDimension m R i) := by
  let P : ℕ → Type := fun d => projectionSpace d 1 ≃ₜ Grassmann 1 (testProjectiveDimension m R i)
  exact Eq.mp (congrArg P (Nat.add_comm 1 (testProjectiveDimension m R i)))
    (projectiveProjectionHomeomorph (testProjectiveDimension m R i))

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_CoordinatesMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.lineStage_complete _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-coordinate smooth bundles and their metrics. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann
variable {S ι : Type*} [Fintype S] [Fintype ι]

variable (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d)

attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.finiteCoordinateHilbertInner

instance finiteCoordinateBundle_norm (P : ProjectiveProduct K) :
    NormedAddCommGroup (FiniteCoordinateBundle K label d hd P) := changeModelFiberNorm _ _ P
instance finiteCoordinateBundle_normedSpace (P : ProjectiveProduct K) :
    NormedSpace ℂ (FiniteCoordinateBundle K label d hd P) := changeModelFiberNormedSpace _ _ P

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Retained
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Retained bundle labels, positive multiplicities, regrouping, and complement rank. -/

section
open scoped BigOperators
namespace Kaplansky

theorem testSummandLineIndex_eq_none {R j : ℕ} (hj : j≤R) (s : Fin (j+1)) :
    testSummandLineIndex hj s = none ↔ s=0 := by
  unfold testSummandLineIndex
  by_cases h : s.val=0
  · rw [dite_eq_left h]
    exact iff_of_true rfl (Fin.ext h)
  · rw [dite_eq_right h]
    simp only [Option.some_ne_none,false_iff]
    intro hs
    exact h (congrArg Fin.val hs)

theorem testSummandLineIndex_eq_some {R j : ℕ} (hj : j≤R) (s : Fin (j+1)) (i : Fin R) :
    testSummandLineIndex hj s = some i ↔ s.val=i.val+1 := by
  unfold testSummandLineIndex
  split
  · simp_all
  · simp only [Option.some.injEq,Fin.ext_iff]
    omega

theorem retainedLabel_some_stage_sum (m R : ℕ) (i : Fin R) (j : Fin (R+1)) :
    (∑ a : Fin (j.val+1), if testSummandLineIndex (Nat.le_of_lt_succ j.isLt) a=some i
      then testMultiplicity m R j.val a else 0) =
      if h : i.val<j.val then testMultiplicity m R j.val ⟨i.val+1,by omega⟩ else 0 := by
  by_cases h : i.val<j.val
  · rw [dite_eq_left h]
    let a : Fin (j.val+1) := ⟨i.val+1,by omega⟩
    have he : ∀ b : Fin (j.val+1), testSummandLineIndex (Nat.le_of_lt_succ j.isLt) b=some i ↔ b=a := by
      intro b
      rw [testSummandLineIndex_eq_some,Fin.ext_iff]
    simp_rw [he]
    simp [a]
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro a _
    rw [ite_eq_right]
    rw [testSummandLineIndex_eq_some]
    omega

theorem sum_suffix_reverse {R : ℕ} (i : Fin R)
    (f : ∀ j : Fin (R+1), i.val<j.val → ℕ) :
    (∑ j : Fin (R+1), if h : i.val<j.val then f j h else 0) =
      ∑ t : Fin (R-i.val), f ⟨R-t.val,by omega⟩ (by change i.val<R-t.val; omega) := by
  let g := fun j : Fin (R+1) => if h : i.val<j.val then f j h else 0
  let s := Finset.univ.filter (fun j : Fin (R+1) => i.val<j.val)
  have hg : (∑ j, g j) = ∑ j ∈ s, g j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i.val<j.val <;> simp [g,h]
  change (∑ j, g j)=_
  rw [hg,Finset.sum_subtype (p := fun j : Fin (R+1) => i.val<j.val) s (by intro j; simp [s]) g]
  apply Fintype.sum_equiv (suffixReverseEquiv i)
  intro j
  have h := j.2
  simp only [g,dite_eq_left h]
  congr 1
  apply Fin.ext
  dsimp [suffixReverseEquiv]
  have hj := j.1.isLt
  omega

end Kaplansky

end

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

def retainedLineRank (m R : ℕ) : Option (Fin R) → ℕ
  | none => retainedTrivialMultiplicity m R
  | some i => testProjectiveDimension m R i

abbrev RetainedGroupedSlot (m R : ℕ) := Σ i : Option (Fin R), Fin (retainedLineRank m R i)

end Kaplansky

end

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Monoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered Cuntz monoid and compression by its order unit. -/

noncomputable section
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

instance instIsOrderedAddMonoidCuntzMonoid : IsOrderedAddMonoid (CuntzMonoid A) where
  add_le_add_left a b h c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    exact (cuntzClass_le _ _).mpr
      (CuntzPositiveMatrix.add_le_add ((cuntzClass_le _ _).mp h) (le_refl c))

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.OrderedStates_Semigroup
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Catalytic orders, ordered group completion, and normalized semigroup states. -/

namespace Kaplansky

section
variable (S : Type*) [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

variable {S}

def SemigroupDifference.flip (a : SemigroupDifference S) : SemigroupDifference S := (a.2,a.1)

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Translation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Order of spectral cutoffs, translations, and continuity. -/

open scoped Matrix CStarAlgebra NNReal
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus productMatrixRealFunctionalCalculus
variable {A : Type*} [CStarAlgebra A]

namespace CuntzDimensionState

theorem spectralValue_lipschitz (d : CuntzDimensionState A) (n : ℕ) :
    LipschitzWith (n : ℝ≥0) (fun a : {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} =>
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a.val, a.property⟩) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [Real.dist_eq, Subtype.dist_eq, dist_eq_norm, NNReal.coe_natCast, Real.norm_eq_abs, mul_comm]
    using d.abs_spectralValue_sub_le a.property b.property

/-- Continuity on the full positive cone, without a finite-spectrum assumption. -/
theorem spectralValue_continuous (d : CuntzDimensionState A) (n : ℕ) :
    Continuous (fun a : {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} =>
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a.val, a.property⟩) :=
  (d.spectralValue_lipschitz n).continuous

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Quasitrace_Extension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix order and the normalization of genuine corner extensions. -/

section

noncomputable section
open scoped ComplexOrder BigOperators CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

theorem corner_nonneg (i : n) {a : A} (ha : 0 ≤ a) : 0 ≤ corner i a := by
  obtain ⟨x, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  rw [← corner_mul, ← corner_star]
  exact star_mul_self_nonneg _

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Quasitrace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Corner-compatible spectral quasitraces and nonunital abelian complex linearity. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus matrixNonUnitalRealFunctionalCalculus matrixNonnegSpectrum
variable {A : Type*} [CStarAlgebra A]

def spectralCornerHom {n : ℕ} (i : Fin n) : A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun := corner i
  map_zero' := corner_zero i
  map_add' := corner_add i
  map_mul' a b := (corner_mul i a b).symm
  map_smul' := corner_smul i
  map_star' a := (corner_star i a).symm

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_BundleWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Continuous bundle words and their finite-tower Hilbert realization. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ}

section Evaluation

variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

def towerOperator (i : Fin 24) (y : ProjectiveProduct K) (j : ℕ) :
    EuclideanSpace ℂ (a j).Slot →L[ℂ] EuclideanSpace ℂ (a (j+1)).Slot := by
  let T : NormalizedHermitianTuple (EuclideanSpace ℂ (a j).Slot)
      (EuclideanSpace ℂ (a (j+1)).Slot) := (X j).tuple y
  exact T.operator i

end Evaluation

open scoped BigOperators

/-- The coordinate at every retained level is the original bundle vector. -/
theorem finiteTowerHilbert_apply (a : ℕ → LineStage K) (R : ℕ)
    (y : ProjectiveProduct K) (v : (LineStage.sum (fun k : Fin (R+1) => a k.val)).Fiber y)
    (j : Fin (R+1)) :
    finiteTowerHilbert a R y v j.val = LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y v := by
  classical
  change (∑ k : Fin (R+1), lp.single (E := fun j => (a j).Fiber y) 2 k.val
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) k y v)) j.val = _
  rw [lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · exact lp.single_apply_self _ _ _
  · intro k _ hkj
    exact lp.single_apply_ne _ _ _ (fun h => hkj (Fin.ext h.symm))
  · simp

/-- This inclusion preserves the actual Hermitian metrics, which is needed
when the operator lower bound is restricted to the finite bundle. -/
theorem finiteTowerHilbert_inner (a : ℕ → LineStage K) (R : ℕ)
    (y : ProjectiveProduct K)
    (v w : (LineStage.sum (fun k : Fin (R+1) => a k.val)).Fiber y) :
    inner ℂ (finiteTowerHilbert a R y v) (finiteTowerHilbert a R y w) = inner ℂ v w := by
  change inner ℂ (∑ j : Fin (R+1), lp.single (E := fun j => (a j).Fiber y) 2 j.val
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y v))
    (finiteTowerHilbert a R y w) = _
  simp only [sum_inner,
    lp.inner_single_left,finiteTowerHilbert_apply]
  change (∑ j : Fin (R+1), inner ℂ
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y v)
    (LineStage.sumProj (fun k : Fin (R+1) => a k.val) j y w)) = _
  exact (LineStage.sum_inner _ y v w).symm

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Products
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded C-star products and the generated separable unital algebra. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- Positivity in the bounded product is equivalent to coordinatewise
positivity. Boundedness of the adjoint-square witnesses is proved. -/
theorem boundedProduct_nonneg_iff (f : BoundedProduct A) :
    0 ≤ f ↔ ∀ i, 0 ≤ f i := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (BoundedProduct A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (BoundedProduct A) := CStarAlgebra.instNonnegSpectrumClass'
  constructor
  · intro h
    obtain ⟨x,rfl⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := f)).mp h
    intro i
    exact star_mul_self_nonneg (x i)
  · intro h
    choose x hx using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (h i)
    obtain ⟨C,hC⟩ := f.property.bddAbove
    have hb (i : I) : ‖x i‖ ≤ |C|+1 := by
      have hi : ‖x i‖ * ‖x i‖ ≤ C := by
        rw [← CStarRing.norm_star_mul_self, ← hx i]
        exact hC ⟨i,rfl⟩
      have hnorm := norm_nonneg (x i)
      have hCa := le_abs_self C
      have hC0 := abs_nonneg C
      nlinarith
    let g : BoundedProduct A := ⟨x, memℓp_infty ⟨|C|+1, by rintro _ ⟨i,rfl⟩; exact hb i⟩⟩
    apply (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := f)).mpr
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact funext hx

theorem boundedProduct_le_iff (f g : BoundedProduct A) : f ≤ g ↔ ∀ i, f i ≤ g i := by
  rw [← sub_nonneg, boundedProduct_nonneg_iff]
  exact forall_congr' (fun i => sub_nonneg)

end Kaplansky

end

noncomputable section
open TopologicalSpace
open scoped Pointwise
namespace Kaplansky

variable {A : Type*} [CStarAlgebra A]

instance generatedAlgebra_closed (s : Set A) : IsClosed (generatedAlgebra s : Set A) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance generatedAlgebra_cstar (s : Set A) : CStarAlgebra (generatedAlgebra s) :=
  inferInstance

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Polynomials
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Star-word polynomials and matrix polynomial density in the generated algebra. -/

noncomputable section
open scoped BigOperators Pointwise
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A] {N : ℕ}

def starWordMonoid (x : Fin N → A) : Submonoid A where
  carrier := Set.range (algebraStarWord x)
  one_mem' := ⟨[],rfl⟩
  mul_mem' := by
    rintro _ _ ⟨u,rfl⟩ ⟨v,rfl⟩
    exact ⟨u++v,algebraStarWord_append x u v⟩

theorem starWordMonoid_eq_closure (x : Fin N → A) :
    starWordMonoid x = Submonoid.closure (Set.range x ∪ star (Set.range x)) := by
  apply le_antisymm
  · rintro _ ⟨w,rfl⟩
    induction w with
    | nil => exact Submonoid.one_mem _
    | cons l w ih =>
      apply Submonoid.mul_mem _ _ ih
      apply Submonoid.subset_closure
      obtain ⟨b,i⟩ := l
      cases b with
      | false => exact Or.inl ⟨i,rfl⟩
      | true =>
        apply Or.inr
        simp [algebraStarLetter]
  · apply Submonoid.closure_le.mpr
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨i,rfl⟩ := hz
      exact ⟨[(false,i)],by simp [algebraStarWord,algebraStarLetter]⟩
    · have hz' : star z ∈ Set.range x := by simpa using hz
      obtain ⟨i,hi⟩ := hz'
      exact ⟨[(true,i)],by simpa [algebraStarWord,algebraStarLetter] using congrArg star hi⟩

theorem starAdjoin_eq_wordSpan (x : Fin N → A) :
    (StarAlgebra.adjoin ℂ (Set.range x)).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (algebraStarWord x)) := by
  rw [StarAlgebra.adjoin_eq_span,← starWordMonoid_eq_closure]
  rfl

def evalStarWordPolynomial (x : Fin N → A) (p : StarWordPolynomial N) : A :=
  Finsupp.linearCombination ℂ (algebraStarWord x) p

end Kaplansky

end

noncomputable section
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] {N : ℕ}

theorem evalStarWordPolynomial_mem (x : Fin N → A) (p : StarWordPolynomial N) :
    evalStarWordPolynomial x p ∈ StarAlgebra.adjoin ℂ (Set.range x) := by
  change evalStarWordPolynomial x p ∈ (StarAlgebra.adjoin ℂ (Set.range x)).toSubalgebra.toSubmodule
  rw [starAdjoin_eq_wordSpan,← Finsupp.range_linearCombination]
  exact ⟨p,rfl⟩

def generatedWordPolynomial (x : Fin N → A) (p : StarWordPolynomial N) :
    generatedAlgebra (Set.range x) :=
  ⟨evalStarWordPolynomial x p,StarSubalgebra.le_topologicalClosure _ (evalStarWordPolynomial_mem x p)⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_BundlePolynomials
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Bundle matrix polynomial evaluation, Hilbert isometries, and polynomial action. -/

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type*} {K : ι → ℕ}

variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

def matrixPolynomialDegree {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24) : ℕ :=
  1 + Finset.univ.sup (fun k : MatrixPolynomialTermIndex p => k.2.2.val.length)

theorem matrixPolynomialDegree_pos {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24) :
    0 < matrixPolynomialDegree p := Nat.add_pos_left Nat.zero_lt_one _

/-- The common positive degree bound and the actual terms of a finite
rectangular polynomial matrix are produced from its entries. -/
def matrixPolynomialTerm {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24)
    (k : MatrixPolynomialTermIndex p) : BoundedMatrixTerm m n (matrixPolynomialDegree p) where
  row := k.1
  col := k.2.1
  coeff := p k.1 k.2.1 k.2.2.val
  word := k.2.2.val
  degree_le := (Finset.le_sup (f := fun k : MatrixPolynomialTermIndex p => k.2.2.val.length)
    (Finset.mem_univ k)).trans (Nat.le_add_left _ _)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Operators
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix operator action and norm perturbation estimates. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {m n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def operatorMatrixAction (W : Fin m → Fin n → H →L[ℂ] H) (v : HilbertColumns n H) :
    HilbertColumns m H := ∑ row, PiLp.single 2 row (∑ col, W row col (v col))

@[simp] theorem operatorMatrixAction_apply (W : Fin m → Fin n → H →L[ℂ] H)
    (v : HilbertColumns n H) (row : Fin m) :
    operatorMatrixAction W v row = ∑ col, W row col (v col) := by
  classical
  simp [operatorMatrixAction]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_ClosedStarQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace KaplanskyConsequences
open scoped ComplexOrder
open Metric Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

namespace ClosedStarIdeal
variable {A : Type*} [CStarAlgebra A] (I : ClosedStarIdeal A)

lemma approximate_unit_mem [Nontrivial A] (j : A) (hj : j ∈ I.submodule) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : A, e ∈ I.submodule ∧ 0 ≤ e ∧ ‖1-e‖ ≤ 1 ∧ ‖j*(1-e)‖ < ε := by
  let J := I.toNonUnitalStarSubalgebra
  let j' : J := ⟨j, hj⟩
  let : PartialOrder J := CStarAlgebra.spectralOrder J
  let : StarOrderedRing J := CStarAlgebra.spectralOrderedRing J
  have hu := CStarAlgebra.increasingApproximateUnit (A := J)
  have ht := hu.tendsto_mul_left j'
  have he := (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨e, he₀, he₁, hej⟩ := (hu.eventually_nonneg.and (hu.eventually_norm.and he)).exists
  have heA : (0 : A) ≤ (e : A) := by
    have h := @NonUnitalStarRingHom.map_le_map_of_map_star J A _
      (CStarAlgebra.spectralOrder J) _ (CStarAlgebra.spectralOrderedRing J) _ _ _ _
      ((NonUnitalStarSubalgebraClass.subtype J : J →⋆ₙₐ[ℂ] A) : J →⋆ₙ+* A) 0 e he₀
    exact h
  have he_le : (e : A) ≤ 1 := by
    apply (IsSelfAdjoint.of_nonneg heA).le_algebraMap_norm_self.trans
    rw [Algebra.algebraMap_eq_smul_one]
    simpa using smul_le_smul_of_nonneg_right he₁ (show (0 : A) ≤ 1 from zero_le_one)
  refine ⟨e, e.property, heA, ?_, ?_⟩
  · exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_self (1 : A) heA)
      (sub_nonneg.mpr he_le)).trans (by rw [norm_one])
  · have hx : ‖j * (e : A) - j‖ < ε := by
      rw [dist_eq_norm] at hej
      exact hej
    simpa only [mul_sub, mul_one, norm_sub_rev] using hx

lemma norm_sq_mk_le_add [Nontrivial A] (x j : A) (hj : j ∈ I.submodule) :
    ‖I.quotientMap x‖ * ‖I.quotientMap x‖ ≤ ‖star x*x+j‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨e, he, he₀, he₁, hej⟩ := I.approximate_unit_mem j hj hε
  let w := 1-e
  have hw : star w = w := (IsSelfAdjoint.one A |>.sub he₀.isSelfAdjoint).star_eq
  have heq : I.quotientMap (x*w) = I.quotientMap x := by
    simp only [w, map_mul, map_sub, map_one, (I.mk_eq_zero e).mpr he, sub_zero, mul_one]
  have hnorm : ‖I.quotientMap x‖ * ‖I.quotientMap x‖ ≤ ‖x*w‖ * ‖x*w‖ := by
    rw [← heq]
    exact mul_self_le_mul_self (norm_nonneg _) (I.norm_mk_le _)
  have hC : ‖x*w‖ * ‖x*w‖ = ‖w * (star x*x) * w‖ := by
    rw [← CStarRing.norm_star_mul_self, star_mul, hw]
    congr 1; noncomm_ring
  have hnorm₁ : ‖w * (star x*x+j) * w‖ ≤ ‖star x*x+j‖ := by
    calc
      _ ≤ ‖w‖ * ‖star x*x+j‖ * ‖w‖ :=
        (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (norm_mul_le ..) (norm_nonneg _))
      _ ≤ 1 * ‖star x*x+j‖ * 1 := by gcongr
      _ = _ := by ring
  have hnorm₂ : ‖w*j*w‖ ≤ ‖j*w‖ := by
    rw [mul_assoc]
    exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) he₁)
  calc
    _ ≤ ‖w * (star x*x) * w‖ := hnorm.trans_eq hC
    _ = ‖w * (star x*x+j) * w - w*j*w‖ := by congr 1; noncomm_ring
    _ ≤ ‖w * (star x*x+j) * w‖ + ‖w*j*w‖ := norm_sub_le ..
    _ ≤ ‖star x*x+j‖ + ε := add_le_add hnorm₁ (hnorm₂.trans hej.le)

instance instCStarRingQuotientOfNontrivial [Nontrivial A] : CStarRing I.Quotient where
  norm_mul_self_le x := by
    obtain ⟨a, rfl⟩ := I.mk_surjective x
    rw [← I.mk_star, ← map_mul]
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b, hb, hnorm⟩ := I.norm_mk_lt (I.quotientMap (star a*a)) hε
    have hj : b - star a*a ∈ I.submodule := by
      apply (I.mk_eq_zero _).mp
      rw [map_sub, hb, sub_self]
    have h := I.norm_sq_mk_le_add a (b-star a*a) hj
    have he : star a*a + (b-star a*a) = b := by abel
    rw [he] at h
    exact h.trans hnorm.le

instance quotientCStarAlgebra [Nontrivial A] : CStarAlgebra I.Quotient where

end ClosedStarIdeal
end KaplanskyConsequences
end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

attribute [local instance] Classical.decEq Classical.propDecidable

@[simp] lemma exponent_genZ (n : ℤ) : exponent (genZ n) = 0 := by
  simp [genZ,exponent,height,a,b]


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_RegularOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open Classical in
def negative (n : ℕ) : HilbertSum F2 H →L[ℂ] HilbertSum F2 H :=
  mask (fun w => Prefix (n:ℤ) false (coordinate w))

def creation (n : ℕ) : HilbertSum F2 H →L[ℂ] HilbertSum F2 H :=
  left (freeGen n) * (1-negative n)
def annihilation (n : ℕ) : HilbertSum F2 H →L[ℂ] HilbertSum F2 H :=
  left (freeGen n) * negative n

omit [CompleteSpace H] in
@[simp] lemma creation_apply (n : ℕ) (x : HilbertSum F2 H) (w : F2) :
    creation n x w = if Prefix (n:ℤ) false (coordinate ((freeGen n)⁻¹*w)) then 0
      else x ((freeGen n)⁻¹*w) := by
  classical
  change (x ((freeGen n)⁻¹*w) - (mask (fun w => Prefix (n:ℤ) false (coordinate w)) x) ((freeGen n)⁻¹*w)) = _
  rw [mask_apply]
  split_ifs <;> simp

@[simp] lemma creation_star_mul_self (n : ℕ) :
    star (creation (H:=H) n) * creation n = 1-negative n := by
  have hu : star (left (H:=H) (freeGen n)) * left (freeGen n) = 1 := by
    rw [left_star,← left_mul,inv_mul_cancel,left_one]
  have hp : star (negative (H:=H) n) = negative n := mask_star _
  have hq : negative (H:=H) n * negative n = negative n := mask_sq _
  simp only [creation,star_mul]
  rw [mul_assoc,← mul_assoc (star (left (H := H) (freeGen n))),hu,one_mul,
    star_sub (1 : HilbertSum F2 H →L[ℂ] HilbertSum F2 H) (negative n),star_one,hp]
  simp only [mul_sub, sub_mul, one_mul, mul_one, hq]
  abel

@[simp] lemma annihilation_star_mul_self (n : ℕ) :
    star (annihilation (H:=H) n) * annihilation n = negative n := by
  simp only [annihilation,star_mul,mul_assoc]
  rw [← mul_assoc (star (left (H := H) (freeGen n))),left_star,← left_mul,inv_mul_cancel,left_one,one_mul]
  exact (congrArg (fun a => a * negative (H:=H) n) (mask_star _)).trans (mask_sq _)


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

def conjugateMap (g : G) : Algebra G →ₗ[ℂ] Algebra G where
  toFun x := generator g*x*generator g⁻¹
  map_add' x y := by simp [mul_add,add_mul]
  map_smul' c x := by simp

@[simp] lemma conjugateMap_one (g : G) : conjugateMap g (1:Algebra G) = 1 := by
  apply Subtype.ext
  change left g*1*left g⁻¹ = 1
  rw [mul_one,←left_mul,mul_inv_cancel,left_one]

def averageConjugate {N : ℕ} (h : Fin N → G) : Algebra G →ₗ[ℂ] Algebra G :=
  @SMul.smul ℂ (Algebra G →ₗ[ℂ] Algebra G) _ (N:ℂ)⁻¹ (∑ i, conjugateMap (h i))


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped InnerProductSpace ComplexOrder BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2200] Complex.partialOrder
variable {G : Type*}

variable [Group G]

def coefficient (T : Algebra G) : ℂ := T.val (delta 1) 1
lemma coefficient_square (T : Algebra G) :
    coefficient (star T*T) = inner ℂ (T.val (delta 1)) (T.val (delta 1)) := by
  calc
    coefficient (star T*T) = inner ℂ (delta 1) (T.val.adjoint (T.val (delta 1))) :=
      (inner_delta 1 _).symm
    _ = _ := T.val.adjoint_inner_right (delta 1) (T.val (delta 1))


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

def polynomial : (G →₀ ℂ) →ₗ[ℂ] Algebra G := Finsupp.linearCombination ℂ generator

@[simp] lemma coefficient_generator (g : G) : coefficient (generator g) = if g=1 then 1 else 0 := by
  simp [coefficient,generator,delta_apply]


end KaplanskyConsequences.Regular

end

end OAI
end


