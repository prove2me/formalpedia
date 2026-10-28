-- Prove2me | Definitions.Def_OAIQ4Kq007
-- name    : OAIQ4Kq007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:33:26.814988+00:00
-- url     : https://prove2.me/theorems/fc3ccaaa-7247-4a13-a452-c5550bac6dc4
-- title:
--   Definitions bundle OAIQ4Kq007 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 186 declarations of OpenAI's Lean: 62 definitions, 7 instances and 117 theorems. The definitions and types are `OAI.Kaplansky.complexDiagonalRelativeMap`, `OAI.Kaplansky.contractibleRelativeBoundaryIso`, `OAI.Kaplansky.euclideanSphereTopHomologyIso`, `OAI.Kaplansky.finiteDimensionalSphereTopHomologyIso`, `OAI.Kaplansky.finiteLineFrameEquiv`, `OAI.Kaplansky.finiteLineFrameHomeomorph`, `OAI.Kaplansky.finiteLineFrameNormalization`, `OAI.Kaplansky.finiteLineFrameRelativeIso`, `OAI.Kaplansky.hyperplaneFunctionalSection`, `OAI.Kaplansky.integralHomologyHomotopyIso`, `OAI.Kaplansky.lineFrameHomeomorph`, `OAI.Kaplansky.lineSumChartPullbackHomeomorph`, `OAI.Kaplansky.localVectorSphereHomologyIso`, `OAI.Kaplansky.openChartCoordinateLocalHomologyIso`, `OAI.Kaplansky.openChartLocalExcisionIso`, `OAI.Kaplansky.openCoverMayerVietorisBoundaryIso`, `OAI.Kaplansky.openCoverMayerVietorisOneIso`, `OAI.Kaplansky.openCoverSmallHomologyIso`, `OAI.Kaplansky.planeSphereHomologyOneIso`, `OAI.Kaplansky.productPairBaseSubsetIso`, `OAI.Kaplansky.productPairChartFiberMap`, `OAI.Kaplansky.productPairCoordinateMap`, `OAI.Kaplansky.productPairFiberMap`, `OAI.Kaplansky.productPairProjection`, `OAI.Kaplansky.productPairProjectionIso`, `OAI.Kaplansky.puncturedVectorBoundaryIso`, `OAI.Kaplansky.relativeChainSequenceMap`, `OAI.Kaplansky.relativeChainsHomeomorphIso`, `OAI.Kaplansky.relativeCoverChainComparison`, `OAI.Kaplansky.relativeCoverChainSequence`, `OAI.Kaplansky.relativeCoverLeftChainsIso`, `OAI.Kaplansky.relativeCoverLeftHomologyIso`, `OAI.Kaplansky.relativeCoverMiddleChainsIso`, `OAI.Kaplansky.relativeCoverMiddleHomologyIso`, `OAI.Kaplansky.relativeCoverQuotientSequence`, `OAI.Kaplansky.relativeCoverQuotientSequenceComparison`, `OAI.Kaplansky.relativeHomologyHomeomorphIso`, `OAI.Kaplansky.relativeMayerVietorisBoundary`, `OAI.Kaplansky.relativeMayerVietorisSumSequence`, `OAI.Kaplansky.relativeMayerVietorisSumSequenceIso` and 22 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Base`, `BundleTests_Normalization`, `BundleTests_Obstruction`, `BundleTests_Retained`, `BundleTests_Twisted`, `ComplexBundle_Hyperplane`, `ComplexBundle_HyperplaneProduct`, `ComplexBundle_Pullback`, `ComplexBundle_Tensor`, `Cuntz_Monoid`, `IntegralHomology_AffineAvoidance`, `IntegralHomology_Connected`, `IntegralHomology_Equivalence`, `IntegralHomology_Excision`, `IntegralHomology_FiniteCover`, `IntegralHomology_FrameNormalization`, `IntegralHomology_LineNormalization`, `IntegralHomology_MayerVietoris`, `IntegralHomology_OpenUnion`, `IntegralHomology_Product`, `IntegralHomology_ProductCover`, `IntegralHomology_ProjectiveLocal`, `IntegralHomology_Relative`, `IntegralHomology_Sections`, `IntegralHomology_SmallExcision`, `IntegralHomology_Sphere`, `Kaplansky_Polynomials`, `OrderedStates_Semigroup`, `Quasitrace_Infiniteness`.
--
--   **Imports.** It imports the bundles `OAIQ4Kq000`, `OAIQ4Kq002`, `OAIQ4Kq003` and `OAIQ4Kq004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ4Kq009` and `OAIQ4Kq010`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ4Kq000
import Definitions.Def_OAIQ4Kq002
import Definitions.Def_OAIQ4Kq003
import Definitions.Def_OAIQ4Kq004

section
-- module Solutions.OAIQ4_Kq.BundleTests_Base
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

theorem testProjectiveDimension_pos {m R : ℕ} (hm : 0 < m) (i : Fin R) :
    0 < testProjectiveDimension m R i := by
  have hn : R-i.val ≠ 0 := by omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hp : 0 < 4^k := pow_pos (by omega) _
  have hh : 0 < 4^(R-i.val)-1 := by rw [hk, pow_succ]; omega
  unfold testProjectiveDimension
  positivity

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

end Kaplansky

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Tensor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

section

variable {B J K : Type*} [TopologicalSpace B]
  (C : VectorBundleCore ℂ B ℂ J) (D : VectorBundleCore ℂ B ℂ K)

theorem tensorLinePair_ne_zero (x : B) (v : C.Fiber x) (w : D.Fiber x)
    (hv : v ≠ 0) (hw : w ≠ 0) : tensorLinePair C D x v w ≠ 0 := by
  change (show ℂ from v) * (show ℂ from w) ≠ 0
  exact mul_ne_zero hv hw

end

variable {B J : Type} [TopologicalSpace B]
  (C : VectorBundleCore ℂ B ℂ J) (u : ∀ b, C.Fiber b)
  (hu : ∀ b, u b ≠ 0)

theorem lineFrameEquiv_chart (b : B) (z : C.Fiber b) (i : J) (hi : b ∈ C.baseSet i) :
    lineFrameEquiv C u hu b z =
      (C.localTriv i ⟨b,z⟩).2 / (C.localTriv i ⟨b,u b⟩).2 := by
  have hc : C.coordChange (C.indexAt b) i b 1 ≠ 0 := by
    intro hz
    have he := C.coordChange_comp (C.indexAt b) i (C.indexAt b) b
      ⟨⟨C.mem_baseSet_at b,hi⟩,C.mem_baseSet_at b⟩ 1
    rw [hz, map_zero, C.coordChange_self _ _ (C.mem_baseSet_at b)] at he
    exact zero_ne_one he
  change (show ℂ from z) / (show ℂ from u b) =
    C.coordChange (C.indexAt b) i b z / C.coordChange (C.indexAt b) i b (u b)
  rw [complexLineMap_scalar (C.coordChange (C.indexAt b) i b) z,
    complexLineMap_scalar (C.coordChange (C.indexAt b) i b) (u b)]
  exact (mul_div_mul_right _ _ hc).symm

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_Sections
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Section classes in one-point compactifications and their naturality. -/

section
open Bundle Topology CategoryTheory AlgebraicTopology OnePoint

/-- A constant map induces zero in every positive homological degree. -/
theorem integralSingularHomology_const {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) {n : ℕ} (hn : n ≠ 0) :
    (integralSingularHomology n).map (TopCat.ofHom (ContinuousMap.const X y)) = 0 := by
  let f : TopCat.of X ⟶ TopCat.of PUnit := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let g : TopCat.of PUnit ⟶ TopCat.of Y := TopCat.ofHom (ContinuousMap.const PUnit y)
  have he : TopCat.ofHom (ContinuousMap.const X y) = f ≫ g := rfl
  rw [he, Functor.map_comp]
  have hz := isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) hn
  have hf : (integralSingularHomology n).map f = 0 := hz.eq_of_tgt _ _
  rw [hf, Limits.zero_comp]

end

open Bundle Topology CategoryTheory OnePoint

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Relative
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSingularChainsIntoSmallRight _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSmallSingularChainInclusion
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

theorem relativeChainMap_id {A X : TopCat.{0}} (i : A ⟶ X) :
    relativeChainMap i i (𝟙 A) (𝟙 X) (by simp) = 𝟙 _ := by
  apply (cancel_epi (relativeChainProjection i)).mp
  simp

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

theorem relativeHomologyMap_id {A X : TopCat.{0}} (i : A ⟶ X) (n : ℕ) :
    relativeHomologyMap i i (𝟙 _) (𝟙 _) (by simp) n = 𝟙 _ := by
  simp [relativeHomologyMap, relativeChainMap_id, relativeSingularHomology]

theorem relativeHomologyMap_comp {A X B Y C Z : TopCat.{0}}
    (i : A ⟶ X) (j : B ⟶ Y) (k : C ⟶ Z)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j)
    (b : B ⟶ C) (g : Y ⟶ Z) (h' : j ≫ g = b ≫ k) (n : ℕ) :
    relativeHomologyMap i j a f h n ≫ relativeHomologyMap j k b g h' n =
      relativeHomologyMap i k (a ≫ b) (f ≫ g) (by rw [← Category.assoc, h,
        Category.assoc, h', Category.assoc]) n := by
  exact (HomologicalComplex.homologyMap_comp (relativeChainMap i j a f h)
    (relativeChainMap j k b g h') n).symm.trans
      (congrArg (fun φ => HomologicalComplex.homologyMap φ n)
        (relativeChainMap_comp i j k a f h b g h'))

theorem relativeHomologyBoundary_inclusion {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (n : ℕ) : relativeHomologyBoundary i n ≫ (integralSingularHomology n).map i = 0 :=
  (relativeChainSequence_shortExact i).δ_comp (n+1) n rfl

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_Equivalence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSingularChainsIntoSmallRight _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSmallSingularChainInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Contractible-pair homology, equivalences, and relative map extensionality. -/

section
open CategoryTheory Limits ContinuousMap

/-- An actual homotopy equivalence induces an integral homology isomorphism. -/
def integralHomologyHomotopyIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (n : ℕ) :
    (integralSingularHomology n).obj (TopCat.of X) ≅
      (integralSingularHomology n).obj (TopCat.of Y) where
  hom := (integralSingularHomology n).map (TopCat.ofHom e.toFun)
  inv := (integralSingularHomology n).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.left_inv
    exact (integralSingularHomology_homotopy H n).trans (CategoryTheory.Functor.map_id _ _)
  inv_hom_id := by
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.right_inv
    exact (integralSingularHomology_homotopy H n).trans (CategoryTheory.Functor.map_id _ _)

theorem integralSingularHomology_isZero_contractible (X : Type)
    [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero ((integralSingularHomology n).obj (TopCat.of X)) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  rw [IsZero.iff_id_eq_zero]
  have h := integralSingularHomology_homotopy
    (f := TopCat.ofHom (ContinuousMap.id X))
    (g := TopCat.ofHom (ContinuousMap.const X x)) H n
  change (integralSingularHomology n).map (𝟙 (TopCat.of X)) = _ at h
  rw [CategoryTheory.Functor.map_id, integralSingularHomology_const x hn] at h
  exact h

/-- In degrees at least two, relative homology in a contractible ambient
space is the preceding homology of the subspace, via the actual boundary. -/
def contractibleRelativeBoundaryIso {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    relativeSingularHomology i (n+1) ≅ (integralSingularHomology n).obj A :=
  (relativeChainSequence_shortExact i).δIso (n+1) n rfl
    (integralSingularHomology_isZero_contractible X (n+1) (Nat.succ_ne_zero n))
    (integralSingularHomology_isZero_contractible X n hn)

def puncturedVectorBoundaryIso (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (hn : n ≠ 0) :
    relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set V)) (n+1) ≅
      (integralSingularHomology n).obj (TopCat.of ({0}ᶜ : Set V)) :=
  contractibleRelativeBoundaryIso _ n hn

end

section
open CategoryTheory Limits
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A genuine homeomorphism of pairs acts invertibly on relative singular chains. -/
def relativeChainsHomeomorphIso (e : X ≃ₜ Y) (U : Set X) (V : Set Y)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) :
    relativeSingularChains (subspaceInclusion U) ≅
      relativeSingularChains (subspaceInclusion V) :=
  cokernel.mapIso _ _
    (integralSingularChains.mapIso (TopCat.isoOfHomeo (e.subtype h)))
    (integralSingularChains.mapIso (TopCat.isoOfHomeo e)) (by
      change integralSingularChains.map _ ≫ integralSingularChains.map _ =
        integralSingularChains.map _ ≫ integralSingularChains.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      apply congrArg integralSingularChains.map
      rfl)

def relativeHomologyHomeomorphIso (e : X ≃ₜ Y) (U : Set X) (V : Set Y)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion U) n ≅
      relativeSingularHomology (subspaceInclusion V) n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (relativeChainsHomeomorphIso e U V h)

/-- The isomorphism is the same map as that induced by the actual map of pairs. -/
theorem relativeHomologyHomeomorphIso_hom (e : X ≃ₜ Y) (U : Set X) (V : Set Y)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) (n : ℕ) :
    (relativeHomologyHomeomorphIso e U V h n).hom =
      relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
        (subspaceMap U V ⟨e, e.continuous⟩ (fun x hx => (h x).mp hx))
        (TopCat.ofHom ⟨e, e.continuous⟩) (subspaceMap_square _ _ _ _) n := rfl

end

section
open CategoryTheory

/-- Into an embedded subspace, the ambient map uniquely determines the
map of relative chains and hence of relative homology. -/
theorem relativeHomologyMap_congr_ambient {A X B Y : TopCat.{0}}
    (i : A ⟶ X) (j : B ⟶ Y) [Mono j]
    (a b : A ⟶ B) (f g : X ⟶ Y)
    (h : i ≫ f = a ≫ j) (h' : i ≫ g = b ≫ j) (he : f = g) (n : ℕ) :
    relativeHomologyMap i j a f h n = relativeHomologyMap i j b g h' n := by
  subst g
  have ha : a = b := (cancel_mono j).mp (h.symm.trans h')
  subst b
  rfl

end

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_SmallExcision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Small relative excision, Mayer-Vietoris, and naturality. -/

section
open CategoryTheory Limits AlgebraicTopology

section
variable {X : Type} [TopologicalSpace X]

instance instMonoTopCatSubspaceInclusionOfLE {U V : Set X} (h : U ⊆ V) : Mono (subspaceInclusionOfLE h) := by
  apply (TopCat.mono_iff_injective _).mpr
  intro a b he
  exact Subtype.ext (congrArg (fun z : V => z.val) he)

/-- Mayer–Vietoris chain sequence for genuine subspaces, with the complex
of small chains at the right. No open-cover comparison is assumed. -/
def smallMayerVietorisSequence (U V : Set X) :=
  (smallSingularChains_isPushout U V).shortComplex

theorem smallMayerVietorisSequence_shortExact (U V : Set X) :
    (smallMayerVietorisSequence U V).ShortExact := by
  have hm₁ : Mono (integralSingularChains.map
      (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U))) := by
    unfold integralSingularChains
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hm : Mono (smallMayerVietorisSequence U V).f := by
    exact @biprod.mono_lift_of_mono_left _ _ _ _ _ _ _ _ _ hm₁
  have he : Epi (smallMayerVietorisSequence U V).g :=
    (smallSingularChains_isPushout U V).epi_shortComplex_g
  exact { exact := (smallSingularChains_isPushout U V).exact_shortComplex }

def smallMayerVietorisBoundary (U V : Set X) (n : ℕ) :
    (smallSingularChains U V).homology (n+1) ⟶
      (integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)) :=
  (smallMayerVietorisSequence_shortExact U V).δ (n+1) n rfl

end

end

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Exactness at the intersection term of the actual small-chain sequence. -/
theorem smallMayerVietoris_exact_at_intersection (n : ℕ) :
    (ShortComplex.mk _ _
      ((smallMayerVietorisSequence_shortExact U V).δ_comp (n+1) n rfl)).Exact :=
  (smallMayerVietorisSequence_shortExact U V).homology_exact₁ (n+1) n rfl

theorem smallMayerVietoris_sum_isZero [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (hn : n ≠ 0) :
    IsZero ((smallMayerVietorisSequence U V).X₂.homology n) :=
  homology_biprod_isZero _ _ n
    (integralSingularHomology_isZero_contractible U n hn)
    (integralSingularHomology_isZero_contractible V n hn)

/-- For two contractible subspaces, the actual small-chain connecting map
is an isomorphism in degrees at least two. Full singular homology still
requires the small-to-full comparison theorem. -/
def smallMayerVietorisBoundaryIso [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (hn : n ≠ 0) :
    (smallSingularChains U V).homology (n+1) ≅
      (integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)) :=
  (smallMayerVietorisSequence_shortExact U V).δIso (n+1) n rfl
    (smallMayerVietoris_sum_isZero U V (n+1) (Nat.succ_ne_zero n))
    (smallMayerVietoris_sum_isZero U V n hn)

end

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_MayerVietoris
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

theorem relativeOpenCoverGlue_restrictions (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (u : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1) ⟶ Z)
    (v : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1) ⟶ Z)
    (hcompat : restrictedPairHomologyMap (Set.inter_subset_left : U ∩ V ⊆ U) A (n+1) ≫ u =
      restrictedPairHomologyMap (Set.inter_subset_right : U ∩ V ⊆ V) A (n+1) ≫ v) :
    restrictedPairToAmbientHomologyMap U A (n+1) ≫
      relativeOpenCoverGlue U V A hU hV hcover n hi u v hcompat = u ∧
    restrictedPairToAmbientHomologyMap V A (n+1) ≫
      relativeOpenCoverGlue U V A hU hV hcover n hi u v hcompat = v := by
  have := relativeOpenCover_sum_epi U V A hU hV hcover n hi
  have he := (relativeMayerVietoris_exact_at_sum U V A hU hV hcover (n+1)).g_desc
    (biprod.desc u v) (show (relativeMayerVietorisSumSequence U V A (n+1)).f ≫
      biprod.desc u v = 0 by
        dsimp only [relativeMayerVietorisSumSequence]
        erw [biprod.lift_desc, Preadditive.neg_comp, hcompat, add_neg_cancel]
        rfl)
  constructor
  · have hl := congrArg (fun f => biprod.inl ≫ f) he
    dsimp only [relativeMayerVietorisSumSequence] at hl
    erw [biprod.inl_desc_assoc, biprod.inl_desc] at hl
    exact hl
  · have hr := congrArg (fun f => biprod.inr ≫ f) he
    dsimp only [relativeMayerVietorisSumSequence] at hr
    erw [biprod.inr_desc_assoc, biprod.inr_desc] at hr
    exact hr

end

open CategoryTheory Limits HomologicalComplex
section
variable {X : Type} [TopologicalSpace X] (U V A : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover

/-- Vanishing criterion in full relative singular homology, suitable for
inductively joining bundle charts. -/
theorem relativeOpenCover_isZero (n : ℕ)
    (hu : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1)))
    (hv : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1)))
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n)) :
    IsZero (relativeSingularHomology (subspaceInclusion A) (n+1)) := by
  have hg : (relativeMayerVietorisSumSequence U V A (n+1)).g = 0 := by
    dsimp only [relativeMayerVietorisSumSequence]
    apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc]
    · exact hu.eq_of_src _ _
    · exact hv.eq_of_src _ _
  exact (relativeMayerVietoris_exact_at_relative U V A hU hV hcover n).isZero_of_both_zeros
    hg (hi.eq_of_tgt _ _)

/-- Agreement on the two charts determines a global normalization uniquely
when the preceding overlap group vanishes. -/
theorem relativeOpenCover_hom_ext (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z)
    (hu : restrictedPairToAmbientHomologyMap U A (n+1) ≫ f =
      restrictedPairToAmbientHomologyMap U A (n+1) ≫ g)
    (hv : restrictedPairToAmbientHomologyMap V A (n+1) ≫ f =
      restrictedPairToAmbientHomologyMap V A (n+1) ≫ g) : f = g := by
  have := relativeOpenCover_sum_epi U V A hU hV hcover n hi
  apply (cancel_epi (relativeMayerVietorisSumSequence U V A (n+1)).g).mp
  dsimp only [relativeMayerVietorisSumSequence]
  apply biprod.hom_ext'
  · erw [biprod.inl_desc_assoc, biprod.inl_desc_assoc]
    exact hu
  · erw [biprod.inr_desc_assoc, biprod.inr_desc_assoc]
    exact hv

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Pullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ4_Kq.ComplexBundle_Hyperplane
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ4_Kq.ComplexBundle_HyperplaneProduct
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
-- module Solutions.OAIQ4_Kq.IntegralHomology_Excision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Excision for chart-small chains, open covers, and open embeddings. -/

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Comparison from the homology of small chains to full integral singular
homology for a genuine two-set open cover. -/
def openCoverSmallHomologyIso (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (smallSingularChains U V).homology n ≅ (integralSingularChains.obj (TopCat.of X)).homology n := by
  haveI := smallSingularChainInclusion_quasiIso U V hU hV hUV
  exact isoOfQuasiIsoAt (smallSingularChainInclusion U V) n

/-- Full singular Mayer–Vietoris boundary isomorphism for a cover by two
contractible open subspaces, in degrees at least two. -/
def openCoverMayerVietorisBoundaryIso [ContractibleSpace U] [ContractibleSpace V]
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) (hn : n ≠ 0) :
    (integralSingularHomology (n+1)).obj (TopCat.of X) ≅
      (integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)) :=
  (openCoverSmallHomologyIso U V hU hV hUV (n+1)).symm ≪≫
    smallMayerVietorisBoundaryIso U V n hn

open ComplexGrassmann

end

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_OpenUnion
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
-- module Solutions.OAIQ4_Kq.IntegralHomology_FiniteCover
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

/-- Relative homology of an empty ambient space is zero in every degree. -/
theorem relativeHomology_isZero_empty [IsEmpty X] (A : Set X) (n : ℕ) :
    IsZero (relativeSingularHomology (subspaceInclusion A) n) := by
  have : IsIso (subspaceInclusion A) := by
    exact (TopCat.isoOfHomeo (X := TopCat.of A) (Y := TopCat.of X) (show A ≃ₜ X from
      { toFun := Subtype.val
        invFun := fun x => isEmptyElim x
        left_inv := fun x => isEmptyElim x.val
        right_inv := fun x => isEmptyElim x
        continuous_toFun := continuous_subtype_val
        continuous_invFun := continuous_of_discreteTopology })).isIso_hom
  have : IsIso (integralSingularChains.map (subspaceInclusion A)) := by infer_instance
  exact (homologyFunctor _ _ n).map_isZero
    (isZero_cokernel_of_epi (integralSingularChains.map (subspaceInclusion A)))

/-- The relative two-chart sum is surjective also in degree zero. There
is no spurious degree-minus-one overlap hypothesis. -/
theorem relativeOpenCover_sum_epi_zero (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Epi (relativeMayerVietorisSumSequence U V A 0).g := by
  have : Epi (relativeCoverChainSequence U V A).g :=
    (relativeCoverChainSequence_shortExact U V A).epi_g
  have hepi : Epi (homologyMap (relativeCoverChainSequence U V A).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by intro j; simp)
  have hiso : IsIso (homologyMap (relativeCoverChainComparison U V A) 0) := by
    change IsIso (relativeOpenCoverHomologyIso U V A hU hV hcover 0).hom
    infer_instance
  have : Epi ((relativeCoverMiddleHomologyIso U V A 0).hom ≫
      (relativeMayerVietorisSumSequence U V A 0).g) := by
    change Epi ((relativeCoverMiddleHomologyIso U V A 0).hom ≫ biprod.desc _ _)
    erw [relativeCoverMiddleHomologyIso_map]
    exact epi_comp' hepi (@IsIso.epi_of_iso _ _ _ _ _ hiso)
  exact epi_of_epi (relativeCoverMiddleHomologyIso U V A 0).hom _

theorem relativeOpenCover_zero_isZero (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hu : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) 0))
    (hv : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) 0)) :
    IsZero (relativeSingularHomology (subspaceInclusion A) 0) := by
  have := relativeOpenCover_sum_epi_zero U V A hU hV hcover
  have hg : (relativeMayerVietorisSumSequence U V A 0).g = 0 := by
    dsimp only [relativeMayerVietorisSumSequence]
    apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc]
    · exact hu.eq_of_src _ _
    · exact hv.eq_of_src _ _
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi (relativeMayerVietorisSumSequence U V A 0).g).mp
  erw [hg, zero_comp]

/-- Nested restrictions give the same actual pair, with ambient subspace
topology and the same removed set. -/
def restrictedPairSubsetIso (U W A : Set X) (h : U ⊆ W) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' (Subtype.val ⁻¹' A : Set W) : Set (Subtype.val ⁻¹' U : Set W))) n ≅
    relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n :=
  relativeHomologyHomeomorphIso (subspaceSubsetHomeomorph U W h)
    (Subtype.val ⁻¹' (Subtype.val ⁻¹' A : Set W) : Set (Subtype.val ⁻¹' U : Set W))
    (Subtype.val ⁻¹' A : Set U) (fun _ => Iff.rfl) n

/-- Uniform vanishing below r is preserved by a two-set open union. -/
theorem relativeOpenUnion_below_isZero (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (r : ℕ)
    (hu : ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) n))
    (hv : ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) n))
    (hi : ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n)) :
    ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∪ V))) n) := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := by ext x; exact iff_true_intro x.property
  have hu' n hn := (hu n hn).of_iso
    (restrictedPairSubsetIso U (U ∪ V) A Set.subset_union_left n)
  have hv' n hn := (hv n hn).of_iso
    (restrictedPairSubsetIso V (U ∪ V) A Set.subset_union_right n)
  have hi' n hn := (hi n hn).of_iso
    (restrictedPairSubsetIso (U ∩ V) (U ∪ V) A
      (fun _ h => Or.inl h.1) n)
  intro n hn
  cases n with
  | zero =>
    exact relativeOpenCover_zero_isZero U' V' _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      hcov (hu' 0 hn) (hv' 0 hn)
  | succ n =>
    exact relativeOpenCover_isZero U' V' _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      hcov n (hu' (n+1) hn) (hv' (n+1) hn) (hi' n (by omega))

end

section
open CategoryTheory Limits Set
variable {X ι : Type} [TopologicalSpace X]

/-- Uniform relative vanishing below r on all nonempty finite intersections
implies the same bound on their union. The empty union and degree zero are
included, and there is no loss depending on the number of charts. -/
theorem finiteRelativeOpenUnion_below_isZero (S : Finset ι) (U : ι → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i)) (r : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ n < r,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) n)) :
    ∀ n < r, IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U i))) n) := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty =>
    intro n _
    have he : (⋃ i ∈ (∅ : Finset ι), U i) = ∅ := by simp
    rw [he]
    exact relativeHomology_isZero_empty _ n
  | @insert a S ha ih =>
    by_cases hs : S.Nonempty
    · have hU : ∀ n < r, IsZero (relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set (U a))) n) := by
        have he : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
        have hz := hinter {a} (by simp) (by simp)
        rw [he] at hz
        exact hz
      have hV := ih U (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
        (fun T ht hts n hn => hinter T ht (hts.trans (Finset.subset_insert a S)) n hn)
      have hI : ∀ n < r, IsZero (relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U a ∩ U i))) n) := by
        apply ih (fun i => U a ∩ U i)
          (fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi)))
        intro T ht hts n hn
        have hb := hinter (insert a T) (by simp) (Finset.insert_subset_insert a hts) n hn
        have he : (⋂ i ∈ T, U a ∩ U i) = ⋂ i ∈ insert a T, U i := by
          ext x
          simp only [mem_iInter, Finset.mem_insert]
          constructor
          · intro hx i hi
            rcases hi with rfl | hi
            · obtain ⟨j,hj⟩ := ht
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
        · rintro ⟨i,hi,hxa,hxi⟩
          exact ⟨hxa,i,hi,hxi⟩
        · rintro ⟨hxa,i,hi,hxi⟩
          exact ⟨i,hi,hxa,hxi⟩
      rw [heI] at hI
      have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by ext x; simp
      rw [heW]
      exact relativeOpenUnion_below_isZero (U a) (⋃ i ∈ S, U i) A
        (hopen a (by simp))
        (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi))))
        r hU hV hI
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst S
      have hz := hinter {a} (by simp) (by simp)
      have hea : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
      have heb : (⋃ i ∈ insert a (∅ : Finset ι), U i) = U a := by ext x; simp
      rw [hea] at hz
      rw [heb]
      exact hz

end

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X]

theorem restrictedPairHomologyMap_comp {U V W : Set X}
    (h : U ⊆ V) (k : V ⊆ W) (A : Set X) (n : ℕ) :
    restrictedPairHomologyMap h A n ≫ restrictedPairHomologyMap k A n =
      restrictedPairHomologyMap (h.trans k) A n := by
  unfold restrictedPairHomologyMap
  erw [← homologyMap_comp]
  congr 1
  unfold restrictedPairChainMap
  erw [relativeChainMap_comp]
  rfl

/-- Actual inclusion after eliminating a redundant enclosing subtype. -/
theorem restrictedPairSubsetIso_toAmbient (U W A : Set X) (h : U ⊆ W) (n : ℕ) :
    (restrictedPairSubsetIso U W A h n).hom ≫ restrictedPairHomologyMap h A n =
      restrictedPairToAmbientHomologyMap (Subtype.val ⁻¹' U : Set W) (Subtype.val ⁻¹' A) n := by
  unfold restrictedPairSubsetIso
  erw [relativeHomologyHomeomorphIso_hom]
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Maps out of a restricted open union are determined on its two actual
subsets when the preceding relative overlap group vanishes. -/
theorem relativeOpenUnion_hom_ext (U V A : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ) (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∪ V))) (n+1) ⟶ Z)
    (hu : restrictedPairHomologyMap (Set.subset_union_left : U ⊆ U ∪ V) A (n+1) ≫ f =
      restrictedPairHomologyMap (Set.subset_union_left : U ⊆ U ∪ V) A (n+1) ≫ g)
    (hv : restrictedPairHomologyMap (Set.subset_union_right : V ⊆ U ∪ V) A (n+1) ≫ f =
      restrictedPairHomologyMap (Set.subset_union_right : V ⊆ U ∪ V) A (n+1) ≫ g) : f = g := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := by ext x; exact iff_true_intro x.property
  apply relativeOpenCover_hom_ext U' V' (Subtype.val ⁻¹' A)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) hcov n
    (hi.of_iso (restrictedPairSubsetIso (U ∩ V) (U ∪ V) A
      (fun _ h => Or.inl h.1) n)) f g
  · rw [← restrictedPairSubsetIso_toAmbient U (U ∪ V) A Set.subset_union_left,
      Category.assoc, Category.assoc, hu]
  · rw [← restrictedPairSubsetIso_toAmbient V (U ∪ V) A Set.subset_union_right,
      Category.assoc, Category.assoc, hv]

end

section
open CategoryTheory Limits Set

section
variable {X ι : Type} [TopologicalSpace X]

/-- The actual chart inclusions jointly detect maps out of a finite open
union in degree n+1 if every intersection vanishes in degrees at most n. -/
theorem finiteRelativeOpenUnion_hom_ext (S : Finset ι) (U : ι → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i)) (n : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U i))) (n+1) ⟶ Z)
    (hfg : ∀ i (_ : i ∈ S) (h : U i ⊆ ⋃ j ∈ S, U j),
      restrictedPairHomologyMap h A (n+1) ≫ f =
      restrictedPairHomologyMap h A (n+1) ≫ g) : f = g := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty =>
    have he : (⋃ i ∈ (∅ : Finset ι), U i) = ∅ := by simp
    have hz : IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ (∅ : Finset ι), U i))) (n+1)) := by
      rw [he]
      exact relativeHomology_isZero_empty _ _
    exact hz.eq_of_src f g
  | @insert a S ha ih =>
    have hI : IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U a ∩ U i))) n) := by
      apply finiteRelativeOpenUnion_below_isZero S (fun i => U a ∩ U i) A
        (fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi))) (n+1)
        ?_ n (by omega)
      intro T ht hts q hq
      have hb := hinter (insert a T) (by simp) (Finset.insert_subset_insert a hts) q hq
      have he : (⋂ i ∈ T, U a ∩ U i) = ⋂ i ∈ insert a T, U i := by
        ext x
        simp only [mem_iInter, Finset.mem_insert]
        constructor
        · intro hx i hi
          rcases hi with rfl | hi
          · obtain ⟨j,hj⟩ := ht
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
      · rintro ⟨i,hi,hxa,hxi⟩
        exact ⟨hxa,i,hi,hxi⟩
      · rintro ⟨hxa,i,hi,hxi⟩
        exact ⟨i,hi,hxa,hxi⟩
    rw [heI] at hI
    have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by ext x; simp
    revert f g hfg
    rw [heW]
    intro f g hfg
    apply relativeOpenUnion_hom_ext (U a) (⋃ i ∈ S, U i) A (hopen a (by simp))
      (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi)))) n hI f g
    · exact hfg a (by simp) Set.subset_union_left
    · apply ih U (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
        (fun T ht hts q hq => hinter T ht (hts.trans (Finset.subset_insert a S)) q hq)
      intro i hi h
      simp only [← Category.assoc, restrictedPairHomologyMap_comp]
      exact hfg i (Finset.mem_insert_of_mem hi) (h.trans Set.subset_union_right)

end

section
variable {X : Type} [TopologicalSpace X]

theorem restrictedPairSubsetIso_map (U V W A : Set X)
    (hUV : U ⊆ V) (hVW : V ⊆ W) (n : ℕ) :
    (restrictedPairSubsetIso U W A (hUV.trans hVW) n).hom ≫
      restrictedPairHomologyMap hUV A n =
    restrictedPairHomologyMap (preimage_mono hUV :
      (Subtype.val ⁻¹' U : Set W) ⊆ Subtype.val ⁻¹' V) (Subtype.val ⁻¹' A) n ≫
      (restrictedPairSubsetIso V W A hVW n).hom := by
  unfold restrictedPairSubsetIso
  erw [relativeHomologyHomeomorphIso_hom, relativeHomologyHomeomorphIso_hom]
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n =
    relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n
  erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Compatible linear maps on two open subspaces glue to a map on
their union when the preceding overlap homology is zero. -/
theorem relativeOpenUnion_exists_glue (U V A : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (hi : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∩ V))) n))
    {Z : ModuleCat.{0} ℤ}
    (u : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set U)) (n+1) ⟶ Z)
    (v : relativeSingularHomology (subspaceInclusion (Subtype.val ⁻¹' A : Set V)) (n+1) ⟶ Z)
    (hcompat : restrictedPairHomologyMap (inter_subset_left : U ∩ V ⊆ U) A (n+1) ≫ u =
      restrictedPairHomologyMap (inter_subset_right : U ∩ V ⊆ V) A (n+1) ≫ v) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(U ∪ V))) (n+1) ⟶ Z,
      restrictedPairHomologyMap (subset_union_left : U ⊆ U ∪ V) A (n+1) ≫ f = u ∧
      restrictedPairHomologyMap (subset_union_right : V ⊆ U ∪ V) A (n+1) ≫ f = v := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  let A' : Set ↥(U ∪ V) := Subtype.val ⁻¹' A
  have hcov : U' ∪ V' = univ := by ext x; exact iff_true_intro x.property
  let eu := restrictedPairSubsetIso U (U ∪ V) A subset_union_left (n+1)
  let ev := restrictedPairSubsetIso V (U ∪ V) A subset_union_right (n+1)
  have hi' : IsZero (relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A' : Set ↥(U' ∩ V'))) n) :=
    hi.of_iso (restrictedPairSubsetIso (U ∩ V) (U ∪ V) A
      (fun _ hx => Or.inl hx.1) n)
  have hc : restrictedPairHomologyMap (inter_subset_left : U' ∩ V' ⊆ U') A' (n+1) ≫
        (eu.hom ≫ u) =
      restrictedPairHomologyMap (inter_subset_right : U' ∩ V' ⊆ V') A' (n+1) ≫
        (ev.hom ≫ v) := by
    rw [← Category.assoc, ← Category.assoc]
    change (_ ≫ (restrictedPairSubsetIso U (U ∪ V) A _ _).hom) ≫ u =
      (_ ≫ (restrictedPairSubsetIso V (U ∪ V) A _ _).hom) ≫ v
    erw [← restrictedPairSubsetIso_map (U ∩ V) U (U ∪ V) A inter_subset_left subset_union_left,
      ← restrictedPairSubsetIso_map (U ∩ V) V (U ∪ V) A inter_subset_right subset_union_right]
    erw [Category.assoc, Category.assoc, hcompat]
  let f := relativeOpenCoverGlue U' V' A'
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    hcov n hi' (eu.hom ≫ u) (ev.hom ≫ v) hc
  have hf := relativeOpenCoverGlue_restrictions U' V' A'
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    hcov n hi' (eu.hom ≫ u) (ev.hom ≫ v) hc
  refine ⟨f, ?_, ?_⟩
  · apply (cancel_epi eu.hom).mp
    rw [← Category.assoc]
    change ((restrictedPairSubsetIso U (U ∪ V) A _ _).hom ≫ _) ≫ f = _
    rw [restrictedPairSubsetIso_toAmbient]
    exact hf.1
  · apply (cancel_epi ev.hom).mp
    rw [← Category.assoc]
    change ((restrictedPairSubsetIso V (U ∪ V) A _ _).hom ≫ _) ≫ f = _
    rw [restrictedPairSubsetIso_toAmbient]
    exact hf.2

end

variable {X ι : Type} [TopologicalSpace X]

/-- Restricting a pair to the whole ambient set changes no homology. -/
theorem restrictedPairToAmbient_univ_isIso (A : Set X) (n : ℕ) :
    IsIso (restrictedPairToAmbientHomologyMap Set.univ A n) := by
  let e := relativeHomologyHomeomorphIso (Homeomorph.Set.univ X)
    (Subtype.val ⁻¹' A) A (fun _ => Iff.rfl) n
  have he : restrictedPairToAmbientHomologyMap Set.univ A n = e.hom := by
    erw [relativeHomologyHomeomorphIso_hom]
    apply relativeHomologyMap_congr_ambient
    rfl
  rw [he]
  infer_instance

/-- Finite chart detection for the whole actual pair. -/
theorem finiteRelativeOpenCover_hom_ext (S : Finset ι) (U : ι → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i))
    (hcover : (⋃ i ∈ S, U i) = Set.univ) (n : ℕ)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (f g : relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z)
    (hfg : ∀ i ∈ S, restrictedPairToAmbientHomologyMap (U i) A (n+1) ≫ f =
      restrictedPairToAmbientHomologyMap (U i) A (n+1) ≫ g) : f = g := by
  have : IsIso (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1)) := by
    rw [hcover]
    exact restrictedPairToAmbient_univ_isIso A (n+1)
  apply (cancel_epi (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1))).mp
  apply finiteRelativeOpenUnion_hom_ext S U A hopen n hinter
  intro i hi h
  simp only [← Category.assoc, restrictedPairHomologyMap_toAmbient]
  exact hfg i hi

end

open CategoryTheory Limits Set
section
variable {X J : Type} [TopologicalSpace X]

/-- Pairwise compatible normalizations on a finite open cover glue in
the first possibly nonzero relative degree. All inclusions are the actual
restricted-pair maps; no extension of a homomorphism is postulated. -/
theorem finiteRelativeOpenUnion_exists_glue (S : Finset J) (U : J → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i)) (n : ℕ)
    (hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (u : ∀ i, relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set (U i))) (n+1) ⟶ Z)
    (hc : ∀ i ∈ S, ∀ j ∈ S,
      restrictedPairHomologyMap (inter_subset_left : U i ∩ U j ⊆ U i) A (n+1) ≫ u i =
      restrictedPairHomologyMap (inter_subset_right : U i ∩ U j ⊆ U j) A (n+1) ≫ u j) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋃ i ∈ S, U i))) (n+1) ⟶ Z,
      ∀ i (_ : i ∈ S) (h : U i ⊆ ⋃ j ∈ S, U j),
        restrictedPairHomologyMap h A (n+1) ≫ f = u i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,fun i hi => (Finset.notMem_empty i hi).elim⟩
  | @insert a S ha ih =>
    obtain ⟨v,hv⟩ := ih (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
      (fun T ht hts q hq => hinter T ht (hts.trans (Finset.subset_insert a S)) q hq)
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    let C : J → Set X := fun i => U a ∩ U i
    have hCopen : ∀ i ∈ S, IsOpen (C i) :=
      fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi))
    have hCI : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
        IsZero (relativeSingularHomology
          (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, C i))) q) := by
      intro T ht hts q hq
      have he : (⋂ i ∈ T, C i) = ⋂ i ∈ insert a T, U i := by
        ext x
        simp only [C, mem_iInter, mem_inter_iff, Finset.mem_insert]
        constructor
        · intro hx i hi
          rcases hi with rfl | hi
          · obtain ⟨j,hj⟩ := ht
            exact (hx j hj).1
          · exact (hx i hi).2
        · intro hx i hi
          exact ⟨hx a (Or.inl rfl),hx i (Or.inr hi)⟩
      rw [he]
      exact hinter (insert a T) (by simp) (Finset.insert_subset_insert a hts) q hq
    have heI : (⋃ i ∈ S, C i) = U a ∩ (⋃ i ∈ S, U i) := by
      ext x
      simp only [C, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨i,hi,hxa,hxi⟩; exact ⟨hxa,i,hi,hxi⟩
      · rintro ⟨hxa,i,hi,hxi⟩; exact ⟨i,hi,hxa,hxi⟩
    have hI := finiteRelativeOpenUnion_below_isZero S C A hCopen (n+1) hCI n (by omega)
    rw [heI] at hI
    have hcv : restrictedPairHomologyMap (inter_subset_left :
          U a ∩ (⋃ i ∈ S, U i) ⊆ U a) A (n+1) ≫ u a =
        restrictedPairHomologyMap (inter_subset_right :
          U a ∩ (⋃ i ∈ S, U i) ⊆ ⋃ i ∈ S, U i) A (n+1) ≫ v := by
      have hext := finiteRelativeOpenUnion_hom_ext S C A hCopen n hCI (Z := Z)
      rw [heI] at hext
      apply hext
      intro i hi h
      simp only [← Category.assoc, restrictedPairHomologyMap_comp]
      have hinc : U i ⊆ ⋃ j ∈ S, U j :=
        fun x hx => mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
      rw [← restrictedPairHomologyMap_comp (inter_subset_right : U a ∩ U i ⊆ U i) hinc,
        Category.assoc, hv i hi hinc]
      exact hc a (by simp) i (Finset.mem_insert_of_mem hi)
    have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by ext x; simp
    rw [heW]
    obtain ⟨f,hfa,hfv⟩ := relativeOpenUnion_exists_glue (U a) (⋃ i ∈ S, U i) A
      (hopen a (by simp))
      (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi))))
      n hI (u a) v hcv
    refine ⟨f,?_⟩
    intro i hi h
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hfa
    · have hinc : U i ⊆ ⋃ j ∈ S, U j :=
        fun x hx => mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
      rw [← restrictedPairHomologyMap_comp hinc subset_union_right, Category.assoc, hfv]
      exact hv i hi hinc

/-- A finite open cover now gives a genuine map on the whole pair. -/
theorem finiteRelativeOpenCover_exists_glue (S : Finset J) (U : J → Set X)
    (A : Set X) (hopen : ∀ i ∈ S, IsOpen (U i))
    (hcover : (⋃ i ∈ S, U i) = univ) (n : ℕ)
    (hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) q))
    {Z : ModuleCat.{0} ℤ}
    (u : ∀ i, relativeSingularHomology
      (subspaceInclusion (Subtype.val ⁻¹' A : Set (U i))) (n+1) ⟶ Z)
    (hc : ∀ i ∈ S, ∀ j ∈ S,
      restrictedPairHomologyMap (inter_subset_left : U i ∩ U j ⊆ U i) A (n+1) ≫ u i =
      restrictedPairHomologyMap (inter_subset_right : U i ∩ U j ⊆ U j) A (n+1) ≫ u j) :
    ∃ f : relativeSingularHomology (subspaceInclusion A) (n+1) ⟶ Z,
      ∀ i ∈ S, restrictedPairToAmbientHomologyMap (U i) A (n+1) ≫ f = u i := by
  obtain ⟨v,hv⟩ := finiteRelativeOpenUnion_exists_glue S U A hopen n hinter u hc
  have : IsIso (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1)) := by
    rw [hcover]
    exact restrictedPairToAmbient_univ_isIso A (n+1)
  refine ⟨inv (restrictedPairToAmbientHomologyMap (⋃ i ∈ S, U i) A (n+1)) ≫ v, ?_⟩
  intro i hi
  have hinc : U i ⊆ ⋃ j ∈ S, U j :=
    fun x hx => mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩
  rw [← restrictedPairHomologyMap_toAmbient hinc, Category.assoc,
    IsIso.hom_inv_id_assoc]
  exact hv i hi hinc

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_Product
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

/-- Composition of homeomorphisms agrees with composition on relative homology. -/
theorem relativeHomologyHomeomorphIso_trans_hom
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y ≃ₜ Z) (U : Set X) (V : Set Y) (W : Set Z)
    (he : ∀ x, x ∈ U ↔ e x ∈ V) (hf : ∀ y, y ∈ V ↔ f y ∈ W) (n : ℕ) :
    (relativeHomologyHomeomorphIso (e.trans f) U W
      (fun x => (he x).trans (hf (e x))) n).hom =
      (relativeHomologyHomeomorphIso e U V he n).hom ≫
        (relativeHomologyHomeomorphIso f V W hf n).hom := by
  simp only [relativeHomologyHomeomorphIso_hom]
  rw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Restricting product coordinates commutes with projection to relative fiber homology. -/
theorem productPairNormalization_restrict
    {X Y A B V : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace V] [Zero V]
    (U : Set X) (W : Set Y) (i : C(X,Y)) (hi : Set.MapsTo i U W)
    (e : X ≃ₜ A × V) (f : Y ≃ₜ B × V)
    (he : ∀ x, x ∈ U ↔ (e x).2 ≠ 0) (hf : ∀ y, y ∈ W ↔ (f y).2 ≠ 0)
    (hcoords : ∀ x, (f (i x)).2 = (e x).2) (n : ℕ) :
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion W)
        (subspaceMap U W i hi) (TopCat.ofHom i) (subspaceMap_square U W i hi) n ≫
      ((relativeHomologyHomeomorphIso f W {z | z.2 ≠ 0} hf n).hom ≫
        productPairProjection (B := B) ({0}ᶜ : Set V) n) =
      (relativeHomologyHomeomorphIso e U {z | z.2 ≠ 0} he n).hom ≫
        productPairProjection (B := A) ({0}ᶜ : Set V) n := by
  simp only [relativeHomologyHomeomorphIso_hom]
  unfold productPairProjection
  erw [← Category.assoc, relativeHomologyMap_comp, relativeHomologyMap_comp,
    relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  ext x : 1
  exact hcoords x

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

/-- The fiber inclusion is split injective over ANY base containing that point. -/
theorem productPairFiberMap_projection (b : B) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n ≫ productPairProjection W n = 𝟙 _ := by
  unfold productPairFiberMap productPairProjection
  erw [relativeHomologyMap_comp, ← relativeHomologyMap_id (subspaceInclusion W) n]
  apply relativeHomologyMap_congr_ambient
  rfl

/-- Over a contractible base the actual inclusion is the inverse normalization. -/
theorem productPairFiberMap_eq_inv [ContractibleSpace B] (b : B) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n = (productPairProjectionIso (B := B) W n).inv := by
  have := productPairProjection_isIso (B := B) W n
  apply (cancel_mono (productPairProjection (B := B) W n)).mp
  rw [productPairFiberMap_projection]
  exact (productPairProjectionIso (B := B) W n).inv_hom_id.symm

theorem productPairFiberMap_eq [ContractibleSpace B] (b c : B) (W : Set V) (n : ℕ) :
    productPairFiberMap b W n = productPairFiberMap c W n := by
  rw [productPairFiberMap_eq_inv, productPairFiberMap_eq_inv]

end

open CategoryTheory ContinuousMap
open scoped unitInterval
section
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homotopy that carries the removed subspace into the removed subspace
at EVERY time gives equal maps on relative singular homology. The proof uses
the actual cylinder projection and its two equal inverse inclusions. -/
theorem relativeHomologyMap_homotopy (U : Set X) (V : Set Y)
    {f g : C(X,Y)} (hf : Set.MapsTo f U V) (hg : Set.MapsTo g U V)
    (H : Homotopy f g) (hH : ∀ t : I, ∀ x ∈ U, H (t,x) ∈ V) (n : ℕ) :
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
      (subspaceMap U V f hf) (TopCat.ofHom f) (by rfl) n =
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
      (subspaceMap U V g hg) (TopCat.ofHom g) (by rfl) n := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let h := relativeHomologyMap (subspaceInclusion {z : I × X | z.2 ∈ U})
    (subspaceInclusion V)
    (subspaceMap _ _ H.toContinuousMap (fun z hz => hH z.1 z.2 hz))
    (TopCat.ofHom H.toContinuousMap) (by rfl) n
  have endpoint (t : I) (k : C(X,Y)) (hk : Set.MapsTo k U V)
      (he : ∀ x, H (t,x) = k x) :
      productPairFiberMap t U n ≫ h =
        relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
          (subspaceMap U V k hk) (TopCat.ofHom k) (by rfl) n := by
    unfold productPairFiberMap
    change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
    erw [relativeHomologyMap_comp]
    apply relativeHomologyMap_congr_ambient
    ext x : 1
    exact he x
  rw [← endpoint 0 f hf (H.apply_zero), ← endpoint 1 g hg (H.apply_one),
    productPairFiberMap_eq (0 : I) 1 U n]

end

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

/-- Every invertible complex diagonal change acts as the identity on actual
integral local relative homology, in every degree. -/
theorem complexDiagonalRelativeMap_eq_id (a : ι → ℂˣ) (n : ℕ) :
    complexDiagonalRelativeMap a n = 𝟙 _ := by
  have h := relativeHomologyMap_homotopy ({0}ᶜ : Set (ι → ℂ)) {0}ᶜ
    (complexDiagonalMap_nonzero a) (fun _ h => h)
    (complexDiagonalHomotopy a) (complexDiagonalHomotopy_nonzero a) n
  change complexDiagonalRelativeMap a n = _ at h
  rw [h, ← relativeHomologyMap_id (subspaceInclusion ({0}ᶜ : Set (ι → ℂ))) n]
  apply relativeHomologyMap_congr_ambient
  rfl

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_Connected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Connected-cover homology, degree-zero components, and degree-one generators. -/

section
open CategoryTheory Limits HomologicalComplex AlgebraicTopology Simplicial

/-- Points in the same path component give equal integral H₀ classes. -/
theorem pointHomology_eq_of_joined (X : TopCat.{0}) {x y : X} (h : Joined x y) :
    pointHomology X x = pointHomology X y := by
  apply (cancel_mono (pointComponentIso X).hom).mp
  rw [pointHomology_component, pointHomology_component]
  have h' := congrArg TopCat.zerothHomotopyEquiv (ZerothHomotopy.sound h.somePath)
  exact congrArg (Sigma.ι _) h'

/-- All actual H₀ classes are determined by their values on point classes. -/
theorem pointHomology_hom_ext (X : TopCat.{0}) {T : ModuleCat.{0} ℤ}
    {f g : (integralSingularHomology 0).obj X ⟶ T}
    (h : ∀ x, pointHomology X x ≫ f = pointHomology X x ≫ g) : f = g := by
  let e := pointComponentIso X
  apply (cancel_epi e.inv).mp
  apply Sigma.hom_ext
  intro c
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective c
  obtain ⟨x, rfl⟩ := TopCat.toSSetObj₀Equiv.symm.surjective s
  have hp : Sigma.ι _ (SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm x)) ≫ e.inv =
      pointHomology X x := by
    rw [← pointHomology_component, Category.assoc, e.hom_inv_id]
    exact Category.comp_id _
  simpa only [← Category.assoc, hp] using h x

/-- For a space with exactly these two path components, their two point
classes span all integral H₀, with canonical integral coefficients. -/
theorem twoComponent_decomposition (X : TopCat.{0}) (a b : X) (hab : ¬ Joined a b)
    (hcover : ∀ x : X, Joined x a ∨ Joined x b) :
    componentCoefficient X a ≫ pointHomology X a +
      componentCoefficient X b ≫ pointHomology X b = 𝟙 _ := by
  apply pointHomology_hom_ext X
  intro x
  rcases hcover x with hx | hx
  · rw [pointHomology_eq_of_joined X hx]
    simp [Preadditive.comp_add, pointHomology_coefficient_other_assoc X a b hab]
  · rw [pointHomology_eq_of_joined X hx]
    have hba : ¬ Joined b a := fun h => hab h.symm
    simp [Preadditive.comp_add, pointHomology_coefficient_other_assoc X b a hba]

theorem twoComponent_decomposition_apply (X : TopCat.{0}) (a b : X) (hab : ¬ Joined a b)
    (hcover : ∀ x : X, Joined x a ∨ Joined x b)
    (z : (integralSingularHomology 0).obj X) :
    pointHomology X a (componentCoefficient X a z) +
      pointHomology X b (componentCoefficient X b z) = z :=
  ConcreteCategory.congr_hom (twoComponent_decomposition X a b hab hcover) z

end

section
open CategoryTheory Limits HomologicalComplex

section

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- A difference of two point classes in the intersection is killed by
both inclusion maps when both cover members are path connected. -/
theorem pointDifference_mayerVietoris_zero [PathConnectedSpace U] [PathConnectedSpace V]
    (a b : ↥(U ∩ V)) :
    (pointHomology (TopCat.of ↥(U ∩ V)) a - pointHomology (TopCat.of ↥(U ∩ V)) b) ≫
      homologyMap (smallMayerVietorisSequence U V).f 0 = 0 := by
  let c := pointHomology (TopCat.of ↥(U ∩ V)) a - pointHomology (TopCat.of ↥(U ∩ V)) b
  apply homology_biprod_detect_zero 0
  · erw [Category.assoc, ← homologyMap_comp]
    have hf : (smallMayerVietorisSequence U V).f ≫ biprod.fst =
        integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) :=
      biprod.lift_fst _ _
    rw [hf]
    change c ≫ (integralSingularHomology 0).map _ = _
    simp only [c, Preadditive.sub_comp, pointHomology_map]
    exact sub_eq_zero.mpr (pointHomology_eq_of_joined _ (PathConnectedSpace.joined _ _))
  · erw [Category.assoc, ← homologyMap_comp]
    have hf : (smallMayerVietorisSequence U V).f ≫ biprod.snd =
        -integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V)) :=
      biprod.lift_snd _ _
    erw [hf, homologyMap_neg, Preadditive.comp_neg]
    change -(c ≫ (integralSingularHomology 0).map _) = _
    simp only [c, Preadditive.sub_comp, pointHomology_map]
    rw [pointHomology_eq_of_joined _ (PathConnectedSpace.joined _ _), sub_self, neg_zero]
    rfl

end

section
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The two intersection coefficients sum to the augmentation after inclusion. -/
theorem twoComponent_inclusion_augmentation (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b) :
    componentCoefficient (TopCat.of ↥(U ∩ V)) a + componentCoefficient (TopCat.of ↥(U ∩ V)) b =
      (integralSingularHomology 0).map
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) ≫
        pointAugmentation (TopCat.of U) := by
  apply pointHomology_hom_ext
  intro x
  rcases hcover x with hx | hx
  · rw [pointHomology_eq_of_joined _ hx]
    simp [Preadditive.comp_add, pointHomology_coefficient_other (TopCat.of ↥(U ∩ V)) a b hab]
  · rw [pointHomology_eq_of_joined _ hx]
    have hba : ¬ Joined b a := fun h => hab h.symm
    simp [Preadditive.comp_add, pointHomology_coefficient_other (TopCat.of ↥(U ∩ V)) b a hba]

/-- Elements killed by the intersection-to-sum map have opposite coefficients. -/
theorem twoComponent_mayerVietoris_kernel (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b)
    (z : (integralSingularHomology 0).obj (TopCat.of ↥(U ∩ V)))
    (hz : homologyMap (smallMayerVietorisSequence U V).f 0 z = 0) :
    componentCoefficient (TopCat.of ↥(U ∩ V)) a z +
      componentCoefficient (TopCat.of ↥(U ∩ V)) b z = 0 := by
  have hf : homologyMap (smallMayerVietorisSequence U V).f 0 ≫ homologyMap biprod.fst 0 =
      (integralSingularHomology 0).map
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) := by
    erw [← homologyMap_comp]
    congr 1
    exact biprod.lift_fst _ _
  have hz' : (integralSingularHomology 0).map
      (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) z = 0 := by
    erw [← hf, ModuleCat.comp_apply]
    erw [hz]
    exact map_zero _
  have h := ConcreteCategory.congr_hom (twoComponent_inclusion_augmentation U V a b hab hcover) z
  change componentCoefficient (TopCat.of ↥(U ∩ V)) a z +
      componentCoefficient (TopCat.of ↥(U ∩ V)) b z =
      pointAugmentation (TopCat.of U)
        ((integralSingularHomology 0).map
          (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) z) at h
  erw [hz', map_zero] at h
  exact h

/-- The coefficient of the first intersection component after the actual
Mayer–Vietoris boundary. This fixes an integral sign convention. -/
def smallMayerVietorisOneCoordinate (a : ↥(U ∩ V)) :
    (smallSingularChains U V).homology 1 ⟶ ModuleCat.of ℤ ℤ :=
  smallMayerVietorisBoundary U V 0 ≫ componentCoefficient (TopCat.of ↥(U ∩ V)) a

/-- Exact integral H₁ calculation for two contractible sets whose intersection
has exactly two path components. No homology or normalization premise. -/
theorem smallMayerVietorisOneCoordinate_bijective [ContractibleSpace U] [ContractibleSpace V]
    (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b) :
    Function.Bijective (smallMayerVietorisOneCoordinate U V a) := by
  let δ := smallMayerVietorisBoundary U V 0
  let : Mono δ := (smallMayerVietorisSequence_shortExact U V).mono_δ 1 0 rfl
    (smallMayerVietoris_sum_isZero U V 1 (by decide))
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    change componentCoefficient (TopCat.of ↥(U ∩ V)) a (δ z) = 0 at hz
    have hk : homologyMap (smallMayerVietorisSequence U V).f 0 (δ z) = 0 :=
      ConcreteCategory.congr_hom
        ((smallMayerVietorisSequence_shortExact U V).δ_comp 1 0 rfl) z
    have hsum := twoComponent_mayerVietoris_kernel U V a b hab hcover (δ z) hk
    rw [hz, zero_add] at hsum
    have hd := twoComponent_decomposition_apply _ a b hab hcover (δ z)
    rw [hz, hsum, map_zero, map_zero, add_zero] at hd
    exact (ModuleCat.mono_iff_injective δ).mp inferInstance
      (hd.symm.trans δ.hom.map_zero.symm)
  · intro k
    let c := pointHomology (TopCat.of ↥(U ∩ V)) a - pointHomology (TopCat.of ↥(U ∩ V)) b
    have hk : c k ∈ LinearMap.ker (homologyMap (smallMayerVietorisSequence U V).f 0).hom := by
      change homologyMap (smallMayerVietorisSequence U V).f 0 (c k) = 0
      exact ConcreteCategory.congr_hom (pointDifference_mayerVietoris_zero U V a b) k
    rw [← (smallMayerVietoris_exact_at_intersection U V 0).moduleCat_range_eq_ker] at hk
    obtain ⟨z, hz⟩ := hk
    refine ⟨z, ?_⟩
    change componentCoefficient (TopCat.of ↥(U ∩ V)) a (δ z) = k
    change δ z = c k at hz
    rw [hz]
    have hba : ¬ Joined b a := fun h => hab h.symm
    have he : c ≫ componentCoefficient (TopCat.of ↥(U ∩ V)) a = 𝟙 _ := by
      simp [c, Preadditive.sub_comp, pointHomology_coefficient_other (TopCat.of ↥(U ∩ V)) b a hba]
    exact ConcreteCategory.congr_hom he k

def smallMayerVietorisOneIso [ContractibleSpace U] [ContractibleSpace V]
    (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b) :
    (smallSingularChains U V).homology 1 ≅ ModuleCat.of ℤ ℤ := by
  haveI := (ConcreteCategory.isIso_iff_bijective (smallMayerVietorisOneCoordinate U V a)).mpr
    (smallMayerVietorisOneCoordinate_bijective U V a b hab hcover)
  exact asIso (smallMayerVietorisOneCoordinate U V a)

/-- Full integral H₁ with the sign fixed by the ordered two intersection components. -/
def openCoverMayerVietorisOneIso [ContractibleSpace U] [ContractibleSpace V]
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (a b : ↥(U ∩ V)) (hab : ¬ Joined a b)
    (hcover : ∀ x : ↥(U ∩ V), Joined x a ∨ Joined x b) :
    (integralSingularHomology 1).obj (TopCat.of X) ≅ ModuleCat.of ℤ ℤ :=
  (openCoverSmallHomologyIso U V hU hV hUV 1).symm ≪≫
    smallMayerVietorisOneIso U V a b hab hcover

end

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Suspension homology and integral top generators of spheres. -/

section
open CategoryTheory ContinuousMap

/-- Relative homology at the origin, in degrees at least two, is identified
with the preceding integral sphere homology. No sphere group calculation is assumed. -/
def localVectorSphereHomologyIso (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (hn : n ≠ 0) :
    relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set V)) (n+1) ≅
      (integralSingularHomology n).obj (TopCat.of (Metric.sphere (0 : V) 1)) :=
  puncturedVectorBoundaryIso V n hn ≪≫
    integralHomologyHomotopyIso (puncturedVectorSphereHomotopyEquiv V) n

open ComplexGrassmann

end

section
open CategoryTheory Metric

section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual integral homology suspension isomorphism for a unit sphere,
obtained from its pole cover and the actual equator. -/
def sphereEquatorHomologyIso (v : sphere (0 : E) 1) (n : ℕ) (hn : n ≠ 0) :
    (integralSingularHomology (n+1)).obj (TopCat.of (sphere (0 : E) 1)) ≅
      (integralSingularHomology n).obj (TopCat.of (sphere (0 : (ℝ ∙ (v : E))ᗮ) 1)) := by
  letI := spherePole_contractible v
  letI := spherePole_contractible (-v)
  obtain ⟨hU, hV, hUV⟩ := sphere_poles_open_cover v
  exact openCoverMayerVietorisBoundaryIso _ _ hU hV hUV n hn ≪≫
    integralHomologyHomotopyIso (spherePoleOverlapHomotopyEquiv v) n

/-- Degree recursion to a sphere in one less real dimension. The base H₁
calculation is not included in this statement. -/
def sphereEuclideanHomologyStep (d : ℕ) [Fact (Module.finrank ℝ E = d+1)]
    (v : sphere (0 : E) 1) (n : ℕ) (hn : n ≠ 0) :
    (integralSingularHomology (n+1)).obj (TopCat.of (sphere (0 : E) 1)) ≅
      (integralSingularHomology n).obj (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  sphereEquatorHomologyIso v n hn ≪≫
    (integralSingularHomology n).mapIso (TopCat.isoOfHomeo (sphereEquatorEuclideanHomeomorph d v))

end

/-- Integral H₁ of a plane sphere, normalized by the ordered negative/positive
components of its chosen stereographic overlap. -/
def planeSphereHomologyOneIso {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 1+1)]
    (v : sphere (0 : E) 1) :
    (integralSingularHomology 1).obj (TopCat.of (sphere (0 : E) 1)) ≅ ModuleCat.of ℤ ℤ := by
  letI := spherePole_contractible v
  letI := spherePole_contractible (-v)
  obtain ⟨hU, hV, hUV⟩ := sphere_poles_open_cover v
  let e := spherePlaneOverlapRealHomeomorph v
  let a : ({0}ᶜ : Set ℝ) := ⟨-1, by simp⟩
  let b : ({0}ᶜ : Set ℝ) := ⟨1, by simp⟩
  apply openCoverMayerVietorisOneIso _ _ hU hV hUV (e.symm a) (e.symm b)
  · intro h
    have hh := h.map e.continuous
    simp only [e.apply_symm_apply] at hh
    exact puncturedReal_not_joined hh
  · intro x
    rcases puncturedReal_two_components (e x) with hx | hx
    · left
      simpa only [e.symm_apply_apply] using hx.map e.symm.continuous
    · right
      simpa only [e.symm_apply_apply] using hx.map e.symm.continuous

/-- The full top integral homology calculation for every positive-dimensional
Euclidean sphere. The recursive pole charts and ordered H₀ components fix a sign. -/
def euclideanSphereTopHomologyIso : (n : ℕ) →
    (integralSingularHomology (n+1)).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n+2))) 1)) ≅ ModuleCat.of ℤ ℤ
  | 0 => by
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1+1) := ⟨by simp⟩
      exact planeSphereHomologyOneIso (euclideanSpherePole 1)
  | n+1 => by
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1+2))) = (n+2)+1) := ⟨by simp⟩
      exact sphereEuclideanHomologyStep (n+2) (euclideanSpherePole (n+2)) (n+1)
        (Nat.succ_ne_zero n) ≪≫ euclideanSphereTopHomologyIso n

end

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_ProjectiveLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Nonzero local classes and local homology of projective spaces and products. -/

section
open CategoryTheory Metric
open ComplexGrassmann

/-- Top integral sphere homology for any finite-dimensional real normed space,
using a chosen linear coordinate system and the recursive sphere normalization. -/
def finiteDimensionalSphereTopHomologyIso (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hd : Module.finrank ℝ E = n+2) :
    (integralSingularHomology (n+1)).obj (TopCat.of (sphere (0 : E) 1)) ≅ ModuleCat.of ℤ ℤ :=
  integralHomologyHomotopyIso
    (continuousLinearEquivSphereHomotopyEquiv
      (ContinuousLinearEquiv.ofFinrankEq (by simpa using hd) :
        E ≃L[ℝ] EuclideanSpace ℝ (Fin (n+2)))) (n+1) ≪≫
    euclideanSphereTopHomologyIso n

end

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
-- module Solutions.OAIQ4_Kq.IntegralHomology_ProductCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair fiber normalization, punctured products, and overlap generators. -/

section
open CategoryTheory Limits Set
variable {E V : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
/-- A convex base, including the empty case, has no relative bundle
homology below the fiber dimension. -/
theorem convexBaseProductPair_below_isZero (C : Set E) (hC : Convex ℝ C)
    (hd : 2 ≤ Module.finrank ℝ V) (n : ℕ) (hn : n < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' {z : E × V | z.2 ≠ 0} : Set {z : E × V | z.1 ∈ C})) n) := by
  by_cases hc : C.Nonempty
  · let : ContractibleSpace C := hC.contractibleSpace hc
    exact ((localVectorHomology_isZero V hd n (by omega)).of_iso
      (productPairProjectionIso (B := C) ({0}ᶜ : Set V) n)).of_iso
        (relativeHomologyHomeomorphIso (firstCoordinateSubspaceHomeomorph C)
          _ {z : C × V | z.2 ≠ 0} (fun _ => Iff.rfl) n)
  · have : IsEmpty {z : E × V | z.1 ∈ C} :=
      ⟨fun z => hc ⟨z.1.1,z.2⟩⟩
    exact relativeHomology_isZero_empty _ n

open ComplexGrassmann

end

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

theorem productPairChartFiberMap_coordinates (C : Set B) (b : C) (W : Set V) (n : ℕ) :
    productPairChartFiberMap C b W n ≫ (productPairBaseSubsetIso C W n).hom =
      productPairFiberMap b W n := by
  unfold productPairChartFiberMap productPairBaseSubsetIso productPairFiberMap
  erw [relativeHomologyHomeomorphIso_hom]
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

theorem productPairChartFiberMap_isIso (C : Set B) [ContractibleSpace C]
    (b : C) (W : Set V) (n : ℕ) : IsIso (productPairChartFiberMap C b W n) := by
  have : IsIso (productPairFiberMap b W n) := by
    rw [productPairFiberMap_eq_inv]
    infer_instance
  have : IsIso (productPairChartFiberMap C b W n ≫ (productPairBaseSubsetIso C W n).hom) := by
    rw [productPairChartFiberMap_coordinates]
    infer_instance
  exact IsIso.of_isIso_comp_right (productPairChartFiberMap C b W n)
    (productPairBaseSubsetIso C W n).hom

/-- Inclusion of a chart fiber is literally the same global fiber inclusion. -/
theorem productPairChartFiberMap_inclusion (C : Set B) (b : C) (W : Set V) (n : ℕ) :
    productPairChartFiberMap C b W n ≫
      restrictedPairToAmbientHomologyMap {z : B × V | z.1 ∈ C} {z | z.2 ∈ W} n =
    productPairFiberMap b.1 W n := by
  unfold productPairChartFiberMap productPairFiberMap
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n = _
  erw [relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

end

open Bundle Topology CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_AffineAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Affine-avoidance covers and convex product-pair homology. -/

section
open Set
variable {E F J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype J]

omit [Fintype J] in
theorem affineAvoidanceCharts_cover (l : J → E →L[ℝ] F) (c : J → F) :
    (⋃ s : J → Fin (Module.finrank ℝ F) × Bool, affineAvoidanceChart l c s) =
      affineAvoidanceSet l c := by
  ext x
  constructor
  · intro hx
    obtain ⟨s,hs⟩ := mem_iUnion.mp hx
    change ∀ j, l j x + c j ≠ 0
    intro j
    have hm : l j x + c j ∈ ⋃ i, signedCoordinateHalfspace i :=
      mem_iUnion.mpr ⟨s j,mem_iInter.mp hs j⟩
    rw [signedCoordinateHalfspaces_cover] at hm
    exact hm
  · intro hx
    have he : ∀ j, ∃ i : Fin (Module.finrank ℝ F) × Bool,
        l j x + c j ∈ signedCoordinateHalfspace i := by
      intro j
      rw [← mem_iUnion, signedCoordinateHalfspaces_cover]
      exact hx j
    choose s hs using he
    exact mem_iUnion.mpr ⟨s,mem_iInter.mpr hs⟩

omit [Fintype J] in
theorem affineAvoidanceChart_subset (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) :
    affineAvoidanceChart l c s ⊆ affineAvoidanceSet l c := by
  rw [← affineAvoidanceCharts_cover]
  exact subset_iUnion _ s

end

section
open CategoryTheory Limits Set
variable {E V J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
/-- A nonempty convex subset remains contractible when viewed inside a
larger base subset, with its actual iterated subspace topology. -/
theorem convexRestrictedBase_contractible (D C : Set E) (hCD : C ⊆ D)
    (hc : Convex ℝ C) (hne : (Subtype.val ⁻¹' C : Set D).Nonempty) :
    ContractibleSpace (Subtype.val ⁻¹' C : Set D) := by
  have : ContractibleSpace C := hc.contractibleSpace ⟨hne.choose.val,hne.choose_spec⟩
  exact (subspaceSubsetHomeomorph C D hCD).contractibleSpace

omit [FiniteDimensional ℝ E] in
/-- Every nonempty intersection of convex base charts has the required
lower relative vanishing. Empty intersections have zero groups as well. -/
theorem convexCover_product_intersection_below_isZero
    (D : Set E) (S : Finset J) (C : J → Set E)
    (hsub : ∀ i ∈ S, C i ⊆ D) (hconv : ∀ i ∈ S, Convex ℝ (C i))
    (T : Finset J) (ht : T.Nonempty) (hts : T ⊆ S)
    (hv : 2 ≤ Module.finrank ℝ V) (q : ℕ) (hq : q < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology
      (subspaceInclusion {z : (⋂ i ∈ T, (Subtype.val ⁻¹' C i : Set D)) × V |
        z.2 ≠ 0}) q) := by
  let W : Set E := ⋂ i ∈ T, C i
  have hW : W ⊆ D := by
    obtain ⟨i,hi⟩ := ht
    intro x hx
    exact hsub i (hts hi) (mem_iInter.mp (mem_iInter.mp hx i) hi)
  have hcv : Convex ℝ W :=
    convex_iInter (fun i => convex_iInter (fun hi => hconv i (hts hi)))
  have heq : (⋂ i ∈ T, (Subtype.val ⁻¹' C i : Set D)) = Subtype.val ⁻¹' W := by
    ext x; simp [W]
  rw [heq]
  by_cases hne : (Subtype.val ⁻¹' W : Set D).Nonempty
  · have := convexRestrictedBase_contractible D W hW hcv hne
    exact (localVectorHomology_isZero V hv q (by omega)).of_iso
      (productPairProjectionIso (B := (Subtype.val ⁻¹' W : Set D)) ({0}ᶜ : Set V) q)
  · have : IsEmpty ((Subtype.val ⁻¹' W : Set D) × V) :=
      ⟨fun z => hne ⟨z.1.val,z.1.property⟩⟩
    exact relativeHomology_isZero_empty _ q

omit [FiniteDimensional ℝ E] in
/-- Relative homology below fiber dimension vanishes over any finite
union of open convex base sets. Neither connectivity nor contractibility
of that union is asserted. -/
theorem convexOpenUnion_product_below_isZero
    (S : Finset J) (C : J → Set E)
    (hopen : ∀ i ∈ S, IsOpen (C i)) (hconv : ∀ i ∈ S, Convex ℝ (C i))
    (hv : 2 ≤ Module.finrank ℝ V) (q : ℕ) (hq : q < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      {z : (⋃ i ∈ S, C i) × V | z.2 ≠ 0}) q) := by
  let U : J → Set (E × V) := fun i => {z | z.1 ∈ C i}
  let A : Set (E × V) := {z | z.2 ≠ 0}
  have hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ k < Module.finrank ℝ V,
      IsZero (relativeSingularHomology
        (subspaceInclusion (Subtype.val ⁻¹' A : Set ↥(⋂ i ∈ T, U i))) k) := by
    intro T _ hts k hk
    have he : (⋂ i ∈ T, U i) = {z : E × V | z.1 ∈ ⋂ i ∈ T, C i} := by
      ext z; simp [U]
    rw [he]
    exact convexBaseProductPair_below_isZero _
      (convex_iInter (fun i => convex_iInter (fun hi => hconv i (hts hi)))) hv k hk
  have hz := finiteRelativeOpenUnion_below_isZero S U A
    (fun i hi => (hopen i hi).preimage continuous_fst) (Module.finrank ℝ V) hinter q hq
  have he : (⋃ i ∈ S, U i) = {z : E × V | z.1 ∈ ⋃ i ∈ S, C i} := by
    ext z; simp [U]
  rw [he] at hz
  exact hz.of_iso (productPairBaseSubsetIso (⋃ i ∈ S, C i) ({0}ᶜ : Set V) q).symm

end

open CategoryTheory Limits Set
section
variable {E F V J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Fintype J]

omit [FiniteDimensional ℝ E] in
/-- Lower relative vanishing over a finite affine-zero complement,
proved by the explicit convex cover. All kernels may intersect. -/
theorem affineAvoidance_product_below_isZero (l : J → E →L[ℝ] F) (c : J → F)
    (hv : 2 ≤ Module.finrank ℝ V) (q : ℕ) (hq : q < Module.finrank ℝ V) :
    IsZero (relativeSingularHomology (subspaceInclusion
      {z : affineAvoidanceSet l c × V | z.2 ≠ 0}) q) := by
  classical
  have h := convexOpenUnion_product_below_isZero
    (Finset.univ : Finset (J → Fin (Module.finrank ℝ F) × Bool)) (affineAvoidanceChart l c)
    (fun s _ => affineAvoidanceChart_open l c s)
    (fun s _ => affineAvoidanceChart_convex l c s) hv q hq
  have he : (⋃ i ∈ (Finset.univ : Finset (J → Fin (Module.finrank ℝ F) × Bool)),
      affineAvoidanceChart l c i) = affineAvoidanceSet l c := by
    simpa only [Finset.mem_univ, iUnion_true] using affineAvoidanceCharts_cover l c
  rw [he] at h
  exact h

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_LineNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Integral line normalization and finite-cover diagonal comparison. -/

section
open CategoryTheory Limits Set
variable {B ι J : Type} [TopologicalSpace B]

/-- A finite contractible cover detects the normalization of a varying
complex diagonal coordinate change. The whole base need not be contractible
or connected; the lower intersection groups are the actual relative groups. -/
theorem productPairCoordinateMap_eq_projection_of_finite_cover
    (S : Finset J) (U : J → Set B)
    (hopen : ∀ i ∈ S, IsOpen (U i)) (hcover : (⋃ i ∈ S, U i) = Set.univ)
    (hchart : ∀ i ∈ S, (U i).Nonempty → ContractibleSpace (U i))
    (n : ℕ)
    (hinter : ∀ T : Finset J, T.Nonempty → T ⊆ S → ∀ q < n+1,
      IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ T, U i) × (ι → ℂ) | z.2 ≠ 0}) q))
    (f : C(B × (ι → ℂ),(ι → ℂ))) (hf : ∀ z, z.2 ≠ 0 → f z ≠ 0)
    (a : B → ι → ℂˣ) (he : ∀ b v, f (b,v) = complexDiagonalMap (a b) v) :
    productPairCoordinateMap f hf (n+1) =
      productPairProjection (B := B) ({0}ᶜ : Set (ι → ℂ)) (n+1) := by
  let C : J → Set (B × (ι → ℂ)) := fun i => {z | z.1 ∈ U i}
  let A : Set (B × (ι → ℂ)) := {z | z.2 ∈ ({0}ᶜ : Set (ι → ℂ))}
  have hC : (⋃ i ∈ S, C i) = Set.univ := by
    ext z
    have hb : z.1 ∈ ⋃ i ∈ S, U i := by rw [hcover]; trivial
    simpa only [mem_iUnion, C, mem_ofPred_eq, mem_univ, iff_true] using hb
  refine finiteRelativeOpenCover_hom_ext S C A
    (fun i hi => (hopen i hi).preimage continuous_fst) hC n ?_ _ _ ?_
  · intro T ht hts q hq
    have heC : (⋂ i ∈ T, C i) = {point : B × (ι → ℂ) | point.1 ∈ ⋂ i ∈ T, U i} := by
      ext point
      simp [C]
    rw [heC]
    exact (hinter T ht hts q hq).of_iso
      (productPairBaseSubsetIso (⋂ i ∈ T, U i) ({0}ᶜ : Set (ι → ℂ)) q)
  · intro i hi
    by_cases hne : (U i).Nonempty
    · let : ContractibleSpace (U i) := hchart i hi hne
      let b : U i := ⟨hne.choose,hne.choose_spec⟩
      have := productPairChartFiberMap_isIso (U i) b ({0}ᶜ : Set (ι → ℂ)) (n+1)
      apply (cancel_epi (productPairChartFiberMap (U i) b ({0}ᶜ : Set (ι → ℂ)) (n+1))).mp
      have hc : productPairFiberMap b.1 ({0}ᶜ : Set (ι → ℂ)) (n+1) ≫
          productPairCoordinateMap f hf (n+1) = complexDiagonalRelativeMap (a b.1) (n+1) := by
        unfold productPairFiberMap productPairCoordinateMap complexDiagonalRelativeMap
        erw [relativeHomologyMap_comp]
        apply relativeHomologyMap_congr_ambient
        ext v : 1
        exact he b.1 v
      have hincl := productPairChartFiberMap_inclusion (U i) b ({0}ᶜ : Set (ι → ℂ)) (n+1)
      have hc' := (congrArg (fun g => g ≫ productPairCoordinateMap f hf (n+1)) hincl).trans
        (hc.trans (complexDiagonalRelativeMap_eq_id (a b.1) (n+1)))
      have hp' := (congrArg (fun g => g ≫ productPairProjection (B := B) ({0}ᶜ : Set (ι → ℂ))
        (n+1)) hincl).trans (productPairFiberMap_projection b.1 ({0}ᶜ : Set (ι → ℂ)) (n+1))
      exact (Category.assoc _ _ _).symm.trans
        (hc'.trans (hp'.symm.trans (Category.assoc _ _ _)))
    · have : IsEmpty (C i) := ⟨fun z => hne ⟨z.1.1,z.2⟩⟩
      exact (relativeHomology_isZero_empty (Subtype.val ⁻¹' A : Set (C i)) (n+1)).eq_of_src _ _

end

open Bundle Topology CategoryTheory Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Twisted
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted hyperplane bundles, zeros, graph coordinates, and frame sections. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedOldBase : C(ProjectiveProduct (twistedProjectiveDimensions K h),ProjectiveProduct K) :=
  ⟨fun P i => P (some i),continuous_pi (fun i => continuous_apply (some i))⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_FrameNormalization
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

variable (w : ∀ s a, (C s).Fiber a) (hwn : ∀ s a, w s a ≠ 0)
  (hwc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (w s a)))

theorem finiteLineFrame_transition (a : A) (z : S → ℂ) :
    finiteLineFrameEquiv C w hwn a ((finiteLineFrameEquiv C v hn a).symm z) =
      complexDiagonalMap (fun s => complexLineCoordinateUnit
        (lineFrameEquiv (C s) (v s) (hn s) a) (lineFrameEquiv (C s) (w s) (hwn s) a)) z := by
  funext s
  exact complexLineCoordinate_change
    (lineFrameEquiv (C s) (v s) (hn s) a) (lineFrameEquiv (C s) (w s) (hwn s) a) (z s)

/-- Normalization of the actual finite sum of actual line cores is independent
of the chosen continuous nonvanishing line frames on a finite contractible
cover with the stated lower intersection vanishing. No global contractibility
or connectedness hypothesis is required. -/
theorem finiteLineFrameNormalization_eq_of_finite_cover
    {J : Type} (T : Finset J) (U : J → Set A)
    (hopen : ∀ i ∈ T, IsOpen (U i)) (hcover : (⋃ i ∈ T, U i) = Set.univ)
    (hchart : ∀ i ∈ T, (U i).Nonempty → ContractibleSpace (U i))
    (n : ℕ)
    (hinter : ∀ I : Finset J, I.Nonempty → I ⊆ T → ∀ q < n+1,
      Limits.IsZero (relativeSingularHomology
        (subspaceInclusion {z : (⋂ i ∈ I, U i) × (S → ℂ) | z.2 ≠ 0}) q)) :
    finiteLineFrameNormalization C v hn hc (n+1) =
      finiteLineFrameNormalization C w hwn hwc (n+1) := by
  let ev := finiteLineFrameHomeomorph C v hn hc
  let ew := finiteLineFrameHomeomorph C w hwn hwc
  let f : C(A × (S → ℂ),(S → ℂ)) :=
    ⟨fun z => (ew (ev.symm z)).2, continuous_snd.comp (ew.continuous.comp ev.symm.continuous)⟩
  have hf : ∀ z : A × (S → ℂ), z.2 ≠ 0 → f z ≠ 0 := by
    intro z hz he
    have hw : (ev.symm z).2 = 0 :=
      (finiteLineFrameHomeomorph_zero_iff C w hwn hwc _).mp he
    have hv := (finiteLineFrameHomeomorph_zero_iff C v hn hc (ev.symm z)).mpr hw
    change (ev (ev.symm z)).2 = 0 at hv
    rw [ev.apply_symm_apply] at hv
    exact hz hv
  let c : A → S → ℂˣ := fun a s => complexLineCoordinateUnit
    (lineFrameEquiv (C s) (v s) (hn s) a)
    (lineFrameEquiv (C s) (w s) (hwn s) a)
  have he : ∀ a z, f (a,z) = complexDiagonalMap (c a) z :=
    finiteLineFrame_transition C v hn w hwn
  have hnorm := productPairCoordinateMap_eq_projection_of_finite_cover
    T U hopen hcover hchart n hinter f hf c he
  have heq : finiteLineFrameNormalization C w hwn hwc (n+1) =
      (finiteLineFrameRelativeIso C v hn hc (n+1)).hom ≫
        productPairCoordinateMap f hf (n+1) := by
    unfold finiteLineFrameNormalization finiteLineFrameRelativeIso
    rw [relativeHomologyHomeomorphIso_hom, relativeHomologyHomeomorphIso_hom]
    unfold productPairProjection productPairCoordinateMap
    erw [relativeHomologyMap_comp, relativeHomologyMap_comp]
    apply relativeHomologyMap_congr_ambient
    ext z : 1
    change (ew z).2 = (ew (ev.symm (ev z))).2
    rw [ev.symm_apply_apply]
  rw [heq, hnorm]
  rfl

end

open Bundle Topology CategoryTheory Set
section
variable {E F J S : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype J] [Fintype S] {I : S → Type}

/-- On the complement of any finite family of affine zero sets, the two
normalizations of the ACTUAL finite sum of line cores coincide in
fiber degree. Contractibility, connectivity, transition degree and homology
vanishing are not premises: the finite convex cover supplies the comparison. -/
theorem affineAvoidance_finiteLineFrameNormalization_eq
    (l : J → E →L[ℝ] F) (c : J → F)
    (C : ∀ s, VectorBundleCore ℂ (affineAvoidanceSet l c) ℂ (I s))
    (v : ∀ s a, (C s).Fiber a) (hn : ∀ s a, v s a ≠ 0)
    (hc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (v s a)))
    (w : ∀ s a, (C s).Fiber a) (hwn : ∀ s a, w s a ≠ 0)
    (hwc : ∀ s, Continuous (fun a => TotalSpace.mk' ℂ a (w s a)))
    (hv : 2 ≤ Module.finrank ℝ (S → ℂ)) :
    finiteLineFrameNormalization C v hn hc (Module.finrank ℝ (S → ℂ)) =
      finiteLineFrameNormalization C w hwn hwc (Module.finrank ℝ (S → ℂ)) := by
  classical
  let I := J → Fin (Module.finrank ℝ F) × Bool
  let U : I → Set (affineAvoidanceSet l c) := fun s => Subtype.val ⁻¹' affineAvoidanceChart l c s
  have hcover : (⋃ s ∈ (Finset.univ : Finset I), U s) = Set.univ := by
    ext x
    have hx : x.val ∈ ⋃ s : I, affineAvoidanceChart l c s := by
      rw [affineAvoidanceCharts_cover]; exact x.property
    simpa only [U, mem_iUnion, Finset.mem_univ, exists_true_left,
      mem_preimage, mem_univ, iff_true] using hx
  let n := Module.finrank ℝ (S → ℂ) - 1
  have hdim : n+1 = Module.finrank ℝ (S → ℂ) := by dsimp [n]; omega
  have h := finiteLineFrameNormalization_eq_of_finite_cover C v hn hc w hwn hwc
    Finset.univ U
    (fun s _ => (affineAvoidanceChart_open l c s).preimage continuous_subtype_val) hcover
    (fun s _ hne => convexRestrictedBase_contractible _ _ (affineAvoidanceChart_subset l c s)
      (affineAvoidanceChart_convex l c s) hne) n
    (fun T ht hts q hq => convexCover_product_intersection_below_isZero
      (affineAvoidanceSet l c) Finset.univ (affineAvoidanceChart l c)
      (fun s _ => affineAvoidanceChart_subset l c s)
      (fun s _ => affineAvoidanceChart_convex l c s) T ht hts hv q (by omega))
  rwa [hdim] at h

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Normalization
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

theorem twistedCoordinateSpace_real_finrank :
    Module.finrank ℝ (TwistedHyperplaneSlot K h → ℂ) = 2*(h+∑ i, K i) := by
  rw [finrank_real_of_complex]
  simp [TwistedHyperplaneSlot, Fintype.card_sigma, Nat.mul_comm]

end Kaplansky

end

open Bundle Topology CategoryTheory Limits Set

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Retained
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

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Polynomials
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

/-- Norm approximation in the actual closed generated algebra by a
finite star polynomial. No density hypothesis is supplied by the caller. -/
theorem generated_exists_wordPolynomial (x : Fin N → A) (z : generatedAlgebra (Set.range x))
    {ε : ℝ} (hε : 0<ε) :
    ∃ p : StarWordPolynomial N, ‖evalStarWordPolynomial x p - (z : A)‖ < ε := by
  have hz : (z : A) ∈ closure (StarAlgebra.adjoin ℂ (Set.range x) : Set A) := z.property
  obtain ⟨w,hw,hd⟩ := Metric.mem_closure_iff.mp hz ε hε
  obtain ⟨p,rfl⟩ := starAdjoin_exists_wordPolynomial x hw
  refine ⟨p,?_⟩
  simpa only [dist_eq_norm,norm_sub_rev] using hd

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Infiniteness
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Proper infiniteness, isometry columns, and C-star matrix amplification. -/

open scoped ComplexOrder CStarAlgebra BigOperators
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

variable {m : ℕ}

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem properlyInfinite_map (f : A →⋆ₐ[ℂ] B) (hp : ProperlyInfinite A) :
    ProperlyInfinite B := by
  obtain ⟨s,t,hs,ht,hst⟩ := hp
  refine ⟨f s,f t,?_,?_,?_⟩
  · simpa only [map_mul,map_star,map_one] using congrArg f hs
  · simpa only [map_mul,map_star,map_one] using congrArg f ht
  · simpa only [map_mul,map_star,map_zero] using congrArg f hst

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Nonvanishing twisted section classes and the stable retained-bundle obstruction. -/

section
open Bundle Topology CategoryTheory Set
namespace Kaplansky
open ComplexGrassmann
theorem sectionProductNormalization
    {X Y A V : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace V] [Zero V]
    (U : Set X) (W : Set Y) (s : C(X,Y)) (hs : MapsTo s U W)
    (e : Y ≃ₜ A × V) (f : X ≃ₜ V)
    (he : ∀ y, y ∈ W ↔ (e y).2 ≠ 0) (hf : ∀ x, x ∈ U ↔ f x ∈ ({0}ᶜ : Set V))
    (hcoords : ∀ x, (e (s x)).2 = f x) (n : ℕ) :
    relativeHomologyMap (subspaceInclusion U) (subspaceInclusion W)
        (subspaceMap U W s hs) (TopCat.ofHom s) (subspaceMap_square U W s hs) n ≫
      ((relativeHomologyHomeomorphIso e W {z | z.2 ≠ 0} he n).hom ≫
        productPairProjection (B := A) ({0}ᶜ : Set V) n) =
      (relativeHomologyHomeomorphIso f U ({0}ᶜ : Set V) hf n).hom := by
  simp only [relativeHomologyHomeomorphIso_hom]
  unfold productPairProjection
  erw [← Category.assoc, relativeHomologyMap_comp, relativeHomologyMap_comp]
  exact relativeHomologyMap_congr_ambient _ _ _ _ _ _ _ _ (by
    ext x : 1
    exact hcoords x) n

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

theorem twistedProjectiveDimensions_sum :
    ∑ i, twistedProjectiveDimensions K h i = h+∑ i, K i := by
  rw [Fintype.sum_option]
  rfl

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Monoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ4_Kq.OrderedStates_Semigroup
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

def semigroupDifferenceClass (a : SemigroupDifference S) : SemigroupOrderedGroup S :=
  toAntisymmetrization (· ≤ ·) a

theorem semigroupDifferenceClass_le (a b : SemigroupDifference S) :
    semigroupDifferenceClass a ≤ semigroupDifferenceClass b ↔
      ∃ c : S, a.1+b.2+c ≤ b.1+a.2+c :=
  toAntisymmetrization_le_toAntisymmetrization_iff

instance instZeroSemigroupOrderedGroup : Zero (SemigroupOrderedGroup S) := ⟨semigroupDifferenceClass 0⟩

instance instAddSemigroupOrderedGroup : Add (SemigroupOrderedGroup S) where
  add := Quotient.map₂ (· + ·) (fun _ _ ha _ _ hb =>
    ⟨SemigroupDifference.add_le_add ha.1 hb.1,
      SemigroupDifference.add_le_add ha.2 hb.2⟩)

instance instNegSemigroupOrderedGroup : Neg (SemigroupOrderedGroup S) where
  neg := Quotient.map SemigroupDifference.flip (fun _ _ h =>
    ⟨SemigroupDifference.flip_le_flip h.2, SemigroupDifference.flip_le_flip h.1⟩)

@[simp] theorem semigroupDifferenceClass_add (a b : SemigroupDifference S) :
    semigroupDifferenceClass (a+b) = semigroupDifferenceClass a + semigroupDifferenceClass b := rfl

@[simp] theorem semigroupDifferenceClass_zero :
    semigroupDifferenceClass (0 : SemigroupDifference S) = 0 := rfl

@[simp] theorem semigroupDifferenceClass_flip (a : SemigroupDifference S) :
    semigroupDifferenceClass a.flip = -semigroupDifferenceClass a := rfl

instance instAddCommGroupSemigroupOrderedGroup : AddCommGroup (SemigroupOrderedGroup S) where
  add_assoc a b c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    exact congrArg semigroupDifferenceClass (add_assoc a b c)
  zero_add a := by
    induction a using Quotient.inductionOn with | h a =>
    exact congrArg semigroupDifferenceClass (zero_add a)
  add_zero a := by
    induction a using Quotient.inductionOn with | h a =>
    exact congrArg semigroupDifferenceClass (add_zero a)
  add_comm a b := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    exact congrArg semigroupDifferenceClass (add_comm a b)
  neg_add_cancel a := by
    induction a using Quotient.inductionOn with | h a =>
    apply Quotient.sound
    constructor
    · refine ⟨0, ?_⟩
      change a.2+a.1+0+0 ≤ 0+(a.1+a.2)+0
      simp [add_comm]
    · refine ⟨0, ?_⟩
      change 0+(a.1+a.2)+0 ≤ a.2+a.1+0+0
      simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instIsOrderedAddMonoidSemigroupOrderedGroup : IsOrderedAddMonoid (SemigroupOrderedGroup S) where
  add_le_add_left a b h c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    exact (semigroupDifferenceClass_le _ _).mpr
      (SemigroupDifference.add_le_add ((semigroupDifferenceClass_le _ _).mp h) (le_refl c))

end

section
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

theorem semigroupDifference_value_mono (f : S →+ G) (hf : Monotone f)
    {a b : SemigroupDifference S} (h : a ≤ b) :
    f a.1 - f a.2 ≤ f b.1 - f b.2 := by
  obtain ⟨c,hc⟩ := h
  have hh := hf hc
  simp only [map_add] at hh
  have hh' := (add_le_add_iff_right (f c)).mp hh
  exact sub_le_sub_iff.mpr hh'

/-- Every monotone additive map to an ordered group descends to the
ordered completion. This constructs the map; it does not postulate a state. -/
def semigroupOrderedGroupLift (f : S →+ G) (hf : Monotone f) : SemigroupOrderedGroup S →+ G where
  toFun := Quotient.lift (fun a : SemigroupDifference S => f a.1-f a.2)
    (fun _ _ h => le_antisymm (semigroupDifference_value_mono f hf h.1)
      (semigroupDifference_value_mono f hf h.2))
  map_zero' := by change f 0-f 0=0; simp
  map_add' a b := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    change f (a.1+b.1)-f (a.2+b.2) = (f a.1-f a.2)+(f b.1-f b.2)
    simp only [map_add]
    abel

@[simp] theorem semigroupOrderedGroupLift_apply (f : S →+ G) (hf : Monotone f) (a b : S) :
    semigroupOrderedGroupLift f hf (semigroupDifferenceClass (a,b)) = f a-f b := rfl

end

end Kaplansky

end

end OAI
end


