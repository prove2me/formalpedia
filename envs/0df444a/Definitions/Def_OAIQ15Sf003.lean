-- Prove2me | Definitions.Def_OAIQ15Sf003
-- name    : OAIQ15Sf003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:19:28.394685+00:00
-- url     : https://prove2.me/theorems/a97bbf37-41ef-49cc-9818-345545deea32
-- title:
--   Definitions bundle OAIQ15Sf003 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 333 declarations of OpenAI's Lean: 136 definitions, 7 instances and 190 theorems. The definitions and types are `OAI.Kaplansky.HilbertColumns`, `OAI.Kaplansky.MatrixPolynomialTermIndex`, `OAI.Kaplansky.QuasitraceCandidate`, `OAI.Kaplansky.StarWordPolynomial`, `OAI.Kaplansky.absoluteToRelative`, `OAI.Kaplansky.affineAvoidanceChart`, `OAI.Kaplansky.algebraStarLetter`, `OAI.Kaplansky.algebraStarWord`, `OAI.Kaplansky.applyWord`, `OAI.Kaplansky.bundleSectionHomotopy`, `OAI.Kaplansky.centeredChartHomeomorph`, `OAI.Kaplansky.chainCycle`, `OAI.Kaplansky.chainHomotopyOfComponents`, `OAI.Kaplansky.chainIterate`, `OAI.Kaplansky.chartBaseMap`, `OAI.Kaplansky.chartRelativeChainInclusion`, `OAI.Kaplansky.chartSmallRelativeChainsIso`, `OAI.Kaplansky.closedSubalgebraLE`, `OAI.Kaplansky.closedSubalgebraPreorder`, `OAI.Kaplansky.cokernelBiprodIso`, `OAI.Kaplansky.compactifiedNonzeroBundle`, `OAI.Kaplansky.complexDiagonalHomotopy`, `OAI.Kaplansky.complexDiagonalMap`, `OAI.Kaplansky.componentCoefficient`, `OAI.Kaplansky.continuousDimensionCutoff`, `OAI.Kaplansky.continuousLinearEquivPuncturedHomeomorph`, `OAI.Kaplansky.continuousLinearEquivSphereHomotopyEquiv`, `OAI.Kaplansky.contractibleRelativeBoundaryIso`, `OAI.Kaplansky.euclideanSpherePole`, `OAI.Kaplansky.euclideanSphereTopHomologyIso`, `OAI.Kaplansky.eventuallySmallChains`, `OAI.Kaplansky.finiteDimensionalSphereTopHomologyIso`, `OAI.Kaplansky.integralHomologyHomotopyIso`, `OAI.Kaplansky.integralSimplicialChains`, `OAI.Kaplansky.integralSingularChains`, `OAI.Kaplansky.integralSingularHomology`, `OAI.Kaplansky.linearIsometrySphereHomeomorph`, `OAI.Kaplansky.localVectorSphereHomologyIso`, `OAI.Kaplansky.openCoverMayerVietorisBoundaryIso`, `OAI.Kaplansky.openCoverMayerVietorisOneIso` and 96 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Twisted`, `ComplexBundle_Pullback`, `ComplexBundle_Sections`, `Cuntz_Content`, `Cuntz_Measure`, `IntegralHomology_AffineAvoidance`, `IntegralHomology_Connected`, `IntegralHomology_Equivalence`, `IntegralHomology_Excision`, `IntegralHomology_Product`, `IntegralHomology_ProductCover`, `IntegralHomology_ProjectiveLocal`, `IntegralHomology_Quotient`, `IntegralHomology_Relative`, `IntegralHomology_Sections`, `IntegralHomology_Simplex`, `IntegralHomology_SmallChains`, `IntegralHomology_SmallExcision`, `IntegralHomology_Smallness`, `IntegralHomology_Sphere`, `IntegralHomology_Subdivision`, `IntegralHomology_TupleChains`, `Kaplansky_BundlePolynomials`, `Kaplansky_Operators`, `Kaplansky_Polynomials`, `Kaplansky_Products`, `Kaplansky_Words`, `Quasitrace_Basic`, `Quasitrace_Compactness`.
--
--   **Imports.** It imports the published bundle `Def_KaplanskyStableFiniteness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ15Sf007` and `OAIQ15Sf008`; the proofs of `OAI_KaplanskyConsequences_simple_stable_tensor_reduction` and `OAI_KaplanskyConsequences_simple_stablyFinite_quotient`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Sections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Gluing, homotopy, and operations on vector bundle sections. -/

section
open Bundle Topology
namespace Kaplansky

section
variable {B V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace V E)]
  [FiberBundle V E] [VectorBundle ℂ V E]

/-- Addition over a varying base, with the actual total-space topology. -/
theorem continuous_bundle_add_over {X : Type*} [TopologicalSpace X]
    (b : X → B) (hb : Continuous b) (v w : ∀ x, E (b x))
    (hv : Continuous (fun x => TotalSpace.mk' V (b x) (v x)))
    (hw : Continuous (fun x => TotalSpace.mk' V (b x) (w x))) :
    Continuous (fun x => TotalSpace.mk' V (b x) (v x + w x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hb.continuousAt, ?_⟩
  have hv' := (FiberBundle.continuousAt_totalSpace V _ (x₀ := x)).mp hv.continuousAt |>.2
  have hw' := (FiberBundle.continuousAt_totalSpace V _ (x₀ := x)).mp hw.continuousAt |>.2
  apply (hv'.add hw').congr_of_eventuallyEq
  let e := trivializationAt V E (b x)
  have hn := hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt V E (b x)))
  filter_upwards [hn] with y hy
  exact (e.linear ℂ hy).map_add (v y) (w y)

/-- Scalar multiplication over a varying base. -/
theorem continuous_bundle_smul_over {X : Type*} [TopologicalSpace X]
    (b : X → B) (hb : Continuous b) (c : X → ℂ) (hc : Continuous c)
    (v : ∀ x, E (b x))
    (hv : Continuous (fun x => TotalSpace.mk' V (b x) (v x))) :
    Continuous (fun x => TotalSpace.mk' V (b x) (c x • v x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hb.continuousAt, ?_⟩
  have hv' := (FiberBundle.continuousAt_totalSpace V _ (x₀ := x)).mp hv.continuousAt |>.2
  apply (hc.continuousAt.smul hv').congr_of_eventuallyEq
  let e := trivializationAt V E (b x)
  have hn := hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt V E (b x)))
  filter_upwards [hn] with y hy
  exact (e.linear ℂ hy).map_smul (c y) (v y)

/-- The genuine global affine homotopy of two continuous bundle sections.
It permits intermediate degenerate zeros. -/
def bundleSectionHomotopy (s t : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (ht : Continuous (fun b => TotalSpace.mk' V b (t b))) :
    ContinuousMap.Homotopy ⟨_, hs⟩ ⟨_, ht⟩ where
  toFun z := ⟨z.2, (1 - (z.1.val : ℂ)) • s z.2 + (z.1.val : ℂ) • t z.2⟩
  continuous_toFun := by
    apply continuous_bundle_add_over Prod.snd continuous_snd
    · apply continuous_bundle_smul_over Prod.snd continuous_snd
      · exact continuous_const.sub (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst))
      · exact hs.comp continuous_snd
    · apply continuous_bundle_smul_over Prod.snd continuous_snd
      · exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
      · exact ht.comp continuous_snd
  map_zero_left b := by simp
  map_one_left b := by simp

end

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Sections
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

/-- Ordinary singular homology with integer coefficients. -/
def integralSingularHomology (n : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
  (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)

theorem integralSingularHomology_homotopy {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) :
    (integralSingularHomology n).map f = (integralSingularHomology n).map g :=
  H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n

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
-- module Solutions.OAIQ15_Sf.IntegralHomology_Relative
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

/-- The same integral singular chains underlying `integralSingularHomology`. -/
def integralSingularChains : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- Relative chains are the actual cokernel of the subspace chain map. -/
def relativeSingularChains {A X : TopCat.{0}} (i : A ⟶ X) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ := cokernel (integralSingularChains.map i)

def relativeChainProjection {A X : TopCat.{0}} (i : A ⟶ X) :
    integralSingularChains.obj X ⟶ relativeSingularChains i :=
  cokernel.π (integralSingularChains.map i)

instance instEpiChainComplexModuleCatIntNatRelativeChainProjection {A X : TopCat.{0}} (i : A ⟶ X) : Epi (relativeChainProjection i) := by
  exact coequalizer.π_epi (f := integralSingularChains.map i) (g := 0)

def relativeChainMap {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) :
    relativeSingularChains i ⟶ relativeSingularChains j :=
  cokernel.map _ _ (integralSingularChains.map a) (integralSingularChains.map f)
    (by rw [← Functor.map_comp, h, Functor.map_comp])

@[reassoc (attr := simp)]
theorem relativeChainProjection_map {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) :
    relativeChainProjection i ≫ relativeChainMap i j a f h =
      integralSingularChains.map f ≫ relativeChainProjection j := by
  exact cokernel.π_desc _ _ _

def relativeChainSequence {A X : TopCat.{0}} (i : A ⟶ X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (integralSingularChains.map i) (relativeChainProjection i)
    (cokernel.condition _)

/-- Injectivity of the actual inclusion supplies short exactness; it is
not an assumed homological property of the pair. -/
theorem relativeChainSequence_shortExact {A X : TopCat.{0}} (i : A ⟶ X)
    [Mono i] : (relativeChainSequence i).ShortExact := by
  have : Mono (integralSingularChains.map i) := by
    unfold integralSingularChains
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
  change (ShortComplex.mk (integralSingularChains.map i)
    (cokernel.π _) (cokernel.condition _)).ShortExact
  exact { exact := ShortComplex.exact_cokernel _ }

/-- Inclusion of an arbitrary subspace with its inherited topology. -/
def subspaceInclusion {X : Type} [TopologicalSpace X] (U : Set X) :
    TopCat.of U ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance instMonoTopCatSubspaceInclusion {X : Type} [TopologicalSpace X] (U : Set X) : Mono (subspaceInclusion U) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

end

section
open CategoryTheory Limits

def relativeSingularHomology {A X : TopCat.{0}} (i : A ⟶ X) (n : ℕ) : ModuleCat.{0} ℤ :=
  (relativeSingularChains i).homology n

def absoluteToRelative {A X : TopCat.{0}} (i : A ⟶ X) (n : ℕ) :
    (integralSingularHomology n).obj X ⟶ relativeSingularHomology i n :=
  HomologicalComplex.homologyMap (relativeChainProjection i) n

def relativeHomologyMap {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) (n : ℕ) :
    relativeSingularHomology i n ⟶ relativeSingularHomology j n :=
  HomologicalComplex.homologyMap (relativeChainMap i j a f h) n

@[reassoc]
theorem absoluteToRelative_naturality {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) (n : ℕ) :
    absoluteToRelative i n ≫ relativeHomologyMap i j a f h n =
      (integralSingularHomology n).map f ≫ absoluteToRelative j n := by
  change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
    HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
  rw [← HomologicalComplex.homologyMap_comp, relativeChainProjection_map,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- The boundary homomorphism of an actual injective topological map. -/
def relativeHomologyBoundary {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] (n : ℕ) :
    relativeSingularHomology i (n+1) ⟶ (integralSingularHomology n).obj A :=
  (relativeChainSequence_shortExact i).δ (n+1) n rfl

theorem absoluteToRelative_boundary {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] (n : ℕ) :
    absoluteToRelative i (n+1) ≫ relativeHomologyBoundary i n = 0 :=
  (relativeChainSequence_shortExact i).comp_δ (n+1) n rfl

end

open Bundle Topology CategoryTheory OnePoint
section

/-- Restriction of a continuous map that really carries one subspace into another. -/
def subspaceMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (V : Set Y) (f : C(X,Y)) (h : Set.MapsTo f U V) :
    TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨f x, h x.2⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem subspaceMap_square {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (V : Set Y) (f : C(X,Y)) (h : Set.MapsTo f U V) :
    subspaceInclusion U ≫ TopCat.ofHom f = subspaceMap U V f h ≫ subspaceInclusion V := rfl

variable {B V : Type} {E : B → Type} [∀ b, NormedAddCommGroup (E b)]

/-- Complement of the actual zero section in the one-point total space.
It includes infinity; it is not just the punctured total space. -/
def compactifiedNonzeroBundle : Set (OnePoint (TotalSpace V E)) :=
  (Set.range (fun b => (TotalSpace.mk' V b (0 : E b) : OnePoint (TotalSpace V E))))ᶜ

theorem coe_mem_compactifiedNonzeroBundle (b : B) (v : E b) :
    (TotalSpace.mk' V b v : OnePoint (TotalSpace V E)) ∈ compactifiedNonzeroBundle ↔ v ≠ 0 := by
  change (¬ ∃ c, (TotalSpace.mk' V c (0 : E c) : OnePoint (TotalSpace V E)) =
    (TotalSpace.mk' V b v : OnePoint (TotalSpace V E))) ↔ v ≠ 0
  constructor
  · intro h hv
    exact h ⟨b, by rw [hv]⟩
  · intro hv ⟨c, hc⟩
    have hz := OnePoint.coe_injective hc
    have hb := congrArg (fun z : TotalSpace V E => z.proj) hz
    change c = b at hb
    subst c
    exact hv ((TotalSpace.mk_injective b) hz).symm

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Equivalence
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

end

open CategoryTheory Limits HomologicalComplex ContinuousMap

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Quotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Short exact quotient complexes and biproduct cokernels. -/

open CategoryTheory Limits
section
variable {C : Type*} [Category* C] [Abelian C]
  {A B X Y : C} (f : A ⟶ X) (g : B ⟶ Y)

/-- The quotient of a direct sum is the direct sum of the actual quotients. -/
def cokernelBiprodIso : cokernel (biprod.map f g) ≅ cokernel f ⊞ cokernel g where
  hom := cokernel.desc _ (biprod.map (cokernel.π f) (cokernel.π g)) (by
    ext <;> simp)
  inv := biprod.desc
    (cokernel.desc f (biprod.inl ≫ cokernel.π (biprod.map f g)) (by
      rw [← biprod.inl_map_assoc, cokernel.condition]; simp))
    (cokernel.desc g (biprod.inr ≫ cokernel.π (biprod.map f g)) (by
      rw [← biprod.inr_map_assoc, cokernel.condition]; simp))
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (biprod.map f g))).mp
    ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply (cancel_epi (cokernel.π f)).mp
      simp [Category.assoc]
    · apply (cancel_epi (cokernel.π g)).mp
      simp [Category.assoc]

@[reassoc (attr := simp)]
theorem cokernelBiprodIso_projection :
    cokernel.π (biprod.map f g) ≫ (cokernelBiprodIso f g).hom =
      biprod.map (cokernel.π f) (cokernel.π g) := by simp [cokernelBiprodIso]

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.StdSimplexCompat
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

namespace OAI

/-- The standard simplex on a finite type, as the subtype `stdSimplex R X`
(the topological simplex of this Mathlib's `SimplexCategory.toTop`). -/
abbrev SStd (R : Type*) [Semiring R] [PartialOrder R] (X : Type*) [Fintype X] : Type _ :=
  ↥(stdSimplex R X)

namespace SStd

section Semiring

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- The weights as a finitely supported function. -/
noncomputable def weights (s : SStd R X) : X →₀ R := Finsupp.equivFunOnFinite.symm s.1

lemma weights_apply (s : SStd R X) (x : X) : s.weights x = s.1 x := rfl

lemma weights_nonneg (s : SStd R X) (x : X) : 0 ≤ s.weights x := s.2.1 x

lemma total_of_fintype (s : SStd R X) : ∑ x, s.weights x = 1 := s.2.2

lemma ext {s t : SStd R X} (h : s.weights = t.weights) : s = t :=
  Subtype.ext (congrArg (fun f : X →₀ R => (f : X → R)) h)

@[simp] lemma weights_inj {s t : SStd R X} : s.weights = t.weights ↔ s = t :=
  ⟨ext, fun h => h ▸ rfl⟩

end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Push a simplex point forward along a map of index types (this Mathlib's `stdSimplex.map`). -/
noncomputable def map (g : X → Y) (s : SStd R X) : SStd R Y := stdSimplex.map g s

lemma map_val_apply [DecidableEq Y] (g : X → Y) (s : SStd R X) (y : Y) :
    (map g s).1 y = ∑ x ∈ Finset.univ.filter (fun x => g x = y), s.1 x := by
  change (FunOnFinite.linearMap R R g s.1) y = _
  rw [FunOnFinite.linearMap_apply_apply]

@[simp] lemma weights_map (g : X → Y) (s : SStd R X) :
    (map g s).weights = s.weights.mapDomain g := by
  classical
  ext y
  rw [weights_apply, map_val_apply, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
    Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, Finset.sum_filter, weights_apply]

@[simp] lemma map_id (s : SStd R X) : map id s = s := stdSimplex.map_id_apply s

/-- The vertex (point mass) at `x`. -/
noncomputable def single (x : X) : SStd R X := by
  classical
  exact ⟨Pi.single x 1, single_mem_stdSimplex R x⟩

@[simp] lemma weights_single (x : X) : (single (R := R) x).weights = Finsupp.single x 1 := by
  classical
  ext y
  simp only [weights_apply, single, Finsupp.single_apply, Pi.single_apply, eq_comm]

@[simp] lemma single_val_apply [DecidableEq X] (x y : X) :
    (single (R := R) x).1 y = if x = y then 1 else 0 := by
  classical
  simp only [single, Pi.single_apply, eq_comm]

@[simp] lemma single_coe_apply [DecidableEq X] (x y : X) :
    DFunLike.coe (F := stdSimplex R X) (single (R := R) x) y = if x = y then 1 else 0 :=
  single_val_apply x y

@[simp] lemma map_single (x : X) (f : X → Y) : map f (single (R := R) x) = single (f x) := by
  classical
  apply ext
  rw [weights_map, weights_single, weights_single, Finsupp.mapDomain_single]

end OrderedRing

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [Fintype X]

/-- The barycenter, with every weight `(card X)⁻¹`. -/
noncomputable def barycenter [Nonempty X] : SStd 𝕜 X := stdSimplex.barycenter

lemma weights_barycenter_apply [Nonempty X] (x : X) :
    (barycenter : SStd 𝕜 X).weights x = (Fintype.card X : 𝕜)⁻¹ := rfl

@[simp] lemma barycenter_val_apply [Nonempty X] (x : X) :
    (barycenter : SStd 𝕜 X).1 x = (Fintype.card X : 𝕜)⁻¹ := rfl

@[simp] lemma barycenter_coe_apply [Nonempty X] (x : X) :
    DFunLike.coe (F := stdSimplex 𝕜 X) (barycenter : SStd 𝕜 X) x = (Fintype.card X : 𝕜)⁻¹ := rfl

end Field

section Topology

variable (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [IsTopologicalRing R]

lemma continuous_map {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y) :
    Continuous (map (R := R) f) := stdSimplex.continuous_map f

lemma continuous_weights_apply {X : Type*} [Fintype X] (x : X) :
    Continuous (fun s : SStd R X => s.weights x) :=
  (continuous_apply x).comp continuous_subtype_val

variable (M : Type*) [Fintype M]

lemma isEmbedding_toFun_comp_weights :
    Topology.IsEmbedding (fun t ↦ t.weights : SStd R M → M → R) :=
  Topology.IsEmbedding.subtypeVal

end Topology

end SStd

end OAI

end StdSimplexCompat
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_SmallChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Simplicial gluing, small singular subcomplexes, and cover meshes. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial

section

/-- Integral simplicial chains, using the same free-chain construction as
the preserved integral singular chain complex. -/
def integralSimplicialChains : SSet.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

instance integralSimplicialChains_preservesColimitsOfShape
    (J : Type) [SmallCategory J] : PreservesColimitsOfShape J integralSimplicialChains := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J
    ((evaluation _ (Type 0)).obj (Opposite.op ⦋n⦌) ⋙
      sigmaConst.obj (ModuleCat.of ℤ ℤ))
  infer_instance

instance integralSimplicialChains_preservesMonomorphisms :
    integralSimplicialChains.PreservesMonomorphisms where
  preserves f _ := by
    unfold integralSimplicialChains
    dsimp [SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    all_goals (dsimp [SimplicialObject.whiskering]; infer_instance)

end

variable {X : Type} [TopologicalSpace X]

def singularSimplexMap (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    C(SimplexCategory.toTop.obj n.unop, X) :=
  (show SimplexCategory.toTop.obj n.unop ⟶ TopCat.of X from σ.down).hom

/-- Singular simplices whose entire image lies in the specified subspace. -/
def singularSubset (U : Set X) : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (subspaceInclusion U))

theorem mem_singularSubset_iff (U : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    σ ∈ (singularSubset U).obj n ↔ ∀ p, singularSimplexMap n σ p ∈ U := by
  constructor
  · rintro ⟨τ, rfl⟩ p
    exact (singularSimplexMap n τ p).property
  · intro h
    refine ⟨ULift.up (TopCat.ofHom ⟨fun p => ⟨singularSimplexMap n σ p, h p⟩,
      (singularSimplexMap n σ).continuous.subtype_mk _⟩), ?_⟩
    rfl

theorem singularSubset_inter (U V : Set X) :
    singularSubset (U ∩ V) = singularSubset U ⊓ singularSubset V := by
  ext n σ
  rw [mem_singularSubset_iff]
  change (∀ p, singularSimplexMap n σ p ∈ U ∩ V) ↔
    σ ∈ (singularSubset U).obj n ∧ σ ∈ (singularSubset V).obj n
  simp only [Set.mem_inter_iff, mem_singularSubset_iff]
  exact forall_and

/-- Identification with singular simplices of the actual subspace,
including its inherited topology, rather than a replacement chain theory. -/
def singularSubsetIso (U : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ≅ (singularSubset U).toSSet := by
  have : Mono (TopCat.toSSet.map (subspaceInclusion U)) :=
    TopCat.toSSet.map_mono _
  let e := asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (subspaceInclusion U)))
  exact e

@[reassoc (attr := simp)]
theorem singularSubsetIso_hom_ι (U : Set X) :
    (singularSubsetIso U).hom ≫ (singularSubset U).ι =
      TopCat.toSSet.map (subspaceInclusion U) := rfl

/-- The complex of simplices small for the two-set family. Its simplices
lie wholly in one member, which need not hold for an arbitrary singular simplex. -/
def smallSingularSet (U V : Set X) : SSet.{0} :=
  (singularSubset U ⊔ singularSubset V).toSSet

def smallSingularChains (U V : Set X) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  integralSimplicialChains.obj (smallSingularSet U V)

def smallSingularChainInclusion (U V : Set X) :
    smallSingularChains U V ⟶ integralSingularChains.obj (TopCat.of X) :=
  integralSimplicialChains.map (singularSubset U ⊔ singularSubset V).ι

instance instMonoChainComplexModuleCatIntNatSmallSingularChainInclusion (U V : Set X) : Mono (smallSingularChainInclusion U V) := by
  exact integralSimplicialChains.map_mono (singularSubset U ⊔ singularSubset V).ι

theorem mem_smallSingularSet_iff (U V : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    σ ∈ (singularSubset U ⊔ singularSubset V).obj n ↔
      (∀ p, singularSimplexMap n σ p ∈ U) ∨
      (∀ p, singularSimplexMap n σ p ∈ V) := by
  change (σ ∈ (singularSubset U).obj n ∨ σ ∈ (singularSubset V).obj n) ↔ _
  simp only [mem_singularSubset_iff]

end

open CategoryTheory Topology Filter
section
variable {P X : Type} [PseudoMetricSpace P] [CompactSpace P] [TopologicalSpace X]

/-- A sufficiently small subset of the domain of one singular simplex is
carried into one member of a two-set open cover. -/
theorem continuousMap_cover_mesh (σ : C(P, X)) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    ∃ δ > 0, ∀ s : Set P, (∀ a ∈ s, ∀ b ∈ s, dist a b < δ) →
      (∀ a ∈ s, σ a ∈ U) ∨ (∀ a ∈ s, σ a ∈ V) := by
  let c : Bool → Set P := fun b => if b then σ ⁻¹' U else σ ⁻¹' V
  have hc : ∀ b, IsOpen (c b) := by
    intro b
    cases b
    · exact hV.preimage σ.continuous
    · exact hU.preimage σ.continuous
  have hcover : (Set.univ : Set P) ⊆ ⋃ b, c b := by
    intro p _
    have hp : σ p ∈ U ∪ V := by rw [hUV]; trivial
    rcases hp with hp | hp
    · exact Set.mem_iUnion.mpr ⟨true, hp⟩
    · exact Set.mem_iUnion.mpr ⟨false, hp⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc hcover
  refine ⟨δ, hδ, fun s hs => ?_⟩
  by_cases he : s.Nonempty
  · obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := hball a (Set.mem_univ _)
    have hin : ∀ p ∈ s, p ∈ c b := fun p hp => hb (hs p hp a ha)
    cases b
    · exact Or.inr hin
    · exact Or.inl hin
  · exact Or.inl (fun a ha => (he ⟨a, ha⟩).elim)

/-- A single positive mesh works simultaneously for a finite collection
of continuous simplices, as required for a finite singular chain. -/
theorem finite_continuousMaps_cover_mesh {ι : Type} (F : Finset ι) (σ : ι → C(P, X))
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    ∃ δ > 0, ∀ i ∈ F, ∀ s : Set P, (∀ a ∈ s, ∀ b ∈ s, dist a b < δ) →
      (∀ a ∈ s, σ i a ∈ U) ∨ (∀ a ∈ s, σ i a ∈ V) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨δ, hδ, hsmall⟩ := continuousMap_cover_mesh (σ i) U V hU hV hUV
    obtain ⟨ε, hε, hF⟩ := ih
    refine ⟨min δ ε, lt_min hδ hε, fun j hj s hs => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hsmall s (fun a ha b hb => (hs a ha b hb).trans_le (min_le_left _ _))
    · exact hF j hj s (fun a ha b hb => (hs a ha b hb).trans_le (min_le_right _ _))

/-- Geometric decay of mesh supplies one subdivision depth for an entire
finite chain. This proves the compactness/limit step; construction of a
subdivision chain operator with this bound remains separate. -/
theorem finite_continuousMaps_eventually_small {ι : Type} (F : Finset ι)
    (σ : ι → C(P, X)) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (L c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c < 1) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ i ∈ F, ∀ s : Set P,
      (∀ a ∈ s, ∀ b ∈ s, dist a b ≤ L * c ^ k) →
      (∀ a ∈ s, σ i a ∈ U) ∨ (∀ a ∈ s, σ i a ∈ V) := by
  obtain ⟨δ, hδ, hmesh⟩ := finite_continuousMaps_cover_mesh F σ U V hU hV hUV
  have hlim : Tendsto (fun k : ℕ => L * c ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc₀ hc₁).const_mul L
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  exact ⟨N, fun k hk i hi s hs => hmesh i hi s
    (fun a ha b hb => (hs a ha b hb).trans_lt (hN k hk))⟩

open Simplicial

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_SmallExcision
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

/-- Inclusion between subspaces of the same ambient space. -/
def subspaceInclusionOfLE {U V : Set X} (h : U ⊆ V) :
    TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨x.val, h x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

instance instMonoTopCatSubspaceInclusionOfLE {U V : Set X} (h : U ⊆ V) : Mono (subspaceInclusionOfLE h) := by
  apply (TopCat.mono_iff_injective _).mpr
  intro a b he
  exact Subtype.ext (congrArg (fun z : V => z.val) he)

@[reassoc (attr := simp)]
theorem subspaceInclusionOfLE_comp {U V : Set X} (h : U ⊆ V) :
    subspaceInclusionOfLE h ≫ subspaceInclusion V = subspaceInclusion U := rfl

def singularIntersectionIso (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)) ≅ (singularSubset U ⊓ singularSubset V).toSSet :=
  singularSubsetIso (U ∩ V) ≪≫ SSet.Subcomplex.eqToIso (singularSubset_inter U V)

theorem singularIntersectionIso_left (U V : Set X) :
    (singularIntersectionIso U V).hom ≫ SSet.Subcomplex.homOfLE inf_le_left =
      TopCat.toSSet.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) ≫
        (singularSubsetIso U).hom := by
  apply (cancel_mono (singularSubset U).ι).mp
  simp [singularIntersectionIso, Category.assoc, ← Functor.map_comp]

theorem singularIntersectionIso_right (U V : Set X) :
    (singularIntersectionIso U V).hom ≫ SSet.Subcomplex.homOfLE inf_le_right =
      TopCat.toSSet.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V)) ≫
        (singularSubsetIso V).hom := by
  apply (cancel_mono (singularSubset V).ι).mp
  simp [singularIntersectionIso, Category.assoc, ← Functor.map_comp]

def singularIntoSmallLeft (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ⟶ smallSingularSet U V :=
  (singularSubsetIso U).hom ≫ SSet.Subcomplex.homOfLE le_sup_left

def singularIntoSmallRight (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of V) ⟶ smallSingularSet U V :=
  (singularSubsetIso V).hom ≫ SSet.Subcomplex.homOfLE le_sup_right

theorem smallSingularSet_isPushout (U V : Set X) :
    IsPushout
      (TopCat.toSSet.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.toSSet.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V)))
      (singularIntoSmallLeft U V) (singularIntoSmallRight U V) := by
  have h := SSet.Subcomplex.BicartSq.isPushout
    (X := TopCat.toSSet.obj (TopCat.of X))
    (A₁ := singularSubset U ⊓ singularSubset V)
    (A₂ := singularSubset U) (A₃ := singularSubset V)
    (A₄ := singularSubset U ⊔ singularSubset V) { sup_eq := rfl, inf_eq := rfl }
  exact h.of_iso' (singularIntersectionIso U V) (singularSubsetIso U)
    (singularSubsetIso V) (Iso.refl _) (singularIntersectionIso_left U V)
    (singularIntersectionIso_right U V) (Category.comp_id (singularIntoSmallLeft U V)).symm
    (Category.comp_id (singularIntoSmallRight U V)).symm

def singularChainsIntoSmallLeft (U V : Set X) :
    integralSingularChains.obj (TopCat.of U) ⟶ smallSingularChains U V :=
  integralSimplicialChains.map (singularIntoSmallLeft U V)

def singularChainsIntoSmallRight (U V : Set X) :
    integralSingularChains.obj (TopCat.of V) ⟶ smallSingularChains U V :=
  integralSimplicialChains.map (singularIntoSmallRight U V)

@[reassoc (attr := simp)]
theorem singularChainsIntoSmallLeft_inclusion (U V : Set X) :
    singularChainsIntoSmallLeft U V ≫ smallSingularChainInclusion U V =
      integralSingularChains.map (subspaceInclusion U) := by
  change integralSimplicialChains.map _ ≫ integralSimplicialChains.map _ = _
  erw [← Functor.map_comp]
  simp [singularIntoSmallLeft]
  rfl

@[reassoc (attr := simp)]
theorem singularChainsIntoSmallRight_inclusion (U V : Set X) :
    singularChainsIntoSmallRight U V ≫ smallSingularChainInclusion U V =
      integralSingularChains.map (subspaceInclusion V) := by
  change integralSimplicialChains.map _ ≫ integralSimplicialChains.map _ = _
  erw [← Functor.map_comp]
  simp [singularIntoSmallRight]
  rfl

theorem smallSingularChains_isPushout (U V : Set X) :
    IsPushout
      (integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)))
      (integralSingularChains.map (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V)))
      (singularChainsIntoSmallLeft U V) (singularChainsIntoSmallRight U V) :=
  integralSimplicialChains.map_isPushout (smallSingularSet_isPushout U V)

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
open CategoryTheory Limits
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Small relative chains modulo the full chains of the second subspace. -/
def smallRelativeChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (singularChainsIntoSmallRight U V)

/-- Actual chain-level excision into small relative chains. This needs no
openness or covering hypothesis because the target only uses small simplices. -/
def smallRelativeExcisionIso :
    relativeSingularChains (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U)) ≅
      smallRelativeChains U V := by
  let sq := smallSingularChains_isPushout U V
  haveI := isIso_cokernel_map_of_isPushout sq
  let e := asIso (cokernel.map _ _ _ _ sq.w)
  exact e

/-- Comparison with the full relative chains of (X,V). -/
def smallRelativeComparison : smallRelativeChains U V ⟶
    relativeSingularChains (subspaceInclusion V) :=
  cokernel.map _ _ (𝟙 _) (smallSingularChainInclusion U V)
    (by simp)

/-- The composition of small excision and comparison is exactly the map
induced by the inclusions of pairs (U,U∩V) → (X,V). -/
theorem smallRelativeExcision_comparison :
    (smallRelativeExcisionIso U V).hom ≫ smallRelativeComparison U V =
      relativeChainMap
        (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U))
        (subspaceInclusion V)
        (subspaceInclusionOfLE (Set.inter_subset_right : U ∩ V ⊆ V))
        (subspaceInclusion U) (by rfl) := by
  apply (cancel_epi (cokernel.π (integralSingularChains.map
    (subspaceInclusionOfLE (Set.inter_subset_left : U ∩ V ⊆ U))))).mp
  dsimp only [smallRelativeExcisionIso, smallRelativeComparison, relativeChainMap, asIso_hom]
  erw [cokernel.π_desc_assoc, cokernel.π_desc]
  erw [Category.assoc, cokernel.π_desc]
  erw [← Category.assoc, singularChainsIntoSmallLeft_inclusion]
  rfl

instance instMonoChainComplexModuleCatIntNatSingularChainsIntoSmallRight : Mono (singularChainsIntoSmallRight U V) := by
  have : Mono (integralSingularChains.map (subspaceInclusion V)) := by
    unfold integralSingularChains
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
  exact mono_of_mono_fac (singularChainsIntoSmallRight_inclusion U V)

def smallRelativeSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (singularChainsIntoSmallRight U V)
    (cokernel.π _) (cokernel.condition _)

theorem smallRelativeSequence_shortExact : (smallRelativeSequence U V).ShortExact := by
  change (ShortComplex.mk (singularChainsIntoSmallRight U V)
    (cokernel.π _) (cokernel.condition _)).ShortExact
  exact { exact := ShortComplex.exact_cokernel _ }

def smallRelativeSequenceComparison :
    smallRelativeSequence U V ⟶ relativeChainSequence (subspaceInclusion V) where
  τ₁ := 𝟙 _
  τ₂ := smallSingularChainInclusion U V
  τ₃ := smallRelativeComparison U V
  comm₁₂ := by simp [smallRelativeSequence, relativeChainSequence]
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- The purely homological step in singular excision. Its explicit premise
is the small-chain theorem, which still requires subdivision for open covers. -/
theorem smallRelativeComparison_quasiIso
    (h : QuasiIso (smallSingularChainInclusion U V)) :
    QuasiIso (smallRelativeComparison U V) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (smallRelativeSequenceComparison U V) (smallRelativeSequence_shortExact U V)
    (relativeChainSequence_shortExact (subspaceInclusion V)) (by
      exact inferInstanceAs (QuasiIso (𝟙 (integralSingularChains.obj (TopCat.of V))))) h

end

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Exactness at the intersection term of the actual small-chain sequence. -/
theorem smallMayerVietoris_exact_at_intersection (n : ℕ) :
    (ShortComplex.mk _ _
      ((smallMayerVietorisSequence_shortExact U V).δ_comp (n+1) n rfl)).Exact :=
  (smallMayerVietorisSequence_shortExact U V).homology_exact₁ (n+1) n rfl

theorem homology_biprod_isZero (C D : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (hC : IsZero (C.homology n)) (hD : IsZero (D.homology n)) :
    IsZero ((C ⊞ D).homology n) := by
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  have hfst : F.map (biprod.fst : C ⊞ D ⟶ C) = 0 := hC.eq_of_tgt _ _
  have hsnd : F.map (biprod.snd : C ⊞ D ⟶ D) = 0 := hD.eq_of_tgt _ _
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (F.obj (C ⊞ D)) = 0
  rw [← F.map_id, ← biprod.total, F.map_add, F.map_comp, F.map_comp,
    hfst, hsnd, zero_comp, zero_comp, add_zero]

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

/-- The induced map on small chains for a continuous map respecting covers.
The construction uses the proved pushout of actual singular-chain complexes. -/
def smallSingularChainsContinuousMap : smallSingularChains U V ⟶ smallSingularChains U' V' :=
  (smallSingularChains_isPushout U V).desc
    (integralSingularChains.map (subspaceMap U U' f hU) ≫ singularChainsIntoSmallLeft U' V')
    (integralSingularChains.map (subspaceMap V V' f hV) ≫ singularChainsIntoSmallRight U' V')
    (by
      apply (cancel_mono (smallSingularChainInclusion U' V')).mp
      simp only [Category.assoc, singularChainsIntoSmallLeft_inclusion,
        singularChainsIntoSmallRight_inclusion, ← Functor.map_comp]
      rfl)

@[reassoc (attr := simp)]
theorem smallSingularChainsContinuousMap_left :
    singularChainsIntoSmallLeft U V ≫ smallSingularChainsContinuousMap U V U' V' f hU hV =
      integralSingularChains.map (subspaceMap U U' f hU) ≫ singularChainsIntoSmallLeft U' V' :=
  (smallSingularChains_isPushout U V).inl_desc _ _ _

@[reassoc (attr := simp)]
theorem smallSingularChainsContinuousMap_right :
    singularChainsIntoSmallRight U V ≫ smallSingularChainsContinuousMap U V U' V' f hU hV =
      integralSingularChains.map (subspaceMap V V' f hV) ≫ singularChainsIntoSmallRight U' V' :=
  (smallSingularChains_isPushout U V).inr_desc _ _ _

@[reassoc (attr := simp)]
theorem smallSingularChainsContinuousMap_inclusion :
    smallSingularChainsContinuousMap U V U' V' f hU hV ≫ smallSingularChainInclusion U' V' =
      smallSingularChainInclusion U V ≫ integralSingularChains.map (TopCat.ofHom f) := by
  apply (smallSingularChains_isPushout U V).hom_ext <;>
    simp [← Functor.map_comp] <;> rfl

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_TupleChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Tuple chains, subdivision, chain maps, and support control. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial

section

/-- Ordered tuples, with deletion and repetition of vertices. -/
def tupleSSet (E : Type) : SSet.{0} where
  obj n := Fin (n.unop.len + 1) → E
  map f := ↾fun v => v ∘ f.unop.toOrderHom

abbrev tupleChains (E : Type) := (tupleSSet E).chainComplex (ModuleCat.of ℤ ℤ)
abbrev tupleGen {E : Type} {n : ℕ} (v : Fin (n+1) → E) :
    ModuleCat.of ℤ ℤ ⟶ (tupleChains E).X n := (tupleSSet E).ιChainComplex v

/-- Maps from tuple chains are determined by their values on tuple generators. -/
theorem tupleChains_hom_ext {E : Type} {n : ℕ} {T : ModuleCat.{0} ℤ}
    {f g : (tupleChains E).X n ⟶ T}
    (h : ∀ v : Fin (n+1) → E, tupleGen v ≫ f = tupleGen v ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

@[reassoc]
theorem tupleGen_d {E : Type} {n : ℕ} (v : Fin (n+2) → E) :
    tupleGen v ≫ (tupleChains E).d (n+1) n =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • tupleGen (v ∘ i.succAbove) := by
  exact SSet.ιChainComplex_d (tupleSSet E) (ModuleCat.of ℤ ℤ) v

/-- Prepending a fixed vertex, extended linearly on actual free chains. -/
def tupleCone {E : Type} (p : E) (n : ℕ) :
    (tupleChains E).X n ⟶ (tupleChains E).X (n+1) :=
  Sigma.desc (fun v => tupleGen (Fin.cons p v))

@[reassoc (attr := simp)]
theorem tupleGen_cone {E : Type} (p : E) {n : ℕ} (v : Fin (n+1) → E) :
    tupleGen v ≫ tupleCone p n = tupleGen (Fin.cons p v) := by
  exact Sigma.ι_desc _ _

/-- Augmentation of zero-chains. -/
def tupleAugmentation (E : Type) : (tupleChains E).X 0 ⟶ ModuleCat.of ℤ ℤ :=
  Sigma.desc (fun _ => 𝟙 _)

@[reassoc (attr := simp)]
theorem tupleGen_augmentation {E : Type} (v : Fin 1 → E) :
    tupleGen v ≫ tupleAugmentation E = 𝟙 _ := by
  exact Sigma.ι_desc _ _

@[reassoc (attr := simp)]
theorem tuple_d_augmentation (E : Type) :
    (tupleChains E).d 1 0 ≫ tupleAugmentation E = 0 := by
  apply tupleChains_hom_ext
  intro v
  rw [← Category.assoc, tupleGen_d]
  simp [Fin.sum_univ_two]

@[reassoc]
theorem tupleCone_d_zero {E : Type} (p : E) :
    tupleCone p 0 ≫ (tupleChains E).d 1 0 =
      𝟙 _ - tupleAugmentation E ≫ tupleGen (fun _ : Fin 1 => p) := by
  apply tupleChains_hom_ext
  intro v
  rw [← Category.assoc, tupleGen_cone, tupleGen_d]
  have hzero : Fin.cons p v ∘ (0 : Fin 2).succAbove = v := by ext i; simp
  have hone : Fin.cons p v ∘ (1 : Fin 2).succAbove = (fun _ : Fin 1 => p) := by
    ext i
    fin_cases i
    rfl
  change (∑ i : Fin 2, (-1 : ℤ)^i.val • tupleGen (Fin.cons p v ∘ i.succAbove)) = tupleGen v ≫ _
  simp only [Fin.sum_univ_two, hzero, hone, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, Category.comp_id,
    tupleGen_augmentation_assoc, sub_eq_add_neg, Preadditive.comp_add, Preadditive.comp_neg]

/-- The cone boundary identity in positive degree. -/
@[reassoc]
theorem tupleCone_d {E : Type} (p : E) (n : ℕ) :
    tupleCone p (n+1) ≫ (tupleChains E).d (n+2) (n+1) =
      𝟙 _ - (tupleChains E).d (n+1) n ≫ tupleCone p n := by
  apply tupleChains_hom_ext
  intro v
  rw [← Category.assoc, tupleGen_cone, tupleGen_d]
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, tupleGen_d]
  rw [Fin.sum_univ_succ]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, tupleGen_cone,
    Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ]
  have hzero : Fin.cons p v ∘ (0 : Fin (n+3)).succAbove = v := by
    ext i
    simp
  have hsucc (i : Fin (n+2)) :
      Fin.cons p v ∘ i.succ.succAbove = Fin.cons p (v ∘ i.succAbove) := by
    ext j
    cases j using Fin.cases <;> simp [Function.comp_def]
  simp only [hzero, hsucc, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    sub_eq_add_neg]

variable {E : Type}

/-- A center is chosen for each positive-dimensional tuple. The chain
identity does not require a metric; barycenters will supply mesh control. -/
def tupleSubdivisionMap (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    ∀ n, (tupleChains E).X n ⟶ (tupleChains E).X n := fun n => match n with
  | 0 => 𝟙 _
  | n+1 => Sigma.desc (fun v => tupleGen v ≫ (tupleChains E).d (n+1) n ≫
      tupleSubdivisionMap b n ≫ tupleCone (b n v) n)

@[simp]
theorem tupleSubdivisionMap_zero (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    tupleSubdivisionMap b 0 = 𝟙 _ := rfl

@[reassoc (attr := simp)]
theorem tupleGen_subdivision_succ (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    {n : ℕ} (v : Fin (n+2) → E) :
    tupleGen v ≫ tupleSubdivisionMap b (n+1) =
      tupleGen v ≫ (tupleChains E).d (n+1) n ≫
      tupleSubdivisionMap b n ≫ tupleCone (b n v) n := by
  exact Sigma.ι_desc _ _

/-- Subdivision commutes with the actual alternating boundary. -/
@[reassoc]
theorem tupleSubdivisionMap_d (b : ∀ n : ℕ, (Fin (n+2) → E) → E) (n : ℕ) :
    tupleSubdivisionMap b (n+1) ≫ (tupleChains E).d (n+1) n =
      (tupleChains E).d (n+1) n ≫ tupleSubdivisionMap b n := by
  induction n with
  | zero =>
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_subdivision_succ]
    simp only [tupleSubdivisionMap_zero, Category.id_comp, Category.comp_id, Category.assoc]
    rw [tupleCone_d_zero]
    simp [Preadditive.comp_sub, ← Category.assoc]
  | succ n ih =>
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_subdivision_succ]
    simp only [Category.assoc, tupleCone_d, Preadditive.comp_sub, Category.comp_id]
    rw [← Category.assoc (tupleSubdivisionMap b (n+1)), ih]
    simp [← Category.assoc]

/-- A constructed chain endomorphism, for any supplied centers. -/
def tupleSubdivision (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    tupleChains E ⟶ tupleChains E :=
  ChainComplex.ofHom (tupleSubdivisionMap b) (tupleSubdivisionMap_d b)

/-- The prism is filled by a cone after subtracting its prescribed boundary.
This recursion constructs the homotopy; it is not a homotopy premise. -/
def tupleSubdivisionPrism (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    ∀ n, (tupleChains E).X n ⟶ (tupleChains E).X (n+1) := fun n => match n with
  | 0 => 0
  | n+1 => Sigma.desc (fun v =>
      (tupleGen v - tupleGen v ≫ tupleSubdivisionMap b (n+1) -
        tupleGen v ≫ (tupleChains E).d (n+1) n ≫ tupleSubdivisionPrism b n) ≫
      tupleCone (b n v) (n+1))

@[simp]
theorem tupleSubdivisionPrism_zero (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    tupleSubdivisionPrism b 0 = 0 := rfl

@[reassoc (attr := simp)]
theorem tupleGen_prism_succ (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    {n : ℕ} (v : Fin (n+2) → E) :
    tupleGen v ≫ tupleSubdivisionPrism b (n+1) =
      (tupleGen v - tupleGen v ≫ tupleSubdivisionMap b (n+1) -
        tupleGen v ≫ (tupleChains E).d (n+1) n ≫ tupleSubdivisionPrism b n) ≫
      tupleCone (b n v) (n+1) := by
  exact Sigma.ι_desc _ _

/-- A cone fills every positive-dimensional cycle in tuple chains. -/
theorem tupleCone_cycle (p : E) (n : ℕ) {A : ModuleCat.{0} ℤ}
    (z : A ⟶ (tupleChains E).X (n+1))
    (hz : z ≫ (tupleChains E).d (n+1) n = 0) :
    z ≫ tupleCone p (n+1) ≫ (tupleChains E).d (n+2) (n+1) = z := by
  rw [tupleCone_d, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hz]
  simp only [zero_comp, sub_zero]

/-- The full positive-degree chain-homotopy equation. -/
theorem tupleSubdivisionPrism_equation (b : ∀ n : ℕ, (Fin (n+2) → E) → E) (n : ℕ) :
    tupleSubdivisionPrism b (n+1) ≫ (tupleChains E).d (n+2) (n+1) =
      𝟙 _ - tupleSubdivisionMap b (n+1) -
      (tupleChains E).d (n+1) n ≫ tupleSubdivisionPrism b n := by
  induction n with
  | zero =>
    have hcycle : (𝟙 _ - tupleSubdivisionMap b 1 -
        (tupleChains E).d 1 0 ≫ tupleSubdivisionPrism b 0) ≫
        (tupleChains E).d 1 0 = 0 := by
      rw [tupleSubdivisionPrism_zero, comp_zero, sub_zero, Preadditive.sub_comp,
        Category.id_comp, tupleSubdivisionMap_d, tupleSubdivisionMap_zero, Category.comp_id]
      exact sub_self _
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_prism_succ, Category.assoc]
    change (tupleGen v - tupleGen v ≫ tupleSubdivisionMap b 1 -
      tupleGen v ≫ (tupleChains E).d 1 0 ≫ tupleSubdivisionPrism b 0) ≫ _ = _
    rw [show tupleGen v - tupleGen v ≫ tupleSubdivisionMap b 1 -
        tupleGen v ≫ (tupleChains E).d 1 0 ≫ tupleSubdivisionPrism b 0 =
        tupleGen v ≫ (𝟙 _ - tupleSubdivisionMap b 1 -
          (tupleChains E).d 1 0 ≫ tupleSubdivisionPrism b 0) by
      simp only [Preadditive.comp_sub, Category.comp_id]]
    exact tupleCone_cycle _ 0 _ (by rw [Category.assoc, hcycle, comp_zero])
  | succ n ih =>
    have hcycle :
        (𝟙 _ - tupleSubdivisionMap b (n+2) -
          (tupleChains E).d (n+2) (n+1) ≫ tupleSubdivisionPrism b (n+1)) ≫
          (tupleChains E).d (n+2) (n+1) = 0 := by
      simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        tupleSubdivisionMap_d, ih, Preadditive.comp_sub, Category.comp_id,
        HomologicalComplex.d_comp_d_assoc, zero_comp]
      abel
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_prism_succ, Category.assoc]
    rw [show tupleGen v - tupleGen v ≫ tupleSubdivisionMap b (n+2) -
        tupleGen v ≫ (tupleChains E).d (n+2) (n+1) ≫ tupleSubdivisionPrism b (n+1) =
        tupleGen v ≫ (𝟙 _ - tupleSubdivisionMap b (n+2) -
          (tupleChains E).d (n+2) (n+1) ≫ tupleSubdivisionPrism b (n+1)) by
      simp only [Preadditive.comp_sub, Category.comp_id]]
    exact tupleCone_cycle _ (n+1) _ (by rw [Category.assoc, hcycle, comp_zero])

def chainHomotopyOfComponents {P Q : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f g : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n+1))
    (hzero : f.f 0 = h 0 ≫ Q.d 1 0 + g.f 0)
    (hsucc : ∀ n, f.f (n+1) = P.d (n+1) n ≫ h n +
      h (n+1) ≫ Q.d (n+2) (n+1) + g.f (n+1)) : Homotopy f g where
  hom i j := if e : i+1 = j then h i ≫ eqToHom (congrArg Q.X e) else 0
  zero i j h' := by simp_all [ComplexShape.down_Rel]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simpa only [dite_true, eqToHom_refl, Category.comp_id, zero_add] using hzero
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simpa only [dite_true, eqToHom_refl, Category.comp_id] using hsucc n

end

variable {E F : Type}

/-- Applying a function to each vertex defines a simplicial map. -/
def tupleSSetMap (f : E → F) : tupleSSet E ⟶ tupleSSet F where
  app _ := ↾fun v => f ∘ v

abbrev tupleChainMap (f : E → F) : tupleChains E ⟶ tupleChains F :=
  SSet.chainComplexMap (tupleSSetMap f) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)]
theorem tupleGen_map (f : E → F) {n : ℕ} (v : Fin (n+1) → E) :
    tupleGen v ≫ (tupleChainMap f).f n = tupleGen (f ∘ v) := by
  exact SSet.ι_chainComplexMap_f (X := tupleSSet E) (Y := tupleSSet F)
    (f := tupleSSetMap f) (R := ModuleCat.of ℤ ℤ) (x := v)

@[reassoc]
theorem tupleCone_map (f : E → F) (p : E) (n : ℕ) :
    tupleCone p n ≫ (tupleChainMap f).f (n+1) =
      (tupleChainMap f).f n ≫ tupleCone (f p) n := by
  apply tupleChains_hom_ext
  intro v
  simp only [← Category.assoc, tupleGen_cone, tupleGen_map, Fin.comp_cons]

/-- Naturality of subdivision for center-preserving vertex maps. -/
@[reassoc]
theorem tupleSubdivisionMap_naturality
    (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    (c : ∀ n : ℕ, (Fin (n+2) → F) → F)
    (f : E → F) (hb : ∀ n v, f (b n v) = c n (f ∘ v)) (n : ℕ) :
    tupleSubdivisionMap b n ≫ (tupleChainMap f).f n =
      (tupleChainMap f).f n ≫ tupleSubdivisionMap c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_subdivision_succ]
    simp only [Category.assoc, tupleCone_map, hb]
    rw [← Category.assoc (tupleSubdivisionMap b n), ih]
    simp only [Category.assoc, ← (tupleChainMap f).comm_assoc (n+1) n]
    simp only [tupleGen_map_assoc, tupleGen_subdivision_succ]

/-- The explicit subdivision homotopy has the same naturality. -/
@[reassoc]
theorem tupleSubdivisionPrism_naturality
    (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    (c : ∀ n : ℕ, (Fin (n+2) → F) → F)
    (f : E → F) (hb : ∀ n v, f (b n v) = c n (f ∘ v)) (n : ℕ) :
    tupleSubdivisionPrism b n ≫ (tupleChainMap f).f (n+1) =
      (tupleChainMap f).f n ≫ tupleSubdivisionPrism c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_prism_succ, Category.assoc, tupleCone_map, hb]
    rw [← Category.assoc]
    simp only [Preadditive.sub_comp, Category.assoc,
      tupleSubdivisionMap_naturality b c f hb, ih]
    simp only [← (tupleChainMap f).comm_assoc (n+1) n]
    simp only [tupleGen_map_assoc, tupleGen_subdivision_succ, tupleGen_subdivision_succ_assoc, Category.assoc, tupleGen_prism_succ,
      Preadditive.sub_comp, Category.assoc]

end

open CategoryTheory Limits AlgebraicTopology Simplicial
section
variable {E F : Type}

/-- Integral chains spanned by tuples satisfying a specified support condition. -/
def tupleChainSpan {n : ℕ} (P : (Fin (n+1) → E) → Prop) :
    Submodule ℤ ((tupleChains E).X n) :=
  Submodule.span ℤ {c | ∃ v, P v ∧ c = tupleGen v (1 : ℤ)}

theorem tupleGen_mem_span {n : ℕ} {P : (Fin (n+1) → E) → Prop}
    (v : Fin (n+1) → E) (hv : P v) : tupleGen v (1 : ℤ) ∈ tupleChainSpan P :=
  Submodule.subset_span ⟨v, hv, rfl⟩

/-- To control a linear operator on supported chains, it suffices to control
each supported generator. -/
theorem tupleChainSpan_map {n m : ℕ} {P : (Fin (n+1) → E) → Prop}
    {Q : (Fin (m+1) → F) → Prop}
    (L : (tupleChains E).X n ⟶ (tupleChains F).X m)
    (hL : ∀ v, P v → L (tupleGen v (1 : ℤ)) ∈ tupleChainSpan Q)
    {c : (tupleChains E).X n} (hc : c ∈ tupleChainSpan P) : L c ∈ tupleChainSpan Q := by
  have h : tupleChainSpan P ≤ (tupleChainSpan Q).comap L.hom := by
    apply Submodule.span_le.mpr
    rintro c ⟨v, hv, rfl⟩
    exact hL v hv
  exact h hc

theorem tupleChainSpan_mono {n : ℕ} {P Q : (Fin (n+1) → E) → Prop}
    (h : ∀ v, P v → Q v) : tupleChainSpan P ≤ tupleChainSpan Q := by
  apply Submodule.span_le.mpr
  rintro c ⟨v, hv, rfl⟩
  exact tupleGen_mem_span v (h v hv)

/-- Coning preserves the support condition exactly when prepending its
vertex preserves the generator condition. -/
theorem tupleCone_mem_span {n : ℕ} (p : E)
    {P : (Fin (n+1) → E) → Prop} {Q : (Fin (n+2) → E) → Prop}
    (h : ∀ v, P v → Q (Fin.cons p v))
    {c : (tupleChains E).X n} (hc : c ∈ tupleChainSpan P) :
    tupleCone p n c ∈ tupleChainSpan Q := by
  apply tupleChainSpan_map (tupleCone p n) (fun v hv => ?_) hc
  change (tupleGen v ≫ tupleCone p n) (1 : ℤ) ∈ _
  rw [tupleGen_cone]
  exact tupleGen_mem_span _ (h v hv)

/-- The recursive subdivision formula evaluated as an actual chain. -/
theorem tupleSubdivision_gen_value (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    {n : ℕ} (v : Fin (n+2) → E) :
    tupleSubdivisionMap b (n+1) (tupleGen v (1 : ℤ)) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        tupleCone (b n v) n (tupleSubdivisionMap b n (tupleGen (v ∘ i.succAbove) (1 : ℤ))) := by
  change (tupleGen v ≫ tupleSubdivisionMap b (n+1)) (1 : ℤ) = _
  rw [tupleGen_subdivision_succ, ← Category.assoc, ← Category.assoc, tupleGen_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  change ((∑ i : Fin (n+2), (-1 : ℤ)^i.val •
    (tupleGen (v ∘ i.succAbove) ≫ tupleSubdivisionMap b n ≫ tupleCone (b n v) n)).hom) (1 : ℤ) = _
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    ModuleCat.hom_comp]

  apply Finset.sum_congr rfl
  intro i hi
  rfl

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Simplex
attribute [-instance] _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSingularChainsIntoSmallRight
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

/-- Affine interpolation of vertices in an actual standard simplex. -/
def simplexCombination {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → OAI.SStd ℝ κ) (t : OAI.SStd ℝ ι) : OAI.SStd ℝ κ :=
  ⟨fun k => ∑ i, t.1 i * (v i).1 k,
    fun k => Finset.sum_nonneg (fun i _ => mul_nonneg (t.2.1 i) ((v i).2.1 k)),
    by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, (v _).2.2, mul_one]
      exact t.2.2⟩

@[simp]
theorem simplexCombination_coe {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → OAI.SStd ℝ κ) (t : OAI.SStd ℝ ι) :
    ⇑(simplexCombination v t).weights = ∑ index, t.weights index • ⇑(v index).weights := by
  classical
  funext k
  simp [simplexCombination, OAI.SStd.weights_apply, Finset.sum_apply]

/-- Interpolation is continuous in the barycentric coordinates. -/
def simplexCombinationMap {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → OAI.SStd ℝ κ) : C(OAI.SStd ℝ ι, OAI.SStd ℝ κ) :=
  ⟨simplexCombination v, by
    apply (OAI.SStd.isEmbedding_toFun_comp_weights ℝ κ).continuous_iff.mpr
    change Continuous (fun point => ⇑(simplexCombination v point).weights)
    simp only [simplexCombination_coe]
    apply continuous_finsetSum
    intro index _
    exact (OAI.SStd.continuous_weights_apply ℝ index).smul continuous_const⟩

@[simp]
theorem simplexCombination_vertex {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (v : ι → OAI.SStd ℝ κ) (i : ι) :
    simplexCombination v (OAI.SStd.single i) = v i := by
  classical
  apply Subtype.ext; funext k
  simp [simplexCombination]

@[simp]
theorem simplexCombination_vertices {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : OAI.SStd ℝ ι) : simplexCombination OAI.SStd.single t = t := by
  classical
  apply Subtype.ext; funext k
  simp [simplexCombination]

/-- Interpolation intertwines vertex reindexing with the genuine
standard-simplex map, including all cofaces. -/
theorem simplexCombination_reindex {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (v : κ → OAI.SStd ℝ μ) (f : ι → κ) (t : OAI.SStd ℝ ι) :
    simplexCombination (v ∘ f) t = simplexCombination v (OAI.SStd.map f t) := by
  classical
  apply Subtype.ext; funext k
  simp only [simplexCombination, Function.comp_apply, OAI.SStd.map_val_apply, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => t.1 x * (v (f x)).1 k)]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro x hx
  rw [(Finset.mem_filter.mp hx).2]

/-- Affine maps of the target simplex commute with interpolation. -/
theorem simplexCombination_map {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (v : ι → OAI.SStd ℝ κ) (f : κ → μ) (t : OAI.SStd ℝ ι) :
    OAI.SStd.map f (simplexCombination v t) =
      simplexCombination (OAI.SStd.map f ∘ v) t := by
  classical
  apply Subtype.ext; funext m
  simp only [simplexCombination, Function.comp_apply, OAI.SStd.map_val_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Barycenter of a tuple in the ambient standard simplex. -/
def simplexTupleCenter {κ : Type} [Fintype κ] (n : ℕ)
    (v : Fin (n+2) → OAI.SStd ℝ κ) : OAI.SStd ℝ κ :=
  simplexCombination v OAI.SStd.barycenter

@[simp]
theorem simplexTupleCenter_map {κ μ : Type} [Fintype κ] [Fintype μ]
    (f : κ → μ) (n : ℕ) (v : Fin (n+2) → OAI.SStd ℝ κ) :
    OAI.SStd.map f (simplexTupleCenter n v) =
      simplexTupleCenter n (OAI.SStd.map f ∘ v) :=
  simplexCombination_map v f _

/-- A convex combination stays within any common distance bound from a point. -/
theorem simplexCombination_dist_le {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → OAI.SStd ℝ κ) (t : OAI.SStd ℝ ι) (p : OAI.SStd ℝ κ)
    (D : ℝ) (hv : ∀ i, dist (v i) p ≤ D) :
    dist (simplexCombination v t) p ≤ D := by
  have he : ⇑(simplexCombination v t).weights - ⇑p.weights =
      ∑ i, t.weights i • (⇑(v i).weights - ⇑p.weights) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, t.total_of_fintype, one_smul,
      simplexCombination_coe]
  change ‖⇑(simplexCombination v t).weights - ⇑p.weights‖ ≤ D
  rw [he]
  calc
    ‖∑ i, t.weights i • (⇑(v i).weights - ⇑p.weights)‖ ≤
      ∑ i, ‖t.weights i • (⇑(v i).weights - ⇑p.weights)‖ := norm_sum_le _ _
    _ = ∑ i, t.weights i * dist (v i) p := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (t.weights_nonneg i)]
      rfl
    _ ≤ ∑ i, t.weights i * D :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (t.weights_nonneg i))
    _ = D := by rw [← Finset.sum_mul, t.total_of_fintype, one_mul]

/-- Affine interpolation cannot increase a bound on pairwise vertex distances. -/
theorem simplexCombination_pair_dist_le {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → OAI.SStd ℝ κ) (s t : OAI.SStd ℝ ι)
    (D : ℝ) (hv : ∀ i j, dist (v i) (v j) ≤ D) :
    dist (simplexCombination v s) (simplexCombination v t) ≤ D := by
  apply simplexCombination_dist_le
  intro i
  rw [dist_comm]
  exact simplexCombination_dist_le v t (v i) D (fun j => hv j i)

/-- Averaging N vertices has distance at most (N-1)/N times the original
mesh from every vertex. This includes repeated vertices. -/
theorem simplexTupleCenter_vertex_dist_le {κ : Type} [Fintype κ]
    (n : ℕ) (v : Fin (n+2) → OAI.SStd ℝ κ) (D : ℝ)
    (hv : ∀ i j, dist (v i) (v j) ≤ D) (j : Fin (n+2)) :
    dist (simplexTupleCenter n v) (v j) ≤ ((n+1 : ℝ) / (n+2)) * D := by
  have hn : (0 : ℝ) < n+2 := by positivity
  have he : ⇑(simplexTupleCenter n v).weights - ⇑(v j).weights =
      (n+2 : ℝ)⁻¹ • ∑ i, (⇑(v i).weights - ⇑(v j).weights) := by
    simp only [simplexTupleCenter, simplexCombination_coe, OAI.SStd.weights_barycenter_apply, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat]
    rw [← Finset.smul_sum, Finset.sum_sub_distrib, smul_sub,
      Finset.sum_const, Finset.card_univ]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [ne_of_gt hn]
  change ‖⇑(simplexTupleCenter n v).weights - ⇑(v j).weights‖ ≤ _
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  have hsum : ‖∑ i, (⇑(v i).weights - ⇑(v j).weights)‖ ≤ (n+1 : ℝ) * D := by
    calc
      ‖∑ i, (⇑(v i).weights - ⇑(v j).weights)‖ ≤
        ∑ i, ‖⇑(v i).weights - ⇑(v j).weights‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (n+2), if i = j then 0 else D := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases h : i = j
        · subst i; simp
        · have distance_bound : ‖⇑(v i).weights - ⇑(v j).weights‖ ≤ D := hv i j
          simpa [h] using distance_bound
      _ = (n+1 : ℝ) * D := by
        have hh (i : Fin (n+2)) : (if i = j then 0 else D) = D - (if i = j then D else 0) := by
          split_ifs <;> simp
        simp_rw [hh]
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
        ring
  calc
    (n+2 : ℝ)⁻¹ * ‖∑ i, (⇑(v i).weights - ⇑(v j).weights)‖ ≤ (n+2 : ℝ)⁻¹ * ((n+1) * D) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = _ := by ring

abbrev standardSimplexSpace (k : ℕ) : TopCat.{0} :=
  TopCat.of (OAI.SStd ℝ (Fin (k+1)))

/-- A continuous simplex as an element of the library singular set. -/
def singularSimplexOfMap {X : TopCat.{0}} {n : ℕ}
    (f : C(OAI.SStd ℝ (Fin (n+1)), X)) : (TopCat.toSSet.obj X) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv X _).symm f

abbrev singularGen {X : TopCat.{0}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ModuleCat.of ℤ ℤ ⟶ (integralSingularChains.obj X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex σ

/-- Maps from singular chains are determined by their values on singular simplices. -/
theorem singularChains_hom_ext {X : TopCat.{0}} {n : ℕ} {T : ModuleCat.{0} ℤ}
    {f g : (integralSingularChains.obj X).X n ⟶ T}
    (h : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌, singularGen σ ≫ f = singularGen σ ≫ g) :
    f = g := SSet.chainComplex_hom_ext h

/-- Interpolation into actual singular simplices, in every degree. -/
def simplexAffineSSet (k : ℕ) :
    tupleSSet (OAI.SStd ℝ (Fin (k+1))) ⟶ TopCat.toSSet.obj (standardSimplexSpace k) where
  app n := ↾fun v => singularSimplexOfMap (simplexCombinationMap v)
  naturality {a b} f := by
    apply ConcreteCategory.hom_ext
    intro v
    apply (TopCat.toSSetObjEquiv _ b).injective
    apply ContinuousMap.ext
    intro t
    change simplexCombination (v ∘ f.unop.toOrderHom) t =
      simplexCombination v (OAI.SStd.map f.unop.toOrderHom t)
    exact simplexCombination_reindex v f.unop.toOrderHom t

abbrev simplexAffineChains (k : ℕ) :
    tupleChains (OAI.SStd ℝ (Fin (k+1))) ⟶
      integralSingularChains.obj (standardSimplexSpace k) :=
  SSet.chainComplexMap (simplexAffineSSet k) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)]
theorem tupleGen_affine {k n : ℕ} (v : Fin (n+1) → OAI.SStd ℝ (Fin (k+1))) :
    tupleGen v ≫ (simplexAffineChains k).f n =
      singularGen (singularSimplexOfMap (simplexCombinationMap v)) :=
  SSet.ι_chainComplexMap_f (X := tupleSSet _) (Y := TopCat.toSSet.obj _)
    (f := simplexAffineSSet k) (R := ModuleCat.of ℤ ℤ) (x := v)

def standardSimplexMap {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) :
    standardSimplexSpace k ⟶ standardSimplexSpace l :=
  TopCat.ofHom ⟨OAI.SStd.map f, OAI.SStd.continuous_map ℝ f⟩

/-- Interpolation is natural in affine maps of ambient simplex coordinates. -/
theorem simplexAffineSSet_naturality {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) :
    tupleSSetMap (OAI.SStd.map f) ≫ simplexAffineSSet l =
      simplexAffineSSet k ≫ TopCat.toSSet.map (standardSimplexMap f) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro v
  apply (TopCat.toSSetObjEquiv _ n).injective
  apply ContinuousMap.ext
  intro t
  change simplexCombination (OAI.SStd.map f ∘ v) t =
    OAI.SStd.map f (simplexCombination v t)
  exact (simplexCombination_map v f t).symm

@[reassoc]
theorem simplexAffineChains_naturality {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) :
    tupleChainMap (OAI.SStd.map f) ≫ simplexAffineChains l =
      simplexAffineChains k ≫ integralSingularChains.map (standardSimplexMap f) := by
  change integralSimplicialChains.map _ ≫ integralSimplicialChains.map _ =
    integralSimplicialChains.map _ ≫ integralSimplicialChains.map _
  rw [← Functor.map_comp, ← Functor.map_comp, simplexAffineSSet_naturality]

/-- The identity simplex is the interpolation of its actual vertices. -/
@[reassoc (attr := simp)]
theorem tupleGen_vertices_affine (n : ℕ) :
    tupleGen (OAI.SStd.single (R := ℝ) (X := Fin (n+1))) ≫ (simplexAffineChains n).f n =
      singularGen (singularSimplexOfMap (ContinuousMap.id _)) := by
  rw [tupleGen_affine]
  congr 2
  apply ContinuousMap.ext
  intro t
  exact simplexCombination_vertices t

end

open CategoryTheory Limits AlgebraicTopology Simplicial Convexity
section

/-- Barycentric subdivision followed by actual affine singular interpolation. -/
def simplexSubdivisionChains (k : ℕ) :
    tupleChains (OAI.SStd ℝ (Fin (k+1))) ⟶
      integralSingularChains.obj (standardSimplexSpace k) :=
  tupleSubdivision simplexTupleCenter ≫ simplexAffineChains k

/-- The corresponding interpolated chain homotopy components. -/
def simplexSubdivisionPrism (k n : ℕ) :
    (tupleChains (OAI.SStd ℝ (Fin (k+1)))).X n ⟶
      (integralSingularChains.obj (standardSimplexSpace k)).X (n+1) :=
  tupleSubdivisionPrism simplexTupleCenter n ≫ (simplexAffineChains k).f (n+1)

@[reassoc]
theorem simplexSubdivisionChains_naturality {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) :
    tupleChainMap (OAI.SStd.map f) ≫ simplexSubdivisionChains l =
      simplexSubdivisionChains k ≫ integralSingularChains.map (standardSimplexMap f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (tupleChainMap (OAI.SStd.map f)).f n ≫
      tupleSubdivisionMap simplexTupleCenter n ≫ (simplexAffineChains l).f n =
    (tupleSubdivisionMap simplexTupleCenter n ≫ (simplexAffineChains k).f n) ≫ _
  rw [← Category.assoc, ← tupleSubdivisionMap_naturality _ _ _ (simplexTupleCenter_map f)]
  rw [Category.assoc]
  have h := congrArg (fun g => g.f n) (simplexAffineChains_naturality f)
  change _ ≫ _ = _ ≫ _ at h
  rw [h, Category.assoc]

@[reassoc]
theorem simplexSubdivisionPrism_naturality {k l : ℕ} (f : Fin (k+1) → Fin (l+1)) (n : ℕ) :
    (tupleChainMap (OAI.SStd.map f)).f n ≫ simplexSubdivisionPrism l n =
      simplexSubdivisionPrism k n ≫ (integralSingularChains.map (standardSimplexMap f)).f (n+1) := by
  unfold simplexSubdivisionPrism
  rw [← Category.assoc, ← tupleSubdivisionPrism_naturality _ _ _ (simplexTupleCenter_map f)]
  rw [Category.assoc]
  have h := congrArg (fun g => g.f (n+1)) (simplexAffineChains_naturality f)
  change _ ≫ _ = _ ≫ _ at h
  rw [h, Category.assoc]

/-- The subdivided universal identity simplex, as a chain in that same simplex. -/
def universalSubdivision (n : ℕ) : ModuleCat.of ℤ ℤ ⟶
    (integralSingularChains.obj (standardSimplexSpace n)).X n :=
  tupleGen OAI.SStd.single ≫ (simplexSubdivisionChains n).f n

def universalSubdivisionPrism (n : ℕ) : ModuleCat.of ℤ ℤ ⟶
    (integralSingularChains.obj (standardSimplexSpace n)).X (n+1) :=
  tupleGen OAI.SStd.single ≫ simplexSubdivisionPrism n n

@[reassoc]
theorem universalSubdivision_boundary (n : ℕ) :
    universalSubdivision (n+1) ≫ (integralSingularChains.obj (standardSimplexSpace (n+1))).d (n+1) n =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        (universalSubdivision n ≫ (integralSingularChains.map (standardSimplexMap i.succAbove)).f n) := by
  unfold universalSubdivision
  rw [Category.assoc, (simplexSubdivisionChains (n+1)).comm, ← Category.assoc, tupleGen_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have h := congrArg (fun g => g.f n) (simplexSubdivisionChains_naturality i.succAbove)
  change _ ≫ _ = _ ≫ _ at h
  rw [← h, ← Category.assoc, tupleGen_map]
  have hv : (OAI.SStd.single (R := ℝ)) ∘ i.succAbove =
      OAI.SStd.map i.succAbove ∘ OAI.SStd.single := by
    funext j
    exact (OAI.SStd.map_single j i.succAbove).symm
  rw [hv]

@[simp]
theorem universalSubdivision_zero :
    universalSubdivision 0 = singularGen (singularSimplexOfMap (ContinuousMap.id _)) := by
  change tupleGen OAI.SStd.single ≫ tupleSubdivisionMap simplexTupleCenter 0 ≫ _ = _
  rw [tupleSubdivisionMap_zero, Category.id_comp, tupleGen_vertices_affine]

@[simp]
theorem universalSubdivisionPrism_zero : universalSubdivisionPrism 0 = 0 := by
  unfold universalSubdivisionPrism simplexSubdivisionPrism
  rw [tupleSubdivisionPrism_zero, zero_comp, comp_zero]

/-- The boundary of the universal prism includes the lower-dimensional prisms
on every oriented face. -/
theorem universalSubdivisionPrism_boundary (n : ℕ) :
    universalSubdivisionPrism (n+1) ≫
      (integralSingularChains.obj (standardSimplexSpace (n+1))).d (n+2) (n+1) =
      singularGen (singularSimplexOfMap (ContinuousMap.id _)) - universalSubdivision (n+1) -
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        (universalSubdivisionPrism n ≫
          (integralSingularChains.map (standardSimplexMap i.succAbove)).f (n+1)) := by
  unfold universalSubdivisionPrism simplexSubdivisionPrism
  simp only [Category.assoc]
  rw [(simplexAffineChains (n+1)).comm, ← Category.assoc (tupleSubdivisionPrism _ _),
    tupleSubdivisionPrism_equation]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.assoc,
    tupleGen_vertices_affine]
  change _ - universalSubdivision (n+1) - _ = _
  congr 1
  rw [← Category.assoc, tupleGen_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  change tupleGen _ ≫ simplexSubdivisionPrism (n+1) n =
    tupleGen _ ≫ simplexSubdivisionPrism n n ≫ _
  rw [← simplexSubdivisionPrism_naturality, ← Category.assoc, tupleGen_map]
  have hv : (OAI.SStd.single (R := ℝ)) ∘ i.succAbove =
      OAI.SStd.map i.succAbove ∘ OAI.SStd.single := by
    funext j
    exact (OAI.SStd.map_single j i.succAbove).symm
  rw [hv]

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Subdivision
attribute [-instance] _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSingularChainsIntoSmallRight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Singular subdivision, small-chain homotopies, and iterated mesh bounds. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial

section
variable {κ : Type} [Fintype κ]

/-- The ambient convex hull of a tuple's vertices. -/
def simplexTupleHull {n : ℕ} (v : Fin (n+1) → OAI.SStd ℝ κ) : Set (κ → ℝ) :=
  convexHull ℝ (Set.range (fun index => ⇑(v index).weights))

theorem simplexTupleHull_vertex {n : ℕ} (v : Fin (n+1) → OAI.SStd ℝ κ) (i : Fin (n+1)) :
    ⇑(v i).weights ∈ simplexTupleHull v := subset_convexHull ℝ _ (Set.mem_range_self i)

theorem simplexTupleHull_face {n : ℕ} (v : Fin (n+2) → OAI.SStd ℝ κ) (i : Fin (n+2)) :
    simplexTupleHull (v ∘ i.succAbove) ⊆ simplexTupleHull v := by
  apply convexHull_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨i.succAbove j, rfl⟩

theorem simplexTupleCenter_mem_hull {n : ℕ} (v : Fin (n+2) → OAI.SStd ℝ κ) :
    ⇑(simplexTupleCenter n v).weights ∈ simplexTupleHull v := by
  simp only [simplexTupleCenter, simplexCombination_coe]
  apply (convex_convexHull ℝ _).sum_mem
  · intro index _
    exact (OAI.SStd.barycenter (𝕜 := ℝ) (X := Fin (n+2))).weights_nonneg index
  · exact (OAI.SStd.barycenter (𝕜 := ℝ) (X := Fin (n+2))).total_of_fintype
  · intro index _
    exact simplexTupleHull_vertex v index

/-- The barycenter contraction estimate holds on the entire old convex hull. -/
theorem simplexTupleCenter_hull_dist_le {n : ℕ} (v : Fin (n+2) → OAI.SStd ℝ κ)
    (D : ℝ) (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (x : OAI.SStd ℝ κ) (hx : ⇑x.weights ∈ simplexTupleHull v) :
    dist (simplexTupleCenter n v) x ≤ ((n+1 : ℝ)/(n+2))*D := by
  have hs : simplexTupleHull v ⊆
      Metric.closedBall ⇑(simplexTupleCenter n v).weights (((n+1 : ℝ)/(n+2))*D) := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨i, rfl⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact simplexTupleCenter_vertex_dist_le n v D hv i
  exact (dist_comm _ _).le.trans (hs hx)

/-- Support condition recording both the original hull and the new mesh. -/
def tupleHullMesh {n m : ℕ} (v : Fin (n+1) → OAI.SStd ℝ κ) (D : ℝ)
    (w : Fin (m+1) → OAI.SStd ℝ κ) : Prop :=
  (∀ i, ⇑(w i).weights ∈ simplexTupleHull v) ∧ ∀ i j, dist (w i) (w j) ≤ D

/-- Every simplex in one barycentric subdivision has mesh at most n/(n+1)
times the old vertex mesh. Support is expressed in the actual free chain group. -/
theorem tupleSubdivision_mesh (n : ℕ) (v : Fin (n+1) → OAI.SStd ℝ κ)
    (D : ℝ) (hD : 0 ≤ D) (hv : ∀ i j, dist (v i) (v j) ≤ D) :
    tupleSubdivisionMap simplexTupleCenter n (tupleGen v (1 : ℤ)) ∈
      tupleChainSpan (tupleHullMesh v (((n : ℝ)/(n+1))*D)) := by
  induction n with
  | zero =>
    rw [tupleSubdivisionMap_zero]
    apply tupleGen_mem_span
    constructor
    · exact simplexTupleHull_vertex v
    · intro i j
      have he : i = j := Fin.ext (by omega)
      simp [he]
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
    rw [tupleSubdivision_gen_value]
    apply Submodule.sum_mem
    intro i hi
    refine (tupleChainSpan (tupleHullMesh v (((n+1 : ℝ)/(n+2))*D))).toAddSubgroup.zsmul_mem ?_ ((-1 : ℤ)^i.val)
    apply tupleCone_mem_span (simplexTupleCenter n v) (P := tupleHullMesh (v ∘ i.succAbove) (((n : ℝ)/(n+1))*D))
      (fun w hw => ?_) (ih (v ∘ i.succAbove) (fun a b => hv _ _))
    constructor
    · intro j
      cases j using Fin.cases with
      | zero => exact simplexTupleCenter_mem_hull v
      | succ j => exact simplexTupleHull_face v i (hw.1 j)
    · have hfactor : ((n : ℝ)/(n+1))*D ≤ ((n+1 : ℝ)/(n+2))*D := by
        apply mul_le_mul_of_nonneg_right _ hD
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      intro a b
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => simp only [dist_self]; positivity
        | succ b =>
          exact simplexTupleCenter_hull_dist_le v D hv (w b) (simplexTupleHull_face v i (hw.1 b))
      | succ a =>
        cases b using Fin.cases with
        | zero =>
          rw [dist_comm]
          exact simplexTupleCenter_hull_dist_le v D hv (w a) (simplexTupleHull_face v i (hw.1 a))
        | succ b => exact (hw.2 a b).trans hfactor

end

section

/-- The actual map represented by a singular simplex, with unlifted domain. -/
def singularSimplexTopMap {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) : standardSimplexSpace n ⟶ X :=
  TopCat.ofHom (TopCat.toSSetObjEquiv X _ σ)

@[reassoc (attr := simp)]
theorem singularGen_map {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularGen σ ≫ (integralSingularChains.map f).f n =
      singularGen ((TopCat.toSSet.map f).app _ σ) :=
  SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
    (f := TopCat.toSSet.map f) (R := ModuleCat.of ℤ ℤ) (x := σ)

@[reassoc]
theorem singularGen_boundary {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n+1⦌) :
    singularGen σ ≫ (integralSingularChains.obj X).d (n+1) n =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • singularGen ((TopCat.toSSet.obj X).δ i σ) :=
  SSet.ιChainComplex_d (X := TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ) (x := σ)

@[simp]
theorem singularSimplexTopMap_face {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n+1⦌) (i : Fin (n+2)) :
    singularSimplexTopMap ((TopCat.toSSet.obj X).δ i σ) =
      standardSimplexMap i.succAbove ≫ singularSimplexTopMap σ := rfl

@[simp]
theorem singularSimplexTopMap_map {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularSimplexTopMap ((TopCat.toSSet.map f).app _ σ) = singularSimplexTopMap σ ≫ f := rfl

@[reassoc (attr := simp)]
theorem singularGen_identity_map {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularGen (singularSimplexOfMap (ContinuousMap.id _)) ≫
      (integralSingularChains.map (singularSimplexTopMap σ)).f n = singularGen σ := by
  rw [singularGen_map]
  congr 1

/-- Barycentric subdivision on the existing integral singular chains. -/
def singularSubdivisionMap (X : TopCat.{0}) (n : ℕ) :
    (integralSingularChains.obj X).X n ⟶ (integralSingularChains.obj X).X n :=
  Sigma.desc (fun σ => universalSubdivision n ≫
    (integralSingularChains.map (singularSimplexTopMap σ)).f n)

@[reassoc (attr := simp)]
theorem singularGen_subdivision {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularGen σ ≫ singularSubdivisionMap X n = universalSubdivision n ≫
      (integralSingularChains.map (singularSimplexTopMap σ)).f n := by
  exact Sigma.ι_desc _ _

@[reassoc]
theorem singularSubdivisionMap_d (X : TopCat.{0}) (n : ℕ) :
    singularSubdivisionMap X (n+1) ≫ (integralSingularChains.obj X).d (n+1) n =
      (integralSingularChains.obj X).d (n+1) n ≫ singularSubdivisionMap X n := by
  apply singularChains_hom_ext
  intro σ
  rw [← Category.assoc, singularGen_subdivision, Category.assoc,
    (integralSingularChains.map (singularSimplexTopMap σ)).comm,
    ← Category.assoc, universalSubdivision_boundary]
  rw [← Category.assoc, singularGen_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, singularGen_subdivision,
    singularSimplexTopMap_face, Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]

/-- Constructed chain endomorphism, with no subdivision or excision hypothesis. -/
def singularSubdivision (X : TopCat.{0}) :
    integralSingularChains.obj X ⟶ integralSingularChains.obj X :=
  ChainComplex.ofHom (singularSubdivisionMap X) (singularSubdivisionMap_d X)

@[reassoc]
theorem singularSubdivision_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    integralSingularChains.map f ≫ singularSubdivision Y =
      singularSubdivision X ≫ integralSingularChains.map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply singularChains_hom_ext
  intro σ
  change singularGen σ ≫ (integralSingularChains.map f).f n ≫ singularSubdivisionMap Y n =
    singularGen σ ≫ singularSubdivisionMap X n ≫ (integralSingularChains.map f).f n
  simp only [singularGen_map_assoc, singularGen_subdivision, singularGen_subdivision_assoc,
    singularSimplexTopMap_map, Functor.map_comp, HomologicalComplex.comp_f]

/-- The universal prism transported along each actual singular simplex. -/
def singularSubdivisionPrism (X : TopCat.{0}) (n : ℕ) :
    (integralSingularChains.obj X).X n ⟶ (integralSingularChains.obj X).X (n+1) :=
  Sigma.desc (fun σ => universalSubdivisionPrism n ≫
    (integralSingularChains.map (singularSimplexTopMap σ)).f (n+1))

@[reassoc (attr := simp)]
theorem singularGen_prism {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularGen σ ≫ singularSubdivisionPrism X n = universalSubdivisionPrism n ≫
      (integralSingularChains.map (singularSimplexTopMap σ)).f (n+1) := by
  exact Sigma.ι_desc _ _

@[simp]
theorem singularSubdivisionPrism_zero (X : TopCat.{0}) : singularSubdivisionPrism X 0 = 0 := by
  apply singularChains_hom_ext
  intro σ
  rw [singularGen_prism, universalSubdivisionPrism_zero]
  simp only [zero_comp, comp_zero]

@[simp]
theorem singularSubdivisionMap_zero (X : TopCat.{0}) : singularSubdivisionMap X 0 = 𝟙 _ := by
  apply singularChains_hom_ext
  intro σ
  rw [singularGen_subdivision, universalSubdivision_zero, singularGen_identity_map]
  exact (Category.comp_id _).symm

/-- The chain homotopy equation on actual singular chains in all positive degrees. -/
theorem singularSubdivisionPrism_equation (X : TopCat.{0}) (n : ℕ) :
    singularSubdivisionPrism X (n+1) ≫ (integralSingularChains.obj X).d (n+2) (n+1) =
      𝟙 _ - singularSubdivisionMap X (n+1) -
      (integralSingularChains.obj X).d (n+1) n ≫ singularSubdivisionPrism X n := by
  apply singularChains_hom_ext
  intro σ
  rw [← Category.assoc, singularGen_prism, Category.assoc,
    (integralSingularChains.map (singularSimplexTopMap σ)).comm,
    ← Category.assoc, universalSubdivisionPrism_boundary]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub,
    singularGen_identity_map, singularGen_subdivision]
  congr 1
  rw [← Category.assoc, singularGen_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, singularGen_prism,
    singularSimplexTopMap_face, Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]

/-- An explicit homotopy between the identity and barycentric subdivision. -/
def singularSubdivisionHomotopy (X : TopCat.{0}) :
    Homotopy (𝟙 (integralSingularChains.obj X)) (singularSubdivision X) :=
  chainHomotopyOfComponents _ _ (singularSubdivisionPrism X)
    (by simp [singularSubdivision]) (fun n => by
      change 𝟙 _ = _ + _ + singularSubdivisionMap X (n+1)
      rw [singularSubdivisionPrism_equation]
      abel)

@[reassoc]
theorem singularSubdivisionPrism_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (integralSingularChains.map f).f n ≫ singularSubdivisionPrism Y n =
      singularSubdivisionPrism X n ≫ (integralSingularChains.map f).f (n+1) := by
  apply singularChains_hom_ext
  intro σ
  simp only [singularGen_map_assoc, singularGen_prism, singularGen_prism_assoc,
    singularSimplexTopMap_map, Functor.map_comp, HomologicalComplex.comp_f]

/-- Subdivision acts as the identity on actual integral singular homology. -/
theorem singularSubdivision_homologyMap (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (singularSubdivision X) n = 𝟙 _ := by
  rw [← (singularSubdivisionHomotopy X).homologyMap_eq, HomologicalComplex.homologyMap_id]

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Every singular simplex inside the image of a small simplex remains small.
The statement uses the entire simplex image, so it also controls the prism. -/
theorem smallSimplex_carrier {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    SSet.Subcomplex.range (TopCat.toSSet.map (singularSimplexTopMap σ.val)) ≤
      singularSubset U ⊔ singularSubset V := by
  intro m τ hτ
  obtain ⟨η, rfl⟩ := hτ
  have hσ := (mem_smallSingularSet_iff U V _ σ.val).mp σ.property
  rw [mem_smallSingularSet_iff]
  rcases hσ with hσ | hσ
  · left
    intro p
    exact hσ (ULift.up (singularSimplexMap m η p))
  · right
    intro p
    exact hσ (ULift.up (singularSimplexMap m η p))

def smallSimplexCarrier {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    TopCat.toSSet.obj (standardSimplexSpace n) ⟶ smallSingularSet U V :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (singularSimplexTopMap σ.val))
    (smallSimplex_carrier U V σ)

def smallSimplexChains {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    integralSingularChains.obj (standardSimplexSpace n) ⟶ smallSingularChains U V :=
  integralSimplicialChains.map (smallSimplexCarrier U V σ)

@[reassoc (attr := simp)]
theorem smallSimplexChains_inclusion {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    smallSimplexChains U V σ ≫ smallSingularChainInclusion U V =
      integralSingularChains.map (singularSimplexTopMap σ.val) := by
  erw [smallSimplexChains, smallSingularChainInclusion, ← Functor.map_comp]
  rfl

abbrev smallSingularGen {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    ModuleCat.of ℤ ℤ ⟶ (smallSingularChains U V).X n :=
  (smallSingularSet U V).ιChainComplex σ

/-- Maps from small chains are determined by their values on small singular simplices. -/
theorem smallSingularChains_hom_ext {n : ℕ} {T : ModuleCat.{0} ℤ}
    {f g : (smallSingularChains U V).X n ⟶ T}
    (h : ∀ σ : (smallSingularSet U V) _⦋n⦌,
      smallSingularGen U V σ ≫ f = smallSingularGen U V σ ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

@[reassoc (attr := simp)]
theorem smallSingularGen_inclusion {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    smallSingularGen U V σ ≫ (smallSingularChainInclusion U V).f n = singularGen σ.val :=
  SSet.ι_chainComplexMap_f (X := smallSingularSet U V) (Y := TopCat.toSSet.obj _)
    (f := (singularSubset U ⊔ singularSubset V).ι) (R := ModuleCat.of ℤ ℤ) (x := σ)

/-- Subdivision restricted to the actual small chain groups. -/
def smallSubdivisionMap (n : ℕ) : (smallSingularChains U V).X n ⟶ (smallSingularChains U V).X n :=
  Sigma.desc (fun σ => universalSubdivision n ≫ (smallSimplexChains U V σ).f n)

/-- The prism restricted to the same small chain groups. -/
def smallSubdivisionPrism (n : ℕ) :
    (smallSingularChains U V).X n ⟶ (smallSingularChains U V).X (n+1) :=
  Sigma.desc (fun σ => universalSubdivisionPrism n ≫ (smallSimplexChains U V σ).f (n+1))

@[reassoc (attr := simp)]
theorem smallGen_subdivision {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    smallSingularGen U V σ ≫ smallSubdivisionMap U V n =
      universalSubdivision n ≫ (smallSimplexChains U V σ).f n := by
  exact Sigma.ι_desc _ _

@[reassoc (attr := simp)]
theorem smallGen_prism {n : ℕ} (σ : (smallSingularSet U V) _⦋n⦌) :
    smallSingularGen U V σ ≫ smallSubdivisionPrism U V n =
      universalSubdivisionPrism n ≫ (smallSimplexChains U V σ).f (n+1) := by
  exact Sigma.ι_desc _ _

@[reassoc]
theorem smallSubdivisionMap_inclusion (n : ℕ) :
    smallSubdivisionMap U V n ≫ (smallSingularChainInclusion U V).f n =
      (smallSingularChainInclusion U V).f n ≫ singularSubdivisionMap (TopCat.of X) n := by
  apply smallSingularChains_hom_ext
  intro σ
  rw [← Category.assoc, smallGen_subdivision, Category.assoc]
  have h := congrArg (fun f => f.f n) (smallSimplexChains_inclusion U V σ)
  change _ ≫ _ = _ at h
  rw [h, smallSingularGen_inclusion_assoc, singularGen_subdivision]

@[reassoc]
theorem smallSubdivisionPrism_inclusion (n : ℕ) :
    smallSubdivisionPrism U V n ≫ (smallSingularChainInclusion U V).f (n+1) =
      (smallSingularChainInclusion U V).f n ≫ singularSubdivisionPrism (TopCat.of X) n := by
  apply smallSingularChains_hom_ext
  intro σ
  rw [← Category.assoc, smallGen_prism, Category.assoc]
  have h := congrArg (fun f => f.f (n+1)) (smallSimplexChains_inclusion U V σ)
  change _ ≫ _ = _ at h
  rw [h, smallSingularGen_inclusion_assoc, singularGen_prism]

/-- The restriction remains a chain map, proved by injectivity of inclusion. -/
theorem smallSubdivisionMap_d (n : ℕ) :
    smallSubdivisionMap U V (n+1) ≫ (smallSingularChains U V).d (n+1) n =
      (smallSingularChains U V).d (n+1) n ≫ smallSubdivisionMap U V n := by
  apply (cancel_mono ((smallSingularChainInclusion U V).f n)).mp
  simp only [Category.assoc, ← (smallSingularChainInclusion U V).comm_assoc,
    ← (smallSingularChainInclusion U V).comm, smallSubdivisionMap_inclusion,
    smallSubdivisionMap_inclusion_assoc, singularSubdivisionMap_d]

def smallSubdivision : smallSingularChains U V ⟶ smallSingularChains U V :=
  ChainComplex.ofHom (smallSubdivisionMap U V) (smallSubdivisionMap_d U V)

end

section

/-- Composition of affine interpolations is affine interpolation of the images. -/
theorem simplexCombination_assoc {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (w : κ → OAI.SStd ℝ μ) (v : ι → OAI.SStd ℝ κ) (t : OAI.SStd ℝ ι) :
    simplexCombination w (simplexCombination v t) =
      simplexCombination (simplexCombination w ∘ v) t := by
  apply Subtype.ext; funext m
  simp only [simplexCombination, Function.comp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

@[simp]
theorem simplexTupleCenter_combination {ι κ : Type} [Fintype ι] [Fintype κ]
    (w : ι → OAI.SStd ℝ κ) (n : ℕ) (v : Fin (n+2) → OAI.SStd ℝ ι) :
    simplexCombination w (simplexTupleCenter n v) =
      simplexTupleCenter n (simplexCombination w ∘ v) :=
  simplexCombination_assoc w v _

/-- Naturality of interpolation for all affine simplex maps, not only cofaces. -/
theorem simplexAffineChains_combination {k l : ℕ}
    (v : Fin (k+1) → OAI.SStd ℝ (Fin (l+1))) :
    tupleChainMap (simplexCombination v) ≫ simplexAffineChains l =
      simplexAffineChains k ≫ integralSingularChains.map (TopCat.ofHom (simplexCombinationMap v)) := by
  have hs : tupleSSetMap (simplexCombination v) ≫ simplexAffineSSet l =
      simplexAffineSSet k ≫ TopCat.toSSet.map (TopCat.ofHom (simplexCombinationMap v)) := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro w
    apply (TopCat.toSSetObjEquiv _ n).injective
    apply ContinuousMap.ext
    intro t
    change simplexCombination (simplexCombination v ∘ w) t = simplexCombination v (simplexCombination w t)
    exact (simplexCombination_assoc v w t).symm
  change integralSimplicialChains.map _ ≫ integralSimplicialChains.map _ =
    integralSimplicialChains.map _ ≫ integralSimplicialChains.map _
  rw [← Functor.map_comp, ← Functor.map_comp, hs]

/-- Interpolation intertwines tuple subdivision with singular subdivision.
This is needed for iterating the geometric mesh estimate. -/
theorem simplexAffineChains_subdivision (k : ℕ) :
    simplexAffineChains k ≫ singularSubdivision (standardSimplexSpace k) =
      tupleSubdivision simplexTupleCenter ≫ simplexAffineChains k := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply tupleChains_hom_ext
  intro v
  change tupleGen v ≫ (simplexAffineChains k).f n ≫ singularSubdivisionMap _ n =
    tupleGen v ≫ tupleSubdivisionMap simplexTupleCenter n ≫ (simplexAffineChains k).f n
  rw [tupleGen_affine_assoc, singularGen_subdivision]
  change universalSubdivision n ≫
    (integralSingularChains.map (TopCat.ofHom (simplexCombinationMap v))).f n = _
  unfold universalSubdivision simplexSubdivisionChains
  change (tupleGen OAI.SStd.single ≫ tupleSubdivisionMap simplexTupleCenter n ≫
    (simplexAffineChains n).f n) ≫ _ = _
  have ha := congrArg (fun f => f.f n) (simplexAffineChains_combination v)
  change _ ≫ _ = _ ≫ _ at ha
  simp only [Category.assoc]
  rw [← ha, ← Category.assoc (tupleSubdivisionMap simplexTupleCenter n),
    tupleSubdivisionMap_naturality _ _ _ (simplexTupleCenter_combination v)]
  simp only [Category.assoc, tupleGen_map_assoc]
  have hv : simplexCombination v ∘ OAI.SStd.single = v := by
    funext i
    exact simplexCombination_vertex v i
  rw [hv]

variable {X : Type} [TopologicalSpace X] (U V : Set X)

@[simp]
theorem smallSubdivisionMap_zero : smallSubdivisionMap U V 0 = 𝟙 _ := by
  apply (cancel_mono ((smallSingularChainInclusion U V).f 0)).mp
  rw [smallSubdivisionMap_inclusion, singularSubdivisionMap_zero]
  simp only [Category.comp_id, Category.id_comp]

@[simp]
theorem smallSubdivisionPrism_zero : smallSubdivisionPrism U V 0 = 0 := by
  apply (cancel_mono ((smallSingularChainInclusion U V).f 1)).mp
  rw [smallSubdivisionPrism_inclusion, singularSubdivisionPrism_zero]
  simp only [zero_comp, comp_zero]

/-- The homotopy equation also holds before inclusion into full chains. -/
theorem smallSubdivisionPrism_equation (n : ℕ) :
    smallSubdivisionPrism U V (n+1) ≫ (smallSingularChains U V).d (n+2) (n+1) =
      𝟙 _ - smallSubdivisionMap U V (n+1) -
      (smallSingularChains U V).d (n+1) n ≫ smallSubdivisionPrism U V n := by
  apply (cancel_mono ((smallSingularChainInclusion U V).f (n+1))).mp
  simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
    ← (smallSingularChainInclusion U V).comm,
    smallSubdivisionPrism_inclusion_assoc, smallSubdivisionMap_inclusion,
    smallSubdivisionPrism_inclusion, singularSubdivisionPrism_equation,
    Preadditive.comp_sub, Category.comp_id]
  rw [(smallSingularChainInclusion U V).comm_assoc]

def smallSubdivisionHomotopy : Homotopy (𝟙 (smallSingularChains U V)) (smallSubdivision U V) :=
  chainHomotopyOfComponents _ _ (smallSubdivisionPrism U V)
    (by simp [smallSubdivision]) (fun n => by
      change 𝟙 _ = _ + _ + smallSubdivisionMap U V (n+1)
      rw [smallSubdivisionPrism_equation]
      abel)

/-- Small-chain subdivision induces the identity on homology, without any
cover hypothesis. Comparison to full homology still needs eventual smallness. -/
theorem smallSubdivision_homologyMap (n : ℕ) :
    HomologicalComplex.homologyMap (smallSubdivision U V) n = 𝟙 _ := by
  rw [← (smallSubdivisionHomotopy U V).homologyMap_eq, HomologicalComplex.homologyMap_id]

@[reassoc]
theorem smallSubdivision_inclusion :
    smallSubdivision U V ≫ smallSingularChainInclusion U V =
      smallSingularChainInclusion U V ≫ singularSubdivision (TopCat.of X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact smallSubdivisionMap_inclusion U V n

end

variable {κ : Type} [Fintype κ]

def tupleMeshSpan (n : ℕ) (D : ℝ) :
    Submodule ℤ ((tupleChains (OAI.SStd ℝ κ)).X n) :=
  tupleChainSpan (fun v => ∀ i j, dist (v i) (v j) ≤ D)

/-- Subdivision contracts the mesh of an arbitrary supported affine chain. -/
theorem tupleSubdivision_mem_mesh {n : ℕ} (D : ℝ) (hD : 0 ≤ D)
    {c : (tupleChains (OAI.SStd ℝ κ)).X n} (hc : c ∈ tupleMeshSpan n D) :
    tupleSubdivisionMap simplexTupleCenter n c ∈ tupleMeshSpan n (((n : ℝ)/(n+1))*D) := by
  refine tupleChainSpan_map (tupleSubdivisionMap simplexTupleCenter n) (fun v hv => ?_) hc
  exact tupleChainSpan_mono (fun w hw => hw.2) (tupleSubdivision_mesh n v D hD hv)

/-- Actual geometric decay for every iterated barycentric subdivision,
including repeated or degenerate vertices and the degree-zero case. -/
theorem tupleSubdivision_iterate_mesh {n : ℕ} (D : ℝ) (hD : 0 ≤ D)
    {c : (tupleChains (OAI.SStd ℝ κ)).X n} (hc : c ∈ tupleMeshSpan n D) (k : ℕ) :
    (tupleSubdivisionMap simplexTupleCenter n)^[k] c ∈
      tupleMeshSpan n (D * ((n : ℝ)/(n+1))^k) := by
  induction k with
  | zero => simpa only [Function.iterate_zero_apply, pow_zero, mul_one] using hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := tupleSubdivision_mem_mesh (D * ((n : ℝ)/(n+1))^k) (by positivity) ih
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf

/-- The universal vertex tuple starts with mesh at most one in the actual
sup metric of the library's standard simplex. -/
theorem simplexVertices_mem_mesh (n : ℕ) :
    tupleGen (OAI.SStd.single (R := ℝ) (X := Fin (n+1))) (1 : ℤ) ∈
      tupleMeshSpan n 1 := by
  apply tupleGen_mem_span
  intro i j
  change dist (⇑(OAI.SStd.single (R := ℝ) i).weights)
    (⇑(OAI.SStd.single (R := ℝ) j).weights) ≤ 1
  apply (dist_pi_le_iff (by norm_num)).mpr
  intro index
  simp only [OAI.SStd.weights_single, Finsupp.single_apply]
  split_ifs <;> norm_num

/-- Geometric mesh estimate for the universal subdivided simplex. -/
theorem universalTupleSubdivision_mesh (n k : ℕ) :
    (tupleSubdivisionMap simplexTupleCenter n)^[k]
      (tupleGen (OAI.SStd.single (R := ℝ) (X := Fin (n+1))) (1 : ℤ)) ∈
      tupleMeshSpan n (((n : ℝ)/(n+1))^k) := by
  simpa only [one_mul] using tupleSubdivision_iterate_mesh 1 (by norm_num) (simplexVertices_mem_mesh n) k

/-- The mesh factor is strictly less than one in every fixed degree. -/
theorem simplexMeshFactor_lt_one (n : ℕ) : (n : ℝ)/(n+1) < 1 := by
  apply (div_lt_one (by positivity)).mpr
  linarith

end

open CategoryTheory Limits AlgebraicTopology Simplicial
section

/-- Iteration on an actual singular simplex agrees with the constructed
iterated affine subdivision inside its domain. -/
theorem singularSubdivision_iterate_gen {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (k : ℕ) :
    (singularSubdivisionMap X n)^[k] (singularGen σ (1 : ℤ)) =
      (integralSingularChains.map (singularSimplexTopMap σ)).f n
        ((simplexAffineChains n).f n
          ((tupleSubdivisionMap simplexTupleCenter n)^[k]
            (tupleGen (OAI.SStd.single (R := ℝ) (X := Fin (n+1))) (1 : ℤ)))) := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply]
    have h := tupleGen_vertices_affine n
    have h' := singularGen_identity_map σ
    exact (ConcreteCategory.congr_hom (by
      rw [← Category.assoc, h]
      exact h' : tupleGen OAI.SStd.single ≫ (simplexAffineChains n).f n ≫
        (integralSingularChains.map (singularSimplexTopMap σ)).f n = singularGen σ) (1 : ℤ)).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    have h := congrArg (fun f => f.f n) (simplexAffineChains_subdivision n)
    have h' := congrArg (fun f => f.f n) (singularSubdivision_naturality (singularSimplexTopMap σ))
    change (simplexAffineChains n).f n ≫ singularSubdivisionMap _ n =
      tupleSubdivisionMap simplexTupleCenter n ≫ (simplexAffineChains n).f n at h
    change (integralSingularChains.map (singularSimplexTopMap σ)).f n ≫ singularSubdivisionMap X n =
      singularSubdivisionMap _ n ≫ (integralSingularChains.map (singularSimplexTopMap σ)).f n at h'
    rw [← ModuleCat.comp_apply, h', ModuleCat.comp_apply,
      ← ModuleCat.comp_apply ((simplexAffineChains n).f n), h, ModuleCat.comp_apply]

/-- A singular generator that is small belongs to the actual image of the
small-chain inclusion. -/
theorem small_singularGen_mem_range {X : Type} [TopologicalSpace X] (U V : Set X)
    {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌)
    (hσ : σ ∈ (singularSubset U ⊔ singularSubset V).obj (Opposite.op ⦋n⦌)) :
    singularGen σ (1 : ℤ) ∈ LinearMap.range ((smallSingularChainInclusion U V).f n).hom := by
  refine ⟨smallSingularGen U V ⟨σ, hσ⟩ (1 : ℤ), ?_⟩
  exact ConcreteCategory.congr_hom (smallSingularGen_inclusion U V ⟨σ, hσ⟩) (1 : ℤ)

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Smallness
attribute [-instance] _root_.OAI.Kaplansky.instMonoChainComplexModuleCatIntNatSingularChainsIntoSmallRight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Eventual smallness of generators and chains and comparison on homology. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial

section
variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Every actual singular simplex becomes a chain of small simplices after
sufficiently many applications of the constructed subdivision operator. -/
theorem singularGen_eventually_small (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌) :
    ∃ N : ℕ, ∀ k ≥ N, (singularSubdivisionMap (TopCat.of X) n)^[k]
      (singularGen σ (1 : ℤ)) ∈ LinearMap.range ((smallSingularChainInclusion U V).f n).hom := by
  let c : ℝ := (n : ℝ)/(n+1)
  obtain ⟨N, hN⟩ := finite_continuousMaps_eventually_small ({()} : Finset Unit)
    (fun _ : Unit => TopCat.toSSetObjEquiv (TopCat.of X) _ σ)
    U V hU hV hUV 1 c (by positivity) (simplexMeshFactor_lt_one n)
  refine ⟨N, fun k hk => ?_⟩
  rw [singularSubdivision_iterate_gen]
  let L := (simplexAffineChains n).f n ≫ (integralSingularChains.map (singularSimplexTopMap σ)).f n
  have hspan : tupleMeshSpan n (c^k) ≤
      (LinearMap.range ((smallSingularChainInclusion U V).f n).hom).comap L.hom := by
    apply Submodule.span_le.mpr
    rintro a ⟨v, hv, rfl⟩
    change L.hom (tupleGen v (1 : ℤ)) ∈ LinearMap.range ((smallSingularChainInclusion U V).f n).hom
    dsimp only [L]
    change (tupleGen v ≫ (simplexAffineChains n).f n ≫
      (integralSingularChains.map (singularSimplexTopMap σ)).f n) (1 : ℤ) ∈ LinearMap.range ((smallSingularChainInclusion U V).f n).hom
    rw [tupleGen_affine_assoc, singularGen_map]
    apply small_singularGen_mem_range
    rw [mem_smallSingularSet_iff]
    have hmesh : ∀ a ∈ Set.range (simplexCombination v), ∀ b ∈ Set.range (simplexCombination v),
        dist a b ≤ 1 * c^k := by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      simpa only [one_mul] using simplexCombination_pair_dist_le v s t (c^k) hv
    have h := hN k hk () (Finset.mem_singleton_self ()) _ hmesh
    rcases h with h | h
    · left
      intro p
      exact h _ ⟨p.down, rfl⟩
    · right
      intro p
      exact h _ ⟨p.down, rfl⟩
  exact hspan (universalTupleSubdivision_mesh n k)

end

/-- Every singular chain is generated by finitely many integral simplex generators.
This uses the actual coproduct universal property, with no support premise. -/
theorem singularChain_submodule_eq_top {X : TopCat.{0}} (n : ℕ)
    (S : Submodule ℤ ((integralSingularChains.obj X).X n))
    (hS : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌, singularGen σ (1 : ℤ) ∈ S) : S = ⊤ := by
  let : Module ℤ (((integralSingularChains.obj X).X n) ⧸ S) := Submodule.Quotient.module S
  let q : (integralSingularChains.obj X).X n ⟶ ModuleCat.of ℤ (((integralSingularChains.obj X).X n) ⧸ S) := ModuleCat.ofHom S.mkQ
  have hq : q = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change S.mkQ (singularGen σ (1 : ℤ)) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hS σ)
  apply top_unique
  intro a ha
  apply (Submodule.Quotient.mk_eq_zero S).mp
  exact ConcreteCategory.congr_hom hq a

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Chains whose iterated subdivisions eventually lie in the actual image
of the small-chain inclusion. -/
def eventuallySmallChains (n : ℕ) : Submodule ℤ ((integralSingularChains.obj (TopCat.of X)).X n) where
  carrier := {a | ∃ N : ℕ, ∀ k ≥ N, (singularSubdivisionMap (TopCat.of X) n)^[k] a ∈
    LinearMap.range ((smallSingularChainInclusion U V).f n).hom}
  zero_mem' := by
    refine ⟨0, fun k hk => ?_⟩
    rw [← Module.End.pow_apply ((singularSubdivisionMap (TopCat.of X) n).hom)]
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    rintro a b ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, fun k hk => ?_⟩
    rw [← Module.End.pow_apply ((singularSubdivisionMap (TopCat.of X) n).hom)]
    rw [map_add]
    simp only [Module.End.pow_apply]
    exact Submodule.add_mem _ (hN k ((le_max_left N M).trans hk)) (hM k ((le_max_right N M).trans hk))
  smul_mem' := by
    rintro r a ⟨N, hN⟩
    refine ⟨N, fun k hk => ?_⟩
    rw [← Module.End.pow_apply ((singularSubdivisionMap (TopCat.of X) n).hom)]
    rw [((singularSubdivisionMap (TopCat.of X) n).hom ^ k).map_smul]
    simp only [Module.End.pow_apply]
    exact Submodule.smul_mem _ r (hN k hk)

/-- The actual open-cover smallness theorem for every finite singular chain. -/
theorem singularChain_eventually_small (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ)
    (a : (integralSingularChains.obj (TopCat.of X)).X n) :
    ∃ N : ℕ, ∀ k ≥ N, (singularSubdivisionMap (TopCat.of X) n)^[k] a ∈
      LinearMap.range ((smallSingularChainInclusion U V).f n).hom := by
  have h : eventuallySmallChains U V n = ⊤ :=
    singularChain_submodule_eq_top n _ (fun σ => singularGen_eventually_small U V hU hV hUV σ)
  change a ∈ eventuallySmallChains U V n
  rw [h]
  trivial

end

section
open CategoryTheory Limits HomologicalComplex

theorem chainNext_nat (n : ℕ) : (ComplexShape.down ℕ).next n = n-1 := by
  cases n <;> simp only [ChainComplex.next_nat_zero, ChainComplex.next_nat_succ, Nat.zero_sub, Nat.add_sub_cancel]

/-- An actual cycle represented by its underlying chain. -/
def chainCycle (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (a : K.X n) (ha : K.d n (n-1) a = 0) : K.cycles n :=
  (K.sc n).moduleCatCyclesIso.inv ⟨a, by
    change K.d n ((ComplexShape.down ℕ).next n) a = 0
    rwa [chainNext_nat]⟩

@[simp]
theorem chainCycle_i (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (a : K.X n) (ha : K.d n (n-1) a = 0) :
    K.iCycles n (chainCycle K n a ha) = a := by
  exact (K.sc n).moduleCatCyclesIso_inv_iCycles_apply ⟨a, by
    change K.d n ((ComplexShape.down ℕ).next n) a = 0
    rwa [chainNext_nat]⟩

theorem chain_cycle_boundary_zero (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (z : K.cycles n) : K.d n (n-1) (K.iCycles n z) = 0 :=
  ConcreteCategory.congr_hom (K.iCycles_d n (n-1)) z

/-- A homology class is zero exactly when its representative cycle is a boundary. -/
theorem chain_homologyπ_eq_zero_iff (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (z : K.cycles n) : K.homologyπ n z = 0 ↔
      ∃ b : K.X (n+1), K.d (n+1) n b = K.iCycles n z := by
  have hi := (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  rw [← hi.eq_iff, map_zero]
  change ((K.homologyπ n ≫ K.homologyι n) z = 0) ↔ _
  rw [K.homology_π_ι]
  have h := (K.sc n).moduleCat_pOpcycles_eq_zero_iff (K.iCycles n z)
  change (K.pOpcycles n (K.iCycles n z) = 0) ↔
    ∃ b : K.X ((ComplexShape.down ℕ).prev n), K.d _ n b = K.iCycles n z at h
  rw [ChainComplex.prev ℕ n] at h
  exact h

@[simp]
theorem chain_cyclesMap_i {P Q : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : P ⟶ Q)
    (n : ℕ) (z : P.cycles n) :
    Q.iCycles n (cyclesMap f n z) = f.f n (P.iCycles n z) :=
  ConcreteCategory.congr_hom (cyclesMap_i f n) z

@[simp]
theorem chain_homologyMap_π {P Q : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : P ⟶ Q)
    (n : ℕ) (z : P.cycles n) :
    homologyMap f n (P.homologyπ n z) = Q.homologyπ n (cyclesMap f n z) :=
  ConcreteCategory.congr_hom (homologyπ_naturality f n) z

/-- Iterates of an actual chain endomorphism. -/
def chainIterate {K : ChainComplex (ModuleCat.{0} ℤ) ℕ} (s : K ⟶ K) : ℕ → (K ⟶ K)
  | 0 => 𝟙 _
  | k+1 => chainIterate s k ≫ s

@[simp]
theorem chainIterate_f_apply {K : ChainComplex (ModuleCat.{0} ℤ) ℕ} (s : K ⟶ K)
    (k n : ℕ) (a : K.X n) : (chainIterate s k).f n a = (s.f n)^[k] a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change s.f n ((chainIterate s k).f n a) = _
    rw [ih, Function.iterate_succ_apply']

theorem chainIterate_homologyMap {K : ChainComplex (ModuleCat.{0} ℤ) ℕ} (s : K ⟶ K)
    (hs : ∀ n, homologyMap s n = 𝟙 _) (k n : ℕ) :
    homologyMap (chainIterate s k) n = 𝟙 _ := by
  induction k with
  | zero => exact homologyMap_id K n
  | succ k ih => rw [chainIterate, homologyMap_comp, ih, hs, Category.id_comp]

theorem chainIterate_commute {P Q : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : P ⟶ Q) (s : P ⟶ P) (t : Q ⟶ Q) (h : s ≫ f = f ≫ t) (k : ℕ) :
    chainIterate s k ≫ f = f ≫ chainIterate t k := by
  induction k with
  | zero => simp only [chainIterate, Category.id_comp, Category.comp_id]
  | succ k ih => rw [chainIterate, chainIterate, Category.assoc, h, ← Category.assoc, ih, Category.assoc]

end

open CategoryTheory Limits HomologicalComplex
section

/-- A monomorphic chain comparison is a quasi-isomorphism if compatible
endomorphisms induce the identity on homology and eventually carry every
chain into its image. All premises are discharged by subdivision below. -/
theorem quasiIso_of_eventual_image
    {P Q : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : P ⟶ Q) [Mono f]
    (s : P ⟶ P) (t : Q ⟶ Q) (hcomm : s ≫ f = f ≫ t)
    (hs : ∀ n, homologyMap s n = 𝟙 _) (ht : ∀ n, homologyMap t n = 𝟙 _)
    (hevent : ∀ n (a : Q.X n), ∃ k, (chainIterate t k).f n a ∈ LinearMap.range (f.f n).hom) :
    QuasiIso f := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro y hy
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (P.homologyπ n)).mp inferInstance y
    rw [chain_homologyMap_π] at hy
    obtain ⟨b, hb⟩ := (chain_homologyπ_eq_zero_iff Q n (cyclesMap f n z)).mp hy
    rw [chain_cyclesMap_i] at hb
    obtain ⟨k, w, hw⟩ := hevent (n+1) b
    have ha : P.d (n+1) n w = (chainIterate s k).f n (P.iCycles n z) := by
      apply (ModuleCat.mono_iff_injective (f.f n)).mp inferInstance
      have hc := ConcreteCategory.congr_hom (congrArg (fun g => g.f n)
        (chainIterate_commute f s t hcomm k)) (P.iCycles n z)
      change f.f n ((chainIterate s k).f n (P.iCycles n z)) =
        (chainIterate t k).f n (f.f n (P.iCycles n z)) at hc
      rw [hc, ← hb]
      rw [← ModuleCat.comp_apply, ← f.comm, ModuleCat.comp_apply, hw,
        ← ModuleCat.comp_apply, (chainIterate t k).comm, ModuleCat.comp_apply]
    have hz : P.homologyπ n (cyclesMap (chainIterate s k) n z) = 0 :=
      (chain_homologyπ_eq_zero_iff P n _).mpr ⟨w, by simpa using ha⟩
    rw [← chain_homologyMap_π, chainIterate_homologyMap s hs] at hz
    exact hz
  · intro y
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ n)).mp inferInstance y
    obtain ⟨k, a, ha⟩ := hevent n (Q.iCycles n z)
    have hda : P.d n (n-1) a = 0 := by
      apply (ModuleCat.mono_iff_injective (f.f (n-1))).mp inferInstance
      rw [map_zero, ← ModuleCat.comp_apply, ← f.comm, ModuleCat.comp_apply, ha]
      rw [← chain_cyclesMap_i]
      exact chain_cycle_boundary_zero Q n _
    let w := chainCycle P n a hda
    have hw : cyclesMap f n w = cyclesMap (chainIterate t k) n z := by
      apply (ModuleCat.mono_iff_injective (Q.iCycles n)).mp inferInstance
      rw [chain_cyclesMap_i, chain_cyclesMap_i, chainCycle_i, ha]
    refine ⟨P.homologyπ n w, ?_⟩
    rw [chain_homologyMap_π, hw, ← chain_homologyMap_π, chainIterate_homologyMap t ht]
    rfl

/-- The two-set open-cover theorem for the actual integral singular chain
complex: the inclusion of small chains is a quasi-isomorphism. -/
theorem smallSingularChainInclusion_quasiIso {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    QuasiIso (smallSingularChainInclusion U V) := by
  apply quasiIso_of_eventual_image (smallSingularChainInclusion U V)
    (smallSubdivision U V) (singularSubdivision (TopCat.of X))
    (smallSubdivision_inclusion U V) (smallSubdivision_homologyMap U V)
    (singularSubdivision_homologyMap (TopCat.of X))
  intro n a
  obtain ⟨N, hN⟩ := singularChain_eventually_small U V hU hV hUV n a
  refine ⟨N, ?_⟩
  rw [chainIterate_f_apply]
  exact hN N le_rfl

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.ComplexBundle_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Pullback line bundles and their continuous chart identifications. -/

open Bundle Topology
namespace Kaplansky
variable {B A S : Type} [TopologicalSpace B] [TopologicalSpace A]
  [Fintype S] {J : S → Type}
  (C : ∀ s, VectorBundleCore ℂ B ℂ (J s)) (U : Set B) (e : U ≃ₜ A)

def chartBaseMap : C(A,B) :=
  ⟨fun a => (e.symm a).val, continuous_subtype_val.comp e.symm.continuous⟩

end Kaplansky

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

section
open CategoryTheory Limits
variable {X : Type} [TopologicalSpace X] (U : Set X) (x : X) (hx : x ∈ U)

/-- The punctured subspace and its ambient intersection have the same
inherited topology, with the same underlying points. -/
def puncturedChartIntersectionHomeomorph (U : Set X) (x : X) (hx : x ∈ U) :
    ({⟨x, hx⟩}ᶜ : Set U) ≃ₜ ↥(U ∩ ({x}ᶜ : Set X)) := by
  let f : ({⟨x, hx⟩}ᶜ : Set U) → ↥(U ∩ ({x}ᶜ : Set X)) := fun p =>
    ⟨p.val.val, p.val.property, fun he => p.property (Subtype.ext he)⟩
  let g : ↥(U ∩ ({x}ᶜ : Set X)) → ({⟨x, hx⟩}ᶜ : Set U) := fun p =>
    ⟨⟨p.val, p.property.1⟩, fun he => p.property.2 (congrArg Subtype.val he)⟩
  refine
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · exact (continuous_subtype_val.subtype_mk _).subtype_mk _

def puncturedChartRelativeChainsIso :
    relativeSingularChains (subspaceInclusion ({⟨x, hx⟩}ᶜ : Set U)) ≅
      relativeSingularChains (subspaceInclusionOfLE
        (Set.inter_subset_left : U ∩ ({x}ᶜ : Set X) ⊆ U)) :=
  cokernel.mapIso _ _
    (integralSingularChains.mapIso (TopCat.isoOfHomeo
      (puncturedChartIntersectionHomeomorph U x hx))) (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom]
      rw [← Functor.map_comp]
      rfl)

def chartRelativeChainInclusion :
    relativeSingularChains (subspaceInclusion ({⟨x, hx⟩}ᶜ : Set U)) ⟶
      relativeSingularChains (subspaceInclusion ({x}ᶜ : Set X)) :=
  relativeChainMap _ _
    (subspaceMap _ _ ⟨Subtype.val, continuous_subtype_val⟩ (by
      intro p hp he
      exact hp (Subtype.ext he)))
    (subspaceInclusion U) (subspaceMap_square _ _ _ _)

/-- Local relative chains are isomorphic to the small relative chains
of the actual cover by the chart and the punctured ambient space. -/
def chartSmallRelativeChainsIso :
    relativeSingularChains (subspaceInclusion ({⟨x, hx⟩}ᶜ : Set U)) ≅
      smallRelativeChains U ({x}ᶜ : Set X) :=
  puncturedChartRelativeChainsIso U x hx ≪≫ smallRelativeExcisionIso U ({x}ᶜ : Set X)

theorem chartSmallRelativeChainsIso_comparison :
    (chartSmallRelativeChainsIso U x hx).hom ≫
        smallRelativeComparison U ({x}ᶜ : Set X) = chartRelativeChainInclusion U x hx := by
  simp only [chartSmallRelativeChainsIso, Iso.trans_hom, Category.assoc,
    smallRelativeExcision_comparison]
  apply (cancel_epi (relativeChainProjection (subspaceInclusion
    ({⟨x, hx⟩}ᶜ : Set U)))).mp
  simp only [puncturedChartRelativeChainsIso, relativeChainProjection,
    chartRelativeChainInclusion, relativeChainMap, cokernel.mapIso_hom, Iso.refl_hom]
  erw [cokernel.π_desc_assoc, Category.id_comp, cokernel.π_desc, cokernel.π_desc]

omit [TopologicalSpace X] in
theorem chart_punctured_cover (U : Set X) (x : X) (hx : x ∈ U) :
    U ∪ ({x}ᶜ : Set X) = Set.univ := by
  ext y
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  by_cases h : y = x
  · exact Or.inl (h ▸ hx)
  · exact Or.inr h

end

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

end

open CategoryTheory Limits HomologicalComplex
section
variable {X : Type} [TopologicalSpace X] [T1Space X]

/-- Center an arbitrary full vector-space chart at the point under study. -/
def centeredChartHomeomorph {E : Type} [NormedAddCommGroup E]
    (U : Set X) (x : X) (hx : x ∈ U) (e : U ≃ₜ E) : U ≃ₜ E :=
  e.trans (Homeomorph.addRight (-e ⟨x,hx⟩))

omit [T1Space X] in
theorem centeredChartHomeomorph_center {E : Type} [NormedAddCommGroup E]
    (U : Set X) (x : X) (hx : x ∈ U) (e : U ≃ₜ E) :
    centeredChartHomeomorph U x hx e ⟨x,hx⟩ = 0 := by
  simp [centeredChartHomeomorph]

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Product-pair homology, pair homotopies, and diagonal normalization. -/

section
open CategoryTheory ContinuousMap
open scoped unitInterval
variable {ι : Type}

/-- Complex diagonal coordinate change with every multiplier invertible. -/
def complexDiagonalMap (a : ι → ℂˣ) : C((ι → ℂ),(ι → ℂ)) :=
  ⟨fun v i => (a i : ℂ) * v i, continuous_pi (fun i => continuous_const.mul (continuous_apply i))⟩

theorem complexDiagonalMap_nonzero (a : ι → ℂˣ) :
    Set.MapsTo (complexDiagonalMap a) ({0}ᶜ : Set (ι → ℂ)) {0}ᶜ := by
  intro v hv he
  apply hv
  funext i
  have h : (a i : ℂ) * v i = 0 := congrFun he i
  exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero (a i))

/-- A path through complex units supplies a genuine nonzero-preserving
homotopy to the identity; no determinant-to-degree assertion is assumed. -/
def complexDiagonalHomotopy (a : ι → ℂˣ) :
    Homotopy (complexDiagonalMap a) (ContinuousMap.id (ι → ℂ)) := by
  let γ : Path a (fun _ => (1 : ℂˣ)) :=
    Classical.choice (PathConnectedSpace.joined a (fun _ => (1 : ℂˣ)))
  exact
    { toFun := fun z i => (γ z.1 i : ℂ) * z.2 i
      continuous_toFun := continuous_pi (fun i =>
        (Units.continuous_val.comp ((continuous_apply i).comp
          (γ.continuous.comp continuous_fst))).mul ((continuous_apply i).comp continuous_snd))
      map_zero_left := fun v => by ext i; simp [complexDiagonalMap]
      map_one_left := fun v => by ext i; simp }

end

open CategoryTheory ContinuousMap

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
open CategoryTheory Limits HomologicalComplex AlgebraicTopology Simplicial

abbrev pointComponentIso (X : TopCat.{0}) :
    (integralSingularHomology 0).obj X ≅
      ∐ fun _ : (TopCat.toSSet.obj X).π₀ => ModuleCat.of ℤ ℤ :=
  (TopCat.toSSet.obj X).homology₀Iso (ModuleCat.of ℤ ℤ)

abbrev pointAugmentation (X : TopCat.{0}) :
    (integralSingularHomology 0).obj X ⟶ ModuleCat.of ℤ ℤ :=
  X.singularHomology₀ε (ModuleCat.of ℤ ℤ)

/-- The actual integral H₀ class of a point, expressed as a map out of ℤ. -/
def pointHomology (X : TopCat.{0}) (x : X) :
    ModuleCat.of ℤ ℤ ⟶ (integralSingularHomology 0).obj X :=
  ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).liftCycles
    ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x))
    0 (by simp) (by simp) ≫ ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ 0

@[reassoc (attr := simp)]
theorem pointHomology_component (X : TopCat.{0}) (x : X) :
    pointHomology X x ≫ (pointComponentIso X).hom =
      Sigma.ι (fun _ : (TopCat.toSSet.obj X).π₀ => ModuleCat.of ℤ ℤ)
        (SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm x)) :=
  by
    dsimp only [pointHomology, pointComponentIso]
    erw [Category.assoc]
    exact (SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
      (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) (TopCat.toSSetObj₀Equiv.symm x))

@[reassoc (attr := simp)]
theorem pointHomology_map {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    pointHomology X x ≫ (integralSingularHomology 0).map f = pointHomology Y (f x) := by
  unfold pointHomology
  change (_ ≫ _) ≫ homologyMap (integralSingularChains.map f) 0 = _
  erw [Category.assoc, homologyπ_naturality, ← Category.assoc,
    liftCycles_comp_cyclesMap]
  have h : (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x) ≫
      (integralSingularChains.map f).f 0 =
      (TopCat.toSSet.obj Y).ιChainComplex (TopCat.toSSetObj₀Equiv.symm (f x)) :=
    SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) _
  simp only [h]
  rfl

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

/-- The integral coefficient of one specified path component. -/
def componentCoefficient (X : TopCat.{0}) (a : X) :
    (integralSingularHomology 0).obj X ⟶ ModuleCat.of ℤ ℤ := by
  classical
  exact (pointComponentIso X).hom ≫
    Sigma.desc (fun c => if c = SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm a) then 𝟙 _ else 0)

@[reassoc (attr := simp)]
theorem pointHomology_coefficient_self (X : TopCat.{0}) (a : X) :
    pointHomology X a ≫ componentCoefficient X a = 𝟙 _ := by
  simp [componentCoefficient]

@[reassoc (attr := simp)]
theorem pointHomology_coefficient_other (X : TopCat.{0}) (a b : X) (hab : ¬ Joined a b) :
    pointHomology X a ≫ componentCoefficient X b = 0 := by
  have h : SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm a) ≠
      SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm b) := by
    intro h
    exact hab (Quotient.exact (TopCat.zerothHomotopyEquiv.injective h))
  simp [componentCoefficient, h]

/-- The augmentation takes each integral point class to one. -/
@[reassoc (attr := simp)]
theorem pointHomology_augmentation (X : TopCat.{0}) (a : X) :
    pointHomology X a ≫ pointAugmentation X = 𝟙 _ := by
  dsimp only [pointHomology, pointAugmentation, TopCat.singularHomology₀ε]
  erw [Category.assoc]
  exact (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
      (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) (TopCat.toSSetObj₀Equiv.symm a))

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

theorem additiveFunctor_biprod_detect_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} [HasBinaryBiproduct X Y]
    {T : D} (f : T ⟶ F.obj (X ⊞ Y))
    (h₁ : f ≫ F.map biprod.fst = 0) (h₂ : f ≫ F.map biprod.snd = 0) : f = 0 := by
  have he := congrArg (fun g : X ⊞ Y ⟶ X ⊞ Y => f ≫ F.map g)
    (biprod.total (X := X) (Y := Y))
  simp only [Functor.map_add, Functor.map_comp, Preadditive.comp_add,
    ← Category.assoc] at he
  erw [F.map_id, Category.comp_id] at he
  rw [h₁, h₂, zero_comp, zero_comp, add_zero] at he
  exact he.symm

/-- Homology of a biproduct is jointly detected by its two projections. -/
theorem homology_biprod_detect_zero {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    {T : ModuleCat.{0} ℤ} (n : ℕ) (f : T ⟶ (C ⊞ D).homology n)
    (h₁ : f ≫ homologyMap biprod.fst n = 0)
    (h₂ : f ≫ homologyMap biprod.snd n = 0) : f = 0 := by
  exact additiveFunctor_biprod_detect_zero
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n) f h₁ h₂

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

end

open CategoryTheory Limits

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

section
open CategoryTheory ContinuousMap

/-- Radial normalization gives a genuine homotopy equivalence of the
punctured vector space with its unit sphere. -/
def puncturedVectorSphereHomotopyEquiv (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ({0}ᶜ : Set V) ≃ₕ Metric.sphere (0 : V) 1 := by
  letI : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
  let e := Classical.choice (ContractibleSpace.hequiv_unit (Set.Ioi (0 : ℝ)))
  exact (homeomorphUnitSphereProd V).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl _).prodCongr e).trans
      (Homeomorph.prodUnique _ Unit).toHomotopyEquiv)

/-- Relative homology at the origin, in degrees at least two, is identified
with the preceding integral sphere homology. No sphere group calculation is assumed. -/
def localVectorSphereHomologyIso (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (hn : n ≠ 0) :
    relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set V)) (n+1) ≅
      (integralSingularHomology n).obj (TopCat.of (Metric.sphere (0 : V) 1)) :=
  puncturedVectorBoundaryIso V n hn ≪≫
    integralHomologyHomotopyIso (puncturedVectorSphereHomotopyEquiv V) n

end

section
open Metric ContinuousMap
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sphere with one pole removed is the actual orthogonal hyperplane. -/
def spherePoleHomeomorph (v : sphere (0 : E) 1) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (v : E))ᗮ :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

@[simp] theorem spherePoleHomeomorph_apply (v : sphere (0 : E) 1)
    (x : ({v}ᶜ : Set (sphere (0 : E) 1))) :
    spherePoleHomeomorph v x = stereographic (norm_eq_of_mem_sphere v) x.val := rfl

theorem sphere_pole_ne_neg (v : sphere (0 : E) 1) : v ≠ -v := by
  intro h
  have h' : (v : E) = -(v : E) := congrArg Subtype.val h
  have hz : (v : E) = 0 := by
    have : (2 : ℝ) • (v : E) = 0 := by rw [two_smul]; exact (congrArg (fun x : E => x + (v : E)) h').trans (neg_add_cancel _)
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)
  have := norm_eq_of_mem_sphere v
  simp [hz] at this

theorem sphere_poles_open_cover (v : sphere (0 : E) 1) :
    IsOpen ({v}ᶜ : Set (sphere (0 : E) 1)) ∧
    IsOpen ({-v}ᶜ : Set (sphere (0 : E) 1)) ∧
    ({v}ᶜ : Set (sphere (0 : E) 1)) ∪ {-v}ᶜ = Set.univ := by
  refine ⟨isOpen_compl_singleton, isOpen_compl_singleton, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : x = v
  · exact Or.inr (h ▸ sphere_pole_ne_neg v)
  · exact Or.inl h

theorem spherePole_contractible (v : sphere (0 : E) 1) :
    ContractibleSpace ({v}ᶜ : Set (sphere (0 : E) 1)) :=
  (spherePoleHomeomorph v).contractibleSpace

/-- Stereographic projection identifies the overlap of the two pole charts
with the punctured orthogonal hyperplane. -/
def spherePoleOverlapHomeomorph (v : sphere (0 : E) 1) :
    ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) ≃ₜ
      ({0}ᶜ : Set (ℝ ∙ (v : E))ᗮ) := by
  let e := spherePoleHomeomorph v
  let s : ({v}ᶜ : Set (sphere (0 : E) 1)) :=
    ⟨-v, by simpa using (sphere_pole_ne_neg v).symm⟩
  have hs : e s = 0 := stereographic_apply_neg v
  let e' : ({s}ᶜ : Set ({v}ᶜ : Set (sphere (0 : E) 1))) ≃ₜ
      ({0}ᶜ : Set (ℝ ∙ (v : E))ᗮ) := e.subtype (fun x => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rw [← hs, e.injective.eq_iff])
  refine Homeomorph.trans ?_ e'
  exact
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, by
        intro h
        exact x.property.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨x.val.val, x.val.property, by
        intro h
        exact x.property (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

/-- The overlap of opposite pole charts is homotopy equivalent to the equator. -/
def spherePoleOverlapHomotopyEquiv (v : sphere (0 : E) 1) :
    ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) ≃ₕ
      sphere (0 : (ℝ ∙ (v : E))ᗮ) 1 :=
  (spherePoleOverlapHomeomorph v).toHomotopyEquiv.trans
    (puncturedVectorSphereHomotopyEquiv _)

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

/-- Restriction of a real linear isometry equivalence to actual unit spheres. -/
def linearIsometrySphereHomeomorph {F : Type} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) :
    sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 :=
  e.toHomeomorph.subtype (fun x => by simp)

/-- The equator has the expected Euclidean dimension. -/
def sphereEquatorEuclideanHomeomorph (d : ℕ) [Fact (Module.finrank ℝ E = d+1)]
    (v : sphere (0 : E) 1) :
    sphere (0 : (ℝ ∙ (v : E))ᗮ) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  linearIsometrySphereHomeomorph
    (OrthonormalBasis.fromOrthogonalSpanSingleton d
      (show (v : E) ≠ 0 by
        intro h
        have := norm_eq_of_mem_sphere v
        simp [h] at this)).repr

/-- Degree recursion to a sphere in one less real dimension. The base H₁
calculation is not included in this statement. -/
def sphereEuclideanHomologyStep (d : ℕ) [Fact (Module.finrank ℝ E = d+1)]
    (v : sphere (0 : E) 1) (n : ℕ) (hn : n ≠ 0) :
    (integralSingularHomology (n+1)).obj (TopCat.of (sphere (0 : E) 1)) ≅
      (integralSingularHomology n).obj (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  sphereEquatorHomologyIso v n hn ≪≫
    (integralSingularHomology n).mapIso (TopCat.isoOfHomeo (sphereEquatorEuclideanHomeomorph d v))

end

/-- Nonzero vectors transport under an actual continuous linear equivalence. -/
def continuousLinearEquivPuncturedHomeomorph {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set F) :=
  e.toHomeomorph.subtype (fun x => by simp)

/-- In a real plane, the overlap of the two pole charts is the punctured real line. -/
def spherePlaneOverlapRealHomeomorph {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 1+1)]
    (v : sphere (0 : E) 1) :
    ↥(({v}ᶜ : Set (sphere (0 : E) 1)) ∩ {-v}ᶜ) ≃ₜ ({0}ᶜ : Set ℝ) :=
  (spherePoleOverlapHomeomorph v).trans (continuousLinearEquivPuncturedHomeomorph
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (show (v : E) ≠ 0 by
        intro h
        have := norm_eq_of_mem_sphere v
        simp [h] at this)).repr.toContinuousLinearEquiv.trans
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))))

/-- The signs lie in different path components of the actual punctured real line. -/
theorem puncturedReal_not_joined :
    ¬ Joined (⟨-1, by simp⟩ : ({0}ᶜ : Set ℝ)) ⟨1, by simp⟩ := by
  rintro ⟨p⟩
  have hc : Continuous (fun t => (p t : ℝ)) := continuous_subtype_val.comp p.continuous
  have hz : (0 : ℝ) ∈ Set.range (fun t => (p t : ℝ)) :=
    intermediate_value_univ 0 1 hc (by simp)
  obtain ⟨t, ht⟩ := hz
  exact (p t).property ht

/-- The punctured real line has exactly its negative and positive path components. -/
theorem puncturedReal_two_components (x : ({0}ᶜ : Set ℝ)) :
    Joined x (⟨-1, by simp⟩ : ({0}ᶜ : Set ℝ)) ∨ Joined x ⟨1, by simp⟩ := by
  have hx : (x : ℝ) ≠ 0 := x.property
  rcases lt_or_gt_of_ne hx with hx | hx
  · left
    have h := ((convex_Iio (0 : ℝ)).isPathConnected ⟨-1, by norm_num⟩).joinedIn
      (x : ℝ) hx (-1) (by norm_num)
    exact (h.mono (by intro y hy; exact ne_of_lt hy)).joined_subtype
  · right
    have h := ((convex_Ioi (0 : ℝ)).isPathConnected ⟨1, by norm_num⟩).joinedIn
      (x : ℝ) hx 1 (by norm_num)
    exact (h.mono (by intro y hy; exact ne_of_gt hy)).joined_subtype

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

/-- A fixed unit vector used to make the recursive sphere calculation a definition. -/
def euclideanSpherePole (n : ℕ) : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :=
  ⟨Classical.choose ((NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin (n+1)))
      (x := 0) (r := 1)).mpr (by norm_num)),
    Classical.choose_spec ((NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin (n+1)))
      (x := 0) (r := 1)).mpr (by norm_num))⟩

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

section
open CategoryTheory Metric ContinuousMap

def continuousLinearEquivSphereHomotopyEquiv {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    sphere (0 : E) 1 ≃ₕ sphere (0 : F) 1 :=
  (puncturedVectorSphereHomotopyEquiv E).symm.trans
    ((continuousLinearEquivPuncturedHomeomorph e).toHomotopyEquiv.trans
      (puncturedVectorSphereHomotopyEquiv F))

end

open CategoryTheory Limits Metric

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
open CategoryTheory
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Real dimension of the actual complex graph-coordinate space. -/
theorem canonicalCoordinateSpace_real_finrank :
    Module.finrank ℝ ((Σ i, Fin (K i)) → ℂ) = 2 * (∑ i, K i) := by
  rw [finrank_real_of_complex]
  simp [Fintype.card_sigma, Nat.mul_comm]

end

section
open CategoryTheory Metric

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
open Set
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite signed halfspace cover, using actual continuous linear coordinates. -/
def signedCoordinateHalfspace (i : Fin (Module.finrank ℝ E) × Bool) : Set E :=
  if i.2 then {x | 0 < (Module.finBasis ℝ E).equivFunL x i.1}
  else {x | (Module.finBasis ℝ E).equivFunL x i.1 < 0}

end

open Bundle Topology CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.IntegralHomology_AffineAvoidance
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

/-- A finite chart chooses a nonzero signed real coordinate for each image. -/
def affineAvoidanceChart (l : J → E →L[ℝ] F) (c : J → F)
    (s : J → Fin (Module.finrank ℝ F) × Bool) : Set E :=
  ⋂ j, (fun x => l j x + c j) ⁻¹' signedCoordinateHalfspace (s j)

end

open CategoryTheory Limits Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Twisted
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
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

/-- The auxiliary factor for the stable obstruction has dimension h. -/
def twistedProjectiveDimensions : Option ι → ℕ
  | none => h
  | some i => K i

end

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Content
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact dimension contents, their finite measures, and positive support. -/

section

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal Topology
namespace Kaplansky

/-- Continuous scalar cutoff, used only for uniform approximation of functions. -/
def continuousDimensionCutoff {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (t : ℝ) : C(X, ℝ) :=
  ⟨fun x => max (f x-t) 0, by fun_prop⟩

theorem continuousDimensionCutoff_nonneg {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (t : ℝ) :
    0 ≤ continuousDimensionCutoff f t := fun _ => le_max_right _ _

theorem continuousDimensionCutoff_zero {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (hf : 0 ≤ f) :
    continuousDimensionCutoff f 0 = f := by
  ext x
  change max (f x-0) 0 = f x
  rw [sub_zero, max_eq_left (show 0 ≤ f x from hf x)]

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Quasitrace_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive square-symmetric quasitraces with complex linearity on closed nonunital abelian subalgebras. -/

section

noncomputable section
open scoped ComplexOrder IsMulCommutative

namespace Kaplansky

variable {A : Type*} [CStarAlgebra A]

/-- The closed unital abelian case follows from the actual nonunital axiom. -/
theorem OneQuasitrace.linearOn (τ : OneQuasitrace A)
    (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (hcomm : ∀ x y : S, x * y = y * x) :
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = τ x := by
  exact τ.abelian_linear S.toNonUnitalStarSubalgebra hS hcomm

namespace OneQuasitrace

variable (τ : OneQuasitrace A)

@[simp] theorem map_zero : τ 0 = 0 := by
  let S := StarAlgebra.elemental ℂ (0 : A)
  obtain ⟨f, hf⟩ := τ.linearOn S (StarAlgebra.elemental.isClosed ℂ 0)
    (fun x y => mul_comm x y)
  exact (hf 0).symm.trans f.map_zero

/-- Abelian linearity applied to the closed star algebra generated by a
commuting family of self-adjoint elements. -/
theorem linearOn_hull (s : Set A) (hsa : ∀ a ∈ s, IsSelfAdjoint a)
    (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∃ f : (StarAlgebra.adjoin ℂ s).topologicalClosure →ₗ[ℂ] ℂ,
      ∀ x, f x = τ x := by
  have := StarAlgebra.isMulCommutative_adjoin ℂ
    (fun element helement other hother => hc element helement other hother)
    (by
      intro element helement other hother
      rw [(hsa other hother).star_eq]
      exact hc element helement other hother)
  have hs : ∀ x y : (StarAlgebra.adjoin ℂ s).toSubalgebra, x * y = y * x := fun x y => mul_comm x y
  letI := Subalgebra.commSemiringTopologicalClosure (StarAlgebra.adjoin ℂ s).toSubalgebra hs
  have key : ∀ a b : (StarAlgebra.adjoin ℂ s).toSubalgebra.topologicalClosure, a * b = b * a :=
    fun a b => mul_comm a b
  exact τ.linearOn _ (StarSubalgebra.isClosed_topologicalClosure _)
    (fun a b => key a b)

/-- Only commuting self-adjoint pairs are added here. -/
theorem map_add {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hc : Commute a b) : τ (a + b) = τ a + τ b := by
  obtain ⟨f, hf⟩ := τ.linearOn_hull {a,b}
    (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> assumption)
    (by intro x hx y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rfl
        · exact hc.eq
        · exact hc.eq.symm
        · rfl)
  have ha' : a ∈ (StarAlgebra.adjoin ℂ ({a,b} : Set A)).topologicalClosure :=
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (by simp))
  have hb' : b ∈ (StarAlgebra.adjoin ℂ ({a,b} : Set A)).topologicalClosure :=
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (by simp))
  exact (hf (⟨a, ha'⟩ + ⟨b, hb'⟩)).symm.trans
    ((f.map_add ⟨a, ha'⟩ ⟨b, hb'⟩).trans (congrArg₂ (· + ·) (hf _) (hf _)))

end OneQuasitrace
end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real functional calculus and signed and complex spectral measures. -/

open scoped Matrix CStarAlgebra ComplexOrder
open Set MeasureTheory TopologicalSpace

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {X : Type*} [TopologicalSpace X]

variable [CompactSpace X]

local instance continuousMapRealFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ C(X, ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] {n : ℕ}

omit [CompactSpace X] in
theorem continuousDimensionCutoff_sub (f : C(X, ℝ)) :
    continuousDimensionCutoff f 0 - continuousDimensionCutoff (-f) 0 = f := by
  ext x
  change max (f x-0) 0 - max (-f x-0) 0 = f x
  simp only [sub_zero]
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Words
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word propagation through Hilbert shifts and normalized tuple operators. -/

namespace Kaplansky
open scoped BigOperators
variable {𝕜 V ι : Type*} [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]

/-- Apply a word of operators, in the multiplication order used by
noncommutative polynomials. A generator and its adjoint are separate
letters of the alphabet. -/
def applyWord (T : ι → Module.End 𝕜 V) : List ι → V → V
  | [], v => v
  | a::w, v => T a (applyWord T w v)

end Kaplansky

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded C-star products and the generated separable unital algebra. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder
attribute [local instance] CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

local instance (priority := 2000) closedSubalgebraLE (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] : LE S := (CStarAlgebra.spectralOrder S).toLE

local instance (priority := 2000) closedSubalgebraPreorder (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] : Preorder S := (CStarAlgebra.spectralOrder S).toPreorder

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Polynomials
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

def algebraStarLetter (x : Fin N → A) (l : Bool × Fin N) : A :=
  if l.1 then star (x l.2) else x l.2

def algebraStarWord (x : Fin N → A) (w : List (Bool × Fin N)) : A :=
  (w.map (algebraStarLetter x)).prod

@[simp] theorem algebraStarWord_append (x : Fin N → A) (u v : List (Bool × Fin N)) :
    algebraStarWord x (u++v)=algebraStarWord x u * algebraStarWord x v := by
  simp [algebraStarWord]

abbrev StarWordPolynomial (N : ℕ) := List (Bool × Fin N) →₀ ℂ

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_BundlePolynomials
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

variable {ι : Type*} {K : ι → ℕ}

abbrev MatrixPolynomialTermIndex {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24) :=
  Σ row : Fin m, Σ col : Fin n, {w // w ∈ (p row col).support}

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Operators
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

abbrev HilbertColumns (n : ℕ) (H : Type*) := PiLp 2 (fun _ : Fin n => H)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Quasitrace_Compactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed quasitrace constraints and compactness of normalized two-quasitraces. -/

section

noncomputable section
open scoped ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable (A : Type*) [CStarAlgebra A]

abbrev QuasitraceCandidate := (A → ℂ) × (CStarMatrix (Fin 2) (Fin 2) A → ℂ)

end Kaplansky

end
end

end OAI
end


