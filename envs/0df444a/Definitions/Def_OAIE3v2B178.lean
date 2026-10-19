-- Prove2me | Definitions.Def_OAIE3v2B178
-- name    : OAIE3v2B178
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:25:35.631432+00:00
-- url     : https://prove2.me/theorems/c1a6686e-9666-4c1e-b497-eaa0507958d8
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 180 of 311
-- statement:
--   Definitions bundle 180 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162` of this split.
--
--   Modules: `Dynamics/PhysicalRowsBudgetedL1Perturbation.lean`, `Estimates/AllocatedFixedScaleJointMarginalTransfer.lean`, `Estimates/AllocatedRecenteredL1Source.lean`, `Estimates/AllocatedReferenceJetWindow.lean`, `Estimates/AllocatedSlicedRowsProjectedSource.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/CubicRootPermutation.lean`, `Estimates/NativePhysicalHaarExpansion.lean`, `Estimates/PhysicalRowsCoveredL1Perturbation.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Geometry/PhysicalRowsStandardCoordinates.lean`, `Geometry/PhysicalSpatialAnalyticFactor.lean`, `Probability/AllocatedReferenceJetMass.lean`, `Probability/PhysicalRowsDensityTransport.lean`, `Sampling/JointMeasureProductiveNarrowSampler.lean`, `Sampling/PhysicalRowsCoveredL1Sampling.lean`, `Sampling/PhysicalRowsProbabilityMassSampling.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

noncomputable def physicalCubePositiveTest {I : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (D : ℕ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (v : I → (Unit ⊕ Fin q) → ℤ) : ℂ :=
  physicalCubeSiteTest test v * (f (physicalCubeEuclideanSample U D p hm v) : ℂ)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

theorem physicalCubeEuclideanSample_frame {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubeEuclideanSample U d p hm v = standardPhysicalJetMap U
      (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))) := by
  rw [coefficientCoverSample_standardPhysicalJet U d p hp hm, standardPhysicalCubeOutput_frame]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem physicalCubeRowSample_translate {X : Type*} {m dim : ℕ}
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (rows : ∀ j, O j → Finset (Fin dim))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (base : X → ℤ)
    (v : X → (Unit ⊕ Fin dim) → ℤ) :
    physicalCubeRowSample U d rows
        (fun j => translate (fun x => (base x : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j)) v =
      physicalCubeRowSample U d rows p hm (translatePhysicalCube base v) := by
  unfold physicalCubeRowSample
  rw [physicalCubeCoveredSample_translate]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem physicalResidueReconstruction_columnResidue {K X : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (stride : X → ℕ) (v : X → (Unit ⊕ Fin q) → ℤ) :
    columnResiduePattern stride
        (standardPhysicalCubeFrame (physicalResidueReconstruction root D base r stride v)) =
      columnResiduePattern stride (standardPhysicalCubeFrame (physicalCubeRootDifferences root D base r)) := by
  funext z
  rcases z with ⟨k,x⟩
  cases k <;> simp [columnResiduePattern, standardPhysicalCubeFrame,
    physicalResidueReconstruction]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

abbrev Seed := RationalTorus.Algebra 1

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicRootPermutation
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift)))

noncomputable def cubicPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ _ : CubicReplicatedIndex, 1) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by decide)) (fun _ : Fin 2 => W.model)

noncomputable def cubicPairTests :
    ∀ k, (V.cubicPairModels k).Niltest (fun _ : Fin 3 => 1)
  | none => (V.test.raiseStep (by decide)).conjugate
  | some k => ![(W.cubicPairComponent i 1 2 0 shift).conjugate,
      W.cubicPairComponent j 2 1 0 shift] k

end NativeSampleCorrelation
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginalTransfer
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

theorem joint_normalization_integral_compare {X Y C : Type*} [Fintype X] [Fintype Y]
    [MeasurableSpace C] (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → X × Y → ℝ) (hDm : ∀ z, Measurable (fun c => D c z))
    (hD0 : ∀ c z, 0 ≤ D c z)
    (hlocal : ∀ c x, 0 < q.mean (fun y => D c (x,y)))
    (hglobal : ∀ c, 0 < (p.prod q).mean (D c))
    (f : X × Y → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ c x, |q.mean (fun y => D c (x,y))-1| ≤ ε) :
    ‖(∫ c, (p.prod q).normalizedDensityTest (D c) f ∂μ) -
      p.complexMean (fun x => ∫ c, q.normalizedDensityTest
        (fun y => D c (x,y)) (fun y => f (x,y)) ∂μ)‖ ≤ 2*ε := by
  have hj := (p.prod q).normalizedDensityTest_integrable μ D hDm hD0 hglobal f hf
  have hl (x : X) := q.normalizedDensityTest_integrable μ (fun c y => D c (x,y))
    (fun y => hDm (x,y)) (fun c y => hD0 c (x,y)) (fun c => hlocal c x)
    (fun y => f (x,y)) (fun y => hf (x,y))
  have hli := p.complexMean_integrable μ
    (fun c x => q.normalizedDensityTest (fun y => D c (x,y)) (fun y => f (x,y))) hl
  rw [← p.integral_complexMean μ _ hl, ← integral_sub hj hli]
  have h := norm_integral_le_of_norm_le (integrable_const (2*ε) (μ := μ))
    (ae_of_all μ (fun c => p.joint_normalization_compare q (D c) (hD0 c)
      (hlocal c) (hglobal c) f hf (hclose c)))
  simpa only [integral_const, probReal_univ, one_smul] using h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

theorem selectedJointFiniteLaw_integral_local_comparison {C : Type*} [MeasurableSpace C]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → B → (K × I → ℤ) → ℝ) (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (hlocal : ∀ c a, 0 < selectedResidueDensityMass modulus T W (D c a))
    (f : B → (K × I → ℤ) → ℂ) (hf : ∀ a z, ‖f a z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ c a, |selectedResidueDensityMass modulus T W (D c a)-1| ≤ ε) :
    ‖(∫ c, (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).complexMean
        (fun z => f z.1.val z.2.val) ∂μ) -
      (𝔼 a ∈ A, ∫ c, ∑' z,
        ((selectedResidueDensityPMF modulus T W hW hZ (D c a) (hD0 c a) (hlocal c a) z).toReal : ℂ) *
          f a z ∂μ)‖ ≤ 2*ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus T W hW hZ
  have h := p.joint_normalization_integral_compare q μ (fun c z => D c z.1.val z.2.val)
    (fun z => hDm z.1.val z.2.val) (fun c z => hD0 c z.1.val z.2.val)
    (fun c a => by
      change 0 < q.mean (fun y => D c a.val y.val)
      rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (D c a.val)]
      exact hlocal c a.val)
    (fun c => by change 0 < (selectedJointReference A hA modulus T W hW hZ).mean _
                 rw [selectedJointReference_densityMass]; exact hD c)
    (fun z => f z.1.val z.2.val) (fun z => hf z.1.val z.2.val)
    (fun c a => by
      change |q.mean (fun y => D c a.val y.val)-1| ≤ ε
      rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (D c a.val)]
      exact hclose c a.val)
  have he (c : C) (a : B) := selectedResidueDensityPMF_normalizedDensityTest modulus T W hW hZ
    (D c a) (hD0 c a) (hlocal c a) (f a)
  have hm := FiniteProbabilityWeights.uniformFinset_complexMean A hA
    (fun a => ∫ c, q.normalizedDensityTest (fun z => D c a z.val) (fun z => f a z.val) ∂μ)
  dsimp only [p] at h
  rw [hm] at h
  simpa only [selectedJointFiniteLaw_complexMean, he, selectedJointReference, q] using h

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory
open scoped BigOperators Classical

theorem fixedScaleJointMarginalTransfer
    {K I C : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (root : K → ℤ) (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i)
    (stride : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I stride))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z)
    (hfit : ∀ i, physicalSiteWidth root W i ≤ (margin i : ℝ))
    (D : C → (I → ℤ) → (Option K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass (trimmedIntegerBox N margin) stride T W (D c))
    (hlocal : ∀ c a, 0 < selectedResidueDensityMass stride T W (D c a))
    {ε η : ℝ}
    (hclose : ∀ c a, |selectedResidueDensityMass stride T W (D c a) - 1| ≤ ε)
    (hmix : ∀ a (ψ : (I → ℝ) → ℂ), (∀ v, ‖ψ v‖ ≤ 1) →
      ‖(∫ c, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ (D c a)
          (hD0 c a) (hlocal c a) z).toReal : ℂ) * ψ (physicalAffineSite root z) ∂μ) -
        ∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          ψ (physicalAffineSite root z)‖ ≤ η) :
    ∀ φ : (I → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
      let f := fun c =>
        (selectedJointFiniteLaw (trimmedIntegerBox N margin)
          (trimmedIntegerBox_nonempty N margin hmargin) stride T W hW hZ
          (D c) (hD0 c) (hD c)).complexMean
            (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
      Integrable f μ ∧
        ‖(∫ c, f c ∂μ) - (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          2 * ε + η + 2 * ∑ i, 2 * (margin i : ℝ) / N i := by
  intro φ hφ
  let Q := trimmedIntegerBox N margin
  have hQ : Q.Nonempty := trimmedIntegerBox_nonempty N margin hmargin
  constructor
  · have hi := (selectedJointReference Q hQ stride T W hW hZ).normalizedDensityTest_integrable μ
      (fun c z => D c z.1.val z.2.val)
      (fun z => hDm z.1.val z.2.val) (fun c z => hD0 c z.1.val z.2.val)
      (fun c => by
        rw [selectedJointReference_densityMass Q hQ stride T W hW hZ (D c)]
        exact hD c)
      (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
      (fun z => hφ _)
    apply hi.congr
    filter_upwards [] with c
    exact (selectedJointFiniteLaw_complexMean Q hQ stride T W hW hZ
      (D c) (hD0 c) (hD c)
      (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z))).symm
  · have hjoint := selectedJointFiniteLaw_integral_local_comparison Q hQ stride T W hW hZ μ
      D hDm hD0 hD hlocal
      (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z))
      (fun _ _ => hφ _) hclose
    have hreference :
        ‖(𝔼 a ∈ Q, ∫ c, ∑' z,
          ((selectedResidueDensityPMF stride T W hW hZ (D c a)
            (hD0 c a) (hlocal c a) z).toReal : ℂ) *
            φ ((fun i => (a i : ℝ)) + physicalAffineSite root z) ∂μ) -
          (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          η + 2 * ∑ i, 2 * (margin i : ℝ) / N i := by
      refine selectedResidue_trimmed_comparison_transfer root N margin hmargin stride T W hW hZ
        hfit (fun x => φ (fun i => (x i : ℝ))) (fun _ _ => hφ _) _ ?_
      intro a _
      have h := hmix a (fun v => φ ((fun i => (a i : ℝ)) + v)) (fun _ => hφ _)
      have hcast (z : Option K × I → ℤ) :
          (fun i => ((a + integerPhysicalSite root z) i : ℝ)) =
            (fun i => (a i : ℝ)) + physicalAffineSite root z := by
        funext i
        simp only [Pi.add_apply, Int.cast_add, integerPhysicalSite_cast_apply]
      simpa only [hcast] using h
    exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add hjoint hreference)).trans_eq (by ring)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalWindow_sum_le_sampled_mass {X : Type*} [Fintype X] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (residue : ColumnResiduePattern (Option (Fin q)) X stride)
    (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {residue} V z)
    (f : (X → (Unit ⊕ Fin q) → ℤ) → ℝ) (hf : ∀ v, 0 ≤ f v)
    (window : Finset (X → (Unit ⊕ Fin q) → ℤ))
    (hresidue : ∀ v ∈ window, columnResiduePattern stride (standardPhysicalCubeFrame v) = residue)
    (hinner : ∀ v ∈ window, ∀ i, |(standardPhysicalCubeFrame v i : ℝ) / V i| ≤ 1 / 2) :
    (∑ v ∈ window, f v) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
          selectedResidueDensityMass stride {residue} V (fun z => f (standardPhysicalCubeOutput z)) := by
  let frames := window.image standardPhysicalCubeFrame
  have hr : ∀ z ∈ frames, columnResiduePattern stride z = residue := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hresidue v hv
  have hi : ∀ z ∈ frames, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hinner v hv
  have h := selectedResidueDensityMass_singleton_window_bound stride hs residue V hV hscale hZ
    (fun z => f (standardPhysicalCubeOutput z)) (fun z => hf _) frames hr hi
  have he : (∑ z ∈ frames, f (standardPhysicalCubeOutput z)) = ∑ v ∈ window, f v := by
    dsimp only [frames]
    rw [Finset.sum_image]
    · simp only [standardPhysicalCubeOutput_frame]
    · intro v _ w _ he
      exact standardPhysicalCubeFrame_injective he
  rwa [he] at h

theorem physicalReconstruction_sum_le_sampled_mass {X K : Type*} [Fintype X] [Fintype K] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ)
    (residue : ColumnResiduePattern (Option K) X stride)
    (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (hscale : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (f : (X → (Unit ⊕ Fin q) → ℤ) → ℝ) (hf : ∀ v, 0 ≤ f v) :
    let r := boundedColumnResidueRepresentative stride residue
    let target := columnResiduePattern stride
      (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 r))
    let V := referenceJetEnvelopeWidths (q := q) stride H
    0 < ∑' z, selectedResidueSmoothWeight stride {target} V z →
    (∑ v ∈ spatialWindow H 4, f (physicalResidueReconstruction root D 0 r stride v)) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
          selectedResidueDensityMass stride {target} V (fun z => f (standardPhysicalCubeOutput z)) := by
  intro r target V hZ
  let window := (spatialWindow H 4).image (physicalResidueReconstruction root D 0 r stride)
  have hr : ∀ k x, |(r (k,x) : ℝ)| ≤ stride x := by
    intro k x
    have h := boundedColumnResidueRepresentative_bounds stride hs residue (k,x)
    rw [abs_of_nonneg (by exact_mod_cast h.1 : (0 : ℝ) ≤ r (k,x))]
    exact_mod_cast h.2.le
  have hoffset := physicalCube_zero_residue_bound root D stride r hr H hrows
  have hres : ∀ v ∈ window, columnResiduePattern stride (standardPhysicalCubeFrame v) = target := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact physicalResidueReconstruction_columnResidue root D 0 r stride w
  have hin : ∀ v ∈ window, ∀ i, |(standardPhysicalCubeFrame v i : ℝ) / V i| ≤ 1 / 2 := by
    intro v hv i
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact physicalResidueReconstruction_envelope root D stride hs r H hH hoffset hw i
  have hsc : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z := by
    intro z
    change _ ≤ residueProfileWidth stride (referenceJetEnvelopeWidths stride H) z
    rw [referenceJetEnvelopeWidths_residue stride hs H]
    exact hscale z.2
  have h := physicalWindow_sum_le_sampled_mass stride hs target V
    (referenceJetEnvelopeWidths_pos stride hs H hH) hsc hZ f hf window hres hin
  have he : (∑ v ∈ window, f v) =
      ∑ v ∈ spatialWindow H 4, f (physicalResidueReconstruction root D 0 r stride v) := by
    dsimp only [window]
    exact Finset.sum_image (fun v _ w _ he => physicalResidueReconstruction_injective root D 0 r stride hs he)
  rwa [he] at h

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedJointReference_collision {K I : Type*} [Fintype K] [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty) (r s : K → ℤ)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z) :
    (selectedJointReference A hA modulus T W hW hZ).mean
      (fun z => if jointIntegerPhysicalSite r (z.1.val,z.2.val) =
        jointIntegerPhysicalSite s (z.1.val,z.2.val) then 1 else 0) =
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0) := by
  simp only [selectedJointReference, FiniteProbabilityWeights.mean_prod,
    jointIntegerPhysicalSite, add_right_inj]
  exact (FiniteProbabilityWeights.uniformFinset A hA).mean_const
    ((selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped BigOperators Classical NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {pw cw pv cv : ℝ} {Lw Lv : ℝ≥0}

noncomputable def product
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv) :
    NormalizedPolynomialTwist X Y (pw * pv) (cw * cv)
      (Lw * max 1 (V.cover : ℝ≥0) + Lv * max 1 (W.cover : ℝ≥0)) where
  modulus := W.modulus * V.modulus
  modulus_pos := Nat.mul_pos W.modulus_pos V.modulus_pos
  modulus_bound := by
    rw [Nat.cast_mul]
    exact mul_le_mul W.modulus_bound V.modulus_bound (Nat.cast_nonneg _)
      ((Nat.cast_nonneg _).trans W.modulus_bound)
  cover := W.cover * V.cover
  cover_pos := Nat.mul_pos W.cover_pos V.cover_pos
  cover_bound := by
    rw [Nat.cast_mul]
    exact mul_le_mul W.cover_bound V.cover_bound (Nat.cast_nonneg _)
      ((Nat.cast_nonneg _).trans W.cover_bound)
  mask := fun r => W.mask (fun x => ZMod.castHom (dvd_mul_right W.modulus V.modulus)
      (ZMod W.modulus) (r x)) *
    V.mask (fun x => ZMod.castHom (dvd_mul_left V.modulus W.modulus) (ZMod V.modulus) (r x))
  mask_bound := by
    intro r
    rw [norm_mul]
    exact (mul_le_mul (W.mask_bound _) (V.mask_bound _) (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1)
  smooth := fun z => W.smooth (z.1, fun y => V.cover • z.2 y) *
    V.smooth (z.1, fun y => W.cover • z.2 y)
  smooth_bound := by
    intro z
    rw [norm_mul]
    exact (mul_le_mul (W.smooth_bound _) (V.smooth_bound _) (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1)
  smooth_lipschitz := by
    have hmap (n : ℕ) : LipschitzWith (max 1 (n : ℝ≥0))
        (fun z : (X → ℝ) × (Y → UnitAddCircle) => (z.1, fun y => n • z.2 y)) := by
      have hn : LipschitzWith (n : ℝ≥0)
          (fun z : (X → ℝ) × (Y → UnitAddCircle) => fun y => n • z.2 y) := by
        simpa only [mul_one, Function.comp_def] using
          (torus_nsmul_reindex_lipschitz (fun y : Y => y) n).comp
            (LipschitzWith.prod_snd (α := X → ℝ))
      exact LipschitzWith.prod_fst.prodMk hn
    have hf := W.smooth_lipschitz.comp (hmap V.cover)
    have hg := V.smooth_lipschitz.comp (hmap W.cover)
    apply LipschitzWith.of_dist_le_mul
    intro z w
    calc
      _ ≤ ‖W.smooth (z.1, fun y => V.cover • z.2 y)‖ *
          dist (V.smooth (z.1, fun y => W.cover • z.2 y))
            (V.smooth (w.1, fun y => W.cover • w.2 y)) +
        dist (W.smooth (z.1, fun y => V.cover • z.2 y))
          (W.smooth (w.1, fun y => V.cover • w.2 y)) *
          ‖V.smooth (w.1, fun y => W.cover • w.2 y)‖ := complex_dist_product _ _ _ _
      _ ≤ 1 * (((Lv * max 1 (W.cover : ℝ≥0) : ℝ≥0) : ℝ) * dist z w) +
        (((Lw * max 1 (V.cover : ℝ≥0) : ℝ≥0) : ℝ) * dist z w) * 1 := by
        exact add_le_add
          (mul_le_mul (W.smooth_bound _) (hg.dist_le_mul z w) dist_nonneg zero_le_one)
          (mul_le_mul (hf.dist_le_mul z w) (V.smooth_bound _) (norm_nonneg _)
            (by positivity))
      _ = _ := by push_cast; ring

@[simp] theorem product_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (V : NormalizedPolynomialTwist X (Σ j, J j) pv cv Lv)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.product V).eval N p u = W.eval N p u * V.eval N p u := by
  have hw : (W.cover : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr W.cover_pos.ne'
  have hv : (V.cover : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr V.cover_pos.ne'
  have hfirst : (fun a => V.cover • physicalGridFactorInput (W.cover * V.cover) p
      (fun x => (u x : ℝ)) a) = physicalGridFactorInput W.cover p (fun x => (u x : ℝ)) := by
    funext a
    simp only [physicalGridFactorInput, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1
    field_simp
  have hsecond : (fun a => W.cover • physicalGridFactorInput (W.cover * V.cover) p
      (fun x => (u x : ℝ)) a) = physicalGridFactorInput V.cover p (fun x => (u x : ℝ)) := by
    funext a
    simp only [physicalGridFactorInput, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1
    field_simp
  have hmaskfirst : (fun x => ZMod.castHom (dvd_mul_right W.modulus V.modulus)
      (ZMod W.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus))) =
      (fun x => (u x : ZMod W.modulus)) := by
    funext x
    exact map_intCast (ZMod.castHom (dvd_mul_right W.modulus V.modulus) (ZMod W.modulus)) (u x)
  have hmasksecond : (fun x => ZMod.castHom (dvd_mul_left V.modulus W.modulus)
      (ZMod V.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus))) =
      (fun x => (u x : ZMod V.modulus)) := by
    funext x
    exact map_intCast (ZMod.castHom (dvd_mul_left V.modulus W.modulus) (ZMod V.modulus)) (u x)
  change (W.mask (fun x => ZMod.castHom (dvd_mul_right W.modulus V.modulus)
      (ZMod W.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus))) *
    V.mask (fun x => ZMod.castHom (dvd_mul_left V.modulus W.modulus)
      (ZMod V.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus)))) *
    (W.smooth ((fun x => (u x : ℝ) / N x), fun a => V.cover •
      physicalGridFactorInput (W.cover * V.cover) p (fun x => (u x : ℝ)) a) *
    V.smooth ((fun x => (u x : ℝ) / N x), fun a => W.cover •
      physicalGridFactorInput (W.cover * V.cover) p (fun x => (u x : ℝ)) a)) = _
  rw [hmaskfirst, hmasksecond, hfirst, hsecond]
  unfold eval
  ring

theorem product_lipschitz_le
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv) :
    Lw * max 1 (V.cover : ℝ≥0) + Lv * max 1 (W.cover : ℝ≥0) ≤
      Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw) := by
  have hw : (W.cover : ℝ≥0) ≤ Real.toNNReal cw := by
    exact (NNReal.coe_le_coe).mp (W.cover_bound.trans (Real.le_coe_toNNReal cw))
  have hv : (V.cover : ℝ≥0) ≤ Real.toNNReal cv := by
    exact (NNReal.coe_le_coe).mp (V.cover_bound.trans (Real.le_coe_toNNReal cv))
  exact add_le_add (mul_le_mul_of_nonneg_left (max_le_max_left 1 hv) (show 0 ≤ Lw from zero_le))
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hw) (show 0 ≤ Lv from zero_le))

noncomputable def productUniform
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv) :
    NormalizedPolynomialTwist X Y (pw * pv) (cw * cv)
      (Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw)) :=
  (W.product V).mono le_rfl le_rfl (W.product_lipschitz_le V)

@[simp] theorem productUniform_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (V : NormalizedPolynomialTwist X (Σ j, J j) pv cv Lv)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.productUniform V).eval N p u = W.eval N p u * V.eval N p u := by
  exact W.product_eval V N p u

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
local notation "rows" => (fun j => (Subtype.val : Row j → Finset (Fin q)))
local notation "jet" => euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : Row j => ν j))

attribute [local instance] OAI.Erdos3.BooleanCubeKernel.physicalRowsFintype
theorem physicalRowsCoefficient_measurePreserving (a : ℕ) (ha : 0 < a) :
    MeasurePreserving (fun z => jet (quotientIntegerCover (coefficientIntegerLattice U) a z)) μ ξ := by
  have hperiod : integerScalarLattice (Fin q) (1 : ℤ) ≤
      (1 : Matrix (Fin q) (Fin q) ℤ).mulVecLin.range := by
    intro v _
    exact ⟨v, by simp⟩
  exact (euclideanCoefficientJetMap_measurePreserving U (fun _ => 0)
    (1 : Matrix (Fin q) (Fin q) ℤ) 1 one_ne_zero hperiod rows
    (fun _ => Subtype.val_injective)
    (fun j s => (mem_boundedBooleanJetRows (j.val + 1) s.val).mp s.property) μ ν).comp
      (coefficientCover_measurePreserving U μ a ha)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalRowsCoveredL1Sampling
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_physical_jet_covered_l1_sampling (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Q)
    (_hLQ : (((Lf + Lg) * ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) -
      g (coveredJetAmbientTorus U 1 y)‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))) -
          g (coveredJetAmbientTorus U 1
            (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z)))‖) ≤ E + 2 * η + ε := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_l1_sampling m
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows P hP hn hd U _ _ _ μ _ _ ν _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP E hmass
  let jet := coefficientAmbientRowsJet (J := J) rows
  let Ljet : ℝ≥0 := ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0)
  have hjet : LipschitzWith Ljet jet := coefficientAmbientRowsJet_lipschitz rows
  have hhaar : (∫ x, ‖f (jet (coefficientAmbientTorus U x)) -
      g (jet (coefficientAmbientTorus U x))‖ ∂μ) ≤ E := by
    let error := fun y => ‖f (coveredJetAmbientTorus U 1 y) - g (coveredJetAmbientTorus U 1 y)‖
    let rowJet := euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin dim) (Fin dim) ℤ) rows
    have hperiod : integerScalarLattice (Fin dim) (1 : ℤ) ≤
        (1 : Matrix (Fin dim) (Fin dim) ℤ).mulVecLin.range := by
      intro v _
      exact ⟨v, by simp⟩
    have hp := euclideanCoefficientJetMap_measurePreserving U (fun _ => 0)
      (1 : Matrix (Fin dim) (Fin dim) ℤ) 1 one_ne_zero hperiod rows hinj hrows μ ν
    have he : AEStronglyMeasurable error (Measure.map rowJet μ) := by
      rw [hp.map_eq]
      exact (((hf.continuous.comp (coveredJetAmbientTorus_continuous U 1)).sub
        (hg.continuous.comp (coveredJetAmbientTorus_continuous U 1))).norm).aestronglyMeasurable
    have hi := (integral_map hp.measurable.aemeasurable he).symm
    rw [hp.map_eq] at hi
    simp only [jet, coefficientAmbientRowsJet_eq]
    exact hi.trans_le hmass
  have hLip : (((Lf * Ljet + Lg * Ljet : ℝ≥0) : ℝ)) ≤ Real.exp Q := by
    simpa only [add_mul] using hLQ
  obtain ⟨hZ, he⟩ := hsample hP hn hd U μ p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun z => f (jet z)) (fun z => g (jet z)) (Lf * Ljet) (Lg * Ljet) Cf Cg
    (hf.comp hjet) (hg.comp hjet) (fun z => hfb _) (fun z => hgb _)
    hη hQ hdim hLip hηQ hfreqP hcoeffP hhaar
  refine ⟨hZ, ?_⟩
  have hid (z : Option (Fin dim) × I → ℤ) :
      jet (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm q
        (fun k j => (z (k,j) : ℝ)))) =
      coveredJetAmbientTorus U 1
        (physicalCubeRowSample U q rows p hm (standardPhysicalCubeOutput z)) :=
    (coefficientAmbientRowsJet_eq rows U _).trans
      (congrArg (coveredJetAmbientTorus U 1) (by
        have he : standardPhysicalCubeFrame (standardPhysicalCubeOutput z) = z := by
          funext t
          rcases t with ⟨k, x⟩
          cases k <;> rfl
        simpa only [he] using
          coefficientCoverSample_physicalRows U q p hp hm rows (standardPhysicalCubeOutput z)))
  simpa only [hid] using he

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsCoveredL1Perturbation
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_physical_jet_covered_l1_perturbation (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Q)
    (_hLQ : (((Lf + Lg) * ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    (ideal : EuclideanJetLayers U O → ℂ) (_hi : Measurable ideal)
    {δ : ℝ} (_happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δ)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))) -
          ideal (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))‖) ≤ E + 2 * δ + (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_physical_jet_covered_l1_sampling m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows P hP hn hd U _ _ _ μ _ _ ν _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP ideal hi δ happ E hmass
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
  let actual := fun y => f (coveredJetAmbientTorus U 1 y)
  let surrogate := fun y => g (coveredJetAmbientTorus U 1 y)
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hP hn hd U μ ν p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb hη hQ hdim hLQ hηQ hfreqP hcoeffP
    (E := ∫ y, ‖actual y - surrogate y‖ ∂ξ) le_rfl
  refine ⟨hZ, ?_⟩
  exact selectedResidueDensityMass_l1_surrogate ξ stride G V hV hZ
    (fun z => physicalCubeRowSample U q rows p hm (standardPhysicalCubeOutput z))
    actual ideal surrogate
    (hf.continuous.comp (coveredJetAmbientTorus_continuous U 1)).measurable hi
    (hg.continuous.comp (coveredJetAmbientTorus_continuous U 1)).measurable
    (fun y => hfb _) (fun y => hgb _) happ hmass
    (he.trans_eq (by ring))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalRowsBudgetedL1Perturbation
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_physical_jet_l1_perturbation_budgeted (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hLg : (Lg : ℝ) ≤ Real.exp T)
    (_hCf : (Cf : ℝ) ≤ Real.exp T) (_hCg : (Cg : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T)
    (ideal : EuclideanJetLayers U O → ℂ) (_hi : Measurable ideal)
    {δ : ℝ} (_happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δ)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))) -
          ideal (physicalCubeRowSample U q rows p _hm (standardPhysicalCubeOutput z))‖) ≤ E + 2 * δ + (2 * η + ε) := by
  obtain ⟨A₀, hA₀, hsample⟩ := exists_physical_jet_covered_l1_perturbation m dim
  obtain ⟨A, hA, hthreshold⟩ := exists_ambientL1SamplingThreshold_bound A₀
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η hη hdim hLf hLg hCf hCg hjet hηT ideal hi δ happ E hmass
  obtain ⟨hQ, hTQ, hTP, hLip, hηQ, hfreq, hcoeff⟩ :=
    ambientL1SamplingBudget_bounds hT hLf hLg hCf hCg hjet hηT
  have heTP := Real.exp_le_exp.mpr hTP
  have hlarge := Real.exp_le_exp.mpr (hthreshold T hT)
  exact hsample rows hinj hrows (hT.trans hTP) (hn.trans hTP) (hd.trans hTP) U μ ν p hp hm
    q hq (hqT.trans heTP) stride hs hS (hST.trans heTP) hρ hε
    (hρT.trans heTP) (hεT.trans heTP) hstride H (fun i => hlarge.trans (hsize i)) hrank
    (hlarge.trans hR) G hG V hV hwidth f g Lf Lg Cf Cg hf hg hfb hgb
    hη hQ (hdim.trans hTQ) hLip hηQ hfreq hcoeff ideal hi happ hmass

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalRowsStandardCoordinates
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})

theorem physicalRowsToStandard_continuous :
    Continuous (physicalRowsToStandard (q := q) U) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro s
  exact (continuous_apply _).comp (continuous_apply j)

theorem physicalRowsToStandard_coefficient {K : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (z : CoefficientTorus (K := K) U) :
    physicalRowsToStandard U
      (euclideanCoefficientJetMap U root D (fun j => (Subtype.val : Row j → Finset (Fin q))) z) =
    euclideanCoefficientJetMap U root D
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) z := by
  funext j s
  unfold physicalRowsToStandard
  simp only [euclideanCoefficientJetMap_apply]
  rfl

theorem physicalRowsToStandard_sample {X : Type*}
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalRowsToStandard U (physicalCubeRowSample U d (fun j => (Subtype.val : Row j → Finset (Fin q))) p hm v) =
      physicalCubeEuclideanSample U d p hm v := by
  rw [← coefficientCoverSample_physicalRows U d p hp hm, physicalRowsToStandard_coefficient]
  exact (physicalCubeEuclideanSample_frame U d p hp hm v).symm

variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include μ in
theorem physicalRowsToStandard_measurePreserving :
    MeasurePreserving (physicalRowsToStandard (q := q) U)
      (Measure.pi (fun j => Measure.pi (fun _ : Row j => ν j)))
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))) := by
  have hr := physicalRowsCoefficient_measurePreserving U μ ν 1 zero_lt_one
  have hs := standardPhysicalJetMap_measurePreserving U μ ν
  have hc := (physicalRowsToStandard_continuous (q := q) U).measurable
  refine ⟨hc, ?_⟩
  rw [← hr.map_eq, Measure.map_map hc hr.measurable]
  have he : (physicalRowsToStandard U ∘ (fun z =>
      euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
        (fun j => (Subtype.val : Row j → Finset (Fin q)))
        (quotientIntegerCover (coefficientIntegerLattice U) 1 z))) = standardPhysicalJetMap U := by
    funext z
    simp only [Function.comp_apply, physicalRowsToStandard_coefficient]
    congr 1
    change (1 : ℕ) • z = z
    exact one_nsmul z
  rw [he]
  exact hs.map_eq

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PhysicalRowsDensityTransport
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
local notation "Std" => (fun j : Fin m => BoundedBooleanJet (Fin q) (Fin.val j + 1))

noncomputable def physicalRowsStandardEquiv : EuclideanJetLayers U Row ≃ᵐ EuclideanJetLayers U Std where
  toFun := physicalRowsToStandard U
  invFun z j s := z j (boundedBooleanJetRowsEquiv (Fin q) (j.val + 1) s)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (physicalRowsToStandard_continuous U).measurable
  measurable_invFun := by
    apply Continuous.measurable
    apply continuous_pi
    intro j
    apply continuous_pi
    intro s
    exact (continuous_apply (boundedBooleanJetRowsEquiv (Fin q) (j.val + 1) s)).comp (continuous_apply j)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedRowsProjectedSource
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})

theorem physicalRowsStandardEquiv_symm_sample {X : Type*}
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    (physicalRowsStandardEquiv U).symm (physicalCubeEuclideanSample U d p hm v) =
      physicalCubeRowSample U d (fun j => (Subtype.val : Row j → Finset (Fin q))) p hm v := by
  rw [← physicalRowsToStandard_sample U d p hp hm]
  rfl

theorem physicalCubePositiveTest_rows {X : Type*}
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (g : EuclideanJetLayers U Row → ℝ)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubePositiveTest U d p hm (fun z => g ((physicalRowsStandardEquiv U).symm z)) test v =
      physicalCubeSiteTest test v *
        (g (physicalCubeRowSample U d (fun j => (Subtype.val : Row j → Finset (Fin q))) p hm v) : ℂ) := by
  simp only [physicalCubePositiveTest, physicalRowsStandardEquiv_symm_sample U d p hp hm]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecenteredL1Source
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_translated_physical_jet_l1_perturbation (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hLg : (Lg : ℝ) ≤ Real.exp T)
    (_hCf : (Cf : ℝ) ≤ Real.exp T) (_hCg : (Cg : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T)
    (ideal : EuclideanJetLayers U O → ℂ) (_hi : Measurable ideal)
    {δ : ℝ} (_happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δ)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))) -
          ideal (physicalCubeRowSample U q rows p _hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ E + 2 * δ + (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_physical_jet_l1_perturbation_budgeted m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η hη hdim hLf hLg hCf hCg hjet hηT ideal hi δ happ E hmass
  let p' := fun j => translate (fun x => (base x : ℝ)) (p j)
  have hp' (j) : DegreeLE (1 : I → ℕ) (j.val + 1) (p' j) :=
    degreeLE_translate _ (fun _ => Nat.zero_lt_one) _ _ (hp j)
  have hm' (j) : ∀ ex, coefficients (p' j) ex ∈ U j :=
    coefficients_translate_mem (U j) _ (p j) (hm j)
  have hrank' (j) : HasLayerSamplingRank (j.val + 1) H R (U j) (p' j) :=
    (hasLayerSamplingRank_translate_iff _ _ H R (U j) (p j) (hp j)).mpr (hrank j)
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hT hn hd U μ ν p' hp' hm' q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank' hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb hη hdim hLf hLg hCf hCg hjet hηT ideal hi happ hmass
  refine ⟨hZ, ?_⟩
  have hid (z : Option (Fin dim) × I → ℤ) :
      physicalCubeRowSample U q rows p' hm' (standardPhysicalCubeOutput z) =
        physicalCubeRowSample U q rows p hm (translatePhysicalCube base (standardPhysicalCubeOutput z)) :=
    physicalCubeRowSample_translate U q rows p hm base _
  simp only [hid] at he
  exact he

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialAnalyticFactor
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (stride N : X → ℕ)
variable {τ : ℝ} (mesh : ℝ≥0) {modulus period : ℕ}
variable (t : X → SpatialSiteLabel α modulus 4 mesh) (site : Finset α)
variable {Y : Type*} (F : Y → ℂ)

local notation "smooth" => physicalResidueSpatialSmooth root D base residue stride 4 mesh
  (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site

noncomputable def physicalSpatialAnalyticContinuous (v : (X → ℝ) × Y) : ℂ :=
  smooth v.1 * F v.2

theorem physicalSpatialAnalytic_normalized [PseudoMetricSpace Y]
    (hN : ∀ x, 0 < N x) (hperiod : ∀ x, stride x * modulus ∣ period)
    (u : X → ℤ) (y : Y) :
    physicalResidueSpatialSiteFactor root D base residue stride 4 mesh
      (trimmedSpatialRootScale τ N stride) t site u * F y =
    physicalResidueSpatialMaskMod root D base residue stride 4 mesh hperiod t site
      (fun x => (u x : ZMod period)) *
    physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N mesh t site F
      (fun x => (u x : ℝ) / N x, y) := by
  rw [physicalResidueSpatialMaskMod_eval,
    physicalResidueSpatialSiteFactor_normalized root D base residue stride 4 mesh
      (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site
      (fun x => Nat.cast_ne_zero.mpr (hN x).ne')]
  exact mul_assoc _ _ _

theorem physicalSpatialAnalyticContinuous_bounds [PseudoMetricSpace Y]
    (hN : ∀ x, 0 < N x) (hstride : ∀ x, 0 < stride x) (hτ : 0 < τ) (hmesh : 0 < mesh)
    {L : ℝ≥0} (hF : LipschitzWith L F) (hFb : ∀ y, ‖F y‖ ≤ 1)
    {P EX ES Eτ : ℝ} (hP : 0 ≤ P)
    (hbox : (4 : ℝ) ≤ Real.exp P) (hinv : 1 / (mesh : ℝ) ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp EX)
    (hα : (Fintype.card (Unit ⊕ α) : ℝ) ≤ Real.exp ES)
    (hτexp : 1 / τ ≤ Real.exp Eτ) :
    (∀ v, ‖physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N mesh t site F v‖ ≤ 1) ∧
      LipschitzWith (⟨Real.exp (ES + EX + (3 * P + 6) + (Eτ + 8)), Real.exp_nonneg _⟩ + L)
        (physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N mesh t site F) := by
  let Lscale : ℝ≥0 := ⟨8 / τ, div_nonneg (by norm_num) hτ.le⟩
  have hscale (x : X) : |(N x : ℝ) / ((stride x : ℝ) * trimmedSpatialRootScale τ N stride x)| ≤ Lscale := by
    rw [trimmedSpatialRootScale_normalized_ratio N stride hτ hN hstride x]
    exact (abs_of_nonneg (div_nonneg (by norm_num) hτ.le)).le
  have hscaleExp : (Lscale : ℝ) ≤ Real.exp (Eτ + 8) := by
    calc
      _ = 8 * (1 / τ) := by change 8 / τ = 8 * (1 / τ); ring
      _ ≤ Real.exp 8 * Real.exp Eτ := mul_le_mul
        (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8)
        hτexp (div_nonneg zero_le_one hτ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hsp := physicalResidueSpatialSmooth_bounds root D base residue stride 4 mesh
    (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site hmesh hscale
  have hspLip := physicalResidueSpatialSmooth_pre_lipschitz root D base residue stride 4 mesh
    (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site hmesh hscale hP
    (by norm_num) hbox hinv hX hα hscaleExp
  exact VectorPolynomial.normalizedSiteTwistProduct_bounds smooth F hspLip hF hsp.1 hFb

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem narrowTrimmedSpatialWidths_fit {G J X : Type*} [Fintype G] [Fintype J]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (x : X) :
    physicalSiteWidth root (narrowTrimmedSpatialWidths W τ ξ N) x ≤
      (spatialTrimMargin τ N x : ℝ) :=
  (physicalSiteWidth_mono root (narrowTrimmedSpatialWidths_le hW hτ hξ1 N hN) x).trans
    (spatialTrimMargin_fits hW hτ.le root hroot N x)

theorem narrow_jointIntegerPhysicalSite_mem_box {G J X : Type*}
    [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hτhalf : τ ≤ 1/2) (hξ1 : ξ ≤ 1)
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) 1) :
    jointIntegerPhysicalSite root (z.1.val,z.2.val) ∈ integerBox N :=
  jointIntegerPhysicalSite_mem_box root N (spatialTrimMargin τ N)
    (fun x => (spatialTrimMargin_proper hτhalf N hN hsize x).le) _
    (narrowTrimmedSpatialWidths_fit hW hτ hξ1 root hroot N hN) z

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalRowsProbabilityMassSampling
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_translated_physical_jet_probability_mass (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U O → ℝ)
    (_hg0 : ∀ a z, 0 ≤ g a z)
    (_hgi : ∀ a, Integrable (g a) (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    (_hgmass : ∀ a, (∫ z, g a z ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) = 1)
    (f : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Cf : ℝ≥0) (_hf : LipschitzWith Lf f) (_hfb : ∀ z, ‖f z‖ ≤ Cf)
    (_hactual : ∀ z, law.complexMean (fun a => (g a z : ℂ)) = f (coveredJetAmbientTorus U 1 z))
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hCf : (Cf : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        law.mean (fun a => g a (physicalCubeRowSample U q rows p _hm
          (translatePhysicalCube base (standardPhysicalCubeOutput z))))) ≤ 1 + (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_l1_perturbation m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    Y _ law g hg0 hgi hgmass f Lf Cf hf hfb hactual η hη hdim hLf hCf hjet hηT
  have hnorm (z) : ‖f (coveredJetAmbientTorus U 1 z)‖ = law.mean (fun a => g a z) := by
    rw [← hactual, FiniteProbabilityWeights.complexMean_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (law.mean_nonneg (fun a => hg0 a z))]
  have hmass : (∫ z, ‖f (coveredJetAmbientTorus U 1 z) - 0‖
      ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ 1 := by
    simp only [sub_zero, hnorm]
    rw [law.integral_mean _ _ hgi]
    simp only [hgmass, law.mean_const, le_refl]
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    f (fun _ => 0) Lf 0 Cf 0 hf (LipschitzWith.const 0) hfb (fun _ => by simp)
    hη hdim hLf (by positivity) hCf (by positivity) hjet hηT (fun _ => 0) measurable_const
    (δ := 0) (fun _ => by simp) hmass
  refine ⟨hZ, ?_⟩
  simpa only [sub_zero, hnorm, mul_zero, add_zero] using he

theorem exists_translated_physical_jet_probability_window_mass (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    {K : Type*} [Fintype K] (root : K → ℤ) (D : Matrix (Fin dim) K ℤ)
    (residue : ColumnResiduePattern (Option K) I stride)
    (Hwindow : I → ℝ) (_hHwindow : ∀ i, 0 < Hwindow i)
    (_hcoef : ∀ i t, (∑ k, |(physicalCubeCoefficient root D t k : ℝ)|) ≤ Hwindow i)
    (_hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hwindow i)
    (_hwidth : ∀ z : Option (Fin dim) × I, ρ * H z.2 ≤ referenceJetEnvelopeWidths stride Hwindow z)
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U O → ℝ)
    (_hg0 : ∀ a z, 0 ≤ g a z)
    (_hgi : ∀ a, Integrable (g a) (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    (_hgmass : ∀ a, (∫ z, g a z ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) = 1)
    (f : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Cf : ℝ≥0) (_hf : LipschitzWith Lf f) (_hfb : ∀ z, ‖f z‖ ≤ Cf)
    (_hactual : ∀ z, law.complexMean (fun a => (g a z : ℂ)) = f (coveredJetAmbientTorus U 1 z))
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hCf : (Cf : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T) (_hsmall : 2 * η + ε ≤ 3),
    (∑ v ∈ spatialWindow Hwindow 4, law.mean (fun a => g a (physicalCubeRowSample U q rows p _hm
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride residue) stride v)))) ≤
      (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I)) *
        (∏ i, ∏ _t : Unit ⊕ Fin dim, Hwindow i) := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_probability_mass m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR K _ root D residue Hwindow hHwindow hcoef hscale hwidth
    Y _ law g hg0 hgi hgmass f Lf Cf hf hfb hactual η hη hdim hLf hCf hjet hηT hsmall
  let target := columnResiduePattern stride (standardPhysicalCubeFrame
    (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride residue)))
  let V := referenceJetEnvelopeWidths (q := dim) stride Hwindow
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR {target} (Finset.singleton_nonempty _)
    V (referenceJetEnvelopeWidths_pos stride hs Hwindow hHwindow) hwidth law g hg0 hgi hgmass
    f Lf Cf hf hfb hactual hη hdim hLf hCf hjet hηT
  have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root D residue Hwindow hHwindow hcoef hscale
    (fun v => law.mean (fun a => g a (physicalCubeRowSample U q rows p hm (translatePhysicalCube base v))))
    (fun v => law.mean_nonneg (fun a => hg0 a _)) hZ
  rw [referenceJetEnvelope_volume stride hs Hwindow] at hraw
  have hvol : 0 ≤ (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I) *
      (∏ i, ∏ _t : Unit ⊕ Fin dim, Hwindow i) := by
    apply mul_nonneg (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
    exact Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun _ _ => (hHwindow i).le))
  have hfour := he.trans (show 1 + (2 * η + ε) ≤ 4 by linarith)
  have hout := hraw.trans (mul_le_mul_of_nonneg_left hfour hvol)
  simp_rw [← physicalResidueReconstruction_translate] at hout
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hout

theorem exists_translated_physical_jet_density_window_mass (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    {K : Type*} [Fintype K] (root : K → ℤ) (D : Matrix (Fin dim) K ℤ)
    (residue : ColumnResiduePattern (Option K) I stride)
    (Hwindow : I → ℝ) (_hHwindow : ∀ i, 0 < Hwindow i)
    (_hcoef : ∀ i t, (∑ k, |(physicalCubeCoefficient root D t k : ℝ)|) ≤ Hwindow i)
    (_hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hwindow i)
    (_hwidth : ∀ z : Option (Fin dim) × I, ρ * H z.2 ≤ referenceJetEnvelopeWidths stride Hwindow z)
    (g : EuclideanJetLayers U O → ℝ)
    (_hg0 : ∀ z, 0 ≤ g z)
    (_hgi : Integrable g (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    (_hgmass : (∫ z, g z ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) = 1)
    (f : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Cf : ℝ≥0) (_hf : LipschitzWith Lf f) (_hfb : ∀ z, ‖f z‖ ≤ Cf)
    (_hactual : ∀ z, (g z : ℂ) = f (coveredJetAmbientTorus U 1 z))
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hCf : (Cf : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T) (_hsmall : 2 * η + ε ≤ 3),
    (∑ v ∈ spatialWindow Hwindow 4, g (physicalCubeRowSample U q rows p _hm
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride residue) stride v))) ≤
      (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I)) *
        (∏ i, ∏ _t : Unit ⊕ Fin dim, Hwindow i) := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_probability_window_mass m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR K _ root D residue Hwindow hHwindow hcoef hscale hwidth
    g hg0 hgi hgmass f Lf Cf hf hfb hactual η hη hdim hLf hCf hjet hηT hsmall
  let law : FiniteProbabilityWeights Unit := {
    weight := fun _ => 1
    nonneg := fun _ => zero_le_one
    total := by simp }
  have he := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR root D residue Hwindow hHwindow hcoef hscale hwidth
    law (fun _ => g) (fun _ => hg0) (fun _ => hgi) (fun _ => hgmass) f Lf Cf hf hfb
    (fun z => by simpa only [law.complexMean_const] using hactual z)
    hη hdim hLf hCf hjet hηT hsmall
  simpa only [law.mean_const] using he

end Erdos3.BooleanCubeKernel

end

end OAI
end


