-- Prove2me | Definitions.Def_OAIQ075A008
-- name    : OAIQ075A008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T07:58:24.572061+00:00
-- url     : https://prove2.me/theorems/30ac6814-5f4a-4c52-ae6a-0d226ec94d10
-- title:
--   Definitions bundle OAIQ075A008 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 18 definitions, 5 instances and 33 theorems. The definitions and types are `OAI.BoundedHochschild.KadisonRingrose.stinespringShift`, `OAI.BoundedHochschild.KadisonRingrose.unitCornerEquiv`, `OAI.BoundedHochschild.KadisonRingrose.unitCornerTrace`, `OAI.BoundedHochschild.KadisonRingrose.weakUnitaryPullback`, `OAI.Generator.MatrixUnitSystem.algebra`, `OAI.Generator.MatrixUnitSystem.amplify`, `OAI.Generator.MatrixUnitSystem.relativeStar`, `OAI.Generator.Tracial.boundedInclusion`, `OAI.Generator.Tracial.conjugateLinear`, `OAI.Generator.Tracial.quotientInclusion`, `OAI.Generator.Tracial.restrictedTrace`, `OAI.PopaCorner.strongEquiv`, `OAI.PopaCorner.weakSpace`, `OAI.PopaTypeII.NoAbelianCorners`, `OAI.PopaTypeII.NoTypeICentralPart`, `OAI.PopaTypeII.TypeICorner`, `OAI.UltrapowerBridge.quotientTrace`, `OAI.UltrapowerBridge.traceRep`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_Corners`, `BoundedHochschild_FiniteCentralDecomposition`, `BoundedHochschild_Frames`, `BoundedHochschild_NormalOrbitInvariance`, `BoundedHochschild_ProperlyInfiniteCorners`, `BoundedHochschild_StinespringLeftAction`, `BoundedHochschild_TracialDecomposition`, `BoundedHochschild_UniformProjectionSums`, `FactorGeneration_GroupTrace`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixUnits`, `FactorGeneration_TraceTopology`, `FactorGeneration_TracialInclusion`, `FactorGeneration_Ultrapower`, `TracialCohomology_Corners`, `TracialCohomology_TracialPrimitives`, `TracialCohomology_TypeII`.
--
--   **Imports.** It imports the bundles `OAIQ075A000`, `OAIQ075A001`, `OAIQ075A002` and `OAIQ075A003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A013`, `OAIQ075A014`, `OAIQ075A015`, `OAIQ075A016` and `OAIQ075A017`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A000
import Definitions.Def_OAIQ075A001
import Definitions.Def_OAIQ075A002
import Definitions.Def_OAIQ075A003

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Corners
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral corners, corner preduals and factor structure. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma mem_corner {p a : M} {hp : IsStarProjection p} :
    a ∈ corner p hp ↔ p*a=a ∧ a*p=a := Iff.rfl

end HochschildCorners

 

 

 

open Filter Topology
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_Corners
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.PopaCorner.trace_apply _root_.OAI.PopaPatching.Rep.inCorner_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corners for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

instance instNormedRing : NormedRing (algebra hp) where
  __ := (inferInstance : NonUnitalNormedRing (algebra hp))
  __ := instRing hp
instance instNormedAlgebra : NormedAlgebra ℂ (algebra hp) where
  norm_smul_le c x := norm_smul_le c x
instance instCStarAlgebra : CStarAlgebra (algebra hp) where

instance instStarOrderedRing : StarOrderedRing (algebra hp) := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z:M)+(x:M) ≤ (z:M)+(y:M)
    simpa only [add_comm] using add_le_add_left (show (x:M) ≤ (y:M) from h) (z:M)
  · intro a
    constructor
    · intro ha
      have hmem : CFC.sqrt (a:M) ∈ algebra hp := by
        rw [CFC.sqrt_eq_real_sqrt (a:M) (show 0 ≤ (a:M) from ha)]
        exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
      refine ⟨⟨CFC.sqrt (a:M),hmem⟩,Subtype.ext ?_⟩
      change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a:M))).star_eq]
      exact (CFC.sqrt_mul_sqrt_self (a:M) ha).symm
    · rintro ⟨b,rfl⟩
      exact star_mul_self_nonneg (b:M)

end PopaCorner

open Filter Topology
open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {p : M} (hp : IsStarProjection p)

def weakSpace : Submodule ℂ (WeakDual ℂ X) :=
  (algebra hp).toNonUnitalSubalgebra.toSubmodule.comap (WeakAlgebra.weakEquiv e).toLinearMap

def strongEquiv : WeakSubspace.strong (weakSpace e hp) ≃ₗᵢ⋆[ℂ] algebra hp where
  toFun f := ⟨e f.val,by
    have hh := (WeakSubspace.mem_strong (weakSpace e hp) f.val).mp f.property
    exact hh⟩
  invFun a := ⟨e.symm a.val,by
    rw [WeakSubspace.mem_strong]
    change e (e.symm a.val) ∈ algebra hp
    simp⟩
  left_inv f := by apply Subtype.ext; exact e.symm_apply_apply f.val
  right_inv a := by apply Subtype.ext; exact e.apply_symm_apply a.val
  map_add' f g := by apply Subtype.ext; exact map_add e f.val g.val
  map_smul' c f := by apply Subtype.ext; exact e.map_smulₛₗ c f.val
  norm_map' f := e.norm_map f.val

end PopaCorner

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_TypeII
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Type ii for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def NoAbelianCorners (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ (p : M) (hp : IsStarProjection p), p ≠ 0 →
    ∃ a b : PopaCorner.algebra hp, ¬ Commute a b

end PopaTypeII

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_TracialPrimitives
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tracial primitives for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder

open scoped ComplexOrder
namespace PopaTypeII
open BoundedHochschild PopaCenter PopaCorner PopaCorners
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def TypeICorner {z : M} (_hz : IsStarProjection z) : Prop :=
  ∀ p : M, ∀ _hp : IsStarProjection p, p ≤ z → p ≠ 0 →
    ∃ q : M, ∃ hq : IsStarProjection q, q ≤ p ∧ q ≠ 0 ∧ AbelianProjection hq

def NoTypeICentralPart (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ z : M, ∀ hz : IsStarProjection z, Central z → z ≠ 0 → ¬ TypeICorner hz

end PopaTypeII

open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteCentralDecomposition
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The maximal finite central cut, constructed without an assumed trace. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_trans {p : M} (hp : IsStarProjection p)
    (q : HochschildCorners.Corner p hp) (hfinite : FiniteCorner q) :
    FiniteCorner (q : M) := by
  intro a hL hR haa
  have hpL : p * a = a := by
    calc
      p * a = p * ((q : M) * a) := by rw [hL]
      _ = a := by rw [← mul_assoc, q.property.1, hL]
  have hpR : a * p = a := by
    calc
      a * p = (a * (q : M)) * p := by rw [hR]
      _ = a := by rw [mul_assoc, q.property.2, hR]
  let b : HochschildCorners.Corner p hp := ⟨a, hpL, hpR⟩
  exact congrArg Subtype.val
    (hfinite b (Subtype.ext hL) (Subtype.ext hR) (Subtype.ext haa))

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Frames
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal frames of partial isometries and maximal frame construction. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace Frame
variable {n : ℕ}
instance instLE : LE (Frame M n) := ⟨fun v w => ∀ i, v.part i ≤ w.part i⟩

end Frame
end HochschildComparison

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UniformProjectionSums
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform summation of orthogonal projections

The positive case of the gliding-block argument in Ringrose, Theorem 4.7:
uniform decay on orthogonal sequences implies uniform complete additivity.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [StarOrderedRing M] in
/-- Uniform orthogonal-sequence decay forces uniformly small remainders of
arbitrary orthogonal sums. Only the positive, completely additive case is used. -/
theorem uniform_orthogonal_sum_remainder
    (K : Set (StrongDual ℂ M))
    (hadd : ∀ F ∈ K, CompletelyAdditive F)
    (hdecay : ∀ q : ℕ → M, (∀ n, IsStarProjection (q n)) →
      (∀ m n, m ≠ n → q m * q n = 0) → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ F ∈ K, ‖F (q n)‖ < ε)
    (I : Type u) (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (P : M) (hP : IsStarProjection P) (hu : ∀ i, p i ≤ P)
    (hl : ∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset I, ∀ F ∈ K, (F (P - ∑ i ∈ s, p i)).re < ε := by
  classical
  by_contra hfail
  push Not at hfail
  have hb : ∀ s : Finset I, ∃ t : Finset I, Disjoint s t ∧
      ∃ F ∈ K, ε / 2 < (F (∑ i ∈ t, p i)).re := by
    intro s
    obtain ⟨F, hFK, hbad⟩ := hfail s
    have ht := Complex.continuous_re.tendsto (F P) |>.comp (hadd F hFK I p hp ho P hP hu hl)
    have hevent : ∀ᶠ t : Finset I in atTop,
        (F P).re - ε / 2 < (∑ i ∈ t, F (p i)).re :=
      (tendsto_order.mp ht).1 _ (by linarith)
    obtain ⟨t, hts, htlarge⟩ := ((eventually_ge_atTop s).and hevent).exists
    refine ⟨t \ s, Finset.disjoint_sdiff, F, hFK, ?_⟩
    have hsum : (∑ i ∈ t \ s, p i) + ∑ i ∈ s, p i = ∑ i ∈ t, p i :=
      Finset.sum_sdiff hts
    have hval := congrArg (fun a : M => (F a).re) hsum
    simp only [map_add, Complex.add_re, map_sum] at hval
    simp only [map_sub, Complex.sub_re, map_sum] at hbad
    rw [map_sum]
    linarith
  obtain ⟨b, hdis, hb⟩ := disjoint_finset_sequence
    (fun t : Finset I => ∃ F ∈ K, ε / 2 < (F (∑ i ∈ t, p i)).re) hb
  let q (n : ℕ) : M := ∑ i ∈ b n, p i
  have hq (n) : IsStarProjection (q n) := orthogonal_projection_finset_sum p hp ho (b n)
  have hqo (m n : ℕ) (hmn : m ≠ n) : q m * q n = 0 := by
    dsimp [q]
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact ho i j (fun hij => Finset.disjoint_left.mp (hdis m n hmn) hi (hij ▸ hj))
  obtain ⟨n, hn⟩ := (hdecay q hq hqo (ε / 2) (half_pos hε)).exists
  obtain ⟨F, hFK, hlarge⟩ := hb n
  have hsmall := hn F hFK
  have hre := Complex.re_le_norm (F (q n))
  exact (not_lt_of_ge (le_trans hlarge.le hre)) hsmall

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalOrbitInvariance
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity and invariance of the compact normal-state orbit. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Unitary pullback is weak-star continuous. -/
def weakUnitaryPullback (u : unitary M) : WeakDual ℂ M →L[ℂ] WeakDual ℂ M where
  toFun F := StrongDual.toWeakDual (unitaryPullback (WeakDual.toStrongDual F) u)
  map_add' F G := by apply WeakDual.toStrongDual.injective; ext a; rfl
  map_smul' c F := by apply WeakDual.toStrongDual.injective; ext a; rfl
  cont := WeakDual.continuous_of_continuous_eval (fun a =>
    WeakDual.eval_continuous ((u : M) * a * star (u : M)))

lemma unitaryOrbitHull_invariant (F : StrongDual ℂ M) (u : unitary M)
    {H : StrongDual ℂ M} (hH : H ∈ unitaryOrbitHull F) :
    unitaryPullback H u ∈ unitaryOrbitHull F := by
  have hconv : Convex ℝ (unitaryOrbitHull F) := (convex_convexHull ℝ _).closure
  have hclosed : IsClosed (unitaryOrbitHull F) := isClosed_closure
  apply closure_minimal (t := (unitaryDualEquiv u) ⁻¹' unitaryOrbitHull F) _
    (hclosed.preimage (unitaryDualEquiv u).continuous) hH
  apply convexHull_min _
    (hconv.linear_preimage ((unitaryDualEquiv u).toLinearEquiv.restrictScalars ℝ).toLinearMap)
  rintro _ ⟨v, rfl⟩
  change unitaryPullback (unitaryPullback F v) u ∈ unitaryOrbitHull F
  rw [unitaryPullback_mul]
  exact subset_closure (subset_convexHull ℝ _ (Set.mem_range_self (v * u)))

lemma weakOrbitClosure_invariant (F : StrongDual ℂ M) (u : unitary M)
    {H : WeakDual ℂ M} (hH : H ∈ weakFunctionalClosure (unitaryOrbitHull F)) :
    weakUnitaryPullback u H ∈ weakFunctionalClosure (unitaryOrbitHull F) := by
  apply closure_minimal (t := (weakUnitaryPullback u) ⁻¹'
    weakFunctionalClosure (unitaryOrbitHull F)) _
    (isClosed_closure.preimage (weakUnitaryPullback u).continuous) hH
  rintro _ ⟨G, hG, rfl⟩
  exact subset_closure ⟨unitaryPullback G u, unitaryOrbitHull_invariant F u hG, rfl⟩

variable [PartialOrder M] [StarOrderedRing M]

omit [CompleteSpace X] [PartialOrder M] [StarOrderedRing M] in
lemma weakPredualOrbit_convex (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : StrongDual ℂ M) :
    Convex ℝ ((weakPredualMap e) ⁻¹' weakFunctionalClosure (unitaryOrbitHull F)) := by
  intro x hx y hy a b ha hb hab
  have heq : weakPredualMap e (a • x + b • y) =
      a • weakPredualMap e x + b • weakPredualMap e y := by
    exact (weakPredualRealMap e).map_add (a • x) (b • y) |>.trans
      (congrArg₂ (· + ·) ((weakPredualRealMap e).map_smul a x)
        ((weakPredualRealMap e).map_smul b y))
  change weakPredualMap e (a • x + b • y) ∈ weakFunctionalClosure (unitaryOrbitHull F)
  rw [heq]
  exact (weakOrbitClosure_convex F) hx hy ha hb hab

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProperlyInfiniteCorners
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner transport and finiteness obstructions for properly infinite projections. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison HochschildCorners FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [StarOrderedRing M] in
lemma properlyInfinite_from_corner {p : M} (hp : IsStarProjection p)
    {q : Corner p hp} (h : ProperlyInfiniteProjection q) : ProperlyInfiniteProjection (q : M) := by
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := h
  exact ⟨partialIsoFromCorner hp v, partialIsoFromCorner hp w,
    congrArg Subtype.val hvi, congrArg Subtype.val hwi,
    hvf, hwf, congrArg Subtype.val ho⟩

lemma properlyInfinite_finite_eq_zero {p : M} (hp : IsStarProjection p)
    (hproper : ProperlyInfiniteProjection p) (hfinite : FiniteCorner p) : p = 0 := by
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := hproper
  have hv : v.final = p := hfinite (v : M) (partialIso_left_support hp v hvf)
    (partialIso_right_support hp v (hvi ▸ le_rfl)) hvi
  have hw : w.final = p := hfinite (w : M) (partialIso_left_support hp w hwf)
    (partialIso_right_support hp w (hwi ▸ le_rfl)) hwi
  rw [hv, hw, hp.isIdempotentElem.eq] at ho
  exact ho

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteAlgebra_of_equiv {N : Type*} [CStarAlgebra N]
    (φ : M ≃⋆ₐ[ℂ] N) (h : FiniteAlgebra N) : FiniteAlgebra M := by
  intro a ha
  apply φ.injective
  change φ (a * star a) = φ 1
  rw [map_mul, map_star, map_one]
  exact h (φ a) (by rw [← map_star, ← map_mul, ha, map_one])

lemma properlyInfinite_central_cut {p z : M} (hp : IsStarProjection p)
    (hz : CentralProjection z) (h : ProperlyInfiniteProjection p) :
    ProperlyInfiniteProjection (z * p) := by
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := h
  let v' := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) v
  let w' := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) w
  have hzp : IsStarProjection (z * p) := hz.1.mul hp (hz.2 p)
  have hvle : v'.final ≤ z * p := by
    apply (v'.final_proj.le_iff_mul_eq_left hzp).mpr
    rw [centralCutPartialIso_final,
      central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq),
      (v.final_proj.le_iff_mul_eq_left hp).mp hvf]
  have hwle : w'.final ≤ z * p := by
    apply (w'.final_proj.le_iff_mul_eq_left hzp).mpr
    rw [centralCutPartialIso_final,
      central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq),
      (w.final_proj.le_iff_mul_eq_left hp).mp hwf]
  refine ⟨v', w', ?_, ?_, hvle, hwle, ?_⟩
  · rw [centralCutPartialIso_initial, hvi]
  · rw [centralCutPartialIso_initial, hwi]
  · rw [centralCutPartialIso_final, centralCutPartialIso_final,
      central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq), ho, mul_zero]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringLeftAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Left multiplication on the auxiliary positive-kernel Hilbert space. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def stinespringShift (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M)
    (x : StinespringPreSpace φ) : StinespringPreSpace φ :=
  Finsupp.mapDomain (stinespringLeftLabel b) x

lemma stinespringShift_one (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (x : StinespringPreSpace φ) : stinespringShift φ 1 x = x := by
  have he : stinespringLeftLabel (H := H) (1 : M) = id := by
    funext p
    simp only [stinespringLeftLabel, one_mul, id_eq]
  unfold stinespringShift
  dsimp only [StinespringPreSpace, PositiveKernelPreSpace] at x ⊢
  rw [he, Finsupp.mapDomain_id]

lemma stinespringShift_mul (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (a b : M) (x : StinespringPreSpace φ) :
    stinespringShift φ a (stinespringShift φ b x) = stinespringShift φ (a * b) x := by
  have he : stinespringLeftLabel (H := H) a ∘ stinespringLeftLabel b =
      stinespringLeftLabel (a * b) := by
    funext p
    simp only [Function.comp_apply, stinespringLeftLabel, mul_assoc]
  unfold stinespringShift
  dsimp only [StinespringPreSpace, PositiveKernelPreSpace] at x ⊢
  rw [← Finsupp.mapDomain_comp, he]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TracialDecomposition
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.nestedCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners
open scoped ComplexOrder

universe u

section CornerEquivalence
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- The unit corner is canonically the original algebra. -/
def unitCornerEquiv : Corner (1 : M) (IsStarProjection.one M) ≃⋆ₐ[ℂ] M where
  toFun := Subtype.val
  invFun := fun a => ⟨a, by simp only [mem_corner, one_mul, mul_one, and_self]⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  map_star' := fun _ => rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma unitCornerEquiv_apply (a : Corner (1 : M) (IsStarProjection.one M)) :
    unitCornerEquiv a = (a : M) := rfl

end CornerEquivalence

section TracialCorner
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

/-- The original trace restricted along the canonical unit-corner equivalence. -/
def unitCornerTrace : Corner (1 : M) (IsStarProjection.one M) →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp (unitCornerEquiv.toAlgEquiv.toLinearMap)
  monotone' := fun _ _ h => τ.monotone h

omit [StarOrderedRing M] in
@[simp] lemma unitCornerTrace_apply (a : Corner (1 : M) (IsStarProjection.one M)) :
    unitCornerTrace τ a = τ (a : M) := rfl

end TracialCorner

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.UltrapowerBridge.TracialRepresentation.trace_add _root_.OAI.UltrapowerBridge.TracialRepresentation.trace_sub _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_le_norm (T : Algebra (M := M)) : τ.norm₂ T ≤ ‖T‖ := by
  have h := (T : H →L[ℂ] H).le_opNorm τ.vector
  simpa [norm₂, τ.norm_vector] using h

theorem norm_trace_le_norm₂ (T : Algebra (M := M)) : ‖τ.trace T‖ ≤ τ.norm₂ T := by
  simpa [trace, norm₂, τ.norm_vector] using norm_inner_le_norm τ.vector ((T : H →L[ℂ] H) τ.vector)

end TracialRepresentation

end

end UltrapowerBridge

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

variable [StarModule ℂ A]

def algebra : StarSubalgebra ℂ A := E.hom.range

theorem mem_algebra (x : A) : x ∈ E.algebra ↔
    ∃ a : Matrix ι ι ℂ, (∑ i, ∑ j, a i j • E.entry i j) = x := Iff.rfl

theorem entry_mem (i j : ι) : E.entry i j ∈ E.algebra := by
  exact ⟨Matrix.single i j 1, (E.hom_single i j 1).trans (one_smul _ _)⟩

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

theorem algebra_le_iff (S : StarSubalgebra ℂ A) :
    E.algebra ≤ S ↔ ∀ i j, E.entry i j ∈ S := by
  constructor
  · exact fun h i j => h (E.entry_mem i j)
  · intro h x hx
    obtain ⟨a,rfl⟩ := (E.mem_algebra x).mp hx
    exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (h i j) _

theorem commute_algebra_iff (x : A) :
    (∀ a ∈ E.algebra, Commute a x) ↔ ∀ i j, Commute (E.entry i j) x := by
  constructor
  · exact fun h i j => h _ (E.entry_mem i j)
  · intro h a ha
    obtain ⟨b,rfl⟩ := (E.mem_algebra a).mp ha
    show (∑ i, ∑ j, b i j • E.entry i j)*x=x*(∑ i, ∑ j, b i j • E.entry i j)
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      (h _ _).eq]

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def amplify (o : ι) (x : A) : A := ∑ i, E.entry i o*x*E.entry o i

omit [StarModule ℂ A] in
theorem amplify_zero (o : ι) : E.amplify o 0=0 := by simp [amplify]

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators

open scoped BigOperators

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem TracialRepresentation.trace_smul (c : ℂ) (a : M.toStarSubalgebra) :
    τ.trace (c • a) = c*τ.trace a := inner_smul_right _ _ _

def traceRep (a : Bounded M) : ℂ := limUnder (ω : Filter ℕ) (fun n => τ.trace (a.val n))

theorem traceRep_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.trace (a.val n)) (ω : Filter ℕ) (𝓝 (traceRep τ ω a)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨C,_,ha⟩ := a.property
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds
    (ω.map (fun n => τ.trace (a.val n))) (by
      apply le_principal_iff.mpr
      change {n | τ.trace (a.val n) ∈ Metric.closedBall 0 C} ∈ (ω : Filter ℕ)
      exact Filter.Eventually.of_forall (fun n => by
        simpa using ((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (ha n)))
  exact ⟨z,hz⟩

theorem traceRep_eq_of_rel {a b : Bounded M} (h : TraceRel τ (ω : Filter ℕ) a b) :
    traceRep τ ω a = traceRep τ ω b := by
  have hz : Tendsto (fun n => ‖τ.trace (a.val n)-τ.trace (b.val n)‖)
      (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
    rw [← τ.trace_sub]
    exact τ.norm_trace_le_norm₂ _
  have hnorm := ((traceRep_tendsto τ ω a).sub (traceRep_tendsto τ ω b)).norm
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hnorm hz))

/-- The actual ultralimit trace on the operator-algebra quotient. -/
def quotientTrace : TracialQuotient τ (ω : Filter ℕ) → ℂ :=
  Quotient.lift (traceRep τ ω) (fun _ _ h => traceRep_eq_of_rel τ ω h)

@[simp] theorem quotientTrace_mk (a : Bounded M) :
    quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) a) = traceRep τ ω a := rfl

@[simp] theorem quotientTrace_one : quotientTrace τ ω 1 = 1 := by
  apply tendsto_nhds_unique (traceRep_tendsto τ ω 1)
  simp

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Operator-norm bounded trace-norm limits remain in the same ball of the algebra, without requiring a cyclic trace vector. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

def conjugateLinear (u : unitary M.toStarSubalgebra) :
    M.toStarSubalgebra →ₗ[ℂ] M.toStarSubalgebra where
  toFun a := (u : M.toStarSubalgebra) * a * star (u : M.toStarSubalgebra)
  map_add' _ _ := by simp only [mul_add, add_mul]
  map_smul' _ _ := by simp only [mul_smul_comm, smul_mul_assoc]; rfl

@[simp] theorem conjugateLinear_one (a : M.toStarSubalgebra) : conjugateLinear 1 a = a := by
  simp [conjugateLinear]

end

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TracialInclusion
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Generator.Tracial

/-! The restricted faithful trace and the actual P^omega -> M^omega
inclusion. All constructions are on the bounded-sequence quotient. -/
noncomputable section
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

def restrictedTrace : TracialRepresentation P where
  vector := τ.vector
  norm_vector := τ.norm_vector
  cyclic a b := τ.cyclic (coordinateInclusion hPM a) (coordinateInclusion hPM b)
  separating a ha := by
    have h := τ.separating (coordinateInclusion hPM a) ha
    apply Subtype.ext
    exact congrArg (fun x : M.toStarSubalgebra => x.val) h

@[simp] theorem restrictedTrace_trace (a : P.toStarSubalgebra) :
    (restrictedTrace τ hPM).trace a = τ.trace (coordinateInclusion hPM a) := rfl

@[simp] theorem restrictedTrace_norm₂ (a : P.toStarSubalgebra) :
    (restrictedTrace τ hPM).norm₂ a = τ.norm₂ (coordinateInclusion hPM a) := rfl

def boundedInclusion : Bounded P →⋆ₐ[ℂ] Bounded M where
  toFun a := ⟨fun n => coordinateInclusion hPM (a.val n), a.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def quotientInclusion (l : Filter ℕ) :
    TracialQuotient (restrictedTrace τ hPM) l →⋆ₐ[ℂ] TracialQuotient τ l where
  toFun := Quotient.map (boundedInclusion hPM) (fun _ _ h => h)
  map_one' := rfl
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl
  map_zero' := rfl
  map_add' a b := by
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => rfl
  commutes' _ := rfl
  map_star' a := by induction a using Quotient.inductionOn with | h a => rfl

@[simp] theorem quotientInclusion_mk (l : Filter ℕ) (a : Bounded P) :
    quotientInclusion τ hPM l (quotientMap (restrictedTrace τ hPM) l a) =
      quotientMap τ l (boundedInclusion hPM a) := rfl

@[simp] theorem quotientInclusion_trace (ω : Ultrafilter ℕ)
    (a : TracialQuotient (restrictedTrace τ hPM) (ω : Filter ℕ)) :
    quotientTrace τ ω (quotientInclusion τ hPM (ω : Filter ℕ) a) =
      quotientTrace (restrictedTrace τ hPM) ω a := by
  induction a using Quotient.inductionOn with
  | h a =>
    change traceRep τ ω (boundedInclusion hPM a) = traceRep (restrictedTrace τ hPM) ω a
    exact tendsto_nhds_unique (traceRep_tendsto τ ω (boundedInclusion hPM a))
      (traceRep_tendsto (restrictedTrace τ hPM) ω a)

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra)

def relativeStar : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {x | ∃ a : E.commutant, a.val.val=x}
  zero_mem' := ⟨0,rfl⟩
  one_mem' := ⟨1,rfl⟩
  add_mem' := by rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,rfl⟩
  mul_mem' := by rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a*b,rfl⟩
  algebraMap_mem' z := ⟨algebraMap ℂ E.commutant z,rfl⟩
  star_mem' := by rintro x ⟨a,rfl⟩; exact ⟨star a,rfl⟩

theorem relativeStar_mem (x : H →L[ℂ] H) :
    x ∈ E.relativeStar ↔ x ∈ M ∧ ∀ i j, (E.entry i j).val*x=x*(E.entry i j).val := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a.val.property,fun i j => congrArg Subtype.val (a.property i j).eq⟩
  · rintro ⟨hx,hc⟩
    exact ⟨⟨⟨x,hx⟩,fun i j => Subtype.ext (hc i j)⟩,rfl⟩

theorem relativeStar_bicommutant :
    Set.centralizer (Set.centralizer (E.relativeStar : Set (H →L[ℂ] H))) =
      (E.relativeStar : Set (H →L[ℂ] H)) := by
  apply Set.Subset.antisymm
  · intro a ha
    apply (E.relativeStar_mem a).mpr
    constructor
    · rw [← SetLike.mem_coe,← M.centralizer_centralizer]
      exact fun b hb => ha b (fun c hc => hb c ((E.relativeStar_mem c).mp hc).1)
    · intro i j
      exact ha (E.entry i j).val
        (fun b hb => (((E.relativeStar_mem b).mp hb).2 i j).symm)
  · intro a ha b hb
    exact (hb a ha).symm

end

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/

open UltrapowerBridge Tracial

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end


