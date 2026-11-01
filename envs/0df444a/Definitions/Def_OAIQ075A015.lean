-- Prove2me | Definitions.Def_OAIQ075A015
-- name    : OAIQ075A015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:09:35.420991+00:00
-- url     : https://prove2.me/theorems/d140b495-f4a2-4c76-a31f-2b15c43e5fbd
-- title:
--   Definitions bundle OAIQ075A015 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 23 definitions, 1 inductive type or structure, 2 instances and 43 theorems. The definitions and types are `OAI.Generator.Tracial.PartialIsometry.adjoint`, `OAI.Generator.Tracial.PartialIsometry.patch`, `OAI.Generator.Tracial.PartialIsometry.target`, `OAI.Generator.Tracial.SpectralInterval`, `OAI.Generator.Tracial.SpectralInterval.highProjection`, `OAI.Generator.Tracial.SpectralInterval.midpoint`, `OAI.Generator.Tracial.algebraOrbit`, `OAI.Generator.Tracial.ambientUnitary`, `OAI.Generator.Tracial.approximationCStar`, `OAI.Generator.Tracial.cornerCutCStar`, `OAI.Generator.Tracial.cornerCutLE`, `OAI.Generator.Tracial.cornerCutOrder`, `OAI.Generator.Tracial.cornerCutPreorder`, `OAI.Generator.Tracial.cornerSpectralCut`, `OAI.Generator.Tracial.intervalLE`, `OAI.Generator.Tracial.intervalOrder`, `OAI.Generator.Tracial.intervalPreorder`, `OAI.Generator.Tracial.polarOrder`, `OAI.Generator.Tracial.polarSupportsCStar`, `OAI.Generator.Tracial.polarSupportsOrder`, `OAI.Generator.Tracial.positiveSupport`, `OAI.Generator.Tracial.positiveSupportCStar`, `OAI.Generator.Tracial.positiveSupportOrder`, `OAI.Generator.Tracial.subalgebraUnitaries`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BoundedHochschild_Frames`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/Frames.lean), [`BoundedHochschild_MixedWords`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/MixedWords.lean), [`FactorGeneration_HilbertLimits`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/HilbertLimits.lean), [`FactorGeneration_OrbitMinima`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/OrbitMinima.lean), [`FactorGeneration_PartialIsometries`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/PartialIsometries.lean), [`FactorGeneration_SpectralApproximation`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/SpectralApproximation.lean), [`FactorGeneration_SpectralPinching`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/SpectralPinching.lean), [`FactorGeneration_Supports`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Supports.lean), [`FactorGeneration_TraceTopology`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/TraceTopology.lean), [`FactorGeneration_Ultrapower`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Ultrapower.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A007`, `OAIQ075A008` and `OAIQ075A009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A020`, `OAIQ075A021`, `OAIQ075A022`, `OAIQ075A023` and `OAIQ075A024`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A007
import Definitions.Def_OAIQ075A008
import Definitions.Def_OAIQ075A009

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MixedWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-word Taylor expansions, moment corners and patch coefficients. -/

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
open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]


variable {I : Type*} (F : I → M)
@[simp] lemma wordCoeff_some (i : I) : wordCoeff F (some i)=F i := rfl
end HochschildPatching

 

 

open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Frames
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
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
instance instPartialOrder : PartialOrder (Frame M n) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ h1 h2 i := (h1 i).trans (h2 i)
  le_antisymm _ _ h1 h2 := ext fun i => le_antisymm (h1 i) (h2 i)

end Frame
end HochschildComparison

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology
namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

/-- Unitary norm bound without requiring a separate nontriviality instance. -/
theorem unitary_norm_le (w : M.toStarSubalgebra) (hw : star w*w = 1) : ‖w‖ ≤ 1 := by
  have h : ‖star w*w‖ = ‖w‖*‖w‖ := CStarRing.norm_star_mul_self
  rw [hw] at h
  have hone : ‖(1 : M.toStarSubalgebra)‖ ≤ 1 := operator_norm_one_le
  nlinarith [norm_nonneg w]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

theorem trace_ball_convex (C : ℝ) :
    Convex ℝ {ξ : H | ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧
      (b : H →L[ℂ] H) τ.vector = ξ} := by
  intro x hx y hy s t hs ht hst
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨s • a + t • b, ?_, rfl⟩
  calc
    ‖s • a + t • b‖ ≤ ‖s • a‖ + ‖t • b‖ := norm_add_le _ _
    _ = s * ‖a‖ + t * ‖b‖ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
    _ ≤ s * C + t * C := add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)
    _ = C := by rw [← add_mul, hst, one_mul]

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

theorem conjugateLinear_mul (u v : unitary M.toStarSubalgebra) (a : M.toStarSubalgebra) :
    conjugateLinear (u*v) a = conjugateLinear u (conjugateLinear v a) := by
  change ((u : M.toStarSubalgebra)*(v : M.toStarSubalgebra))*a*star ((u : M.toStarSubalgebra)*(v : M.toStarSubalgebra)) = _
  simp only [conjugateLinear, LinearMap.coe_mk, AddHom.coe_mk, star_mul, mul_assoc]

theorem conjugate_norm_le (u : unitary M.toStarSubalgebra) (a : M.toStarSubalgebra) :
    ‖conjugateLinear u a‖ ≤ ‖a‖ := by
  have hu := unitary_norm_le (u : M.toStarSubalgebra) (by simp)
  have hs := unitary_norm_le (star (u : M.toStarSubalgebra)) (by simp)
  calc
    ‖conjugateLinear u a‖ ≤ (‖(u : M.toStarSubalgebra)‖ * ‖a‖) * ‖star (u : M.toStarSubalgebra)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖a‖) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hu (norm_nonneg _)) hs (norm_nonneg _) (by simp)
    _ = ‖a‖ := by ring

theorem conjugate_norm₂_le (u : unitary M.toStarSubalgebra) (a : M.toStarSubalgebra) :
    τ.norm₂ (conjugateLinear u a) ≤ τ.norm₂ a := by
  have hu := unitary_norm_le (u : M.toStarSubalgebra) (by simp)
  have hs := unitary_norm_le (star (u : M.toStarSubalgebra)) (by simp)
  calc
    τ.norm₂ (conjugateLinear u a) ≤ τ.norm₂ ((u : M.toStarSubalgebra)*a) * ‖star (u : M.toStarSubalgebra)‖ := τ.norm₂_mul_le_right _ _
    _ ≤ (‖(u : M.toStarSubalgebra)‖ * τ.norm₂ a) * ‖star (u : M.toStarSubalgebra)‖ :=
      mul_le_mul_of_nonneg_right (τ.norm₂_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * τ.norm₂ a) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hu (norm_nonneg _)) hs (norm_nonneg _) (by simpa only [one_mul] using (show 0 ≤ τ.norm₂ a from norm_nonneg _))
    _ = τ.norm₂ a := by ring

theorem conjugate_norm₂ (u : unitary M.toStarSubalgebra) (a : M.toStarSubalgebra) :
    τ.norm₂ (conjugateLinear u a) = τ.norm₂ a := by
  apply le_antisymm (conjugate_norm₂_le τ u a)
  have h := conjugate_norm₂_le τ u⁻¹ (conjugateLinear u a)
  simpa only [← conjugateLinear_mul, inv_mul_cancel, conjugateLinear_one] using h

def algebraOrbit (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra) : Set M.toStarSubalgebra :=
  {a | ∃ u : G, conjugateLinear u.val b = a}

theorem conjugate_mem_convexHull (G : Subgroup (unitary M.toStarSubalgebra))
    (b : M.toStarSubalgebra) (u : G) {a : M.toStarSubalgebra}
    (ha : a ∈ convexHull ℝ (algebraOrbit G b)) :
    conjugateLinear u.val a ∈ convexHull ℝ (algebraOrbit G b) := by
  have h := Set.mem_image_of_mem (conjugateLinear u.val) ha
  change conjugateLinear u.val a ∈ (conjugateLinear u.val |>.restrictScalars ℝ) '' convexHull ℝ (algebraOrbit G b) at h
  rw [(conjugateLinear u.val |>.restrictScalars ℝ).image_convexHull] at h
  apply convexHull_mono _ h
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  exact ⟨u*v, conjugateLinear_mul _ _ _⟩

end

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem trace_conjugate (u : unitary M.toStarSubalgebra) (b : M.toStarSubalgebra) :
    τ.trace (conjugateLinear u b) = τ.trace b := by
  change τ.trace ((u : M.toStarSubalgebra)*b*star (u : M.toStarSubalgebra)) = _
  rw [τ.trace_mul_comm]
  simp [← mul_assoc]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/
namespace Tracial
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_limit_mul {I : Type*} {l : Filter I}
    (a c : I → M.toStarSubalgebra) (b d : M.toStarSubalgebra)
    (C : ℝ) (hC : ∀ i, ‖a i‖ ≤ C)
    (ha : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0))
    (hc : Tendsto (fun i => τ.norm₂ (c i-d)) l (𝓝 0)) :
    Tendsto (fun i => τ.norm₂ (a i*c i-b*d)) l (𝓝 0) := by
  have hbound : ∀ i, τ.norm₂ (a i*c i-b*d) ≤ C*τ.norm₂ (c i-d)+τ.norm₂ (a i-b)*‖d‖ := by
    intro i
    have he : a i*c i-b*d = a i*(c i-d)+(a i-b)*d := by
      simp only [mul_sub,sub_mul]; abel
    rw [he]
    exact (τ.norm₂_add_le _ _).trans (add_le_add
      ((τ.norm₂_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)))
      (τ.norm₂_mul_le_right _ _))
  apply squeeze_zero (fun i => norm_nonneg _) hbound
  simpa using (hc.const_mul C).add (ha.mul_const ‖d‖)

end Tracial

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_OrbitMinima
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The least-norm unitary-orbit point is scalar when the coordinate inclusion has scalar commutant. -/
section
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def subalgebraUnitaries (P : StarSubalgebra ℂ M.toStarSubalgebra) : Subgroup (unitary M.toStarSubalgebra) where
  carrier := {u | (u : M.toStarSubalgebra) ∈ P}
  one_mem' := P.one_mem
  mul_mem' hu hv := P.mul_mem hu hv
  inv_mem' hu := by
    change star _ ∈ P
    exact star_mem hu

def ambientUnitary (P : StarSubalgebra ℂ M.toStarSubalgebra) (u : unitary P) :
    subalgebraUnitaries P :=
  ⟨Unitary.map { toFun := P.subtype, map_one' := map_one _, map_mul' := map_mul _, map_star' := map_star _ } u, u.val.property⟩

theorem commutes_of_fixed_unitaries (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
    (c : M.toStarSubalgebra)
    (hc : ∀ u : subalgebraUnitaries P, conjugateLinear u.val c = c) :
    ∀ a : P, (a : M.toStarSubalgebra)*c = c*(a : M.toStarSubalgebra) := by
  let : CStarAlgebra P := {}
  intro a
  obtain ⟨u, s, ha, _⟩ := CStarAlgebra.exists_sum_four_unitary a
  have hu (i : Fin 4) : ((u i).val : M.toStarSubalgebra)*c = c*((u i).val : M.toStarSubalgebra) := by
    have h := congrArg (fun z : M.toStarSubalgebra => z * ((u i).val : M.toStarSubalgebra)) (hc (ambientUnitary P (u i)))
    change (((u i).val : M.toStarSubalgebra)*c*star ((u i).val : M.toStarSubalgebra))*((u i).val : M.toStarSubalgebra) = _ at h
    have he : star ((u i).val : M.toStarSubalgebra)*((u i).val : M.toStarSubalgebra) = 1 :=
      congrArg Subtype.val (u i).property.1
    simpa only [mul_assoc, he, mul_one] using h
  change P.subtype a*c = c*P.subtype a
  rw [ha, map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul, smul_mul_assoc, mul_smul_comm]
  exact congrArg (fun z : M.toStarSubalgebra => s i • z) (hu i)

end

/-! Irreducibility excludes disconnected nonzero ambient projections.
This gives the projection part of irreducibility in every nonzero corner. -/
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_PartialIsometries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual partial isometries, allowing distinct initial and final projections,
with the extension order and its exact trace distance. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

theorem mul_support (v : PartialIsometry M) : v.val*v.support.val=v.val := by
  have htr : star v.val*(v.val*v.support.val)=v.support.val := by
    rw [← mul_assoc,v.initial,v.support.property.isIdempotentElem.eq]
  have he : star (v.val-v.val*v.support.val)*(v.val-v.val*v.support.val)=0 := by
    simp only [star_sub,star_mul,v.support.property.isSelfAdjoint.star_eq,sub_mul,mul_sub,
      mul_assoc,v.initial,htr,v.support.property.isIdempotentElem.eq,sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp he)).symm

def target (v : PartialIsometry M) : AlgebraProjection M :=
  ⟨v.val*star v.val,⟨by
    change (v.val*star v.val)*(v.val*star v.val)=v.val*star v.val
    calc _ = (v.val*(star v.val*v.val))*star v.val := by simp only [mul_assoc]
         _ = v.val*star v.val := by rw [v.initial,v.mul_support],
    IsSelfAdjoint.mul_star_self _⟩⟩

theorem target_mul (v : PartialIsometry M) : v.target.val*v.val=v.val := by
  change (v.val*star v.val)*v.val=v.val
  rw [mul_assoc,v.initial,v.mul_support]

def adjoint (v : PartialIsometry M) : PartialIsometry M :=
  ⟨v.target,star v.val,by simp only [star_star]; rfl⟩

theorem trace_support_eq_target (τ : TracialRepresentation M) (v : PartialIsometry M) :
    τ.trace v.support.val=τ.trace v.target.val := by
  rw [← v.initial]
  exact τ.trace_mul_comm _ _

theorem support_le_of_extends {v w : PartialIsometry M} (h : Extends v w) :
    v.support ≤ w.support := by
  have hh := congrArg (fun z : M.toStarSubalgebra => star z*z) h
  have hcomp : v.support.val*w.support.val*v.support.val=v.support.val := by
    calc _ = v.support.val*(star w.val*w.val)*v.support.val := by rw [w.initial]
         _ = star (w.val*v.support.val)*(w.val*v.support.val) := by
           simp only [star_mul,v.support.property.isSelfAdjoint.star_eq,mul_assoc]
         _ = v.support.val := hh.trans v.initial
  have hdouble : v.support.val*w.support.val*w.support.val*v.support.val=v.support.val := by
    calc _ = v.support.val*(w.support.val*w.support.val)*v.support.val := by
           simp only [mul_assoc]
         _ = v.support.val := by rw [w.support.property.isIdempotentElem.eq,hcomp]
  have hz : star (v.support.val-w.support.val*v.support.val)*
      (v.support.val-w.support.val*v.support.val)=0 := by
    simp only [star_sub,star_mul,v.support.property.isSelfAdjoint.star_eq,
      w.support.property.isSelfAdjoint.star_eq,sub_mul,mul_sub]
    simp only [← mul_assoc,v.support.property.isIdempotentElem.eq,hcomp,hdouble,
      sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)).symm

theorem cross_initial {v w : PartialIsometry M} (h : Extends v w) :
    star w.val*v.val=v.support.val := by
  calc star w.val*v.val = star w.val*(w.val*v.support.val) := by rw [h]
       _ = v.support.val := by rw [← mul_assoc,w.initial]; exact support_le_of_extends h

theorem cross_initial_rev {v w : PartialIsometry M} (h : Extends v w) :
    star v.val*w.val=v.support.val := by
  simpa only [star_mul,star_star,v.support.property.isSelfAdjoint.star_eq]
    using congrArg star (cross_initial h)

theorem extends_refl (v : PartialIsometry M) : Extends v v := v.mul_support

theorem extends_trans {u v w : PartialIsometry M} (huv : Extends u v) (hvw : Extends v w) :
    Extends u w := by
  change w.val*u.support.val=u.val
  calc w.val*u.support.val = w.val*(v.support.val*u.support.val) := by
         rw [show v.support.val*u.support.val=u.support.val from support_le_of_extends huv]
       _ = u.val := by rw [← mul_assoc,hvw,huv]

instance instPartialOrder : PartialOrder (PartialIsometry M) where
  le := Extends
  le_refl := extends_refl
  le_trans _ _ _ := extends_trans
  le_antisymm v w hvw hwv := by
    apply ext
    have hs := le_antisymm (support_le_of_extends hvw) (support_le_of_extends hwv)
    change w.val*v.support.val=v.val at hvw
    rw [hs,w.mul_support] at hvw
    exact hvw.symm

theorem difference_square {v w : PartialIsometry M} (h : v ≤ w) :
    star (w.val-v.val)*(w.val-v.val)=w.support.val-v.support.val := by
  simp only [star_sub,sub_mul,mul_sub,w.initial,v.initial,
    cross_initial h,cross_initial_rev h,sub_self,sub_zero]

end PartialIsometry

end

/-! Actual L2 limits of partial isometries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Orthogonal patching with distinct source and target supports. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem support_le_iff_mul (v : PartialIsometry M) (p : AlgebraProjection M) :
    v.support ≤ p ↔ v.val*p.val=v.val := by
  constructor
  · intro h
    calc _ = (v.val*v.support.val)*p.val := by rw [v.mul_support]
         _ = v.val := by rw [mul_assoc,projection_mul_of_le h,v.mul_support]
  · intro h
    have he : v.support.val*p.val=v.support.val := by
      rw [← v.initial,mul_assoc,h]
    change p.val*v.support.val=v.support.val
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
      v.support.property.isSelfAdjoint.star_eq] using congrArg star he

theorem target_le_iff_mul (v : PartialIsometry M) (q : AlgebraProjection M) :
    v.target ≤ q ↔ q.val*v.val=v.val := by
  constructor
  · intro h
    calc _ = q.val*(v.target.val*v.val) := by rw [v.target_mul]
         _ = v.val := by rw [← mul_assoc,h,v.target_mul]
  · intro h
    change q.val*(v.val*star v.val)=v.val*star v.val
    rw [← mul_assoc,h]

theorem mul_eq_zero (v w : PartialIsometry M) (h : v.support.val*w.target.val=0) :
    v.val*w.val=0 := by
  calc _ = (v.val*v.support.val)*(w.target.val*w.val) := by
         rw [v.mul_support,w.target_mul]
       _ = v.val*(v.support.val*w.target.val)*w.val := by simp only [mul_assoc]
       _ = 0 := by rw [h,mul_zero,zero_mul]

def patch (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    PartialIsometry M where
  support := ⟨v.support.val+w.support.val,v.support.property.add w.support.property hp⟩
  val := v.val+w.val
  initial := by
    have h₁ : star v.val*w.val=0 := v.adjoint.mul_eq_zero w hq
    have h₂ : star w.val*v.val=0 :=
      w.adjoint.mul_eq_zero v (orthogonal_reverse _ _ hq)
    simp only [star_add,add_mul,mul_add,v.initial,w.initial,h₁,h₂,add_zero,zero_add]

theorem le_patch (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    v ≤ patch v w hp hq := by
  have hw : w.val*v.support.val=0 := by
    calc _ = (w.val*w.support.val)*v.support.val := by rw [w.mul_support]
         _ = 0 := by rw [mul_assoc,orthogonal_reverse _ _ hp,mul_zero]
  change (v.val+w.val)*v.support.val=v.val
  rw [add_mul,v.mul_support,hw,add_zero]

theorem patch_ne (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0)
    (hw : w.support.val≠0) : patch v w hp hq ≠ v := by
  intro he
  have hh := congrArg (fun z : PartialIsometry M => z.support.val) he
  change v.support.val+w.support.val=v.support.val at hh
  exact hw (add_left_cancel (hh.trans (add_zero _).symm))

end PartialIsometry

end

/-! A maximal actual partial isometry between subprojections of prescribed
projections. Chain upper bounds are constructed L2 limits, not assumed. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Supports
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance positiveSupportCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance positiveSupportOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance positiveSupportPreorder_rdc3386_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance positiveSupportLE_rdc3386_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance positiveSupportStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

def positiveSupport (x : M.toStarSubalgebra) : AlgebraProjection M := rangeProjection x⁺

theorem positiveSupport_mul_pos (x : M.toStarSubalgebra) :
    (positiveSupport x).val*x⁺=x⁺ := rangeProjection_mul _

theorem positiveSupport_mul_neg (x : M.toStarSubalgebra) :
    (positiveSupport x).val*x⁻=0 :=
  rangeProjection_mul_eq_zero x⁺ x⁻ (CFC.posPart_nonneg x).isSelfAdjoint
    (CFC.posPart_mul_negPart x)

theorem positiveSupport_mul (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (positiveSupport x).val*x=x⁺ := by
  calc (positiveSupport x).val*x = (positiveSupport x).val*(x⁺-x⁻) :=
         congrArg (fun z => (positiveSupport x).val*z) (CFC.posPart_sub_negPart x hx).symm
    _ = x⁺ := by rw [mul_sub,positiveSupport_mul_pos,positiveSupport_mul_neg,sub_zero]

theorem mul_positiveSupport (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    x*(positiveSupport x).val=x⁺ := by
  have h := congrArg star (positiveSupport_mul x hx)
  simpa only [star_mul,hx.star_eq,(positiveSupport x).property.isSelfAdjoint.star_eq,
    (CFC.posPart_nonneg x).isSelfAdjoint.star_eq] using h

theorem positiveSupport_compression (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (positiveSupport x).val*x*(positiveSupport x).val=x⁺ := by
  rw [mul_assoc,mul_positiveSupport x hx,positiveSupport_mul_pos]

end

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance polarCStar_rdc3386_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance polarStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarSupportsCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance polarSupportsOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance polarSupportsStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem sqrt_rangeProjection (x : M.toStarSubalgebra) :
    rangeProjection (CFC.sqrt (star x*x)) = rangeProjection (star x) := by
  let a := CFC.sqrt (star x*x)
  have ha : star a=a := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have he : star a.val*a.val=star x.val*x.val := by
    change ((star a*a : M.toStarSubalgebra) : H →L[ℂ] H)=_
    rw [ha,CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)]
    rfl
  have hk (z : H →L[ℂ] H) : (star z*z).ker=z.ker := by
    exact z.ker_adjoint_comp_self
  have hker : a.val.ker=x.val.ker := by rw [← hk a.val,he,hk]
  apply Subtype.ext
  apply Subtype.ext
  change 1-(star a.val).ker.starProjection=1-(star (star x.val)).ker.starProjection
  have has : star a.val=a.val := congrArg Subtype.val ha
  simp only [has,star_star,hker]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerCutCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerCutOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerCutPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerCutLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerCutStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

/-- Functional calculus positive parts retain a given right support. -/
theorem positivePart_right_support (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (p : AlgebraProjection M) (hp : x*p.val=x) : x⁺*p.val=x⁺ := by
  have he : x⁺*(1-p.val)=x⁻*(1-p.val) := by
    apply sub_eq_zero.mp
    rw [← sub_mul,CFC.posPart_sub_negPart x hx,mul_sub,mul_one,hp,sub_self]
  have hz : star (x⁺*(1-p.val))*(x⁺*(1-p.val))=0 := by
    nth_rw 2 [he]
    rw [star_mul,star_sub,star_one,p.property.isSelfAdjoint.star_eq,
      (CFC.posPart_nonneg x).isSelfAdjoint.star_eq]
    calc (1-p.val)*x⁺*(x⁻*(1-p.val)) = (1-p.val)*(x⁺*x⁻)*(1-p.val) := by
           simp only [mul_assoc]
      _ = 0 := by rw [CFC.posPart_mul_negPart,mul_zero,zero_mul]
  have h := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  rw [mul_sub,mul_one,sub_eq_zero] at h
  exact h.symm

theorem positiveSupport_le_corner (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (p : AlgebraProjection M) (hp : x*p.val=x) : positiveSupport x ≤ p := by
  apply (rangeProjection_le_iff _ p).mpr
  have h := congrArg star (positivePart_right_support x hx p hp)
  simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
    (CFC.posPart_nonneg x).isSelfAdjoint.star_eq] using h

theorem cornerSpectralShift_selfAdjoint (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℝ) :
    IsSelfAdjoint (cornerSpectralShift p x t) := by
  change star (p.val*x*p.val-(t : ℂ) • p.val) = _
  simp only [cornerSpectralShift,star_sub,star_mul,star_smul,p.property.isSelfAdjoint.star_eq,hx.star_eq,
    Complex.star_def,Complex.conj_ofReal,mul_assoc]

def cornerSpectralCut (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    AlgebraProjection M := positiveSupport (cornerSpectralShift p x t)

theorem cornerSpectralCut_le (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) : cornerSpectralCut p x t ≤ p :=
  positiveSupport_le_corner _ (cornerSpectralShift_selfAdjoint p x hx t) p
    (cornerSpectralShift_support p x t)

end

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance intervalOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance intervalPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance intervalLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance intervalCStar_rdc3386_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance intervalStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

structure SpectralInterval (x : M.toStarSubalgebra) where
  proj : AlgebraProjection M
  lo : ℝ
  hi : ℝ
  lower : 0 ≤ proj.val*x*proj.val-(lo : ℂ) • proj.val
  upper : proj.val*x*proj.val-(hi : ℂ) • proj.val ≤ 0

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def midpoint : ℝ := (I.lo+I.hi)/2

def highProjection : AlgebraProjection M := cornerSpectralCut I.proj x I.midpoint

theorem high_le (hx : IsSelfAdjoint x) : I.highProjection ≤ I.proj :=
  cornerSpectralCut_le I.proj x hx I.midpoint

end SpectralInterval

end

/-! Finite dyadic trees of actual spectral interval cuts. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Finite spectral approximations constructed by successive sign cuts.
The approximation bound is proved from the leaf intervals. -/
local instance approximationCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! Constructed cuts preserve commutation with other operators. -/

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

/-- A spectral sum on Q is represented exactly on the common refinement. -/
theorem joint_sum_left (c : Fin Q.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size, c a.1 • (Q.jointPiece R hc a).val)=
      ∑ i, c i • (Q.piece i).val := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, c i • ((Q.piece i).val*(R.piece j).val))=_
  rw [← Finset.smul_sum,← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le i)]

theorem joint_sum_right (c : Fin R.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size, c a.2 • (Q.jointPiece R hc a).val)=
      ∑ j, c j • (R.piece j).val := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i, c j • ((Q.piece i).val*(R.piece j).val))=_
  rw [← Finset.smul_sum,← Finset.sum_mul,Q.total]
  have hleft : p.val*(R.piece j).val=(R.piece j).val := R.piece_le j
  rw [hleft]

end CornerPartition

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

end

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end


