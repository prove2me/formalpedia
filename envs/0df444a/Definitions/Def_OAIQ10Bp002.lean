-- Prove2me | Definitions.Def_OAIQ10Bp002
-- name    : OAIQ10Bp002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:25:45.433761+00:00
-- url     : https://prove2.me/theorems/b198a7a3-eb35-4d2c-b0a9-73a1153e4324
-- title:
--   Definitions bundle OAIQ10Bp002 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 35 definitions and 25 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenFrameLocal1`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenIsomorphismLocal1`, `OAI.HigherDimensionalBallPacking.Rigidity.FrozenIsomorphismLocal2`, `OAI.HigherDimensionalBallPacking.Rigidity.PseudoHolomorphicAt`, `OAI.HigherDimensionalBallPacking.Rigidity.affineFamilyDomainNormedAddCommGroup`, `OAI.HigherDimensionalBallPacking.Rigidity.affineSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderAffineCompose`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderConstantCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderDx`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderMap`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderMultiply`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderApply`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderMul`, `OAI.HigherDimensionalBallPacking.Rigidity.compactSmoothC1Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.euclideanNorm`, `OAI.HigherDimensionalBallPacking.Rigidity.holderAffineFamily`, `OAI.HigherDimensionalBallPacking.Rigidity.holderComp`, `OAI.HigherDimensionalBallPacking.Rigidity.holderConst`, `OAI.HigherDimensionalBallPacking.Rigidity.holderConstCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.holderCutoffAffine`, `OAI.HigherDimensionalBallPacking.Rigidity.holderJetEval`, `OAI.HigherDimensionalBallPacking.Rigidity.holderLinearPost`, `OAI.HigherDimensionalBallPacking.Rigidity.holderOperatorCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.holderOperatorLinear`, `OAI.HigherDimensionalBallPacking.Rigidity.holderSourceCutoff`, `OAI.HigherDimensionalBallPacking.Rigidity.holderSourceCutoffLinear`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealHolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.localizedAffineFamily`, `OAI.HigherDimensionalBallPacking.Rigidity.markedCRInverse`, `OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.phaseEuclidean`, `OAI.HigherDimensionalBallPacking.Rigidity.realCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.stdOmega`, `OAI.HigherDimensionalBallPacking.Rigidity.unmarkedLower`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: `BallPacking_Necessity_FiniteReduction`, `BallPacking_Necessity_FrozenInverse`, `BallPacking_Necessity_FrozenOperators`, `BallPacking_Necessity_FrozenResponse`, `BallPacking_Necessity_HolderCompactness`, `BallPacking_Necessity_MarkedInverse`, `BallPacking_Necessity_MarkedProfiles`, `BallPacking_Necessity_NonlinearCR`, `BallPacking_Necessity_OrbitRegularity`, `BallPacking_Necessity_PlanarEnergy`, `BallPacking_Necessity_SchauderBounds`, `BallPacking_Rigidity_Adapted`, `BallPacking_Rigidity_CompatibleStructures`, `BallPacking_Rigidity_Correction`, `BallPacking_Rigidity_CurveArea`, `BallPacking_Rigidity_RadialForm`.
--
--   **Imports.** It imports the published bundle `Def_BallPackingNecessity`; the bundles `OAIQ10Bp000` and `OAIQ10Bp001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ10Bp004`, `OAIQ10Bp005`, `OAIQ10Bp006` and `OAIQ10Bp008`; the statements `OAI.HigherDimensionalBallPacking.Rigidity.framed_unmarked_surjective`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_C0_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_curve_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_common_affine_carrier`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_density_common_support`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_limit_has_nonzero_asymptotic`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_slopes_bounded_above` and `OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction`; the proofs of `OAI_HigherDimensionalBallPacking_Rigidity_actual_affine_line_exists` and `OAI.HigherDimensionalBallPacking.Rigidity.framed_frozen_solution`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp000
import Definitions.Def_OAIQ10Bp001

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CompatibleStructures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

def PseudoHolomorphicAt {n : ℕ} (J : Phase n → End n) (u : ℂ → Phase n) (z : ℂ) : Prop :=
  DifferentiableAt ℝ u z ∧ ∀ w : ℂ,
    fderiv ℝ u z (Complex.I * w) = J (u z) (fderiv ℝ u z w)

end Rigidity
end
end HigherDimensionalBallPacking

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Adapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter

def AffineLineCurve {n : ℕ} (J : Phase n → End n) (p q : Phase n)
    (u : ℂ → Phase n) : Prop :=
  ContDiff ℝ ∞ u ∧ (∀ z, PseudoHolomorphicAt J u z) ∧ u 0 = p ∧ u 1 = q ∧
    ∃ v : Phase n, v ≠ 0 ∧ Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_RadialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def stdOmega (n : ℕ) : Phase n →L[ℝ] Phase n →L[ℝ] ℝ :=
  -((stdDot n).flip.comp (standardJ n)).flip

@[simp] theorem stdOmega_apply {n : ℕ} (v w : Phase n) :
    stdOmega n v w = standardForm v w := by
  change -(stdDot n v (standardJ n w)) = standardForm v w
  rw [stdDot_J_right,neg_neg]

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCompactness
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderGraph_isClosed _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSubmodule_isClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance instNormedSpaceRealHolderSpace (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

def holderOperatorLinear (α : ℝ) :
    HolderSpace K (E →L[ℝ] F) α →ₗ[ℝ] (HolderSpace K E α →L[ℝ] HolderSpace K F α) where
  toFun M := holderCLM α M
  map_add' := by
    intro M N
    apply ContinuousLinearMap.ext
    intro v
    apply holderValue_injective α
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' := by
    intro c M
    apply ContinuousLinearMap.ext
    intro v
    apply holderValue_injective α
    apply BoundedContinuousFunction.ext
    intro x
    rfl

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpace
theorem holderCLM_norm_bound (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α) :
    ‖holderCLM α M‖ ≤ 2*‖M‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (holderApply_norm α M)

def holderOperatorCLM (α : ℝ) :
    HolderSpace K (E →L[ℝ] F) α →L[ℝ] (HolderSpace K E α →L[ℝ] HolderSpace K F α) :=
  LinearMap.mkContinuous (holderOperatorLinear (K := K) (E := E) (F := F) α) 2
    (holderCLM_norm_bound α)

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]



def markedCRInverse (R : ℝ) (u : CompactHolderSpace E R) (z : ℂ) : E :=
  compactCRInverseValue R u z - compactCRInverseValue R u 0 -
    z • (compactCRInverseValue R u 1-compactCRInverseValue R u 0)

@[simp] lemma markedCRInverse_zero (R : ℝ) (u : CompactHolderSpace E R) : markedCRInverse R u 0=0 := by
  simp [markedCRInverse]
@[simp] lemma markedCRInverse_one (R : ℝ) (u : CompactHolderSpace E R) : markedCRInverse R u 1=0 := by
  simp [markedCRInverse]

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_NonlinearCR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction



namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def holderConst (α : ℝ) (c : E) : HolderSpace K E α :=
  ⟨(BoundedContinuousFunction.const K c,0),by intro p; simp⟩

@[simp] theorem holderConst_apply (α : ℝ) (c : E) (z : K) :
    holderValue α (holderConst α c) z = c := rfl

def holderLinearPost (α : ℝ) (T : E →L[ℝ] F) : HolderSpace K E α →L[ℝ] HolderSpace K F α :=
  holderCLM α (holderConst α T)

@[simp] theorem holderLinearPost_apply (α : ℝ) (T : E →L[ℝ] F) (u : HolderSpace K E α) (z : K) :
    holderValue α (holderLinearPost α T u) z = T (holderValue α u z) := rfl

variable [CompleteSpace E]

def holderJetEval (α : ℝ) (w : ℂ) :
    HolderSpace K (ℂ →L[ℝ] E) α →L[ℝ] HolderSpace K E α :=
  holderLinearPost α ((ContinuousLinearMap.apply ℝ E) w)

omit [CompleteSpace E] in
@[simp] theorem holderJetEval_apply (α : ℝ) (w : ℂ)
    (A : HolderSpace K (ℂ →L[ℝ] E) α) (z : K) :
    holderValue α (holderJetEval α w A) z = holderValue α A z w := rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction



namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def holderConstCLM (α : ℝ) : E →L[ℝ] HolderSpace K E α :=
  LinearMap.mkContinuous
    { toFun := holderConst α
      map_add' := fun c d => by apply holderValue_injective α; ext z; rfl
      map_smul' := fun c d => by apply holderValue_injective α; ext z; rfl }
    1 (fun c => by
      change max ‖BoundedContinuousFunction.const K c‖ ‖(0 : OffDiagonal K →ᵇ E)‖ ≤ 1*‖c‖
      rw [norm_zero,one_mul]
      exact max_le (BoundedContinuousFunction.norm_const_le c) (norm_nonneg c))

@[simp] theorem holderConstCLM_apply (α : ℝ) (c : E) :
    holderConstCLM (K := K) α c = holderConst α c := rfl

 

def holderSourceCutoff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (b : ContDiffBump (0:ℂ)) :
    HolderSpace ℂ ℝ α :=
  compactSmoothHolder α hα₀ hα₁ b b.contDiff b.hasCompactSupport

def holderSourceCutoffLinear (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (b : ContDiffBump (0:ℂ)) :
    HolderSpace ℂ ℂ α :=
  compactSmoothHolder α hα₀ hα₁ (fun z => b z • z) (b.contDiff.smul contDiff_id)
    b.hasCompactSupport.smul_right

def holderCutoffAffine (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (b : ContDiffBump (0:ℂ))
    (p : E × (ℂ →L[ℝ] E)) : HolderSpace ℂ E α :=
  holderCLM α (holderLinearPost α (ContinuousLinearMap.lsmul ℝ ℝ)
    (holderSourceCutoff α hα₀ hα₁ b)) (holderConst α p.1) +
  holderLinearPost α p.2 (holderSourceCutoffLinear α hα₀ hα₁ b)

@[simp] theorem holderCutoffAffine_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (b : ContDiffBump (0:ℂ)) (p : E × (ℂ →L[ℝ] E)) (z : ℂ) :
    holderValue α (holderCutoffAffine α hα₀ hα₁ b p) z = b z • (p.1+p.2 z) := by
  change b z • p.1+p.2 (b z • z) = _
  rw [map_smul,smul_add]

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local instance affineFamilyDomainNormedAddCommGroup (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance

def holderAffineFamily (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α) : HolderSpace ℂ F α :=
  holderProfilePost α hα₀ hα₁ (realAffineProfile p.1.1 p.1.2)
    (realAffineProfile_lipschitz p.1.1 p.1.2) f hf hc p.2

omit [CompleteSpace E] in
@[simp] theorem holderAffineFamily_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α) (z : ℂ) :
    holderValue α (holderAffineFamily α hα₀ hα₁ f hf hc p) z =
      f (p.1.1+p.1.2 z+holderValue α p.2 z) := rfl

def localizedAffineFamily (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (b : ContDiffBump (0:ℂ))
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α) : HolderSpace ℂ F α :=
  holderProfilePost α hα₀ hα₁ (realAffineProfile c A) (realAffineProfile_lipschitz c A) f hf hc
    (holderCutoffAffine α hα₀ hα₁ b (p.1.1-c,p.1.2-A)+p.2)

omit [CompleteSpace E] in
@[simp] theorem localizedAffineFamily_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (b : ContDiffBump (0:ℂ))
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α) (z : ℂ) :
    holderValue α (localizedAffineFamily α hα₀ hα₁ f hf hc c A b p) z =
      f (c+A z+b z • ((p.1.1-c)+(p.1.2-A) z)+holderValue α p.2 z) := by
  change f (c+A z+(holderValue α (holderCutoffAffine α hα₀ hα₁ b (p.1.1-c,p.1.2-A)) z+
    holderValue α p.2 z)) = _
  rw [holderCutoffAffine_apply]
  simp only [add_assoc]

end HigherDimensionalBallPacking.Rigidity



open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma c1HolderGraph_mem_of_hasFDerivAt (α : ℝ) (f : HolderSpace ℂ E α)
    (D : HolderSpace ℂ (ℂ →L[ℝ] E) α)
    (hD : ∀ z, HasFDerivAt (holderValue α f) (holderValue α D z) z) :
    (f,D) ∈ c1HolderGraph α := by
  intro x y
  change holderValue α f y-holderValue α f x = linearSegmentIntegral x y (holderValue α D)
  rw [linearSegmentIntegral_apply]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => holderValue α f (x+s • (y-x)))
      (holderValue α D (x+t • (y-x)) (y-x)) t := by
    simpa only [id_eq,one_smul,Function.comp_def] using
      ((hD (x+t • (y-x))).comp_hasDerivAt t (((hasDerivAt_id t).smul_const (y-x)).const_add x))
  symm
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((segmentIntegrand_continuous (holderValue α D) x y).intervalIntegrable (0:ℝ) 1)

 
def compactSmoothC1Holder (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : ℂ → E) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : C1HolderSpace E α :=
  ⟨(compactSmoothHolder α hα₀ hα₁ f hf hc,
      compactSmoothHolder α hα₀ hα₁ (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ)),
    c1HolderGraph_mem_of_hasFDerivAt α _ _ (fun z => (hf.differentiable (by simp) z).hasFDerivAt)⟩

@[simp] lemma compactSmoothC1Holder_value (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : ℂ → E) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (z : ℂ) :
    holderValue α (c1HolderValue α (compactSmoothC1Holder α hα₀ hα₁ f hf hc)) z=f z := rfl

 

def c1HolderMultiply (α : ℝ) (P : C1HolderSpace (E →L[ℝ] F) α) :
    C1HolderSpace E α →L[ℝ] C1HolderSpace F α := by
  let V := (holderCLM α (c1HolderValue α P)).comp (c1HolderValue α)
  let A : HolderSpace ℂ ((ℂ →L[ℝ] E) →L[ℝ] (ℂ →L[ℝ] F)) α :=
    holderMap α (ContinuousLinearMap.compL ℝ ℂ E F) (c1HolderValue α P)
  let B : HolderSpace ℂ (E →L[ℝ] (ℂ →L[ℝ] F)) α :=
    holderMap α (ContinuousLinearMap.flipₗᵢ ℝ ℂ E F).toContinuousLinearEquiv.toContinuousLinearMap
      (c1HolderDeriv α P)
  let D := ((holderCLM α A).comp (c1HolderDeriv α))+((holderCLM α B).comp (c1HolderValue α))
  exact (V.prod D).codRestrict (c1HolderGraph α) (by
    intro u
    apply c1HolderGraph_mem_of_hasFDerivAt α
    intro z
    exact (c1Holder_hasFDerivAt α P z).clm_apply (c1Holder_hasFDerivAt α u z))

@[simp] lemma c1HolderMultiply_value (α : ℝ) (P : C1HolderSpace (E →L[ℝ] F) α)
    (u : C1HolderSpace E α) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderMultiply α P u)) z =
      holderValue α (c1HolderValue α P) z (holderValue α (c1HolderValue α u) z) := rfl

 
def c1HolderConstantCLM (α : ℝ) : E →L[ℝ] C1HolderSpace E α :=
  ((holderConstantCLM α).prod 0).codRestrict (c1HolderGraph α) (by
    intro c
    apply c1HolderGraph_mem_of_hasFDerivAt α
    intro z
    exact hasFDerivAt_const c z)

@[simp] lemma c1HolderConstantCLM_value (α : ℝ) (c : E) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderConstantCLM α c)) z = c := rfl

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FiniteReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]



def compactHolderMul (R : ℝ) (A : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) :
    CompactHolderSpace E R →L[ℝ] CompactHolderSpace E R :=
  ((holderCLM ((1:ℝ)/3) A).comp (compactHolderSubmodule R).subtypeL).codRestrict
    (compactHolderSubmodule R) (by
      intro g z hz
      change holderValue ((1:ℝ)/3) A z (holderValue ((1:ℝ)/3) g.val z)=0
      rw [g.property z hz,map_zero])

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
@[simp] lemma compactHolderMul_value (R : ℝ)
    (A : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (g : CompactHolderSpace E R) (z : ℂ) :
    compactHolderValue R (compactHolderMul R A g) z =
      holderValue ((1:ℝ)/3) A z (compactHolderValue R g z) := rfl

end

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter


open scoped ContDiff Topology
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



open scoped ContDiff Topology
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter





open Set Function Filter Topology

 

open Set Function

 

open Set Function

 

open Function

 

open Set Function

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CurveArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

def realCurve {n : ℕ} (u : ℂ → Phase n) : Plane → Phase n :=
  u ∘ Complex.equivRealProdCLM.symm


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory



open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)

def normalizedPrimitive {n : ℕ} (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (1 / (2 * capacity x)) • stdOmega n x

@[simp] theorem normalizedPrimitive_apply {n : ℕ} (x v : Phase n) :
    normalizedPrimitive x v = standardForm x v / (2 * capacity x) := by
  simp only [normalizedPrimitive,smul_apply,smul_eq_mul,stdOmega_apply]
  ring


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Correction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane )

@[simp] theorem realCurve_zero {n : ℕ} (u : ℂ → Phase n) : realCurve u 0 = u 0 := by
  simp [realCurve,Complex.equivRealProdCLM_symm_apply]


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance FrozenFrameLocal1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance

 def unmarkedLower {n : ℕ} (R : ℝ) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0) :
    CompactHolderSpace (Phase n) R →L[ℝ] CompactHolderSpace (Phase n) R :=
  ((c1LowerOrderCLM M).comp (compactCRInverse R)).codRestrict (compactHolderSubmodule R) (by
    intro g z hz
    change holderValue ((1:ℝ)/3) M z (compactCRInverseValue R g z)=0
    rw [hs z hz,zero_apply])

 @[simp] theorem unmarkedLower_value {n : ℕ} (R : ℝ) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    compactHolderValue R (unmarkedLower R M hs g) z=
      holderValue ((1:ℝ)/3) M z (compactCRInverseValue R g z) := rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

 def c1HolderMap (α : ℝ) (L : E →L[ℝ] F) : C1HolderSpace E α →L[ℝ] C1HolderSpace F α :=
  (((holderMap α L).comp (c1HolderValue α)).prod
    ((holderMap α ((ContinuousLinearMap.compL ℝ ℂ E F) L)).comp (c1HolderDeriv α))).codRestrict
      (c1HolderGraph α) (by
        intro u
        apply c1HolderGraph_mem_of_hasFDerivAt α
        intro z
        exact L.hasFDerivAt.comp z (c1Holder_hasFDerivAt α u z))

 @[simp] theorem c1HolderMap_value (α : ℝ) (L : E →L[ℝ] F) (u : C1HolderSpace E α) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderMap α L u)) z=
      L (holderValue α (c1HolderValue α u) z) := rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 def holderComp {n : ℕ} (A B : HolderSpace ℂ (End n) ((1:ℝ)/3)) :
    HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  holderCLM ((1:ℝ)/3) (holderMap ((1:ℝ)/3) (ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n)) A) B

 @[simp] theorem holderComp_value {n : ℕ} (A B : HolderSpace ℂ (End n) ((1:ℝ)/3)) (z : ℂ) :
    holderValue ((1:ℝ)/3) (holderComp A B) z=
      (holderValue ((1:ℝ)/3) A z).comp (holderValue ((1:ℝ)/3) B z) := rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance FrozenIsomorphismLocal1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance FrozenIsomorphismLocal2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

 def c1HolderAffineCompose (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (v : C1HolderSpace E α) : C1HolderSpace F α := by
  let p := ((c,A),c1HolderValue α v)
  let V := holderAffineFamily α hα₀ hα₁ f hf hc p
  let D := holderAffineFamily α hα₀ hα₁ (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ) p
  let j : HolderSpace ℂ (ℂ →L[ℝ] E) α := holderConstantCLM α A+c1HolderDeriv α v
  let L := holderCLM α (holderMap α (ContinuousLinearMap.compL ℝ ℂ E F) D) j
  refine ⟨(V,L),c1HolderGraph_mem_of_hasFDerivAt α V L ?_⟩
  intro z
  have heV : holderValue α V=(fun z => f (c+A z+holderValue α (c1HolderValue α v) z)) := by
    ext z
    exact holderAffineFamily_apply α hα₀ hα₁ f hf hc p z
  rw [heV]
  change HasFDerivAt _ ((fderiv ℝ f (c+A z+holderValue α (c1HolderValue α v) z)).comp
    (A+holderValue α (c1HolderDeriv α v) z)) z
  exact (hf.differentiable (by simp) _).hasFDerivAt.comp z
    ((A.hasFDerivAt.const_add c).add (c1Holder_hasFDerivAt α v z))

 @[simp] theorem c1HolderAffineCompose_value (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (v : C1HolderSpace E α) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderAffineCompose α hα₀ hα₁ f hf hc c A v)) z=
      f (c+A z+holderValue α (c1HolderValue α v) z) :=
  holderAffineFamily_apply α hα₀ hα₁ f hf hc ((c,A),c1HolderValue α v) z

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_OrbitRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 def affineSlope {n : ℕ} (a : Phase n) : ℂ →L[ℝ] Phase n :=
  ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Phase n →L[ℝ] Phase n).flip) a

 @[simp] theorem affineSlope_apply {n : ℕ} (a : Phase n) (z : ℂ) : affineSlope a z=z • a := rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_PlanarEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

def phaseEuclidean (n : ℕ) : Phase n ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm

def euclideanNorm {n : ℕ} (v : Phase n) : ℝ := ‖phaseEuclidean n v‖

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_SchauderBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical
open scoped BoundedContinuousFunction
open Topology
open scoped NNReal

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def c1HolderDx : C1HolderSpace E ((1:ℝ)/3) →L[ℝ] HolderSpace ℂ E ((1:ℝ)/3) :=
  (holderJetEval ((1:ℝ)/3) 1).comp (c1HolderDeriv ((1:ℝ)/3))

@[simp] theorem c1HolderDx_value (u : C1HolderSpace E ((1:ℝ)/3)) (z : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderDx u) z =
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1 := by
  rw [c1Holder_fderiv]
  rfl

def compactHolderApply (R : ℝ) (A : CompactHolderSpace (E →L[ℝ] E) R)
    (v : HolderSpace ℂ E ((1:ℝ)/3)) : CompactHolderSpace E R :=
  ⟨holderApply ((1:ℝ)/3) A.val v,by
    intro z hz
    change (holderValue ((1:ℝ)/3) A.val z) (holderValue ((1:ℝ)/3) v z)=0
    rw [A.property z hz]
    rfl⟩

omit [CompleteSpace E] in
@[simp] theorem compactHolderApply_value [CompleteSpace E] (R : ℝ) (A : CompactHolderSpace (E →L[ℝ] E) R)
    (v : HolderSpace ℂ E ((1:ℝ)/3)) (z : ℂ) :
    compactHolderValue R (compactHolderApply R A v) z =
      compactHolderValue R A z (holderValue ((1:ℝ)/3) v z) := rfl

end

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end


