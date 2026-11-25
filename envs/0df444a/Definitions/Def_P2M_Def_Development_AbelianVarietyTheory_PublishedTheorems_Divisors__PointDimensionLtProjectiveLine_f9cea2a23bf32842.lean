-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:19.425798+00:00
-- url     : https://prove2.me/theorems/d2bf634a-657b-509b-8635-164ff85b7307
-- title:
--   Point Dimension Lt Projective Line
-- statement:
--   Definitions and structural lemmas for Point Dimension Lt Projective Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
namespace AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
def singularLocus (A : FinHolAtlas d X) (T : Set X) : Set X :=
  T \ ⋃ n, regularLocus A T n
def analyticDim (A : FinHolAtlas d X) (T : Set X) : WithBot ℕ∞ :=
  ⨆ (n : ℕ) (_ : (regularLocus A T n).Nonempty), (n : WithBot ℕ∞)
end AnDim
namespace Published
open AnDim
def AnalyticSetDimension : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    (∀ T : Set X, A.IsAnalyticSubset T →
      A.IsAnalyticSubset (singularLocus A T) ∧
        (T.Nonempty → analyticDim A (singularLocus A T) < analyticDim A T)) ∧
    (∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
      analyticDim A Z = n) ∧
    (∀ C S : Set X, IsIrreducibleAnalytic A C → A.IsAnalyticSubset S → ¬ C ⊆ S →
      analyticDim A (C ∩ S) < analyticDim A C) ∧
    (∀ T : Set X, A.IsAnalyticSubset T →
      {C | IsIrreducibleComponent A T C}.Finite ∧ T = ⋃₀ {C | IsIrreducibleComponent A T C})
end Published
namespace AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
def padL (k d : ℕ) : (Fin k → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => if h : (i : ℕ) < k then ContinuousLinearMap.proj ⟨i, h⟩ else 0
end AnDim
end
end GlobalTheory


