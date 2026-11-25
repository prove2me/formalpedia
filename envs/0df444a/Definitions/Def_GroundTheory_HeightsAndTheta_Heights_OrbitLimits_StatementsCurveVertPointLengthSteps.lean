-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointLengthSteps
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointLengthSteps
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:11:02.009735+00:00
-- url     : https://prove2.me/theorems/8b54ab7a-53e7-4f71-91fa-ac03a9a8efa6
-- title:
--   Statements Curve Vert Point Length Steps
-- statement:
--   Definitions and structural lemmas for Statements Curve Vert Point Length Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsCurveVertPointLengthSteps.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointLengthSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
def CurveVertPointChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        (curvePtIdeal y W).IsMaximal ∧
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧
          (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) ∧
        ∀ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k)
def CurveVertPointInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)
def CurveVertPointSurj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ m : Ideal (curveRing y), m.IsMaximal →
        locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0 →
          ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m
def CurveVertPointMultChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        ∀ a b : curveRing y, b ∉ curvePtIdeal y W →
          (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
            multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
              locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a})
def CurveSectionQuotLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ (m : Ideal (curveRing y)) (c : ∀ k, ι k), m.IsPrime → (∀ k, y ⟨k, c k⟩ ≠ 0) →
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) →
        ∀ a b : curveRing y, b ∉ m → (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
          locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) =
            locLen m (curveRing y ⧸ Ideal.span {a})
end
end GroundTheory.Heights₂.Heights.Targets


