-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:23:19.454019+00:00
-- url     : https://prove2.me/theorems/ea98e173-2ede-5e7b-ba43-a903e5767e0e
-- title:
--   Telescoping
-- statement:
--   Definitions and structural lemmas for Telescoping, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)
noncomputable section
def Telescoping.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (S : System R), ∃ C' ℓ₁ : ℝ, ∀ t t' : ℝ, 0 < t' → t' ≤ t → ℓ₁ ≤ ell t → ∀ x ∈ R.Yo,
      (R.r x ≤ ell t → |S.ph t x - S.ph t' x| ≤ C' * (t ^ (1 / 3 : ℝ) + errE S.C t)) ∧
      (ell t < R.r x → |S.ph t x - S.ph t' x| ≤ C' * Real.log (R.r x))
def TelescopingFamily.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (F : Family A) (Λ : ℝ),
    ∃ C' ℓ₁ : ℝ, ∀ c : Fin F.m → ℝ, ∑ i, |c i| ≤ Λ →
      ∀ t t' : ℝ, 0 < t' → t' ≤ t → ℓ₁ ≤ ell t → ∀ x ∈ F.Yo,
        (F.r x ≤ ell t →
          |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤
            C' * (t ^ (1 / 3 : ℝ) + errE C' t)) ∧
        (ell t < F.r x →
          |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤ C' * Real.log (F.r x))
namespace System
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegChartData A}
  (S : System R)
def teleConst : ℝ := 1 + |S.C| + S.C ^ 2 + |R.C|
end System
end
end GroundTheory.Heights₂.Heights.AnalyticLimit


