-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:53.861797+00:00
-- url     : https://prove2.me/theorems/43f898ec-572c-495a-af1b-08cda87261f5
-- title:
--   Cont Diff At Of Is Potential
-- statement:
--   Definitions and structural lemmas for Cont Diff At Of Is Potential, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
def HoloSmoothStatement : Prop :=
  ∀ {e e' : ℕ} (F : (Fin e → ℂ) → (Fin e' → ℂ)) (U : Set (Fin e → ℂ)), IsOpen U →
    AnalyticOnNhd ℂ F U → ContDiffOn ℝ ∞ F U
def SmoothOnAlgStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U V : Set X) (f g : X → ℝ)
    (c : ℝ), A.SmoothOn U f → A.SmoothOn V g → V ⊆ U →
      A.SmoothOn V (fun x => f x + g x) ∧ A.SmoothOn U (fun x => c * f x)
section SlopeTestRemainingChoices
variable {e : ℕ} {X : Type} [TopologicalSpace X]
end SlopeTestRemainingChoices
end
end ReciprocityTheory.AnForm.M


