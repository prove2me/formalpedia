-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffStatement
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:01.563455+00:00
-- url     : https://prove2.me/theorems/c2d7f837-973d-43f5-9ee8-f8c20c246051
-- title:
--   Holo Cont Diff Statement
-- statement:
--   Definitions and structural lemmas for Holo Cont Diff Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/HoloContDiffStatement.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.C
open Set
open scoped ContDiff
def HoloSmoothStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ f Ω → ContDiffOn ℝ ∞ f Ω
def HoloDerivStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ f Ω →
      ∀ v : EuclideanSpace ℂ (Fin n), DifferentiableOn ℂ (fun x => fderiv ℂ f x v) Ω
def HoloContDiffStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ f Ω → ContDiffOn ℂ ∞ f Ω
end ReciprocityTheory.L2DbarEstimates.C


