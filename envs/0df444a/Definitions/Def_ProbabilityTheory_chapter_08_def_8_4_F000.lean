-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_08_def_8_4_F000
-- name    : ProbabilityTheory_chapter_08_def_8_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:03:37.016355+00:00
-- url     : https://prove2.me/theorems/a5b9a04a-a495-47ff-a04f-58136c9a85c4
-- title:
--   Chapter 8, def_8_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 8, source module `def_8_4`: `ContinuousPdfCoupling`, `DiscretePmfCoupling`, `def_8_4`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_08/def_8_4.lean

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory

structure ContinuousPdfCoupling (fX fY : ℝ → ENNReal) where
  jointDensity : ℝ → ℝ → ENNReal
  totalMass : ∫⁻ p : ℝ × ℝ, jointDensity p.1 p.2 ∂(volume.prod volume) = 1
  marginal_X : ∀ x : ℝ, fX x = ∫⁻ y : ℝ, jointDensity x y ∂volume
  marginal_Y : ∀ y : ℝ, fY y = ∫⁻ x : ℝ, jointDensity x y ∂volume

structure DiscretePmfCoupling {α β : Type*} [Countable α] [Countable β]
    (pX : PMF α) (pY : PMF β) where
  jointPMF : PMF (α × β)
  marginal_X : jointPMF.map Prod.fst = pX
  marginal_Y : jointPMF.map Prod.snd = pY

def def_8_4 :=
  (ContinuousPdfCoupling, @DiscretePmfCoupling)


