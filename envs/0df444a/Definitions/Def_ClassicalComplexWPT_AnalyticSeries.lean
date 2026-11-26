-- Prove2me | Definitions.Def_ClassicalComplexWPT_AnalyticSeries
-- name    : ClassicalComplexWPT_AnalyticSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:56:25.363649+00:00
-- url     : https://prove2.me/theorems/ab162006-15d7-5e1d-b613-71cff4b77b8f
-- title:
--   Analytic Series
-- statement:
--   Definitions and structural lemmas for Analytic Series, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
set_option autoImplicit true
namespace ClassicalComplexWPT
noncomputable def lastAxis (n : ℕ) : ℂ →L[ℂ] Ambient n :=
  ContinuousLinearMap.inr ℂ (Base n) ℂ
def lastDirection (n : ℕ) : Ambient n := (0, 1)
noncomputable def lastTaylorCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k : ℕ) (z : Base n) : ℂ :=
  p.changeOrigin (z, 0) k (fun _ ↦ lastDirection n)
end ClassicalComplexWPT


