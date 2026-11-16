-- Prove2me | Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
-- name    : Kyprianou_Ch01_McKeanRightContinuousFiltration
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T08:21:37.897934+00:00
-- url     : https://prove2.me/theorems/bbeb11c0-ffe1-43c1-a73a-d0a013751833
-- title:
--   Right-continuous natural filtration and admissible Brownian stopping times
-- statement:
--   Define F(t+) as the intersection of all raw natural sigma-algebras F(s), for s>t. A possibly infinite stopping time is admissible when {tau<=t} belongs to F(t+) at every time. This retains the raw natural filtration for unrelated source theorems. The correction is necessary for strict first passage into an open half-line, which is not always a stopping time for the raw natural filtration.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; Perla Sousi (2011) Advanced Probability Proposition 3.5 and Example 3.2, https://www.statslab.cam.ac.uk/~ps422/notes-2011.pdf

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

open Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch01

/-- Right-continuous enlargement of the raw natural filtration of X:
    F(t+) is the intersection of all raw F(s) for s > t. -/
noncomputable def naturalSigmaRight
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨅ s : ℝ≥0, ⨅ _hs : t < s, naturalSigma X s

/-- A possibly infinite stopping time for the right-continuous
    natural filtration of X. -/
def IsNaturalRightStoppingTime
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) : Prop :=
  ∀ t : ℝ≥0,
    @MeasurableSet Ω (naturalSigmaRight X t)
      {ω | τ ω ≤ (t : WithTop ℝ≥0)}

end Kyprianou.Ch01


