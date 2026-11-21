-- Prove2me | Definitions.Def_TorusEuler_Phase
-- name    : TorusEuler_Phase
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T19:37:40.47898+00:00
-- url     : https://prove2.me/theorems/c49c4c37-fd89-4db0-92af-9feb5879f7af
-- title:
--   Phase mean over the unit period
-- statement:
--   The phase average over the frozen paper's unit period: for a function $f:\mathbb{R}\to E$ into a real normed space,
--   $$\operatorname{phaseMean}(f) = \int_0^1 f(s)\,ds.$$
--   It is used to normalize the wave profiles: the primitive $P_h$ of the profile $F_h$ in Lemma 3.1 is required to have phase mean zero.
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/PhaseCalculus.lean#L22; TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/02_affine.tex (phase average).

import Mathlib

open MeasureTheory

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Phase average over the frozen paper's unit period. -/
noncomputable def phaseMean (f : ℝ → E) : E :=
  ∫ s in (0 : ℝ)..1, f s

end TorusEuler


