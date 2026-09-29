-- Prove2me | Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
-- name    : auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:01:54.832979+00:00
-- url     : https://prove2.me/theorems/823feec5-45b2-4f8e-97e4-cc3a26ad5b8c
-- title:
--   Line-free sets and characteristic cones
-- statement:
--   A set K in real d-dimensional space is line-free when it contains no translated full line with nonzero direction. Its characteristic cone consists of the vectors v such that x + t v belongs to K for every x in K and every real t ≥ 0. For nonempty closed convex sets this is the basepoint-independent cone of §2.5. The empty set has the whole space as its cone under this convention.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (2003), §2.5, Theorem 6 (2.5.6), printed p.25 / source.pdf p.43; characteristic cone and line-free sets: printed p.24 / PDF42; extreme points: §2.4, printed p.17 / PDF35.

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Group.Pointwise.Set.Basic

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003

/-- No straight line is contained in K: §2.5, printed p.24 / PDF p.42.
A nonzero direction parametrizes a genuine line, with all real parameters.
Local expression adapter; not a published Prove2Me definition. -/
def IsLineFree {d : ℕ} (K : Set (Fin d → ℝ)) : Prop :=
  ¬ ∃ x v : Fin d → ℝ, v ≠ 0 ∧ ∀ t : ℝ, x + t • v ∈ K

/-- The characteristic cone cc K of §2.5, p.24 / PDF p.42.
For nonempty closed convex K, the source's basepoint definition is independent
of the point x ∈ K. Universal quantification expresses that same cone without
choosing a basepoint. For the empty set it gives the whole space; this explicit
totalization does not change the representation since conv(ext ∅) is empty.
Local expression adapter; not a published Prove2Me definition. -/
def characteristicCone {d : ℕ} (K : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {v | ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → x + t • v ∈ K}

end Grunbaum2003


