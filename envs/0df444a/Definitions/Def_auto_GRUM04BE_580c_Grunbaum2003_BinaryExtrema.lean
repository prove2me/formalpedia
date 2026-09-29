-- Prove2me | Definitions.Def_auto_GRUM04BE_580c_Grunbaum2003_BinaryExtrema
-- name    : auto_GRUM04BE_580c_Grunbaum2003_BinaryExtrema
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:02:47.128577+00:00
-- url     : https://prove2.me/theorems/aab85e28-1fa7-4c0f-abb6-a4aa580a60a1
-- title:
--   Full-dimensional binary polytopes and face counts
-- statement:
--   IsDPolytope P means that P is a nonempty finite convex hull spanning the full real coordinate space. IsZeroOnePolytope P means that P is the convex hull of a set of binary-coordinate points. faceCount P k counts the nonempty exposed faces of P whose affine dimension is k.
-- source:
--   Grünbaum, Convex Polytopes, 2nd ed. (2003), §2.4 p.17; §3.1 p.31; §4.9 p.69a (PDF94).

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

def IsDPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  (∃ V : Set (Fin d → ℝ), V.Finite ∧ V.Nonempty ∧ P = convexHull ℝ V) ∧
    affineSpan ℝ P = ⊤

noncomputable def faceCount {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) : ℕ :=
  {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = k}.ncard

def IsZeroOnePolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  ∃ V : Set (Fin d → ℝ),
    (∀ x ∈ V, ∀ i, x i = 0 ∨ x i = 1) ∧ P = convexHull ℝ V

end Grunbaum2003


