-- Prove2me | Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_SchemeRealizes
-- name    : auto_GRU_M05_EFFECTIVE_TYPES_SchemeRealizes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:11:33.699957+00:00
-- url     : https://prove2.me/theorems/85cc989e-7597-429f-8cc4-231aac0398d8
-- title:
--   Realization of a finite incidence scheme
-- statement:
--   A full-dimensional real d-polytope with exactly k injectively labelled vertices realizes S when its nonempty proper faces have exactly the vertex subsets represented by S. Labels lie in Fin k; list order and repetition within the encoding of a subset are immaterial.
-- source:
--   Grünbaum, Convex Polytopes, 2nd ed., Springer (2003), §5.5, printed p.91 / PDF117

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Basic
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_IsDPolytope

set_option autoImplicit false
open scoped BigOperators


namespace Grunbaum2003

def SchemeRealizes {d : ℕ} (k : ℕ) (S : List (List ℕ))
    (P : Set (Fin d → ℝ)) : Prop :=
  IsDPolytope P ∧
    ∃ V : Fin k → (Fin d → ℝ), Function.Injective V ∧
      Set.range V = {x | IsExposed ℝ P {x}} ∧
      ∀ J : Finset ℕ,
        (∃ L ∈ S, L.toFinset = J) ↔
          ∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
            (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F}

end Grunbaum2003


