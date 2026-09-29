-- Prove2me | Definitions.Def_auto_GRU_M05_GALE_EQ_IsGaleTransform
-- name    : auto_GRU_M05_GALE_EQ_IsGaleTransform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:03:57.7569+00:00
-- url     : https://prove2.me/theorems/cbfc8805-0464-4238-8e58-cf2448a6f5e3
-- title:
--   Gale transforms from affine dependencies
-- statement:
--   The columns of the Gale row configuration are linearly independent and span exactly the affine dependencies of the given point configuration. Repeated and zero rows are allowed.
-- source:
--   Grünbaum, Convex Polytopes (2003), §5.4, printed pp.85–86 / PDF111–112

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Basic
import Mathlib.Analysis.Convex.Intrinsic
set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

def IsGaleTransform {d n : ℕ} (V : Fin n → (Fin d → ℝ))
    (G : Fin n → (Fin (n - d - 1) → ℝ)) : Prop :=
  LinearIndependent ℝ (fun j : Fin (n - d - 1) => fun i : Fin n => G i j) ∧
    (Submodule.span ℝ
      (Set.range (fun j : Fin (n - d - 1) => fun i : Fin n => G i j)) :
        Set (Fin n → ℝ)) =
      {a | (∑ i, a i) = 0 ∧ (∑ i, a i • V i) = 0}

end Grunbaum2003


