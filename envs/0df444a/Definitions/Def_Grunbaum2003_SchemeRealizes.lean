-- Prove2me | Definitions.Def_Grunbaum2003_SchemeRealizes
-- name    : Grunbaum2003_SchemeRealizes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:39:28.888154+00:00
-- url     : https://prove2.me/theorems/4f0739d9-7c5a-42e5-b5b6-e90379bf3303
-- title:
--   Realization of a finite vertex-face incidence scheme
-- statement:
--   A finite list of finite vertex-label lists realizes a d-polytope with k labelled vertices exactly when it records all nonempty proper exposed faces, up to an injective vertex labelling.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §5.5, scheme paragraph, printed pp. 90–91 / PDF pp. 116–117; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

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


