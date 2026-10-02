-- Prove2me | Definitions.Def_LeblSCV_Bergman_holoRep
-- name    : LeblSCV_Bergman_holoRep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T09:41:45.912588+00:00
-- url     : https://prove2.me/theorems/d0040560-2be6-4d89-8120-f0d6219b6a1f
-- title:
--   Pointwise values of an element of $A^2(U)$ (holomorphic representative)
-- statement:
--   An element $f \in A^2(U)$ is a class of functions equal almost everywhere on $U$; the book evaluates it pointwise, $f(z)$, meaning the value of the holomorphic function in the class. For $f \in A^2(U)$ let
--   $$f(z) := g(z), \qquad z \in \mathbb{C}^n,$$
--   where $g$ is a (chosen) function holomorphic on $U$ that agrees with $f$ almost everywhere on $U$.
--
--   When $U$ is open this is well defined on $U$: two continuous functions that agree almost everywhere on an open set agree everywhere on it, since nonempty open sets have positive Lebesgue measure. Values outside $U$ depend on the choice and are never used.
--
--   **Formalization Note.** `holoRep U f` is defined by `Classical.choose` on the defining property of `bergmanSpace U`; the `else 0` branch is unreachable for elements of `bergmanSpace U`. Every statement of this mission evaluates `holoRep U f` only at points of $U$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 160–162 (point evaluation on $A^2(U)$)

import Mathlib
import Definitions.Def_LeblSCV_Bergman_bergmanSpace

open MeasureTheory

namespace LeblSCV.Bergman

open Classical in
/-- The holomorphic representative of an element `f ∈ A²(U)`, i.e. the function `f(z)` that the
book evaluates pointwise (Lebl, pp. 160–162): a function holomorphic on `U` that agrees with `f`
almost everywhere on `U`. On an open `U` it is unique on `U` (two continuous functions that agree
almost everywhere on an open set agree on it); its values off `U` are irrelevant. -/
noncomputable def holoRep {n : ℕ} (U : Set (Fin n → ℂ)) (f : bergmanSpace U) :
    (Fin n → ℂ) → ℂ :=
  if h : ∃ g : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ g U ∧
      ((f : Lp ℂ 2 (volume.restrict U)) : (Fin n → ℂ) → ℂ) =ᵐ[volume.restrict U] g then
    h.choose
  else 0

end LeblSCV.Bergman


