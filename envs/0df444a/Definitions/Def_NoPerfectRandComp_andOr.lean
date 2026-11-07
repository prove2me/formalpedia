-- Prove2me | Definitions.Def_NoPerfectRandComp_andOr
-- name    : NoPerfectRandComp_andOr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:14.421337+00:00
-- url     : https://prove2.me/theorems/3cb3ccfb-0a61-4c93-b9ad-6ea1ed3c7691
-- title:
--   The partial short-circuit AND–OR rule on an $m\times m$ array
-- statement:
--   Let each entry $e = (i,j)$ of an $m \times m$ array carry a possibly partial Boolean function $h_e$ on its own block of coordinates, and call entry $e$ **promised with value $z$** when its block lies in $\mathrm{Dom}(h_e)$ and $h_e$ takes the value $z$ there. The **partial short-circuit AND–OR rule** has value
--   1. one, when every row contains an entry promised with value one;
--   2. zero, when some row consists entirely of entries promised with value zero;
--
--   and all other inputs are outside its domain. The two conditions are disjoint.
--
--   This is the core rule of the outer function and the rule evaluated robustly in Lemma 5.11.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4.2, p.13; Lemma 5.11, p.25; p.26

import Mathlib
import Definitions.Def_NoPerfectRandComp_PartialFn

namespace NoPerfectRandComp

open Classical in
/-- The partial short-circuit AND–OR rule on an `m × m` array of blocks (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4.2, p.13;
Lemma 5.11, p.25). Entry `(i, j)` carries a possibly partial function `h (i, j)` on its block.
The value is one when every row contains a promised entry of value one, and zero when some row
consists entirely of promised entries of value zero; all other inputs are outside the domain.
The two conditions are disjoint. -/
noncomputable def andOr {κ : Type} (m : ℕ) (h : Fin m × Fin m → PartialFn κ) :
    PartialFn (Fin m × Fin m × κ) where
  dom := {x | (∀ i, ∃ j, (fun t => x (i, j, t)) ∈ (h (i, j)).dom ∧
        (h (i, j)).val (fun t => x (i, j, t)) = true) ∨
      (∃ i, ∀ j, (fun t => x (i, j, t)) ∈ (h (i, j)).dom ∧
        (h (i, j)).val (fun t => x (i, j, t)) = false)}
  val := fun x => decide (∀ i, ∃ j, (fun t => x (i, j, t)) ∈ (h (i, j)).dom ∧
    (h (i, j)).val (fun t => x (i, j, t)) = true)

end NoPerfectRandComp


