-- Prove2me | Definitions.Def_LeblSCV_Varieties_singularPoints
-- name    : LeblSCV_Varieties_singularPoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:39.14976+00:00
-- url     : https://prove2.me/theorems/2ccebe55-9b8d-489a-8886-552e23d72fe5
-- title:
--   Definition 6.5.5 — the singular set $X_{\mathrm{sing}}$
-- statement:
--   For $X \subset \mathbb{C}^n$, a point of $X$ that is not regular is **singular**, and the **singular set** is
--   $$X_{\mathrm{sing}} = X \setminus X_{\mathrm{reg}}.$$
--
--   The mission's goal says that for a hypervariety this set is again a subvariety, of dimension at most $n-2$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 185, Definition 6.5.5

import Mathlib
import Definitions.Def_LeblSCV_Varieties_regularPoints

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.5.5: `X_sing`, the set of points of `X` that are not regular. -/
def singularPoints {n : ℕ} (X : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  X \ regularPoints X

end LeblSCV.Varieties


