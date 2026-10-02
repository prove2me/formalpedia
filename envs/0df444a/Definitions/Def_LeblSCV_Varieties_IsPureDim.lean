-- Prove2me | Definitions.Def_LeblSCV_Varieties_IsPureDim
-- name    : LeblSCV_Varieties_IsPureDim
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:10:04.433303+00:00
-- url     : https://prove2.me/theorems/55607428-ccb8-40cd-b02c-120b83c6af91
-- title:
--   Definition 6.5.7 — pure dimension
-- statement:
--   A set $X \subset \mathbb{C}^n$ is of **pure dimension $d$** if at every regular point $q \in X_{\mathrm{reg}}$ the dimension of $X$ at $q$ is $d$:
--   $$\dim_q X = d \quad \text{for all } q \in X_{\mathrm{reg}}.$$
--
--   **Formalization Note.** $d$ is an integer (`ℤ`), so that the codimension $n - c$ is never truncated at $0$. The condition reads "whenever $q$ is a regular point of dimension $k$, then $k = d$"; since the dimension at a regular point is well defined (Exercise 6.5.6) this is the book's condition. A set with no regular points, such as $\emptyset$, is of pure dimension $d$ for every $d$, as in the book's wording.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 186, Definition 6.5.7

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsRegularPointOfDim

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.5.7: `X` is of **pure dimension `d`** if at every regular point `q` of `X`
the dimension `dim_q X` is `d`. The dimension is taken in `ℤ` so that no truncated subtraction
occurs when `d` is written as `n - c`; an `X` without regular points (e.g. `X = ∅`) is of pure
dimension `d` for every `d`, as in the book's wording. -/
def IsPureDim {n : ℕ} (X : Set (Fin n → ℂ)) (d : ℤ) : Prop :=
  ∀ (q : Fin n → ℂ) (k : ℕ), IsRegularPointOfDim X q k → (k : ℤ) = d

end LeblSCV.Varieties


