-- Prove2me | Definitions.Def_RandGraphStates_Cunif
-- name    : RandGraphStates_Cunif
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:40.912371+00:00
-- url     : https://prove2.me/theorems/169435a5-6a66-4bef-8bde-9a7f9f8826f1
-- title:
--   The constant $C_{\mathrm{unif}}$
-- statement:
--   The constant
--   $$
--   C_{\mathrm{unif}}:=\prod_{i=1}^\infty\bigl(1-2^{-2i}\bigr)^{-1}\approx 1.452
--   $$
--   is the leading coefficient in the nullity tail of a uniformly random symmetric zero-diagonal matrix over $\mathbb F_2$.
--
--   **Formalization Note** The product is indexed from $i=0$ with $i+1$ in the exponent. It is multipliable, so the infinite product in Lean is the true value and not a default.
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Corollary 4.4, p.19

import Mathlib

set_option autoImplicit false

namespace RandGraphStates

/-- `C_unif := ∏_{i ≥ 1} (1 - 2^{-2i})⁻¹ ≈ 1.452`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), Corollary 4.4, p.19.

**Formalization Note.** Indexed from `i = 0` with `i + 1` in the exponent. The product is
multipliable, so `∏'` is its true value and not the default `1`;
`Solutions/verification/RandGraphStates_Sanity.lean` proves it. -/
noncomputable def Cunif : ℝ :=
  ∏' i : ℕ, (1 - (2 : ℝ) ^ (-(2 * ((i : ℤ) + 1))))⁻¹

end RandGraphStates


