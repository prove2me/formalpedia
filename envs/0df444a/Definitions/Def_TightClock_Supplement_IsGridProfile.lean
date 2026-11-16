-- Prove2me | Definitions.Def_TightClock_Supplement_IsGridProfile
-- name    : TightClock_Supplement_IsGridProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:59:23.862367+00:00
-- url     : https://prove2.me/theorems/6100371d-d9c9-4e1b-ab6a-0454fb7e1c8e
-- title:
--   Grid value profile $v\in(\delta\mathbb Z_{\ge0})^n$
-- statement:
--   For a grid step $\delta$, a value profile $v=(v_1,\dots,v_n)$ is a **grid profile** if every value lies on the public grid,
--
--   $$v_i\in\delta\mathbb Z_{\ge0}=\{0,\delta,2\delta,\dots\}\qquad(i\in[n]).$$
--
--   This is the public-grid model of the prior-free upper bounds of §4 and §5: values are finite but no public upper bound on them is assumed.
--
--   **Formalization Note** The positivity $\delta>0$ is a separate hypothesis of the theorems that use this predicate.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- The public-grid model of the prior-free upper bounds: every value lies on the grid `δℤ≥0`,
`vᵢ ∈ δℤ≥0`, with no public upper bound. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, p.13 (PDF 16): "we assume that bidder values
lie on a public grid, vi ∈ δZ≥0 for a public δ > 0. Every value is finite, but no public upper bound
is assumed."

**Formalization Note** The positivity `0 < δ` is a separate hypothesis of the theorems, not part of
this predicate. -/
def IsGridProfile {n : ℕ} (δ : ℝ) (v : Fin n → ℝ) : Prop :=
  ∀ i, ∃ m : ℕ, v i = δ * m

end TightClock.Supplement


