-- Prove2me | Definitions.Def_PorteusGenSS_C2
-- name    : PorteusGenSS_C2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:35.645875+00:00
-- url     : https://prove2.me/theorems/4fd60ead-8994-4394-9d6b-289b98badada
-- title:
--   Tangent parameters with least intercept $C_2(z)$
-- statement:
--   For $z>0$,
--
--   $$
--   C_2(z)=\{(a,K)\in C_1(z):\ K\le K'\ \text{for all }(a',K')\in C_1(z)\},
--   $$
--
--   the tangent line at $z$ with the smallest intercept (the left tangent). For concave $c$ it is a single point.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412

import Mathlib
import Definitions.Def_PorteusGenSS_C1

namespace PorteusGenSS

/-- **Tangent parameters with least intercept, C₂(z) (§II).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412: "To achieve uniqueness, let, for z > 0,
C2(z) = {(c, K) ∈ C1(z); K ≤ K′ for all (c′, K′) ∈ C1(z)}."

`C2 c z` is the set of pairs of `C1 c z` whose intercept is least among all pairs of `C1 c z`. -/
def C2 (c : ℝ → ℝ) (z : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ C1 c z ∧ ∀ q ∈ C1 c z, p.2 ≤ q.2}

end PorteusGenSS


