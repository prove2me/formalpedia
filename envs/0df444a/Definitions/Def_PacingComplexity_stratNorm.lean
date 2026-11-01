-- Prove2me | Definitions.Def_PacingComplexity_stratNorm
-- name    : PacingComplexity_stratNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:57.646345+00:00
-- url     : https://prove2.me/theorems/1a9afb98-02cf-48c6-bf0b-2f8ee5a80038
-- title:
--   The mixed strategies $x$ and $y$ read off the gadget
-- statement:
--   From the vectors $x'$, $y'$ define player 1's strategy $x$ and player 2's strategy $y$ by
--   $$
--   x_s=\frac{x'_s}{\sum_i x'_i},\qquad y_s=\frac{y'_s}{\sum_i y'_i}.
--   $$
--   Lemma 15 shows that, in every approximate pacing equilibrium of the gadget, $(x,y)$ is a well-supported Nash equilibrium of the bimatrix game.
--
--   **Formalization Note** Lean's division by zero returns $0$, so a zero denominator would give the zero vector, which is not a mixed strategy; Lemma 14 rules this case out.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Appendix A, p.33

import Mathlib
import Definitions.Def_PacingComplexity_GBuyer
import Definitions.Def_PacingComplexity_stratPrime

namespace PacingComplexity

/-- **The mixed strategies `(x, y)`** read off pacing multipliers of the gadget game (Chen, Kroer,
Kumar, *The Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2, Appendix A,
p.33): "Set player 1's mixed strategy x to be x_s = x′_s / Σ_i x′_i and player 2's mixed strategy
y to be y_s = y′_s / Σ_i y′_i."

`stratNorm α 0` is `x` and `stratNorm α 1` is `y`.

**Formalization Note** Lean's division by `0` returns `0`, so when `Σ_i x′_i = 0` this is the
zero vector, which is not a mixed strategy; Lemma 14 (`Σ_s x′_s > 1/8`) excludes that case in
every approximate pacing equilibrium of the gadget. -/
noncomputable def stratNorm {n : ℕ} (α : GBuyer n → ℝ) (p : Fin 2) (s : Fin n) : ℝ :=
  stratPrime α p s / ∑ i, stratPrime α p i

end PacingComplexity


