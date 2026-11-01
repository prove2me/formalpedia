-- Prove2me | Definitions.Def_PacingComplexity_stratPrime
-- name    : PacingComplexity_stratPrime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:18.001012+00:00
-- url     : https://prove2.me/theorems/6e7c6b29-10e4-4579-bb08-ae71db17187b
-- title:
--   The vectors $x'$ and $y'$
-- statement:
--   Given pacing multipliers $\alpha$ of the gadget game, write $\alpha(p,s)$ for the multiplier of buyer $C(p,s)$ and $\alpha(T)$ for that of the threshold buyer. Define, for $s\in[n]$,
--   $$
--   x'_s=\Big\{\alpha(1,s)-\frac{\alpha(T)}2\Big\}^+,\qquad y'_s=\Big\{\alpha(2,s)-\frac{\alpha(T)}2\Big\}^+,
--   $$
--   where $a^+=\max\{a,0\}$. After normalization they become the mixed strategies read off an approximate pacing equilibrium.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Appendix A, p.32

import Mathlib
import Definitions.Def_PacingComplexity_GBuyer

namespace PacingComplexity

/-- **The vectors `x′` and `y′`** read off pacing multipliers of the gadget game (Chen, Kroer,
Kumar, *The Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2, Appendix A,
p.32): "x′_s = {α(1, s) − (α(T)/2)}⁺ and y′_s = {α(2, s) − (α(T)/2)}⁺ for each s ∈ [n], where
a⁺ denotes max{a, 0}", with `α(p, s)` the multiplier of buyer `C(p, s)`.

`stratPrime α 0` is `x′` and `stratPrime α 1` is `y′`.

**Formalization Note** Player `1` is `p = 0`, player `2` is `p = 1` (`Fin 2`). -/
noncomputable def stratPrime {n : ℕ} (α : GBuyer n → ℝ) (p : Fin 2) (s : Fin n) : ℝ :=
  max (α (.C p s) - α .T / 2) 0

end PacingComplexity


