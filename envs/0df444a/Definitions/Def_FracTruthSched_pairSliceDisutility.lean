-- Prove2me | Definitions.Def_FracTruthSched_pairSliceDisutility
-- name    : FracTruthSched_pairSliceDisutility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:15.530386+00:00
-- url     : https://prove2.me/theorems/4ed69bf7-4987-4e40-8493-9514f7a61102
-- title:
--   Disutility $V_i(t;s)$ in the $(e,f)$-slice
-- statement:
--   Machine $i$'s **disutility in the $(e,f)$-slice** is its disutility as a function of its values $t=(t_1,t_2)$ on the two tasks, with opposing values $s$ and all other values fixed, normalized to vanish at $t=(0,0)$:
--   $$V_i(t;s)=V_i\big(z[t,s]\big)-V_i\big(z[(0,0),s]\big),$$
--   where $z[t,s]$ is the slice input. This is the restriction formula (6) of §2.3, $V_{J'}(a;z)=V_J(a,z)-V_J(0_{J'},z)$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 2, p.11; §2.3, eq. (6), p.5

import Mathlib
import Definitions.Def_FracTruthSched_disutility
import Definitions.Def_FracTruthSched_pairSliceInput

set_option autoImplicit false

namespace FracTruthSched

/-- Machine `i`'s **disutility in the `(e, f)`-slice**, `V_i(t; s)` (Anastasiadis et al.,
arXiv:2611.06642v1, Lemma 2, p.11, with §2.3, eq. (6), p.5: `V_{J'}(a; z) = V_J(a, z) − V_J(0_{J'}, z)`):
the full disutility of `i` at the slice input with own values `t` on `(e, f)` and opposing values `s`,
minus its value at own values `(0, 0)` on `(e, f)`. It vanishes at `t = (0, 0)`. -/
def pairSliceDisutility {n ℓ : ℕ} (M : FracMech n (CoreTask n ℓ)) (z : Fin n → CoreTask n ℓ → ℝ)
    (i j : Fin n) (e f : CoreTask n ℓ) (t s : ℝ × ℝ) : ℝ :=
  disutility M (pairSliceInput z i j e f t s) i - disutility M (pairSliceInput z i j e f 0 s) i

end FracTruthSched


