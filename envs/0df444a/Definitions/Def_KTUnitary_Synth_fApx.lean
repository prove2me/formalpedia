-- Prove2me | Definitions.Def_KTUnitary_Synth_fApx
-- name    : KTUnitary_Synth_fApx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:27.160877+00:00
-- url     : https://prove2.me/theorems/49334bf7-6000-48cc-8ba3-2a14c529fdba
-- title:
--   The promise problem $f\mathrm{Apx}$
-- statement:
--   For $f:\{0,1\}^*\to\mathbb R$, the promise problem on inputs $(x,\phi,\varepsilon)$ with $\phi$ and $\varepsilon>0$ in fixed-point binary:
--   - YES: $f(x)>\phi+\varepsilon$;
--   - NO: $f(x)<\phi-\varepsilon$;
--   - otherwise undefined.
--
--   $\mathcal U\mathrm{EntryApx}=(\mathcal U\mathrm{Entry})\mathrm{Apx}$ is items 5 and 7 of Theorem 6.17.
--
--   **Formalization Note** The input is the string `tup [x, φ, e]`; strings not of this form, or with $\varepsilon\le 0$, are outside the promise.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.3, p. 24

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_fixedPoint
import Definitions.Def_KTUnitary_Synth_PromiseProblem

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The promise problem `fApx`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.3, p. 24): "If `f : {0,1}* → ℝ` is a
function, then `fApx` is the following promise problem defined on inputs `x ∈ {0,1}*`, `ϕ ∈ ℝ`, and
`ε > 0`, with the latter two encoded in fixed-point binary: (YES) `fApx(x, ϕ, ε) = 1` if
`f(x) > ϕ + ε`. (NO) `fApx(x, ϕ, ε) = 0` if `f(x) < ϕ − ε`. Otherwise, `fApx(x, ϕ, ε)` is undefined."

Here the input is the string `tup [x, φ, e]`, with `φ` and `e` decoded by `fixedPoint` and the
decoded `e` positive. Strings not of this form are outside the promise. -/
def fApx (f : Str → ℝ) : PromiseProblem :=
  ({s | ∃ x φ e : Str, s = tup [x, φ, e] ∧ 0 < fixedPoint e ∧
      ((fixedPoint φ : ℚ) : ℝ) + ((fixedPoint e : ℚ) : ℝ) < f x},
   {s | ∃ x φ e : Str, s = tup [x, φ, e] ∧ 0 < fixedPoint e ∧
      f x < ((fixedPoint φ : ℚ) : ℝ) - ((fixedPoint e : ℚ) : ℝ)})

end KTUnitary.Synth


