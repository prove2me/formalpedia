-- Prove2me | Definitions.Def_ChapterHermiteExpWall
-- name    : ChapterHermiteExpWall
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:11:04.093969+00:00
-- url     : https://prove2.me/theorems/0ca3749e-626f-46f2-bf97-1e55cc641e1b
-- title:
--   Chapter HermiteExpWall
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHermiteExpWall.lean`): generated def bundle for ChapterHermiteExpWall. See BookProof/ChapterHermiteExpWall.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteExpWall.lean

import Definitions.Def_ChapterQgHermiteCore
import Mathlib


/-!
# The exponential wall is not a relatively bounded perturbation (plan §10.6.1, target 2)

`CONSOLIDATED_PLAN.md` §10.6.1 target 2 proposes to obtain essential self-adjointness of
the one-particle scalaron Hamiltonian on the Gauss–polynomial (Hermite) core by a
Kato–Rellich argument: *"`V(φ)` is `(−Δ)`-bounded with arbitrarily small relative bound on
the Gauss core"*.  The plan itself flags that this target "needs restating".  This module
proves that it is in fact **false**, in the strongest sense: the scalaron potential is not
relatively bounded on the Hermite core with respect to the kinetic term, nor with respect
to the harmonic (conformal-mode) oscillator `−Δ + x²/4` — not with a small relative bound,
and not with *any* pair of constants.

## The mechanism

On the monomial core elements `ψ_N(x) = x^N e^{−x²/4}` the reference operators grow only
polynomially in `N`, because they act on the core by polynomial maps of fixed degree
increment:

* `osc_psi` — `(−d²/dx² + x²/4)(x^N e^{−x²/4}) = ((N + ½)x^N − N(N−1)x^{N−2})e^{−x²/4}`,
  so `‖H₀ψ_N‖ ≤ (N² + 1)‖ψ_N‖` (`l2_osc_le`);
* `neg_deriv2_psi` — `−d²/dx²(x^N e^{−x²/4}) = ((N + ½)x^N − N(N−1)x^{N−2} − ¼x^{N+2})e^{−x²/4}`,
  so `‖−ψ_N''‖ ≤ (N² + 1)‖ψ_N‖` (`l2_kin_le`).

The exponential wall, on the other hand, grows *super-polynomially* along the same family.
The quadratic form of the potential is an exponentially tilted Gaussian moment, and
expanding the tilt to eighth order gives

* `gaussMoment_tilt_ge` — `∫ e^{−2sx}x^{2N}e^{−x²/2}dx ≥ (2s⁸/315)·M_{2N+8}`,
* `gaussMoment_shift_eight` — `M_{2N+8} = (2N+7)(2N+5)(2N+3)(2N+1)·M_{2N}`,

hence `⟪ψ_N, Vψ_N⟫ ≥ c₀(K N⁴ − 1)‖ψ_N‖²` with `K = 8s⁸/315` (`quadForm_scalaron_ge`), and
Cauchy–Schwarz turns this into `‖Vψ_N‖ ≥ c₀(K N⁴ − 1)‖ψ_N‖` (`l2_scalaron_ge`).  A quartic
lower bound against a cubic upper bound is the contradiction.

## What is proved

* `not_relatively_bounded_of_cubic` — the abstract form: no operator whose norm along the
  monomial family grows at most cubically can dominate the scalaron potential;
* **`scalaronV_not_kinetic_relativelyBounded`** — there are **no** constants `a, b` with
  `‖Vψ‖ ≤ a‖ψ''‖ + b‖ψ‖` for all Gauss polynomials `ψ`;
* **`scalaronV_not_oscillator_relativelyBounded`** — there are **no** constants `a, b` with
  `‖Vψ‖ ≤ a‖(−Δ + x²/4)ψ‖ + b‖ψ‖` for all Gauss polynomials `ψ`.

Consequently the Kato–Rellich route of §10.6.1 target 2 — and, a fortiori, the
"arbitrarily small relative bound" it asks for — cannot be taken for the exponential wall,
either against the free kinetic term or against the conformal-mode oscillator whose Hermite
functions define the core.  This is a genuine obstruction, not a gap in the argument: it is
why `BookProof.ChapterQgHermiteOscillatorEsa` can only reach *bounded* perturbations of the
oscillator by Kato–Rellich, and why the exponential case in
`BookProof.ChapterScalaronHermiteEsa` had to be handled by a Fourier/moment argument
instead.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.HermiteExpWall

open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

/-- The `L²(ℝ)` norm of a real function, as a plain integral. -/
noncomputable def l2 (f : ℝ → ℝ) : ℝ := Real.sqrt (∫ x, f x ^ 2)



/-! ## 1. Gaussian moments -/











/-! ## 2. The exponentially tilted moment -/







/-! ## 3. The core family -/

/-- The monomial core elements `ψ_N(x) = x^N e^{−x²/4}`. -/
noncomputable def psi (N : ℕ) : ℝ → ℝ := gaussPoly ((Polynomial.X : Polynomial ℝ) ^ N)

















/-! ## 4. The quadratic form of the wall -/







/-! ## 5. The reference operators grow polynomially

Both `−d²/dx²` and `−d²/dx² + x²/4` map the monomial core family into itself, shifting the
degree by at most two, so their `L²` norms along the family grow only polynomially in `N`. -/











/-- The two-parameter shape of the polynomial of `(−d²/dx² + x²/4)ψ_{m+2}`. -/
noncomputable def oscQ (m : ℕ) (a b : ℝ) : Polynomial ℝ :=
  Polynomial.C a * Polynomial.X ^ (m + 2) - Polynomial.C b * Polynomial.X ^ m

/-- The two-parameter shape of the polynomial of `−d²/dx² ψ_{m+2}`. -/
noncomputable def kinQ (m : ℕ) (a b : ℝ) : Polynomial ℝ :=
  oscQ m a b - Polynomial.C (1 / 4 : ℝ) * Polynomial.X ^ (m + 4)

/-- The coefficient of `x^{m+2}`: `N + ½` with `N = m + 2`. -/
noncomputable def aCoef (m : ℕ) : ℝ := ((m : ℝ) + 2) + 1 / 2

/-- The coefficient of `x^m`: `N(N−1)` with `N = m + 2`. -/
noncomputable def bCoef (m : ℕ) : ℝ := ((m : ℝ) + 2) * ((m : ℝ) + 1)































/-! ## 6. No relative bound -/







end

end BookProof.HermiteExpWall


