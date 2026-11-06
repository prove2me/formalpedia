-- Prove2me | Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
-- name    : BianchiIX_Analysis_ConnectionAmplitudeDifferential
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T09:12:19.668462+00:00
-- url     : https://prove2.me/theorems/3dc65f43-56ff-4a16-9276-294b52e461e4
-- title:
--   Logarithmic strong and weak wall rates and their derivatives
-- statement:
--   For the positive reflected phase variable $m$, put
--   $$n(a,b)=\sqrt{a^2+b^2},\quad j(a,b)=\frac1{n(a,b)(n(a,b)+a)},$$
--   $$\phi=n(m+1,v)+n(m-1,w)-m,\quad
--   h=\frac{m+1}{n(m+1,v)}+\frac{m-1}{n(m-1,w)}-1,$$
--   $$Q=mh+\frac{v^2}{n(m+1,v)}+\frac{w^2}{n(m-1,w)},\quad
--   k=j(m+1,v)-j(m-1,w).$$
--   Write $\kappa=u(v+w-u)$, $s=m-1-\kappa$,
--   $b=(1-m^2-(v-w)^2+u^2)/2$, and
--   $$M_v=-\frac{v^2}{n(m+1,v)h},\qquad M_w=-\frac{w^2}{n(m-1,w)h}.$$
--   The four coordinate differential operators, in the order
--   $(\phi,\log u,\log v,\log w)$, are
--   $$L_0=h^{-1}\partial_m,\quad L_1=u\partial_u,\quad
--   L_2=M_v\partial_m+v\partial_v,\quad L_3=M_w\partial_m+w\partial_w.$$
--   Subscripts $i$ below denote the rational expressions obtained by these
--   rules, with total real-field division. On the regular positive-wall
--   region they are the corresponding coordinate partial derivatives. Set
--   $$N=h(v-w)+(v+w-u)Q,\quad R=h(v-w)+(v+w-u)(Q-s),$$
--   $$A=-N/s,\quad B=k/s,\quad G=uA+(vw)^2B,\quad
--   \alpha=b/s,\quad \beta=-1-2(1+\kappa)/s.$$
--   The coefficient matrix $C$ has rows $(G_i)_i$, $(\alpha_i)_i$ and
--   $(\beta_i)_i$.
--
--   The wall rates are $\alpha=b/s$ and $\beta=-1-2(1+\kappa)/s$.
--   Their derivative arrays are the expanded expressions
--   $(L_i\alpha)_i$ and $(L_i\beta)_i$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionAmplitudeDifferential.lean

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeighted
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace BianchiIX

def connectionStrongClockRate (m u v w : ℝ) : ℝ :=
  connectionStrongRate m u v w / connectionSpeed m u v w

def connectionWeakClockRate (m u v w : ℝ) : ℝ :=
  -1 - 2 * (1 + coupling u v w) / connectionSpeed m u v w









/-- The four columns are J, log U, log V, log W, with J fixed in the last three. -/
def connectionStrongClockPartials (m u v w : ℝ) : Fin 4 → ℝ :=
  let a := connectionStrongClockRate m u v w
  let D := connectionSpeed m u v w
  ![-(m + a) / (D * matchingPhaseSlope m v w),
    (u ^ 2 + a * u * (v + w - 2 * u)) / D,
    (-(m + a) * matchingPhaseVVariation m v w - v * (v - w) + a * u * v) / D,
    (-(m + a) * matchingPhaseWVariation m v w + w * (v - w) + a * u * w) / D]

def connectionWeakClockPartials (m u v w : ℝ) : Fin 4 → ℝ :=
  let D := connectionSpeed m u v w
  ![2 * (1 + coupling u v w) / (D ^ 2 * matchingPhaseSlope m v w),
    -(2 * m * u * (v + w - 2 * u)) / D ^ 2,
    (2 * (1 + coupling u v w) * matchingPhaseVVariation m v w - 2 * m * u * v) / D ^ 2,
    (2 * (1 + coupling u v w) * matchingPhaseWVariation m v w - 2 * m * u * w) / D ^ 2]



end BianchiIX


