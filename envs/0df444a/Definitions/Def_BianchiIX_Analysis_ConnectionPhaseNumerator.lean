-- Prove2me | Definitions.Def_BianchiIX_Analysis_ConnectionPhaseNumerator
-- name    : BianchiIX_Analysis_ConnectionPhaseNumerator
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T09:20:26.382907+00:00
-- url     : https://prove2.me/theorems/0b061eff-ac71-49b1-9d86-3b3088ee0f02
-- title:
--   The interaction numerator and its coordinate derivatives
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
--   Define $N=h(v-w)+(v+w-u)Q$, $N_i=L_iN$ and
--   $A_i=-N_i/s-As_i/s$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionPhaseNumerator.lean

import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseKernel
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWallDifferential
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

def connectionPhaseNumerator (m u v w : ℝ) : ℝ :=
  matchingPhaseSlope m v w * (v - w) + (v + w - u) * matchingPhaseWeight m v w

def connectionPhaseNumeratorPartials (m u v w : ℝ) : Fin 4 → ℝ :=
  ![matchingPhaseSlopePartials m v w 0 * (v - w) + (v + w - u) * matchingPhaseWeightPartials m v w 0,
    -u * matchingPhaseWeight m v w,
    matchingPhaseSlopePartials m v w 2 * (v - w) + matchingPhaseSlope m v w * v +
      v * matchingPhaseWeight m v w + (v + w - u) * matchingPhaseWeightPartials m v w 2,
    matchingPhaseSlopePartials m v w 3 * (v - w) - matchingPhaseSlope m v w * w +
      w * matchingPhaseWeight m v w + (v + w - u) * matchingPhaseWeightPartials m v w 3]

def connectionPhaseAPartials (m u v w : ℝ) (i : Fin 4) : ℝ :=
  -connectionPhaseNumeratorPartials m u v w i / connectionSpeed m u v w -
    connectionPhaseA m u v w * connectionSpeedPartials m u v w i / connectionSpeed m u v w







end BianchiIX


