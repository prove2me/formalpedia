-- Prove2me | Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeightDifferential
-- name    : BianchiIX_Analysis_MatchingPhaseWeightDifferential
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T09:09:18.632203+00:00
-- url     : https://prove2.me/theorems/d19e4a57-b282-43b0-af4a-d487100274f6
-- title:
--   Ordinary phase derivatives of the slope, weight and remainder
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
--   Define $h_m=v^2/n(m+1,v)^3+w^2/n(m-1,w)^3$,
--   $Q_m=h-v^2/n(m+1,v)^3+w^2/n(m-1,w)^3$, and
--   $R_m=h_m(v-w)+(v+w-u)(Q_m-1)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/MatchingPhaseWeightDifferential.lean

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
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

open Filter
open scoped Topology



def matchingPhaseSlopeDm (m v w : ℝ) : ℝ :=
  v ^ 2 / phaseNorm (m + 1) v ^ 3 + w ^ 2 / phaseNorm (m - 1) w ^ 3

def matchingPhaseWeightDm (m v w : ℝ) : ℝ :=
  matchingPhaseSlope m v w - v ^ 2 / phaseNorm (m + 1) v ^ 3 + w ^ 2 / phaseNorm (m - 1) w ^ 3





def connectionPhaseRemainderDm (m u v w : ℝ) : ℝ :=
  matchingPhaseSlopeDm m v w * (v - w) + (v + w - u) * (matchingPhaseWeightDm m v w - 1)





end BianchiIX


