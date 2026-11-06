-- Prove2me | Definitions.Def_BianchiIX_Analysis_ConnectionCoefficientMatrix
-- name    : BianchiIX_Analysis_ConnectionCoefficientMatrix
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T09:27:47.374114+00:00
-- url     : https://prove2.me/theorems/54ac1230-a9d2-49bb-8a1b-8b68fc8e98ee
-- title:
--   The three rate functions and their four coordinate columns
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
--   The rate vector is $(G,\alpha,\beta)$ and its matrix of coordinate
--   derivatives is $C$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionCoefficientMatrix.lean

import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseKernel
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseLinearization
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

def connectionLogRates (m u v w : ℝ) : Fin 3 → ℝ :=
  ![connectionPhaseG m u v w, connectionStrongClockRate m u v w, connectionWeakClockRate m u v w]

/-- Rows are G, a, b; columns are J, log U, log V, log W. -/
def connectionLogCoefficientMatrix (m u v w : ℝ) : Fin 3 → Fin 4 → ℝ :=
  ![connectionPhaseGPartials m u v w, connectionStrongClockPartials m u v w, connectionWeakClockPartials m u v w]











end BianchiIX


