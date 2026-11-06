-- Prove2me | Definitions.Def_BianchiIX_Analysis_ConnectionTransverseCoefficients
-- name    : BianchiIX_Analysis_ConnectionTransverseCoefficients
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T09:16:05.843404+00:00
-- url     : https://prove2.me/theorems/08db65f4-b4b8-4a11-9a33-4e69286b3c45
-- title:
--   Weighted transverse matrix and its decreasing budget
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
--   Define
--   $$M_\mu=\begin{pmatrix}\alpha_1&\alpha_2/\mu^2\\
--   \mu^2\beta_1&\beta_2\end{pmatrix},\quad
--   r_\mu=64(2\mu u+v^2/\mu^3+vw/\mu^3),$$
--   $$B_\mu(u,v,w)=64(4u+v^2/(2\mu^3)+vw/(2\mu^2)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionTransverseCoefficients.lean

import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
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
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FunProp

noncomputable section

namespace BianchiIX

/-- The homogeneous equation for (X, mu^2 Y). -/
def connectionTransverseMatrix (μ m u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![connectionStrongClockPartials m u v w 1, connectionStrongClockPartials m u v w 2 / μ ^ 2;
     μ ^ 2 * connectionWeakClockPartials m u v w 1, connectionWeakClockPartials m u v w 2]

def connectionTransverseRate (μ u v w : ℝ) : ℝ :=
  64 * (2 * μ * u + v ^ 2 / μ ^ 3 + v * w / μ ^ 3)

/-- A decreasing state function pays for the entire transverse growth. -/
def connectionTransverseBudget (μ u v w : ℝ) : ℝ :=
  64 * (4 * u + v ^ 2 / (2 * μ ^ 3) + v * w / (2 * μ ^ 2))











end BianchiIX


