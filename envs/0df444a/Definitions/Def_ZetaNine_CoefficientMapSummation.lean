-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapSummation
-- name    : ZetaNine_CoefficientMapSummation
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-03T20:23:00.597558+00:00
-- url     : https://prove2.me/theorems/31bff972-299f-4bf7-ba2e-eec29a733fd4
-- title:
--   Actual positive weighted rational sequence and odd-zeta linear sum
-- statement:
--   Define $z_s=\Re(\zeta(s))$ using the actual Mathlib Riemann zeta function. For the genuine weighted rational function $f_{n,W}(t)=R_n(t)W(t(t+n))$, define the actual positive sequence $a_k=f_{n,W}(k+1)$, as a real cast of its rational value. Define $L_n(W)=B_n(W)+\rho_{n,3}(W)z_3+\rho_{n,5}(W)z_5+\rho_{n,7}(W)z_7+\rho_{n,9}(W)z_9$, where $B$ and $\rho$ are the genuine finite harmonic constant and actual local coefficient totals from the finite-sum definition chain. These are three actual definitions; no convergence, summability, coefficient cancellation or zeta-series identity is assumed by defining them.
-- source:
--   Zeta(9) actual p9,q1,m=n,d0 infinite summation: missions/zeta9/research/coefficient-map-summation-2026-10-04.md. Frozen actual source SHA256 c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d. Actual numerator/pole products, shifted unit-denominator coefficient array, finite harmonic B/rho and actual strong-domain cancellation prove absolute convergence and the actual infinite L.

import Definitions.Def_ZetaNine_CoefficientMapReflection
import Definitions.Def_ZetaNine_CoefficientMapFiniteSum
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapSummation

open scoped BigOperators Topology
open Finset Polynomial Filter
open HarmonicStability CoefficientMapInjectivity CoefficientMapReflection

def zetaReal (s : ℕ) : ℝ := (riemannZeta (s : ℂ)).re

def exactL (n : ℕ) (W : ℚ[X]) : ℝ :=
  (CoefficientMapFiniteSum.constantTerm n W : ℝ) +
    ((CoefficientMapFiniteSum.rho n 3 W : ℝ) * zetaReal 3 +
     (CoefficientMapFiniteSum.rho n 5 W : ℝ) * zetaReal 5 +
     (CoefficientMapFiniteSum.rho n 7 W : ℝ) * zetaReal 7 +
     (CoefficientMapFiniteSum.rho n 9 W : ℝ) * zetaReal 9)

def actualSeries (n : ℕ) (W : ℚ[X]) (t : ℕ) : ℝ :=
  (CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ)

end ZetaNine.CoefficientMapSummation


