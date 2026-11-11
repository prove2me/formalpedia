-- Prove2me | Definitions.Def_TwoItemMenu1393_Main_Certificate
-- name    : TwoItemMenu1393_Main_Certificate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:38.202998+00:00
-- url     : https://prove2.me/theorems/f37d894c-5876-44fa-aa17-ac66e0f8b19c
-- title:
--   Finite weighted atomic measures
-- statement:
--   For a finite set $V\subset\mathbb R^2$, real weights $w_v$ and a real normalizing quantity $S$, define the raw measure
--   $$F=\sum_{v\in V}\max(w_v/S,0)\,\delta_v.$$
--   Here $\delta_v$ is the unit point mass at $v$. Lemma D.1 uses this construction only with $S>0$ and nonnegative weights, where truncation changes nothing. Normalization, support on the square and optimality are conclusions of that lemma, not fields of this definition. This finite measure interface is independent of the lattice construction and can be reused for other finite incentive certificates.
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma D.1, pp. 23–24, equations (14)–(15). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf

import Definitions.Def_TwoItemMenu1393_Main_Model
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace TwoItemMenu1393.Main

/-! Chan–Guo–Thach, submission #1393 (October 2026), Lemma D.1,
pp. 23–24, equations (14)–(15). This module defines only the finite weighted
measure, independently of any balance, positivity or optimality assertion. -/
def finiteLaw (V : Finset Vec) (w : Vec → ℝ) (S : ℝ) : Measure Vec :=
  ∑ v ∈ V, ENNReal.ofReal (w v / S) • Measure.dirac v

end TwoItemMenu1393.Main


