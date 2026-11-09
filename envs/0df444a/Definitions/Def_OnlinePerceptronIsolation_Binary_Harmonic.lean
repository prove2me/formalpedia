-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Harmonic
-- name    : OnlinePerceptronIsolation_Binary_Harmonic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:28.304996+00:00
-- url     : https://prove2.me/theorems/8f3783c9-ab07-45de-99a6-958e35510742
-- title:
--   The exact harmonic window
-- statement:
--   For an integer lower endpoint $a$ and real radius $h$, set
--   $$H(a,h)=\sum_{k=a}^{\lfloor h/2\rfloor}\frac1k.$$
--   The sum uses inclusive endpoints. Lemma 4.1 guarantees eventually $1\le a\le\lfloor h/2\rfloor$, so its bound uses a positive finite harmonic sum. Outside that domain the finite sum is still total, with an empty interval contributing zero. This quantity retains the exact bound $H^{-1}$ rather than replacing it by an unspecified logarithmic rate.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma 4.1, Eq. (4.3), printed p.12, PDF p.14; Eq. (4.16), printed p.14, PDF p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- The exact finite harmonic sum H in (4.3). The asymptotic hypotheses ensure
1 ≤ a ≤ floor(h/2), so neither the empty interval nor division by zero is used. -/
noncomputable def harmonicWindow (a : ℕ) (h : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc a ⌊h / 2⌋₊, (1 : ℝ) / k

end OnlinePerceptronIsolation.Binary


