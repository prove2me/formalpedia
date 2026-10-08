-- Prove2me | Definitions.Def_Helfgott_MajorArcArithmeticSharp
-- name    : Helfgott_MajorArcArithmeticSharp
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-06T02:32:30.693367+00:00
-- url     : https://prove2.me/theorems/4b8d3405-c605-45b4-816f-519906c2cffb
-- title:
--   Sharper complete arithmetic moments of the actual Goldbach major arcs
-- statement:
--   Let $D$ consist of the odd integers $1\le q\le150000$ and even integers $1\le q\le300000$, the actual major-arc denominators of the three-prime Goldbach challenge. Set $R(q)=600000/q$ for odd $q$ and $R(q)=1200000/q$ for even $q$. Then
--   $$\sum_{q\in D}\frac1{\varphi(q)}\le64,\qquad \sum_{q\in D}2R(q)\le50000000,\qquad \sum_{q\in D}\varphi(q)2R(q)\le720000000000.$$
--   These complete finite arithmetic bounds sharpen the constants in the integrated prime-model error, reducing the inverse-totient budget from 1750 to 64 and the width budget from 4200000000 to 50000000. They allow a larger intermediate smoothing error while preserving the original major-arc target.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897. Original dyadic refinement of the complete inverse-totient-square remainder estimate. Written by Codex.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Intervals
open scoped BigOperators

namespace Helfgott
def MajorArcArithmeticSharp : Prop :=
  let D := (Finset.Icc 1 150000).filter (fun q => Odd q) ∪
    (Finset.Icc 1 300000).filter (fun q => Even q)
  let R : ℕ → ℝ := fun q => if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ)
  (∑ q ∈ D,1/(Nat.totient q : ℝ))≤64 ∧
  (∑ q ∈ D,2*R q)≤50000000 ∧
  (∑ q ∈ D,(Nat.totient q : ℝ)*(2*R q))≤720000000000
end Helfgott


