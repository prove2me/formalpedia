-- Prove2me | Definitions.Def_AvgPHETH_IsEfficientUniversal
-- name    : AvgPHETH_IsEfficientUniversal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:43.344856+00:00
-- url     : https://prove2.me/theorems/666ac79c-1903-4336-a331-7bf17d97b020
-- title:
--   Efficient universal oracle Turing machine
-- statement:
--   An oracle Turing machine $U$ is **efficient universal** if for every oracle machine $M$ there are a program prefix $\pi$ and an exponent $e$, independent of the oracle, such that for all $O,d,y,s$: if $M^O(d,y)$ halts within $s$ steps with output $w$, then $U^O(\pi d,y)$ halts with output $w$ within $(s+|d|+|y|+2)^e+e$ steps.
--
--   **Formalization Note** The paper prints no overhead bound. This is polynomial overhead, the weakest usual meaning, and every statement about $K^t$ in the mission is proved for all such $U$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.17 (PDF 19)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_outAt
open KarpLiptonOM

namespace AvgPHETH

/-- `U` is an **efficient universal oracle Turing machine** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.17 (PDF 19): "Fix an
efficient universal oracle Turing machine `U`"): for every machine `M` there are a program prefix `π`
and an exponent `e`, not depending on the oracle, such that whenever `M^O(d, y)` halts within `s` steps
with output `w`, also `U^O(π d, y)` halts with output `w` within `(s + |d| + |y| + 2)^e + e` steps.

**Formalization Note** "Efficient" is printed without a bound; this is polynomial overhead, the weakest
usual meaning, and every statement about `K^t` holds for all such `U`. -/
def IsEfficientUniversal (U : OracleTM) : Prop :=
  ∀ M : OracleTM, ∃ (π : List Bool) (e : ℕ), ∀ (O : Set (List Bool)) (d y : List Bool) (s : ℕ)
    (w : List Bool), M.HaltsWithin O s (tupleEnc [d, y]) → outAt M O s (tupleEnc [d, y]) = w →
    U.HaltsWithin O ((s + d.length + y.length + 2) ^ e + e) (tupleEnc [π ++ d, y]) ∧
      outAt U O ((s + d.length + y.length + 2) ^ e + e) (tupleEnc [π ++ d, y]) = w

end AvgPHETH


