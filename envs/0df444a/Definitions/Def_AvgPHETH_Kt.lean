-- Prove2me | Definitions.Def_AvgPHETH_Kt
-- name    : AvgPHETH_Kt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:52.236339+00:00
-- url     : https://prove2.me/theorems/539922c4-d3bb-4dd6-b185-5c33f77ceedf
-- title:
--   Time-bounded Kolmogorov complexity $K^{t,O}(z\mid y)$
-- statement:
--   The $t$-time-bounded Kolmogorov complexity $K^{t,O}(z\mid y)$ of $z$ given $y$ is the length of a shortest program $d$ such that $U^O(d,y)$ outputs $z$ within $t$ steps. It is $+\infty$ when there is no such program. The conditional is omitted when $y$ is the empty string.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, pp.17–18 (PDF 19–20)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_outAt
open KarpLiptonOM

namespace AvgPHETH

/-- The `t`-time-bounded Kolmogorov complexity `K^{t,O}(z | y)`: the length of a shortest program `d`
such that `U^O(d, y)` outputs `z` within `t` steps (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, pp.17–18 (PDF 19–20)).

**Formalization Note** The value is in `ℕ∞`, and it is `⊤` when no program does it; a value `0` on the
empty set of programs would make every upper bound on `K^t` free. The empty `y` is the omitted condition. -/
noncomputable def Kt (U : OracleTM) (O : Set (List Bool)) (t : ℕ) (z y : List Bool) : ℕ∞ :=
  ⨅ (d : List Bool) (_ : U.HaltsWithin O t (tupleEnc [d, y]) ∧ outAt U O t (tupleEnc [d, y]) = z),
    (d.length : ℕ∞)

end AvgPHETH


