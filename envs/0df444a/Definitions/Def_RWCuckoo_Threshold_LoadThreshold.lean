-- Prove2me | Definitions.Def_RWCuckoo_Threshold_LoadThreshold
-- name    : RWCuckoo_Threshold_LoadThreshold
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:30:32.180307+00:00
-- url     : https://prove2.me/theorems/df23a7f2-ff65-480a-92c9-b01930d95059
-- title:
--   The load threshold of d-ary cuckoo hashing: ξ_d, c∗_d, ε∗_d = 1 − c∗_d, ε_Δ, the two s, and m = ⌊(1 − ε)n⌋
-- statement:
--   For an integer $d$ let
--   $$f_d(\xi)=(d-\xi)e^{\xi}-d-(d-1)\xi .$$
--   Following Fountoulakis and Panagiotou (as quoted on p. 41), $\xi_d$ is the positive root of $f_d(\xi)=0$, and the **critical load** and the **threshold** are
--   $$c^*_d=\frac{\xi_d}{d\,(1-e^{-\xi_d})^{d-1}},\qquad \varepsilon^*_d=1-c^*_d .$$
--   The quantity $1-\varepsilon^*_d$ is the load threshold of $d$-ary cuckoo hashing: below it all keys can be stored with high probability, above it they cannot (p. 4). For $\varepsilon>\varepsilon^*_d$ the paper writes $\varepsilon_\Delta=\varepsilon-\varepsilon^*_d$.
--
--   Two different quantities are both called $s$ in the paper and are kept apart here: $s_{\mathrm{goal}}=\ln(\varepsilon/\varepsilon^*_d)$ is the $s$ of Theorem 1.1, and $s_{\mathrm{fresh}}=d-\log(1/\varepsilon)$, roughly the number of fresh probes per key, is the $s$ of Section 6. Finally $m=\lfloor(1-\varepsilon)n\rfloor$ is the number of keys already in a table of $n$ cells; the key being inserted is the $(m+1)$-th.
--
--   Logarithms are natural.
--
--   **Formalization Note** For $d\ge3$, $f_d(0)=f_d'(0)=0$, $f_d''(0)=d-2>0$ and $f_d\to-\infty$, with a single positive root; $\xi_d$ is defined as $\sup\{\xi>0: f_d(\xi)\ge0\}$, which is that root, so no existence proof is needed inside the definition (for $d\le2$ the value is a junk value never used). $m$ is `Nat.floor`.
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 2 (Theorem 1.1), p. 4 (§2), p. 21 (§6), p. 41 (App. A.4, Thresholds)

import Mathlib

namespace RWCuckoo.Threshold

/-- The function `f_d(ξ) = (d − ξ) e^ξ − d − (d − 1) ξ` whose positive root is `ξ_d`
(Hu–Kuszmaul–Liang, App. A.4 "Thresholds", p. 41, quoting [FP12, Theorem 1.1]). -/
noncomputable def thresholdEquation (d : ℕ) (ξ : ℝ) : ℝ :=
  ((d : ℝ) - ξ) * Real.exp ξ - d - ((d : ℝ) - 1) * ξ

/-- `ξ_d`, the positive root of `(d − ξ) e^ξ − d − (d − 1) ξ = 0` (p. 41). For `d ≥ 3` the
equation has exactly one positive root and the left side is positive on `(0, ξ_d)` and negative
after it, so `ξ_d` is the supremum of the positive `ξ` at which the left side is `≥ 0`. -/
noncomputable def xi (d : ℕ) : ℝ :=
  sSup {ξ : ℝ | 0 < ξ ∧ 0 ≤ thresholdEquation d ξ}

/-- The critical load `c∗_d = ξ_d / (d (1 − e^{−ξ_d})^{d−1})` (p. 41, [FP12, Theorem 1.1]). -/
noncomputable def cStar (d : ℕ) : ℝ :=
  xi d / ((d : ℝ) * (1 - Real.exp (-xi d)) ^ (d - 1))

/-- The threshold `ε∗_d = 1 − c∗_d` (p. 36: "Write `c∗_d = 1 − ε∗_d` for the critical load");
`1 − ε∗_d` is the load threshold of `d`-ary cuckoo hashing (p. 4). -/
noncomputable def epsStar (d : ℕ) : ℝ :=
  1 - cStar d

/-- `ε_Δ = ε − ε∗_d` (pp. 4–5). -/
noncomputable def epsDelta (d : ℕ) (ε : ℝ) : ℝ :=
  ε - epsStar d

/-- The `s` of Theorem 1.1: `s = ln(ε / ε∗_d)` (p. 2). -/
noncomputable def sGoal (d : ℕ) (ε : ℝ) : ℝ :=
  Real.log (ε / epsStar d)

/-- The `s` of Section 6: `s = d − log(1/ε)`, roughly the number of fresh probes per key
(p. 21). Not the `s` of Theorem 1.1. -/
noncomputable def sFresh (d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) - Real.log (1 / ε)

/-- The number of keys already in the table, `m = ⌊(1 − ε) n⌋` (p. 4); the new key is the
`(m + 1)`-th. -/
noncomputable def numKeys (n : ℕ) (ε : ℝ) : ℕ :=
  ⌊(1 - ε) * (n : ℝ)⌋₊

end RWCuckoo.Threshold


