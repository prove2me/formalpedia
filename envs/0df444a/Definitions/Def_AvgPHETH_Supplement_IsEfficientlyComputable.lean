-- Prove2me | Definitions.Def_AvgPHETH_Supplement_IsEfficientlyComputable
-- name    : AvgPHETH_Supplement_IsEfficientlyComputable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:26:35.256851+00:00
-- url     : https://prove2.me/theorems/f3f84189-1386-4372-8481-dde62a13e61e
-- title:
--   $\varepsilon$ is efficiently computable (through $g(n)=\max\{16,\lceil\log(1/\varepsilon(n))\rceil\}$)
-- statement:
--   A function $\varepsilon:\mathbb N\to\mathbb R$ is **efficiently computable** if the number
--
--   $$g(n)=\max\Big\{16,\Big\lceil\log_2\frac1{\varepsilon(n)}\Big\rceil\Big\}$$
--
--   can be computed in binary from $1^n$ by a single deterministic machine in time $n^e+e$ for a constant $e$.
--
--   This is the hypothesis of Theorem 1.5. The oracle construction of Section 8 uses $\varepsilon$ only through $g(n)$, which must be computable in polynomial time so that the hard languages lie in $\Pi_k^{p,O}$.
--
--   **Formalization Note** The paper does not define "efficiently computable". Every standard reading (for instance, a rational $\varepsilon(n)$ computable in time $\mathrm{poly}(n)$) implies this one, so a theorem under this hypothesis is at least as strong. The machine runs with the empty oracle; its output is read from the work-tape head as `Nat.bits`, as in the published `AvgPHETH.IsTimeConstructible`.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.5, p.4 (PDF 6); §8.1 'Parameters', pp.38–39 (PDF 40–41)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_outAt
import Definitions.Def_AvgPHETH_unary

namespace AvgPHETH.Supplement

open KarpLiptonOM AvgPHETH

/-- "`ε` is efficiently computable" (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.5, p.4 (PDF 6); §8.1, pp.38–39 (PDF 40–41)),
in the form the construction uses: the parameter `g(n) = max{16, ⌈log(1/ε(n))⌉}` of p.39 is
computed from `1^n`, in binary, by one machine (with the empty oracle) in time polynomial in `n`.

**Formalization Note** The paper does not define "efficiently computable" and uses `ε` only through
`g(n)`. Every standard reading (a rational `ε(n)` computable in time `poly(n)`) implies this one, so a
theorem assuming it is at least as strong. `log` is `log₂`; the output is `Nat.bits` read from the
work-tape head, as in the published `AvgPHETH.IsTimeConstructible`. The positivity of `ε(n)`, which
`log(1/ε(n))` presupposes, is a separate hypothesis of the theorems. -/
def IsEfficientlyComputable (ε : ℕ → ℝ) : Prop :=
  ∃ (M : OracleTM) (e : ℕ), ∀ n : ℕ,
    M.HaltsWithin ∅ (n ^ e + e) (tupleEnc [unary n]) ∧
      outAt M ∅ (n ^ e + e) (tupleEnc [unary n]) =
        Nat.bits (max 16 ⌈Real.logb 2 (1 / ε n)⌉₊)

end AvgPHETH.Supplement


