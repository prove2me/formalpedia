-- Prove2me | Definitions.Def_AvgPHETH_IsTimeConstructible
-- name    : AvgPHETH_IsTimeConstructible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:41.279572+00:00
-- url     : https://prove2.me/theorems/961e20c8-60e8-4488-ba5a-3a99e74b9549
-- title:
--   Time-constructible bound $t(n)\ge n$
-- statement:
--   A bound with $t(n)\ge n$ for all $n$ is time-constructible if one machine computes $t(n)$ in binary from $1^n$ in time $O(t(n))$. This is the standard notion, which the paper uses without defining it.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 6.5, p.29 (PDF 31); §4.2, p.15 (PDF 17)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_outAt
import Definitions.Def_AvgPHETH_unary
open KarpLiptonOM

namespace AvgPHETH

/-- `t(n) ≥ n` is time-constructible: one machine on `1^n` outputs `t(n)` in binary in time `O(t(n))`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 6.5, p.29 (PDF 31); §4.2, p.15 (PDF 17)).

**Formalization Note** The page uses the standard notion without defining it. -/
def IsTimeConstructible (t : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ t n) ∧ ∃ (M : OracleTM) (C : ℕ), ∀ n,
    M.HaltsWithin ∅ (C * t n + C) (tupleEnc [unary n]) ∧
      outAt M ∅ (C * t n + C) (tupleEnc [unary n]) = Nat.bits (t n)

end AvgPHETH


