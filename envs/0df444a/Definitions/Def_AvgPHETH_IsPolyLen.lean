-- Prove2me | Definitions.Def_AvgPHETH_IsPolyLen
-- name    : AvgPHETH_IsPolyLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:06.8972+00:00
-- url     : https://prove2.me/theorems/a4b06aa4-f0a6-4dae-a4f3-f7203b6b1739
-- title:
--   Polynomial-time computable length function
-- statement:
--   A function $\ell:\mathbb N\to\mathbb N$ is a polynomial-time computable length function if a single machine computes $\ell(n)$ in binary from $1^n$ in time polynomial in $n$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 4.9, p.19 (PDF 21)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_outAt
import Definitions.Def_AvgPHETH_unary
open KarpLiptonOM

namespace AvgPHETH

/-- `ℓ` is a polynomial-time computable integer-valued length function: one machine on `1^n` outputs
`ℓ(n)` in binary in time polynomial in `n` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 4.9, p.19 (PDF 21)).

**Formalization Note** The oracle `∅` makes this an unrelativized computation. Binary is `Nat.bits`,
least significant bit first. -/
def IsPolyLen (ℓ : ℕ → ℕ) : Prop :=
  ∃ (M : OracleTM) (e : ℕ), ∀ n : ℕ,
    M.HaltsWithin ∅ (n ^ e + e) (tupleEnc [unary n]) ∧
      outAt M ∅ (n ^ e + e) (tupleEnc [unary n]) = Nat.bits (ℓ n)

end AvgPHETH


