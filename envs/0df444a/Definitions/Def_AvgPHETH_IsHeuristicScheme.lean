-- Prove2me | Definitions.Def_AvgPHETH_IsHeuristicScheme
-- name    : AvgPHETH_IsHeuristicScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:21.056928+00:00
-- url     : https://prove2.me/theorems/75711013-dc82-448e-984f-ee7453c91ccb
-- title:
--   Errorless heuristic scheme
-- statement:
--   A machine $A$ with oracle $O$ and exponent $e$ is an **errorless heuristic scheme** for $(L,D)$ if for every $n\in\mathbb N$ and $\delta\in(0,1)$, with $m=\lceil 1/\delta\rceil$:
--
--   1. for every $x$ in the support of $D_n$, the machine on $(x,1^n,1^m)$ halts within $(n+m+2)^e+e$ steps and outputs either $L(x)$ or $\bot$;
--   2. $\Pr_{x\sim D_n}[A(x,1^n,1^m)=\bot]\le\delta$.
--
--   **Formalization Note** The output strings "1" and "0" are the two bits, and every other output string is $\bot$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 4.1, p.14 (PDF 16)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_outAt
import Definitions.Def_AvgPHETH_unary
open KarpLiptonOM

namespace AvgPHETH

/-- `M` with time exponent `e` is an **errorless heuristic scheme** for `(L, D)` with oracle `O`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 4.1, p.14 (PDF 16)): for every `n` and `δ ∈ (0,1)`, with `m = ⌈1/δ⌉`, on input
`(x, 1^n, 1^m)` for `x` in the support of `D_n` the machine halts within `(n + m + 2)^e + e` steps,
it never outputs a wrong bit, and it outputs `⊥` with probability at most `δ` over `x ∼ D_n`.

**Formalization Note** The outputs `[true]`, `[false]` are the bits; every other output string is `⊥`.
The correctness clause holds on the whole support, not only with high probability. -/
def IsHeuristicScheme (O L : Set (List Bool)) (D : ℕ → PMF (List Bool)) (M : OracleTM) (e : ℕ) :
    Prop :=
  ∀ (n : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
    let m := ⌈1 / δ⌉₊
    let T := (n + m + 2) ^ e + e
    let w := fun x : List Bool => tupleEnc [x, unary n, unary m]
    (∀ x ∈ (D n).support, M.HaltsWithin O T (w x) ∧
      (outAt M O T (w x) = [true] → x ∈ L) ∧ (outAt M O T (w x) = [false] → x ∉ L)) ∧
    (D n).toOuterMeasure {x | outAt M O T (w x) ≠ [true] ∧ outAt M O T (w x) ≠ [false]} ≤
      ENNReal.ofReal δ

end AvgPHETH


