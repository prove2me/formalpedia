-- Prove2me | Definitions.Def_AvgPHETH_IsSampler
-- name    : AvgPHETH_IsSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:03.800644+00:00
-- url     : https://prove2.me/theorems/e8fb2d6f-6591-4844-8bdb-e115da8589e8
-- title:
--   A sampler of a family of distributions
-- statement:
--   A machine $M$ with oracle $O$, a coin-length polynomial $r$ and an exponent $e$ form a **sampler** of the family $D=\{D_n\}$ if for every $n$: on input $(1^n,\mathrm{coins})$ with $|\mathrm{coins}|=r(n)$ the machine halts within $(n+r(n))^e+e$ steps, and on uniformly random coins its output is distributed exactly according to $D_n$.
--
--   One machine serves all $n$. The support of $D_n$ consists of strings of length polynomial in $n$ automatically, because the output fits in the running time.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.1, p.14 (PDF 16)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_outAt
import Definitions.Def_AvgPHETH_unary
open KarpLiptonOM

namespace AvgPHETH

/-- The machine `M` with oracle `O`, coin length `r` and time exponent `e` is a **sampler** of the
family `D`: on input `(1^n, coins)` with `|coins| = r(n)` it halts within `(n + r(n))^e + e` steps,
and on uniform coins its output is distributed according to `D n`, for every `n`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.1, p.14 (PDF 16): "there is a randomized polynomial-time algorithm `S`, referred to as a
sampler, such that for all `n ∈ ℕ` the output of `S(1^n)` is distributed according to `D_n`").

**Formalization Note** One machine serves every `n`. The support is on strings of length at most
polynomial in `n` automatically, since the output fits in the running time. -/
def IsSampler (M : OracleTM) (r : Polynomial ℕ) (e : ℕ) (O : Set (List Bool))
    (D : ℕ → PMF (List Bool)) : Prop :=
  ∀ n : ℕ,
    (∀ coins : Fin (r.eval n) → Bool,
      M.HaltsWithin O ((n + r.eval n) ^ e + e) (tupleEnc [unary n, List.ofFn coins])) ∧
    D n = (PMF.uniformOfFintype (Fin (r.eval n) → Bool)).map (fun coins =>
      outAt M O ((n + r.eval n) ^ e + e) (tupleEnc [unary n, List.ofFn coins]))

end AvgPHETH


