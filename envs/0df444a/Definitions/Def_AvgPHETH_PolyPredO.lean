-- Prove2me | Definitions.Def_AvgPHETH_PolyPredO
-- name    : AvgPHETH_PolyPredO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:08.259341+00:00
-- url     : https://prove2.me/theorems/750b9658-7327-4bab-ac4f-b008a46b9904
-- title:
--   Polynomial-time predicates with oracle $O$
-- statement:
--   A $k$-ary predicate $V$ on binary strings is polynomial-time with oracle $O$ if a single machine with oracle $O$ decides $V(x_1,\dots,x_k)$ on input $x_1\#\cdots\#x_k$, within a time polynomial in the length of that input.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4); §4.2, p.15 (PDF 17)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_acceptsAt
open KarpLiptonOM

namespace AvgPHETH

/-- A `k`-ary predicate on strings decidable in polynomial time with oracle `O`: one machine decides
`V l` on input `tupleEnc l`, for every tuple `l` of `k` strings, in time polynomial in the length of
that input (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4): "some polynomial-time verifier `V`"; §4.2, p.15 (PDF 17)). -/
def PolyPredO (O : Set (List Bool)) (k : ℕ) (V : List (List Bool) → Prop) : Prop :=
  ∃ (M : OracleTM) (e : ℕ), ∀ l : List (List Bool), l.length = k →
    M.HaltsWithin O ((tupleEnc l).length ^ e + e) (tupleEnc l) ∧
      (V l ↔ acceptsAt M O ((tupleEnc l).length ^ e + e) (tupleEnc l))

end AvgPHETH


