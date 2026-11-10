-- Prove2me | Definitions.Def_NearOptOWF_OracleDist_run
-- name    : NearOptOWF_OracleDist_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:05.195996+00:00
-- url     : https://prove2.me/theorems/8b3b2831-0603-4ce6-83cf-4fed282d30da
-- title:
--   Run of an oracle distinguisher
-- statement:
--   The output bit of an oracle distinguisher run with an oracle on $n$-bit queries. Each query circuit in turn reads the answers so far, its output is cut or padded with zeros to $n$ bits and asked to the oracle, and the final circuit reads all answers.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19); its proof, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_NearOptOWF_OracleDist

namespace NearOptOWF

open LaconicBarrier

/-- The output bit of the oracle distinguisher `D` with oracle `O` on `n`-bit queries (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…),
Lemma 4.10, p.17 (PDF p.19); its proof's test, p.18 (PDF p.20)): each query circuit, in order, reads
the tuple of the answers so far (through `padIn`), its output is cut or padded with zeros to `n` bits
and asked to `O`; the final circuit reads all answers and its first output bit is the result. -/
def OracleDist.run (D : OracleDist) (n : ℕ) (O : List Bool → List Bool) : Bool :=
  let ans := D.queries.foldl (fun ans Q => ans ++
    [O ((Q.eval (padIn D.arity (QAdvFew.PoQOracle.tup ans)) ++ List.replicate n false).take n)]) []
  (D.final.eval (padIn D.arity (QAdvFew.PoQOracle.tup ans))).headD false

end NearOptOWF


