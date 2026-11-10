-- Prove2me | Definitions.Def_NearOptOWF_OracleDist_size
-- name    : NearOptOWF_OracleDist_size
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:40.337902+00:00
-- url     : https://prove2.me/theorems/c10883b5-fc73-4837-be83-eaa1629ffc24
-- title:
--   Size of an oracle distinguisher
-- statement:
--   The size of an oracle distinguisher: its number of inputs, its number of queries, and the sizes of all its circuits.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_NearOptOWF_OracleDist

namespace NearOptOWF

open LaconicBarrier

/-- The size of an oracle distinguisher: its arity, its number of queries and the sizes of all its
circuits (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19): polynomial-size distinguishers). -/
def OracleDist.size (D : OracleDist) : ℕ :=
  D.arity + D.queries.length + (D.queries.map (fun Q => Q.size)).sum + D.final.size

end NearOptOWF


