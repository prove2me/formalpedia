-- Prove2me | Definitions.Def_CharonChurn_Main_Encoding
-- name    : CharonChurn_Main_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:55:50.414194+00:00
-- url     : https://prove2.me/theorems/ab8ad793-ff61-45a4-998b-0a5cf637610c
-- title:
--   Binary encoding of the decision input and the Boolean decision
-- statement:
--   Every natural number is written in a self-delimiting binary code (each binary digit $b$ as the pair $1,b$, then a terminating $0$), so identities, rounds, session and parameters cost their bit length; no $O(\log n)$ identifier bound is assumed. Lists are length-prefixed. A record is coded as its payload fields (type, version, session, round, signer, neighbour list) followed by its signature bits. The decision input is coded as $n,D,t$, the session, $s$, $e$, the eligibility bit and the retained records listed in increasing canonical key order. The Boolean decision is true exactly when the verdict is Not Partitionable.
--
--   The shared natural-number, payload and record codes are declared in Reports so that parser validation measures exactly the same bits.
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), §3.7, pp. 17–18; Theorem 1, p. 3

import Mathlib
import Definitions.Def_CharonChurn_Main_Reports
import Definitions.Def_CharonChurn_Main_Decision

namespace CharonChurn.Main

/-! # Binary encoding of the decision input (§3.7, pp. 17–18; Theorem 1, p. 3)

The polynomial-computation clause of Theorem 1 is measured in the length of this encoding of the
public context and the retained evidence. Every natural number (identities, rounds, session,
parameters) is written in binary, so no `O(log n)` bound on identifier lengths is assumed. -/

/-- The retained cache listed in increasing canonical key order. -/
noncomputable def sortedCache (C : Finset Record) : List Record := by
  classical
  exact C.toList.mergeSort (fun a b => decide (a.key ≤ b.key))

/-- Code of the whole decision input: `n, D, t`, session, `s, e`, the eligibility bit and the
retained evidence. -/
noncomputable def encodeInput (I : DecisionInput) : List Bool :=
  encNat I.n ++ encNat I.D ++ encNat I.t ++ encNat I.sid ++ encNat I.s ++ encNat I.e ++
    [I.eligible] ++ encList encRecord (sortedCache I.cache)

/-- The decision as a Boolean (`true` = Not Partitionable). -/
noncomputable def decisionBool (I : DecisionInput) : Bool := by
  classical
  exact decide (I.verdict = Verdict.notPartitionable)

end CharonChurn.Main


