-- Prove2me | Definitions.Def_ReplicableOL_Supplement_Kbar
-- name    : ReplicableOL_Supplement_Kbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:19:12.03858+00:00
-- url     : https://prove2.me/theorems/2632f56f-ca3b-4881-a567-0fe67d11455f
-- title:
--   $\bar K=\lceil\log_2\log_2 T\rceil$
-- statement:
--   The number
--
--   $$
--   \bar K=\lceil \log_2\log_2 T\rceil ,
--   $$
--
--   an upper bound on the number of levels of the chain of Theorem 3.
--
--   **Formalization Note** Computed as `Nat.ceil` of the iterated real base-$2$ logarithm; it agrees with the integer ceiling whenever $T>2$. The theorems that use it assume $\bar K\ge1$, the case in which the paper's parameters are defined.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 3 (with parameters), p.20

import Mathlib

namespace ReplicableOL.Supplement

/-- **$\bar K = \lceil \log_2\log_2 T\rceil$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 3 (with parameters), p.20.

**Formalization Note.** `Nat.ceil` of the iterated real `log₂`; it equals the integer ceiling whenever `log₂ log₂ T > 0`, i.e. `T > 2`. Theorems using it assume `1 ≤ K̄` (see their notes). -/
noncomputable def Kbar (T : ℕ) : ℕ := ⌈Real.logb 2 (Real.logb 2 T)⌉₊

end ReplicableOL.Supplement


