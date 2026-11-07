-- Prove2me | Definitions.Def_ReplicableOL_M
-- name    : ReplicableOL_M
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:16.942207+00:00
-- url     : https://prove2.me/theorems/1cea0e6a-a379-48d1-a75f-da1d492e05cf
-- title:
--   Agreement indicator $M_j$
-- statement:
--   The indicator $M_j$ that two runs with the same seed, on data $S,S'$, have played the same action strings through epoch $j$; $M_0=1$.
--
--   **Formalization Note** `M Φ j S S'` (`j : ℕ`) is the indicator that the action strings agree on the 0-based epochs before `j`. So Lean's `M Φ j` is the paper's `M_{j−1}` for the paper's epoch `j + 1`, and `M Φ k` is the paper's `M_k`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8; Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_EpochRule
import Definitions.Def_ReplicableOL_Bits
import Definitions.Def_ReplicableOL_hist

namespace ReplicableOL

/-- **Agreement indicator $M_j$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8; Sec. 4.1, p.15. `M_j := 1{the runs agree through epoch j}`, with `M_0 := 1`.

**Formalization Note.** `M Φ j S S'` (`j : ℕ`) is the indicator that the action strings agree on the 0-based epochs before `j`. So Lean's `M Φ j` is the paper's `M_{j−1}` for the paper's epoch `j + 1`, and `M Φ k` is the paper's `M_k`. -/
noncomputable def M {k L : ℕ} (Φ : EpochRule k L) (j : ℕ) (S S' : Bits k L) : ℝ :=
  if ∀ i : Fin k, i.val < j → Φ i (hist S i) (S i) = Φ i (hist S' i) (S' i) then 1 else 0

end ReplicableOL


