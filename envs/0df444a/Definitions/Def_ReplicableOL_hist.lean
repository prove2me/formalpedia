-- Prove2me | Definitions.Def_ReplicableOL_hist
-- name    : ReplicableOL_hist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:18.329565+00:00
-- url     : https://prove2.me/theorems/86511083-7f5f-44ca-94b6-aad1d5284963
-- title:
--   The prefix $S_{<j}$ of blocks
-- statement:
--   The data $S_{<j}$ of the epochs before epoch $j$.
--
--   **Formalization Note** 0-based epochs: the entries are indexed by `Fin j`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib
import Definitions.Def_ReplicableOL_Bits

namespace ReplicableOL

/-- **The prefix $S_{<j}$ of blocks.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `S_{<j}`: the blocks of the epochs before `j`.

**Formalization Note.** 0-based epochs: the entries are indexed by `Fin j`. -/
def hist {k L : ℕ} (S : Bits k L) (j : Fin k) : Fin j → Block L :=
  fun i => S ⟨i, i.2.trans j.2⟩

end ReplicableOL


