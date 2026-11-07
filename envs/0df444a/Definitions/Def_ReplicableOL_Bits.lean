-- Prove2me | Definitions.Def_ReplicableOL_Bits
-- name    : ReplicableOL_Bits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:16.896763+00:00
-- url     : https://prove2.me/theorems/45eab4cf-ac29-4676-ac13-4c8cb2859af7
-- title:
--   The bits of all epochs
-- statement:
--   The sequence of blocks $(S_1,\dots,S_k)$. Fixed-seed statements are finite sums over this set.
--
--   **Formalization Note** The trailing rounds carry no randomness, so at a fixed `θ` a sequence is determined by these bits.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_Block

namespace ReplicableOL

/-- **The bits of all epochs.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. `S = (S_1, …, S_k)`, the epoch blocks.

**Formalization Note.** The trailing rounds carry no randomness, so at a fixed `θ` a sequence is determined by these bits. -/
abbrev Bits (k L : ℕ) : Type := Fin k → Block L

end ReplicableOL


