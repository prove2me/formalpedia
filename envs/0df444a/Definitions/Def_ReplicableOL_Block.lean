-- Prove2me | Definitions.Def_ReplicableOL_Block
-- name    : ReplicableOL_Block
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:15.158648+00:00
-- url     : https://prove2.me/theorems/d9d277ac-daa8-49e7-87a0-566bd258ce74
-- title:
--   An epoch block $s\in\{0,1\}^L$
-- statement:
--   The bits of one epoch of Construction C, $s\in\{0,1\}^L$.
--
--   **Formalization Note** `true` is the bit `1`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib

namespace ReplicableOL

/-- **An epoch block $s\in\{0,1\}^L$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. A block `s = (s_1, …, s_L) ∈ {0,1}^L`.

**Formalization Note.** `true` is the bit `1`. -/
abbrev Block (L : ℕ) : Type := Fin L → Bool

end ReplicableOL


