-- Prove2me | Definitions.Def_ReplicableOL_EpochRule
-- name    : ReplicableOL_EpochRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:19.6826+00:00
-- url     : https://prove2.me/theorems/7b3eaa3c-f0a8-48ac-9e26-64402c0d64b7
-- title:
--   An epoch rule $\Phi_j(h;s)$
-- statement:
--   An **epoch rule** assigns to each epoch $j$, each prefix $h$ of earlier blocks and each block $s$ of the current epoch an action string in $\{1,2\}^L$. Actions of earlier epochs do not read later data (epoch-level causality), but within an epoch the rule may read the whole block: this is the setting of Theorem 2.
--
--   **Formalization Note** 0-based epochs; Lean's action `0` is the paper's expert 1. An arbitrary function of this type encodes (H2) and epoch-level causality at a fixed seed: the rule of epoch `j` reads only the blocks before `j` and the block `j`. Measurability is automatic on this finite space.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_Block

namespace ReplicableOL

/-- **An epoch rule $\Phi_j(h;s)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. `Φ_j(h; s) ∈ {1,2}^L` is the epoch-`j` action string that the learner produces from the prefix `h` and the block `s`, at a fixed seed.

**Formalization Note.** 0-based epochs; Lean's action `0` is the paper's expert 1. An arbitrary function of this type encodes (H2) and epoch-level causality at a fixed seed: the rule of epoch `j` reads only the blocks before `j` and the block `j`. Measurability is automatic on this finite space. -/
abbrev EpochRule (k L : ℕ) : Type := (j : Fin k) → (Fin j → Block L) → Block L → (Fin L → Fin 2)

end ReplicableOL


